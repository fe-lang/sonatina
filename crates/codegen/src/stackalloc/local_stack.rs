use super::{Action, Actions};
use crate::{bitset::BitSet, liveness::Liveness};
use if_chain::if_chain;
use smallvec::{smallvec, SmallVec};
use sonatina_ir::{DataFlowGraph, Immediate, Value};
use std::collections::{HashMap, VecDeque};

pub type MemSlot = SmallVec<[Value; 4]>;

#[derive(Clone, Default, Debug)]
pub struct LocalStack {
    stack: VecDeque<Value>,
    dead: BitSet<Value>,
}
impl LocalStack {
    // Initialize stack with given `vals`, in order (ie, first element of `vals`
    // is on top of stack).
    pub fn with_values(vals: &[Value]) -> Self {
        Self {
            stack: VecDeque::from_iter(vals.iter().copied()),
            dead: BitSet::new(),
        }
    }

    pub fn push_bottom(&mut self, val: Value) {
        self.stack.push_back(val)
    }
    pub fn force_rotate_up(&mut self, index: usize) {
        let val = self.stack.remove(index).unwrap();
        self.stack.push_front(val);
    }

    /// "Rename" the value in a given stack slot; for phi values.
    /// Panics if slot >= stack.len().
    pub fn rename_slot(&mut self, slot: usize, val: Value) {
        self.stack[slot] = val;
    }

    // fn contains_in_range(&self, val: Value, range: Range<usize>) -> bool {
    //     self.stack.range(range).
    // }

    fn first_dead(&self) -> Option<usize> {
        self.stack.iter().position(|v| self.dead.contains(*v))
    }

    fn push(&mut self, act: &mut Actions, val: Value, imm: Immediate) {
        self.stack.push_front(val);
        act.push(Action::Push(imm));
    }

    /// Exchange 0th and nth items
    fn swap(&mut self, act: &mut Actions, n: usize) {
        assert!(n <= 16);
        act.push(Action::StackSwap(n as u8));
        self.stack.swap(0, n);
    }

    fn swap_m_n(&mut self, act: &mut Actions, m: usize, n: usize) {
        assert!(m <= 16 && n <= 16);
        if m == 0 {
            self.swap(act, n);
        } else if n == 0 {
            self.swap(act, m);
        } else {
            self.swap(act, n);
            self.swap(act, m);
            self.swap(act, n);
        }
    }

    // xxx 0 vs 1 indexing of swap and dup
    /// Push a copy of the n-1th item onto the stack
    fn dup(&mut self, act: &mut Actions, n: usize) {
        assert!(n <= 16);
        act.push(Action::StackDup(n as u8));
        self.stack.push_front(self.stack[n]);
    }

    fn pop(&mut self, act: &mut Actions) {
        act.push(Action::Pop);
        self.stack.pop_front();
    }

    fn remove_leading_deads(&mut self, act: &mut Actions) {
        while let Some(v) = self.stack.front() {
            if self.dead.contains(*v) {
                self.pop(act)
            } else {
                break;
            }
        }
    }

    fn pop_all(&mut self, act: &mut Actions) {
        while !self.stack.is_empty() {
            self.pop(act);
        }
    }

    /// Ensure `out` is atop an otherwise empty stack. // xxx name
    pub fn ret(&mut self, act: &mut Actions, memory: &[MemSlot], val: Option<Value>) {
        if let Some(val) = val {
            while let Some(v) = self.stack.front() {
                if val != *v {
                    self.pop(act);
                } else if self.stack.len() > 1 {
                    // If there are vals below the return val,
                    // swap the return val downward and pop the rest off.
                    self.swap(act, 16.min(self.stack.len() - 1));
                } else {
                    break;
                }
            }
            if self.stack.is_empty() {
                for (idx, slot) in memory.iter().enumerate() {
                    if slot.contains(&val) {
                        act.push(Action::MemLoadFrameSlot(idx as u32));
                        return;
                    }
                }
            }
        } else {
            self.pop_all(act);
        }
    }

    pub fn move_to_top(
        &mut self,
        args: &[Value],
        last_use: &BitSet<Value>,
        act: &mut Actions,
        memory: &mut Vec<MemSlot>,
        dfg: &DataFlowGraph,
        liveness: &Liveness,
    ) {
        self.remove_leading_deads(act);

        let consumable: BitSet<Value> = args
            .iter()
            .copied()
            .filter(|a| {
                last_use.contains(*a)
                    || self.stack.iter().filter(|v| *v == a).count() > 1
                    || memory_slot_of(*a, memory).is_some()
                    || dfg.is_imm(*a)
            })
            .collect();

        // if there are deads following the top val, swap it down and pop them off
        let swap_to = self
            .stack
            .iter()
            .skip(1)
            .take_while(|v| self.dead.contains(**v))
            .count();
        if swap_to > 0 {
            self.swap(act, swap_to);
            self.remove_leading_deads(act);
        }

        // if the top val isn't used by this insn...
        if let Some(v) = self.stack.front() {
            if !args.contains(v) {
                if_chain! {
                    if let Some(last) = args.last();
                    if consumable.contains(*last);
                    if let ValueLocation::Stack(pos) = self.location_of(*last, memory, dfg);
                    then {
                        // ... swap it with the last arg value.
                        self.swap(act, pos);
                    } else {
                        if let Some(pos) = self.first_dead() {
                            // ... or swap it down to a dead slot.
                            self.swap(act, pos);
                            self.pop(act);
                        }
                    }
                }
            }
        }

        let all_consumable = args.iter().all(|a| consumable.contains(*a));
        if all_consumable && args.iter().eq(self.stack.iter().take(args.len())) {
            // happy case: all vals are at top of stack, in order
        } else if all_consumable && args.iter().rev().eq(self.stack.iter().take(args.len())) {
            // all vals are at top of stack, but in reverse order
            for swap in reverse(args.len() as u8) {
                self.swap(act, swap as usize);
            }

            // TODO: other cases where we can do better than duping all args
        } else {
            // Default behavior: dupe all args to the top.

            // If any args are unreachable in the stack, try to remove enough
            // unnecessary values from the stack to make them reachable.

            while args.iter().any(|&v| self.is_buried(v, memory, dfg)) {
                if !self.shrink_stack(act, memory, dfg, |v| !args.contains(&v)) {
                    break;
                }
            }

            // TODO: duplicate any immediates that are used again this block
            for (idx, val) in args.iter().copied().rev().enumerate() {
                match self.location_of(val, memory, dfg) {
                    ValueLocation::Immediate(imm) => {
                        self.push(act, val, imm);
                    }
                    ValueLocation::Stack(pos) => {
                        if pos == 0 && consumable.contains(val) {
                            // do nothing
                        } else if idx == 0 && consumable.contains(val) {
                            // last arg is consumable; swap it up.
                            self.swap(act, pos)
                        } else if pos == 1
                            && args.last() == Some(&self.stack[0])
                            && consumable.contains(val)
                        {
                            // stack is [prev_arg, this_arg, ..]; swap.
                            self.swap(act, 1);
                        } else if pos >= 16 {
                            // Value is unreachable in the stack, so we allocate
                            // a slot for the value in the stack. At the val def
                            // point, we'll duplicate it and store it in this
                            // slot, while leaving a copy on the stack.
                            let slot = allocate_slot(memory, val, liveness);
                            act.push(Action::MemLoadFrameSlot(slot as u32));
                            self.stack.push_front(val);
                        } else {
                            self.dup(act, pos);
                        }
                    }
                    ValueLocation::Memory(pos) => {
                        act.push(Action::MemLoadFrameSlot(pos as u32));
                        self.stack.push_front(val);
                    }
                    ValueLocation::Nowhere => {
                        panic!("{val:?} not found on stack or in memory");
                    }
                }
            }
        }
        // pop consumed args off stack, and mark other copies as dead
        self.dead.union_with(last_use);
    }

    pub fn step(
        &mut self,
        args: &[Value],
        consumable: &BitSet<Value>,
        result: Option<Value>,
        act: &mut Actions,
        memory: &mut Vec<MemSlot>,
        dfg: &DataFlowGraph,
        liveness: &Liveness,
    ) {
        self.move_to_top(args, consumable, act, memory, dfg, liveness);
        for _ in args {
            self.stack.pop_front();
        }
        if let Some(res) = result {
            self.stack.push_front(res);
        }
    }

    fn shrink_stack<F>(
        &mut self,
        act: &mut Actions,
        memory: &[MemSlot],
        dfg: &DataFlowGraph,
        poppable: F,
    ) -> bool
    where
        F: Fn(Value) -> bool,
    {
        // TODO: prioritize popping deads
        if let Some(pos) = self.stack.iter().take(16).position(|v| {
            poppable(*v)
                && (self.dead.contains(*v)
                    || dfg.is_imm(*v)
                    || memory_slot_of(*v, memory).is_some())
        }) {
            self.swap(act, pos);
            self.pop(act);
            true
        } else {
            false
        }
    }

    pub fn reconcile_with(
        &mut self,
        act: &mut Actions,
        other: &LocalStack,
        live: &BitSet<Value>,
        skip: usize,
    ) {
        if self
            .stack
            .iter()
            .skip(skip)
            .zip(other.stack.iter().skip(skip))
            .all(|(a, b)| a == b || (!live.contains(*a) && !live.contains(*b)))
        {
            return; // hooray
        }

        if self.stack.len() == other.stack.len()
            && items_not_in_set(self.stack.iter().copied().skip(skip), live)
                == items_not_in_set(other.stack.iter().copied().skip(skip), live)
        {
            // Same (non-dead) items, different order
            let target: HashMap<Value, usize> = other
                .stack
                .iter()
                .copied()
                .enumerate()
                .skip(skip)
                .filter(|(_, v)| live.contains(*v))
                .map(|(i, v)| (v, i))
                .collect();

            for i in skip..self.stack.len() {
                let v = self.stack[i];
                if !live.contains(v) {
                    continue;
                }
                if target[&v] != i {
                    self.swap_m_n(act, i, target[&v]);
                }
            }
            assert!(self
                .stack
                .iter()
                .skip(skip)
                .zip(other.stack.iter().skip(skip))
                .all(|(a, b)| a == b || (!live.contains(*a) && !live.contains(*b))));
        } else {
            todo!("reconcile stacks of different length")
        }
    }

    fn is_buried(&self, val: Value, memory: &[MemSlot], dfg: &DataFlowGraph) -> bool {
        if let ValueLocation::Stack(pos) = self.location_of(val, memory, dfg) {
            pos >= 16
        } else {
            false
        }
    }

    fn location_of(&self, val: Value, memory: &[MemSlot], dfg: &DataFlowGraph) -> ValueLocation {
        if let Some(pos) = self.stack.iter().position(|v| *v == val) {
            // If item is buried, check if it's imm or in memory
            if pos >= 16 {
                if let Some(imm) = dfg.value_imm(val) {
                    return ValueLocation::Immediate(imm);
                } else if let Some(pos) = memory_slot_of(val, memory) {
                    return ValueLocation::Memory(pos);
                }
            }
            ValueLocation::Stack(pos)
        } else if let Some(pos) = memory_slot_of(val, memory) {
            ValueLocation::Memory(pos)
        } else if let Some(imm) = dfg.value_imm(val) {
            ValueLocation::Immediate(imm)
        } else {
            ValueLocation::Nowhere
        }
    }
}

enum ValueLocation {
    Immediate(Immediate),
    Stack(usize),
    Memory(usize),
    Nowhere,
}

fn items_not_in_set(stack: impl Iterator<Item = Value>, set: &BitSet<Value>) -> BitSet<Value> {
    stack.filter(|v| !set.contains(*v)).collect()
}

pub fn memory_slot_of(val: Value, memory: &[MemSlot]) -> Option<usize> {
    memory.iter().position(|vs| vs.contains(&val))
}

fn allocate_slot(mem: &mut Vec<MemSlot>, val: Value, liveness: &Liveness) -> usize {
    for (i, slot) in mem.iter_mut().enumerate() {
        if slot_can_hold(slot, val, liveness) {
            slot.push(val);
            return i;
        }
    }
    mem.push(smallvec![val]);
    mem.len() - 1
}

fn slot_can_hold(slot: &[Value], val: Value, liveness: &Liveness) -> bool {
    // xxx use insn-level liveness for single-block conflict case
    let live = &liveness.val_live_blocks[val];
    slot.iter()
        .all(|v| live.is_disjoint(&liveness.val_live_blocks[*v]))
}

/// Generate SWAP operations required to reverse the top `n` items of the stack
fn reverse(n: u8) -> SmallVec<[u8; 8]> {
    let mut swaps = smallvec![];
    for i in 1..n / 2 + 1 {
        swaps.push(n - i);
        if i < n - i - 1 {
            swaps.push(i);
        }
    }
    for i in (1..n / 2).rev() {
        swaps.push(i);
    }
    swaps
}

// xxx
// #[test]
// fn test_reverse() {
//     assert_eq!(reverse(2), vec![1]);
//     assert_eq!(reverse(3), vec![2]);
//     assert_eq!(reverse(4), vec![3, 1, 2, 1]);
//     assert_eq!(reverse(5), vec![4, 1, 3, 1]);
//     assert_eq!(reverse(6), vec![5, 1, 4, 2, 3, 2, 1]);
//     assert_eq!(reverse(7), vec![6, 1, 5, 2, 4, 2, 1]);
//     assert_eq!(reverse(8), vec![7, 1, 6, 2, 5, 3, 4, 3, 2, 1]);
//     assert_eq!(reverse(9), vec![8, 1, 7, 2, 6, 3, 5, 3, 2, 1]);
//     assert_eq!(reverse(10), vec![9, 1, 8, 2, 7, 3, 6, 4, 5, 4, 3, 2, 1]);
//     assert_eq!(reverse(11), vec![10, 1, 9, 2, 8, 3, 7, 4, 6, 4, 3, 2, 1]);
// }
