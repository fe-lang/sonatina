use super::{Action, Actions};
use crate::{bitset::BitSet, liveness::Liveness};
use if_chain::if_chain;
use smallvec::{smallvec, SmallVec};
use sonatina_ir::{DataFlowGraph, Immediate, ValueId};
use std::{collections::VecDeque, fmt};

pub type MemSlot = SmallVec<[ValueId; 4]>;

const REACH: usize = 16;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum StackEntry {
    Live(ValueId),
    // xxx Frozen(ValueId),
    ReturnJumpTarget,
    Junk,
}

// xxx rename
#[derive(Clone, Default)]
pub struct LocalStack {
    stack: VecDeque<StackEntry>,
    dead: BitSet<ValueId>,

    /// `usize` is reverse index (position relative to bottom of stack).
    /// Eg. [a, b, c] freeze(a)
    ///     [2, 1, 0] ridxs
    ///     is_frozen(0) => len - 1 - 0 == 3
    frozen: SmallVec<[(usize, ValueId); 2]>,
}
impl LocalStack {
    /// Initialize stack with given `vals`, in order (ie, first element of `vals`
    /// is on top of stack).
    pub fn with_values(vals: &[ValueId]) -> Self {
        Self {
            stack: VecDeque::from_iter(vals.iter().copied().map(StackEntry::Live)),
            dead: BitSet::new(),
            frozen: SmallVec::default(),
        }
    }

    pub fn force_pop(&mut self) {
        self.stack.pop_front();
    }

    /// "Rename" the value in a given stack slot; for phi values.
    /// Panics if slot >= stack.len().
    pub fn rename_slot(&mut self, slot: usize, val: ValueId) {
        debug_assert!(!self.is_frozen(slot));
        debug_assert!(matches!(self.stack[slot], StackEntry::Live(_)));
        self.stack[slot] = StackEntry::Live(val);
    }

    pub fn freeze(&mut self, mut values: BitSet<ValueId>) {
        if values.is_empty() {
            self.unfreeze();
            return;
        }

        // We only freeze the bottommost instance of each value.
        for (ridx, val) in self.stack.iter_mut().rev().enumerate() {
            if let StackEntry::Live(val) = val {
                if values.remove(*val) {
                    self.frozen.push((ridx, *val));
                }
            }
        }
    }

    pub fn unfreeze(&mut self) {
        self.frozen.clear();
    }

    fn is_frozen(&self, slot: usize) -> bool {
        debug_assert!(self.stack.len() > slot);

        self.frozen
            .iter()
            .any(|(ridx, _)| *ridx == self.stack.len() - 1 - slot)
    }

    fn top(&self) -> Option<StackEntry> {
        self.stack.front().copied()
    }

    fn top_n(&self, n: usize) -> impl Iterator<Item = &'_ StackEntry> + '_ {
        self.stack.iter().take(n)
    }

    fn top_n_is(&self, n: usize, iter: &mut dyn Iterator<Item = &ValueId>) -> bool {
        self.stack
            .iter()
            .take(n)
            .copied()
            .eq(iter.map(|v| StackEntry::Live(*v)))
    }

    fn first_reachable_dead(&self) -> Option<usize> {
        self.position_within_reach(|v| self.dead.contains(v))
    }

    fn push(&mut self, act: &mut Actions, val: ValueId, imm: Immediate) {
        self.stack.push_front(StackEntry::Live(val));
        act.push(Action::Push(imm));
    }

    /// Exchange 0th and nth items
    fn swap(&mut self, act: &mut Actions, n: usize) {
        if n == 0 {
            return; // No-op
        }
        debug_assert!(n <= REACH);
        // xxx relax this (for temporary swaps)
        debug_assert!(!self.is_frozen(0));
        debug_assert!(!self.is_frozen(n));

        act.push(Action::StackSwap(n as u8));
        self.stack.swap(0, n);
    }

    // xxx remove?
    // fn swap_m_n(&mut self, act: &mut Actions, m: usize, n: usize) {
    //     assert!(m <= REACH && n <= REACH);
    //     if m == 0 {
    //         self.swap(act, n);
    //     } else if n == 0 {
    //         self.swap(act, m);
    //     } else {
    //         self.swap(act, n);
    //         self.swap(act, m);
    //         self.swap(act, n);
    //     }
    // }

    // xxx 0 vs 1 indexing of swap and dup
    /// Push a copy of the n-1th item onto the stack
    fn dup(&mut self, act: &mut Actions, n: usize) {
        debug_assert!(n <= REACH);
        let v = self.stack[n];
        self.stack.push_front(v);
        act.push(Action::StackDup(n as u8));
    }

    /// Panics if stack is empty, or if top entry is frozen.
    fn pop(&mut self, act: &mut Actions) {
        debug_assert!(!self.is_frozen(0));
        self.stack.pop_front().unwrap();
        act.push(Action::Pop);
    }

    fn pop_while<F>(&mut self, act: &mut Actions, pred: F)
    where
        F: Fn(ValueId, &Self) -> bool,
    {
        while let Some(val) = self.stack.front() {
            if match val {
                StackEntry::Live(val) => pred(*val, self),
                StackEntry::Junk => true,
                StackEntry::ReturnJumpTarget => false,
            } {
                self.pop(act);
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

    // xxx rename/remove?
    pub fn push_jump_target(&mut self) {
        self.stack.push_front(StackEntry::ReturnJumpTarget);
    }
    pub fn pop_jump_target(&mut self) {
        assert_eq!(self.stack.pop_front(), Some(StackEntry::ReturnJumpTarget));
    }

    /// Ensure `out` is atop an otherwise empty stack. // xxx name
    pub fn ret(&mut self, act: &mut Actions, memory: &[MemSlot], return_val: Option<ValueId>) {
        let Some(return_val) = return_val else {
            self.pop_all(act);
            return;
        };

        while let Some(val) = self.stack.front() {
            if *val != StackEntry::Live(return_val) {
                self.pop(act);
            } else if self.stack.len() > 1 {
                // If there are vals below the return val,
                // swap the return val downward and pop the rest off.
                self.swap(act, REACH.min(self.stack.len() - 1));
            } else {
                break;
            }
        }
        if self.stack.is_empty() {
            for (idx, slot) in memory.iter().enumerate() {
                if slot.contains(&return_val) {
                    act.push(Action::MemLoadFrameSlot(idx as u32));
                    return;
                }
            }
            panic!("return value not found");
        }
    }

    fn clean_top_of_stack<F>(&mut self, act: &mut Actions, pred: F)
    where
        F: Fn(ValueId, &Self) -> bool,
    {
        self.pop_while(act, &pred);

        if !self.stack.is_empty() && self.is_frozen(0) {
            return;
        }

        // if there are deads following the top val, swap it down and pop them off
        // xxx only within REACH
        let swap_to = self
            .stack
            .iter()
            .skip(1)
            .take_while(|e| match e {
                StackEntry::Live(v) => pred(*v, self),
                StackEntry::ReturnJumpTarget => false,
                StackEntry::Junk => true,
            })
            .count();

        if swap_to > 0 {
            self.swap(act, swap_to);
            self.pop_while(act, pred);
        }
    }

    pub fn xxx_branch_prep(
        &mut self,
        arg: ValueId,
        last_use: bool,
        act: &mut Actions,
        memory: &mut Vec<MemSlot>,
        dfg: &DataFlowGraph,
        liveness: &Liveness,
    ) {
        // xxx is `dead` complete here?
        self.clean_top_of_stack(act, |val, zelf| zelf.dead.contains(val));

        let consumable = last_use
            || self
                .stack
                .iter()
                .filter(|v| **v == StackEntry::Live(arg))
                .count()
                > 1
            || memory_slot_of(arg, memory).is_some()
            || dfg.value_is_imm(arg);

        match self.location_of(arg, memory, dfg) {
            ValueLocation::Stack(pos) => {
                if pos >= REACH {
                    // ValueId is unreachable in the stack, so we allocate
                    // a slot for the value in memory. At the val def
                    // point, we'll duplicate it and store it in this
                    // slot, while leaving a copy on the stack.
                    let slot = allocate_slot(memory, arg, liveness);
                    act.push(Action::MemLoadFrameSlot(slot as u32));
                    self.stack.push_front(StackEntry::Live(arg));
                } else if !consumable {
                    self.dup(act, pos);
                } else if !self.is_frozen(0) {
                    // if pos is 0, no swap op is emitted
                    self.swap(act, pos);
                } else {
                    self.dup(act, pos)
                }
            }
            ValueLocation::Immediate(imm) => {
                self.push(act, arg, imm);
            }
            ValueLocation::Memory(pos) => {
                act.push(Action::MemLoadFrameSlot(pos as u32));
                self.stack.push_front(StackEntry::Live(arg));
            }
            ValueLocation::Nowhere => {
                panic!("{arg:?} not found on stack or in memory");
            }
        }
    }

    pub fn move_to_top(
        &mut self,
        args: &[ValueId],
        last_use: &BitSet<ValueId>,
        act: &mut Actions,
        memory: &mut Vec<MemSlot>,
        dfg: &DataFlowGraph,
        liveness: &Liveness,
    ) {
        self.clean_top_of_stack(act, |val, zelf| zelf.dead.contains(val));

        let consumable: BitSet<ValueId> = args
            .iter()
            .copied()
            .filter(|a| {
                last_use.contains(*a)
                // We allow a val to be consumed if the stack contains
                // any additional copies, even if buried.
                    || self.stack.iter().filter(|e| **e == StackEntry::Live(*a)).count() > 1
                    || memory_slot_of(*a, memory).is_some()
                    || dfg.value_is_imm(*a)
            })
            .collect();

        // if the top val isn't used by this insn...
        if let Some(StackEntry::Live(top)) = self.stack.front() {
            // xxx consider case where top entry is a jump target we just pushed on
            if !args.contains(top) {
                if_chain! {
                    if let Some(last) = args.last();
                    if consumable.contains(*last);
                    if let ValueLocation::Stack(pos) = self.location_of(*last, memory, dfg);
                    then {
                        // ... swap it with the last arg value.
                        self.swap(act, pos);
                    } else {
                        if let Some(pos) = self.first_reachable_dead() {
                            // ... or swap it down to a dead slot.
                            self.swap(act, pos);
                            self.pop(act);
                        }
                    }
                }
            }
        }

        let all_consumable = args.iter().all(|a| consumable.contains(*a));
        if all_consumable && self.top_n_is(args.len(), &mut args.iter()) {
            // happy case: all vals are at top of stack, in order
        } else if all_consumable && self.top_n_is(args.len(), &mut args.iter().rev()) {
            // xxx if args.len() == 2 and insn commutes, do nothing
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
                            && self.top() == args.last().map(|a| StackEntry::Live(*a))
                            && consumable.contains(val)
                        {
                            // stack is [prev_arg, this_arg, ..]; swap.
                            self.swap(act, 1);
                        } else if pos >= REACH {
                            // ValueId is unreachable in the stack, so we allocate
                            // a slot for the value in the stack. At the val def
                            // point, we'll duplicate it and store it in this
                            // slot, while leaving a copy on the stack.
                            let slot = allocate_slot(memory, val, liveness);
                            act.push(Action::MemLoadFrameSlot(slot as u32));
                            self.stack.push_front(StackEntry::Live(val));
                        } else {
                            self.dup(act, pos);
                        }
                    }
                    ValueLocation::Memory(pos) => {
                        act.push(Action::MemLoadFrameSlot(pos as u32));
                        self.stack.push_front(StackEntry::Live(val));
                    }
                    ValueLocation::Nowhere => {
                        panic!("{val:?} not found on stack or in memory");
                    }
                }
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub fn step(
        &mut self,
        args: &[ValueId],
        last_use: &BitSet<ValueId>,
        result: Option<ValueId>,
        act: &mut Actions,
        memory: &mut Vec<MemSlot>,
        dfg: &DataFlowGraph,
        liveness: &Liveness,
    ) {
        self.move_to_top(args, last_use, act, memory, dfg, liveness);

        // pop consumed args off stack, and mark other copies as dead
        for _ in args {
            self.stack.pop_front();
        }
        self.dead.union_with(last_use);

        // xxx assert that the current insn is a call
        if self.stack.front() == Some(&StackEntry::ReturnJumpTarget) {
            self.stack.pop_front();
        }

        if let Some(res) = result {
            self.stack.push_front(StackEntry::Live(res));
        }
    }

    /// Remove all dead values from unfrozen portion of stack,
    /// leaving any `args` values at the top, and any
    /// `live_out` values at the bottom.
    /// Args must be moved to the top before calling `retain`.
    /// xxx rework this. don't require args to be at top
    pub fn retain(&mut self, act: &mut Actions, args: &[ValueId], live_out: &BitSet<ValueId>) {
        debug_assert!(self.top_n_is(args.len(), &mut args.iter()));

        self.clean_top_of_stack(act, |val, _| {
            !args.contains(&val) && !live_out.contains(val)
        });

        // xxx
        // while let Some(mut pos) = self
        //     .stack
        //     .iter()
        //     .take(REACH)
        //     .skip(args.len())
        //     .position(|e| !live_out.contains(e.val))
        // {
        //     pos += args.len();

        //     self.swap(act, pos);
        //     eprintln!("swapped {:?} {:?}", &self, act);

        //     self.remove_leading_deads(act);
        //     eprintln!("popped  {:?} {:?}", &self, act);

        //     if args.len() > 1 {
        //         // Swap first arg back to the top, so the args don't get shuffled
        //         debug_assert_eq!(self.stack.get(pos - 1).map(|e| &e.val), args.first());
        //         self.swap(act, pos - 1);
        //     }
        // }

        // xxx remove
        // if let Some(arg) = args.first() {
        //     let pos = self
        //         .position_within_reach(|v| v == *arg)
        //         .expect("`retain` arg must be reachable");
        //     self.swap(act, pos);
        // }
    }

    fn position_within_reach<F>(&self, mut predicate: F) -> Option<usize>
    where
        F: FnMut(ValueId) -> bool,
    {
        self.top_n(REACH).copied().position(|e| {
            if let StackEntry::Live(v) = e {
                predicate(v)
            } else {
                false
            }
        })
    }

    fn shrink_stack<F>(
        &mut self,
        act: &mut Actions,
        memory: &[MemSlot],
        dfg: &DataFlowGraph,
        poppable: F,
    ) -> bool
    where
        F: Fn(ValueId) -> bool,
    {
        // TODO: prioritize popping deads
        let Some(pos) = self.position_within_reach(|v| {
            poppable(v)
                && (self.dead.contains(v)
                    || dfg.value_is_imm(v)
                    || memory_slot_of(v, memory).is_some())
        }) else {
            return false;
        };

        self.swap(act, pos);
        self.pop(act);
        true
    }

    fn is_buried(&self, val: ValueId, memory: &[MemSlot], dfg: &DataFlowGraph) -> bool {
        if let ValueLocation::Stack(pos) = self.location_of(val, memory, dfg) {
            pos >= REACH
        } else {
            false
        }
    }

    fn location_of(&self, val: ValueId, memory: &[MemSlot], dfg: &DataFlowGraph) -> ValueLocation {
        if let Some(pos) = self.stack.iter().position(|e| *e == StackEntry::Live(val)) {
            // If item is buried, check if it's imm or in memory
            if pos >= REACH {
                if let Some(imm) = dfg.value_imm(val) {
                    return ValueLocation::Immediate(imm);
                } else if let Some(pos) = memory_slot_of(val, memory) {
                    return ValueLocation::Memory(pos);
                }
            }
            ValueLocation::Stack(pos)
        } else if let Some(imm) = dfg.value_imm(val) {
            ValueLocation::Immediate(imm)
        } else if let Some(pos) = memory_slot_of(val, memory) {
            ValueLocation::Memory(pos)
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

pub fn memory_slot_of(val: ValueId, memory: &[MemSlot]) -> Option<usize> {
    memory.iter().position(|vs| vs.contains(&val))
}

fn allocate_slot(mem: &mut Vec<MemSlot>, val: ValueId, liveness: &Liveness) -> usize {
    for (i, slot) in mem.iter_mut().enumerate() {
        if slot_can_hold(slot, val, liveness) {
            slot.push(val);
            return i;
        }
    }
    mem.push(smallvec![val]);
    mem.len() - 1
}

fn slot_can_hold(slot: &[ValueId], val: ValueId, liveness: &Liveness) -> bool {
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

impl fmt::Debug for LocalStack {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        let mut pref = "";
        for (idx, val) in self.stack.iter().enumerate() {
            write!(f, "{pref}")?;
            match val {
                StackEntry::Live(val) => {
                    if self.dead.contains(*val) {
                        write!(f, "dead({})", val.as_u32())?;
                    } else if self.is_frozen(idx) {
                        write!(f, "frozen({})", val.as_u32())?;
                    } else {
                        write!(f, "{}", val.as_u32())?;
                    }
                }
                StackEntry::ReturnJumpTarget => write!(f, "jump target")?,
                StackEntry::Junk => write!(f, "junk!")?,
            }
            pref = ", ";
        }
        write!(f, "]")
    }
}

#[cfg(test)]
mod tests {
    use std::collections::VecDeque;

    use super::BitSet;
    use sonatina_ir::ValueId;

    use crate::stackalloc::{local_stack::StackEntry, Actions};

    use super::{reverse, LocalStack};

    #[test]
    fn test_reverse() {
        assert_eq!(reverse(2).as_slice(), [1].as_slice());
        assert_eq!(reverse(3).as_slice(), [2].as_slice());
        assert_eq!(reverse(4).as_slice(), [3, 1, 2, 1].as_slice());
        assert_eq!(reverse(5).as_slice(), [4, 1, 3, 1].as_slice());
        assert_eq!(reverse(6).as_slice(), [5, 1, 4, 2, 3, 2, 1].as_slice());
        assert_eq!(reverse(7).as_slice(), [6, 1, 5, 2, 4, 2, 1].as_slice());
        assert_eq!(
            reverse(8).as_slice(),
            [7, 1, 6, 2, 5, 3, 4, 3, 2, 1].as_slice()
        );
        assert_eq!(
            reverse(9).as_slice(),
            [8, 1, 7, 2, 6, 3, 5, 3, 2, 1].as_slice()
        );
        assert_eq!(
            reverse(10).as_slice(),
            [9, 1, 8, 2, 7, 3, 6, 4, 5, 4, 3, 2, 1].as_slice()
        );
        assert_eq!(
            reverse(11).as_slice(),
            [10, 1, 9, 2, 8, 3, 7, 4, 6, 4, 3, 2, 1].as_slice()
        );
    }

    #[test]
    fn clean_top_of_stack() {
        let mut stack =
            LocalStack::with_values(&[ValueId(1), ValueId(2), ValueId(3), ValueId(4), ValueId(5)]);
        let live = BitSet::from([ValueId(2), ValueId(5)]);

        let mut act = Actions::default();
        stack.clean_top_of_stack(&mut act, |val, _| !live.contains(val));

        assert_eq!(
            stack.stack,
            VecDeque::from([StackEntry::Live(ValueId(2)), StackEntry::Live(ValueId(5))])
        );
    }
}
