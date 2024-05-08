use super::local_stack::{memory_slot_of, LocalStack, MemSlot};
use super::{Action, Actions, Allocator};
use crate::domtree::{DFSet, DomTree};
use crate::liveness;
use crate::{bitset::BitSet, cfg::ControlFlowGraph, liveness::Liveness};
use cranelift_entity::SecondaryMap;
use smallvec::{smallvec, SmallVec};
use sonatina_ir::{Block, Function, Insn, InsnData, Value};
use std::collections::BTreeMap;

// xxx notes
//
// stack layout constraints:
// - if any values escape block dominance region:
//   - those values must exist on the stack on block entry
//   - they must remain in the same position, relative to one another
//
// - if next block is not dominated by current block:
//   - there can be no entries at the top of the stack above the live-out values
//     (which must be in their respective locked positions relative to each other)
//   - xxx consider live-in status of next blocks, not live-out of current block
//
// - values defined in a block can out-live the block, but can't escape the dominance zone
//
// - if block is inside of a loop:
//   - it can't increase the stack depth (except for live-out values and phi args)
//
// - function return blocks:
//   - stack must be empty, except return val
//   - TODO: leave junk on stack when it doesn't matter
//           eg main fn, tail call from main fn, ...
//

#[derive(Default)]
pub struct SimpleAlloc {
    /// The actions that must be performed to arrange the stack prior to the
    /// execution of each instruction.
    actions: SecondaryMap<Insn, Actions>,
    brtable_actions: BTreeMap<(Insn, Value), Actions>,
    edge_actions: BTreeMap<(Block, Block), Actions>,
    /// Memory slot assignments are fn-global.
    /// Slots can be shared by values with non-overlapping liveness.
    memory: Vec<MemSlot>,
}

impl SimpleAlloc {
    pub fn for_function(
        func: &Function,
        cfg: &ControlFlowGraph,
        dom: &DomTree,
        liveness: &Liveness,
        _stack_size: u8, // xxx
    ) -> Self {
        let g = SimpleAllocBuilder::new(func, cfg, dom, liveness);
        g.compute()
    }
}

pub struct SimpleAllocBuilder<'a> {
    func: &'a Function,
    cfg: &'a ControlFlowGraph,
    dom: &'a DomTree,
    liveness: &'a Liveness,

    alloc: SimpleAlloc,
}
impl<'a> SimpleAllocBuilder<'a> {
    pub fn new(
        func: &'a Function,
        cfg: &'a ControlFlowGraph,
        dom: &'a DomTree,
        liveness: &'a Liveness,
    ) -> Self {
        Self {
            func,
            cfg,
            dom,
            liveness,
            // block_val_live_range: BTreeMap::new(),
            alloc: SimpleAlloc::default(),
        }
    }

    fn frozen_values_for_block(&self, block: Block, dom_frontiers: &DFSet) -> BitSet<Value> {
        // Values that escape into the block's dominance frontier must
        // remain in their current positions relative to each other.
        let mut escapees = self.liveness.block_live_outs(block).clone();
        for frontier_block in dom_frontiers.frontiers(block) {
            escapees.difference_with(self.liveness.block_live_ins(*frontier_block));
        }

        // If there's only one value that escapes, it can be moved around freely.
        if escapees.len() > 1 {
            escapees
        } else {
            BitSet::default()
        }
    }

    pub fn compute(mut self) -> SimpleAlloc {
        let Some(entry) = self.cfg.entry() else {
            return self.alloc;
        };
        // xxx ensure entry block can't have preds
        assert_eq!(self.cfg.pred_num_of(entry), 0);

        let dom_frontiers = self.dom.compute_df(self.cfg);

        // The inherited stack of the entry block contains the fn args.
        // xxx store SplitStack
        let mut inherited_stack = BTreeMap::new();
        inherited_stack.insert(entry, LocalStack::with_values(&self.func.arg_values));

        for block in self.dom.rpo().iter().copied() {
            // xxx allow crit edges, but no actions on crit edge
            debug_assert!(
                !has_critical_edge(self.func, self.cfg, block),
                "stack_alloc assumes no critical edges. \
                 Please run `CriticalEdgeSplitter` prior to `Liveness` analysis"
            );

            // xxx if block has incoming backedge we should keep a copy
            //     of the inherited stack so we can verify that the stacks match
            let mut stack = inherited_stack.remove(&block).unwrap_or_else(|| {
                // We must have visited a pred block and stored an inherited stack
                // if there are live-in values or phi arguments.
                debug_assert!(self.liveness.block_live_ins(block).is_empty());
                debug_assert!(!self
                    .func
                    .layout
                    .first_insn_of(block)
                    .map(|insn| self.func.dfg.is_phi(insn))
                    .unwrap_or_default());

                LocalStack::default()
            });

            stack.freeze(self.frozen_values_for_block(block, &dom_frontiers));

            let live_out = self.liveness.block_live_outs(block);
            let die_set = BitSet::difference(self.liveness.block_live_ins(block), live_out);
            let mut remaining_uses =
                liveness::value_uses_in_block_matching_predicate(self.func, block, |val| {
                    die_set.contains(val)
                });

            if block == entry {
                for arg in &self.func.arg_values {
                    if !live_out.contains(*arg) {
                        // xxx check and remove this block
                        debug_assert!(remaining_uses.contains_key(arg));
                    }
                }
            }

            for (idx, insn) in self.func.layout.iter_insn(block).enumerate() {
                let insn_data = self.func.dfg.insn_data(insn);
                let result = self.func.dfg.insn_result(insn);

                match insn_data {
                    InsnData::Phi { .. } => {
                        let r = result.unwrap();
                        stack.rename_slot(idx, result.unwrap());
                        if !live_out.contains(r) {
                            // xxx check and remove
                            debug_assert!(remaining_uses.contains_key(&r));
                        }
                        continue;
                    }

                    InsnData::Return { args } => {
                        // Put return val on top of stack.
                        stack.ret(&mut self.alloc.actions[insn], &self.alloc.memory, *args);
                        break;
                    }

                    InsnData::Jump { dests: [dest], .. } => {
                        // Only JUMP can have phi vals

                        let act = &mut self.alloc.actions[insn];
                        let args = phi_args_for_edge(self.func, block, *dest);

                        if !args.is_empty() {
                            stack.move_to_top(
                                &args,
                                &dead_set(&args, &live_out),
                                act,
                                &mut self.alloc.memory,
                                &self.func.dfg,
                                &self.liveness,
                            );
                        }
                        eprintln!("JUMP {block:?}->{dest:?}, args: {args:?}, stack: {stack:?}, live_out: {live_out:?}");
                        // xxx allow phi vals to move into dead xfer slots
                        stack.retain(act, &args, live_out);
                        eprintln!("after retain: {:?}", &stack);
                        // xxx debug_assert inherited stacks are equal
                        inherited_stack.insert(*dest, stack);
                        break;
                    }

                    InsnData::Branch {
                        args: [arg],
                        dests: [left, right],
                    } => {
                        // These things only happen on critical edges, which
                        // must be split before stack alloc is performed.
                        debug_assert!(!inherited_stack.contains_key(left));
                        debug_assert!(!inherited_stack.contains_key(right));
                        debug_assert!(phi_args_for_edge(self.func, block, *left).is_empty());
                        debug_assert!(phi_args_for_edge(self.func, block, *right).is_empty());

                        let act = &mut self.alloc.actions[insn];
                        stack.xxx_branch_prep(
                            *arg,
                            !live_out.contains(*arg),
                            act,
                            &mut self.alloc.memory,
                            &self.func.dfg,
                            &self.liveness,
                        );
                        eprintln!(
                            "BRANCH {block:?}->{left:?} | {right:?}, {arg:?}, {:?}",
                            &stack
                        );

                        // "Consume" branch condition
                        stack.force_pop();

                        inherited_stack.insert(*left, stack.clone());
                        inherited_stack.insert(*right, stack);
                        break;
                    }

                    InsnData::BrTable {
                        args,
                        default,
                        table,
                    } => {
                        // Remove all dead locals
                        let mut live = BitSet::from(args.as_slice());
                        live.union_with(live_out);

                        eprintln!("BRTABLE {args:?}, {:?}", &stack);
                        stack.retain(&mut self.alloc.actions[insn], &[], &live);
                        eprintln!("after retain: {:?}", &stack);

                        let mut args_iter = args.iter();
                        let comp = args_iter.next().unwrap();

                        for (idx, (arg, dest)) in args_iter.zip(table.iter()).enumerate() {
                            let case_args = &[*arg, *comp];
                            let mut dead = dead_set(case_args, live_out);
                            // The first arg (`comp`) needs to be available
                            // for each case. The last case can consume it.
                            if idx != table.len() - 1 {
                                dead.remove(*comp);
                            }
                            let mut act = Actions::new();
                            stack.step(
                                case_args,
                                &dead,
                                None,
                                &mut act,
                                &mut self.alloc.memory,
                                &self.func.dfg,
                                &self.liveness,
                            );

                            // Assert that this is not a critical edge
                            debug_assert!(!inherited_stack.contains_key(dest));
                            debug_assert!(phi_args_for_edge(self.func, block, *dest).is_empty());

                            inherited_stack.insert(*dest, stack.clone());
                            self.alloc.brtable_actions.insert((insn, *arg), act);
                        }

                        if let Some(dest) = default {
                            debug_assert!(!inherited_stack.contains_key(dest));
                            debug_assert!(phi_args_for_edge(self.func, block, *dest).is_empty());
                            inherited_stack.insert(*dest, stack);
                        }
                        break;
                    }
                    _ => {}
                };

                let mut args = insn_data.args();
                let consumable = args
                    .iter()
                    .copied()
                    .filter(|v| {
                        if let Some(count) = remaining_uses.get_mut(v) {
                            *count -= 1;
                            *count == 0
                        } else {
                            false
                        }
                    })
                    .collect::<BitSet<Value>>();

                // Silly calling convention:
                //  1) Place args on top of stack in order [a2, a3, ..., aN, a1]
                //  2) Push continuation code offset location
                //  3) Swap continuation code offset with a1
                let mut call_args: SmallVec<[Value; 4]> = smallvec![];
                if args.len() > 1 && matches!(insn_data, InsnData::Call { .. }) {
                    call_args.extend_from_slice(&args[1..]);
                    call_args.push(args[0]);
                    args = &call_args;
                }

                let act = &mut self.alloc.actions[insn];
                stack.step(
                    args,
                    &consumable,
                    result,
                    act,
                    &mut self.alloc.memory,
                    &self.func.dfg,
                    &self.liveness,
                );

                if matches!(insn_data, InsnData::Call { .. }) {
                    act.push(Action::PushContinuationOffset);
                    if !args.is_empty() {
                        act.push(Action::StackSwap(args.len() as u8));
                        stack.force_rotate_up(args.len() - 1);
                    }
                }

                if let Some(val) = result {
                    if !live_out.contains(val) {
                        remaining_uses.insert(val, self.liveness.val_use_count[val]);
                    }
                }
            }
        }

        self.alloc
    }
}

fn phi_args_for_edge(func: &Function, from: Block, to: Block) -> SmallVec<[Value; 2]> {
    func.layout
        .iter_insn(to)
        .map_while(|insn| match func.dfg.insn_data(insn) {
            InsnData::Phi { values, blocks, .. } => {
                blocks.iter().position(|b| *b == from).map(|i| values[i])
            }
            _ => None,
        })
        .collect()
}

fn dead_set(args: &[Value], live: &BitSet<Value>) -> BitSet<Value> {
    args.iter()
        .copied()
        .filter(|a| !live.contains(*a))
        .collect()
}

fn has_critical_edge(func: &Function, cfg: &ControlFlowGraph, block: Block) -> bool {
    let Some(insn) = func.layout.last_insn_of(block) else {
        return false;
    };

    let branch = func.dfg.analyze_branch(insn);
    if branch.dests_num() > 2 {
        branch.iter_dests().any(|d| cfg.pred_num_of(d) > 1)
    } else {
        false
    }
}

impl Allocator for SimpleAlloc {
    fn enter_function(&self, function: &Function) -> Actions {
        let mut act = Actions::new();
        for (i, arg) in function.arg_values.iter().enumerate() {
            if let Some(slot) = memory_slot_of(*arg, &self.memory) {
                act.push(Action::StackDup(i as u8));
                act.push(Action::MemStoreFrameSlot(slot as u32));
            }
        }
        act
    }

    fn read(&self, insn: Insn, vals: &[Value]) -> Actions {
        if let [val] = vals {
            if let Some(act) = self.brtable_actions.get(&(insn, *val)) {
                return act.clone();
            }
        }
        self.actions[insn].clone()
    }
    fn write(&self, _insn: Insn, val: Value) -> Actions {
        if let Some(pos) = memory_slot_of(val, &self.memory) {
            return smallvec![Action::StackDup(0), Action::MemStoreFrameSlot(pos as u32)];
        }
        smallvec![]
    }

    fn traverse_edge(&self, from: Block, to: Block) -> Actions {
        self.edge_actions
            .get(&(from, to))
            .cloned()
            .unwrap_or_default()
    }
}
