use super::local_stack::{memory_slot_of, LocalStack, MemSlot};
use super::{Action, Actions, Allocator};
use crate::{bitset::BitSet, cfg::ControlFlowGraph, liveness::Liveness};
use cranelift_entity::SecondaryMap;
use smallvec::{smallvec, SmallVec};
use sonatina_ir::{Block, Function, Insn, InsnData, Value};
use std::collections::BTreeMap;

// xxx remove 16s

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
        liveness: &Liveness,
        _stack_size: u8, // xxx
    ) -> Self {
        let g = SimpleAllocBuilder::new(func, cfg, liveness);
        g.compute()
    }
}

pub struct SimpleAllocBuilder<'a> {
    func: &'a Function,
    cfg: &'a ControlFlowGraph,
    liveness: &'a Liveness,

    // xxx block_val_live_range: BTreeMap<(Block, Value), Range<u16>>,
    alloc: SimpleAlloc,
}
impl<'a> SimpleAllocBuilder<'a> {
    pub fn new(func: &'a Function, cfg: &'a ControlFlowGraph, liveness: &'a Liveness) -> Self {
        Self {
            func,
            cfg,
            liveness,
            // block_val_live_range: BTreeMap::new(),
            alloc: SimpleAlloc::default(),
        }
    }

    pub fn compute(mut self) -> SimpleAlloc {
        let Some(entry) = self.cfg.entry() else {
            return self.alloc;
        };
        // xxx ensure entry block can't have preds
        assert_eq!(self.cfg.pred_num_of(entry), 0);

        let mut rpo = self.cfg.post_order().collect::<SmallVec<[Block; 8]>>();
        rpo.reverse();

        // The inherited stack of the entry block contains the fn args.
        let mut inherited_stack = BTreeMap::new();
        inherited_stack.insert(entry, LocalStack::with_values(&self.func.arg_values));

        for block in rpo {
            // xxx allow crit edges, but no actions on crit edge
            debug_assert!(
                !has_critical_edge(self.func, self.cfg, block),
                "stack_alloc assumes no critical edges. \
                 Please run `CriticalEdgeSplitter` prior to `Liveness` analysis"
            );

            let mut stack = inherited_stack.remove(&block).unwrap_or_else(|| {
                let mut stack = LocalStack::default();
                for phi in self
                    .func
                    .layout
                    .iter_insn(block)
                    .take_while(|insn| self.func.dfg.is_phi(*insn))
                {
                    let val = self.func.dfg.insn_result(phi).unwrap();
                    stack.push_bottom(val);
                }
                stack
            });

            let live_out = self.liveness.block_live_outs(block);

            // Val liveness range is `A..B`, ie `[A, B)` where A is the index of
            // the defining instruction, and B is the index of the last using
            // instruction.
            // xxx let mut val_insn_range: BTreeMap<Value, Range<u32>> = BTreeMap::new();
            let mut local_uses_remaining: BTreeMap<Value, u32> = BTreeMap::new();
            if block == entry {
                for arg in &self.func.arg_values {
                    if !live_out.contains(*arg) {
                        local_uses_remaining.insert(*arg, self.liveness.val_use_count[*arg]);
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
                            local_uses_remaining.insert(r, self.liveness.val_use_count[r]);
                        }
                        continue;
                    }

                    InsnData::Return { args } => {
                        // Put return val on top of stack.
                        stack.ret(&mut self.alloc.actions[insn], &self.alloc.memory, *args);
                        break;
                    }

                    InsnData::Jump { dests: [dest], .. } => {
                        let act = self.compute_edge_actions(
                            block,
                            *dest,
                            &mut stack,
                            inherited_stack.get(dest),
                            live_out,
                        );
                        self.alloc.edge_actions.insert((block, *dest), act);

                        inherited_stack.insert(*dest, stack);
                        break;
                    }

                    InsnData::Branch {
                        args,
                        dests: [left, right],
                    } => {
                        stack.step(
                            args,
                            &dead_set(args, live_out),
                            None,
                            &mut self.alloc.actions[insn],
                            &mut self.alloc.memory,
                            &self.func.dfg,
                            &self.liveness,
                        );

                        // These things only happen on critical edges, which
                        // must be split before stack alloc is performed.
                        debug_assert!(!inherited_stack.contains_key(left));
                        debug_assert!(!inherited_stack.contains_key(right));
                        debug_assert!(phi_args_for_edge(self.func, block, *left).is_empty());
                        debug_assert!(phi_args_for_edge(self.func, block, *right).is_empty());

                        inherited_stack.insert(*left, stack.clone());
                        inherited_stack.insert(*right, stack);
                        break;
                    }

                    InsnData::BrTable {
                        args,
                        default,
                        table,
                    } => {
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
                        if let Some(count) = local_uses_remaining.get_mut(v) {
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
                        local_uses_remaining.insert(val, self.liveness.val_use_count[val]);
                    }
                }
            }
        }

        self.alloc
    }

    #[must_use]
    pub fn compute_edge_actions(
        &mut self,
        from: Block,
        to: Block,
        stack: &mut LocalStack,
        to_match: Option<&LocalStack>,
        live: &BitSet<Value>,
    ) -> Actions {
        let mut act = Actions::new();
        let args = phi_args_for_edge(self.func, from, to);
        // xxx remove everything that's not live-in
        //     (only if `to` has multiple preds?)
        if !args.is_empty() {
            stack.move_to_top(
                &args,
                &dead_set(&args, live),
                &mut act,
                &mut self.alloc.memory,
                &self.func.dfg,
                &self.liveness,
            );
        }
        if let Some(to_match) = to_match {
            stack.reconcile_with(&mut act, to_match, live, args.len());
        }

        act
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
