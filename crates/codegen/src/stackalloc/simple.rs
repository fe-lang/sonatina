use super::local_stack::{LocalStack, MemSlot};
use super::{Action, Actions, Allocator};
use crate::{bitset::BitSet, cfg::ControlFlowGraph, liveness::Liveness};
use cranelift_entity::packed_option::PackedOption;
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
    brtable_actions: BTreeMap<(Insn, PackedOption<Value>, Block), (Actions, Actions)>,
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
        // A non-entry block can have an "inherited" stack if it has one
        // predecessor.
        // FUTURE: allow inherited stacks in two-pred blocks, with backedge given priority
        let mut inherited_stack = BTreeMap::new();
        inherited_stack.insert(entry, LocalStack::with_values(&self.func.arg_values));

        for block in rpo {
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
                        let spills = stack.step(
                            args,
                            &dead_set(args, live_out),
                            None,
                            &mut self.alloc.actions[insn],
                            &self.alloc.memory,
                            &self.func.dfg,
                        );
                        if !spills.is_empty() {
                            todo!("handle spills");
                        }

                        let mut left_stack = stack.clone();

                        let lact = self.compute_edge_actions(
                            block,
                            *left,
                            &mut left_stack,
                            inherited_stack.get(left),
                            self.liveness.block_live_ins(*left),
                        );
                        self.alloc.edge_actions.insert((block, *left), lact);

                        let ract = self.compute_edge_actions(
                            block,
                            *right,
                            &mut stack,
                            inherited_stack.get(right),
                            self.liveness.block_live_ins(*right),
                        );
                        self.alloc.edge_actions.insert((block, *right), ract);

                        inherited_stack.insert(*left, left_stack);
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
                            let mut v_act = Actions::new();
                            let spills = stack.step(
                                case_args,
                                &dead,
                                None,
                                &mut v_act,
                                &self.alloc.memory,
                                &self.func.dfg,
                            );
                            if !spills.is_empty() {
                                todo!("handle spills");
                            }

                            let mut st = stack.clone();
                            let e_act = self.compute_edge_actions(
                                block,
                                *dest,
                                &mut st,
                                inherited_stack.get(dest),
                                self.liveness.block_live_ins(*dest),
                            );
                            inherited_stack.insert(*dest, st);

                            self.alloc
                                .brtable_actions
                                .insert((insn, Some(*arg).into(), *dest), (v_act, e_act));
                        }

                        if let Some(dest) = default {
                            let e_act = self.compute_edge_actions(
                                block,
                                *dest,
                                &mut stack,
                                inherited_stack.get(dest),
                                self.liveness.block_live_ins(*dest),
                            );
                            self.alloc
                                .brtable_actions
                                .insert((insn, None.into(), *dest), (smallvec![], e_act));
                            inherited_stack.insert(*dest, stack);
                        }
                        break;
                    }
                    _ => {}
                };

                let args = insn_data.args();
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

                let spills = stack.step(
                    args,
                    &consumable,
                    result,
                    &mut self.alloc.actions[insn],
                    &self.alloc.memory,
                    &self.func.dfg,
                );
                if !spills.is_empty() {
                    self.alloc.actions[insn].clear();
                    for val in spills {
                        self.allocate_slot(val);
                    }
                    todo!("redo block after spill")
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
            let spills = stack.move_to_top(
                &args,
                &dead_set(&args, live),
                &mut act,
                &self.alloc.memory,
                &self.func.dfg,
            );

            if !spills.is_empty() {
                for val in spills {
                    self.allocate_slot(val);
                }
                todo!("redo block after spill")
            }
        }

        if let Some(to_match) = to_match {
            stack.reconcile_with(&mut act, to_match, live, args.len());
        }

        act
    }

    fn allocate_slot(&mut self, val: Value) {
        for slot in self.alloc.memory.iter_mut() {
            if slot_can_hold(slot, val, self.liveness) {
                slot.push(val);
                return;
            }
        }
        self.alloc.memory.push(smallvec![val]);
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

fn slot_can_hold(slot: &[Value], val: Value, liveness: &Liveness) -> bool {
    // xxx use insn-level liveness for single-block conflict case
    let live = &liveness.val_live_blocks[val];
    slot.iter()
        .all(|v| live.is_disjoint(&liveness.val_live_blocks[*v]))
}

impl Allocator for SimpleAlloc {
    fn read(&self, insn: Insn, _vals: &[Value]) -> Actions {
        self.actions[insn].clone()
    }
    fn write(&self, _insn: Insn, val: Value) -> Actions {
        if let Some(pos) = self.memory.iter().position(|slot| slot.contains(&val)) {
            return smallvec![Action::MemStoreFrameSlot(pos as u32)];
        }
        smallvec![]
    }

    fn brtable_case(&self, insn: Insn, value: Option<Value>, block: Block) -> (Actions, Actions) {
        self.brtable_actions[&(insn, value.into(), block)].clone()
    }

    fn traverse_edge(&self, from: Block, to: Block) -> Actions {
        self.edge_actions
            .get(&(from, to))
            .cloned()
            .unwrap_or_default()
    }
}
