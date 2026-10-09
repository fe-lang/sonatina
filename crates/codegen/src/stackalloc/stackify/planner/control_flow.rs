use smallvec::SmallVec;
use sonatina_ir::{BlockId, InstId, ValueId};
use std::collections::BTreeMap;

use crate::{bitset::BitSet, liveness::phi_args_for_edge, stackalloc::Action};

use super::{
    super::{sym_stack::StackItem, templates::BlockTemplate},
    Planner,
};

impl<'a, 'ctx: 'a> Planner<'a, 'ctx> {
    pub(in super::super) fn plan_edge_fixup_to_template(
        &mut self,
        tmpl: &BlockTemplate,
        pred: BlockId,
        succ: BlockId,
    ) {
        let phi_results = &self.ctx.phi_results[succ];

        let phi_srcs: SmallVec<[ValueId; 4]> = phi_args_for_edge(self.ctx.func, pred, succ)
            .into_iter()
            .map(|v| self.ctx.canonicalize_value(v))
            .collect();
        debug_assert_eq!(
            phi_srcs.len(),
            phi_results.len(),
            "phi source/result arity mismatch for edge {pred:?}->{succ:?}"
        );

        let mut stack_phi_pairs: SmallVec<[(ValueId, ValueId); 4]> = SmallVec::new();
        let mut spilled_phi_pairs: SmallVec<[(ValueId, ValueId); 4]> = SmallVec::new();
        for (&phi_res, &src) in phi_results.iter().zip(phi_srcs.iter()) {
            if !self.mem.spill_set().contains(phi_res) {
                stack_phi_pairs.push((phi_res, src));
            } else if src != phi_res {
                // A spilled self-copy leaves the phi's spill word unchanged.
                spilled_phi_pairs.push((phi_res, src));
            }
        }

        // The edge is a parallel copy: every source must be read with its predecessor value, but
        // storing a spilled phi overwrites that phi's old value, which may itself be a source on
        // this edge. Store a phi once no pending copy still reads it, emitting the ready stores
        // against the full predecessor stack.
        let mut readers: BTreeMap<ValueId, usize> = BTreeMap::new();
        for &(_, src) in stack_phi_pairs.iter().chain(&spilled_phi_pairs) {
            *readers.entry(src).or_default() += 1;
        }
        let mut pending: BTreeMap<ValueId, ValueId> = spilled_phi_pairs.iter().copied().collect();
        let mut ready: SmallVec<[ValueId; 4]> = spilled_phi_pairs
            .iter()
            .rev()
            .map(|&(phi_res, _)| phi_res)
            .filter(|phi_res| !readers.contains_key(phi_res))
            .collect();
        while let Some(phi_res) = ready.pop() {
            let src = pending
                .remove(&phi_res)
                .expect("ready phi store is pending");
            self.emit_spilled_phi_store(phi_res, src);
            let remaining = readers.get_mut(&src).expect("phi store reads its source");
            *remaining -= 1;
            if *remaining == 0 && pending.contains_key(&src) {
                ready.push(src);
            }
        }

        // The old value of each remaining phi is still read by a stack phi or by another remaining
        // store (as in a copy cycle). Stage their sources above the template, so normalization
        // reads every old value before any of these stores.
        let staged: SmallVec<[(ValueId, ValueId); 4]> = spilled_phi_pairs
            .into_iter()
            .filter(|(phi_res, _)| pending.contains_key(phi_res))
            .collect();

        // Normalize the predecessor stack directly to the staged sources above the successor
        // entry template:
        //
        //   StackIn(succ) = P(succ) ++ T(succ)
        //
        // Where `P(succ)` includes:
        // - function args (entry block only)
        // - stack-resident phi results (replaced here by per-edge phi sources, then renamed
        //   in-place; spilled phis are stored to memory and omitted from `P(succ)`)
        let phi_count = stack_phi_pairs.len();
        debug_assert!(
            phi_count <= tmpl.params.len(),
            "template params missing phi results for block {succ:?}"
        );
        let args_prefix_len = tmpl.params.len() - phi_count;
        let expected_phi_params: SmallVec<[ValueId; 4]> = stack_phi_pairs
            .iter()
            .map(|(phi_res, _)| *phi_res)
            .collect();
        debug_assert_eq!(
            &tmpl.params.as_slice()[args_prefix_len..],
            expected_phi_params.as_slice(),
            "template phi prefix mismatch for block {succ:?}"
        );

        let mut desired: SmallVec<[ValueId; 16]> = staged.iter().map(|&(_, src)| src).collect();
        desired.extend(tmpl.params.iter().take(args_prefix_len).copied());
        desired.extend(stack_phi_pairs.iter().map(|(_, src)| *src));
        desired.extend(tmpl.transfer().iter().copied());

        self.normalize_to_exact(desired.as_slice());

        for &(phi_res, src) in &staged {
            debug_assert_eq!(
                self.stack.top(),
                Some(&StackItem::Value(src)),
                "edge normalization failed to stage phi source for {pred:?}->{succ:?}"
            );
            self.mem.emit_store_for_spilled_value(phi_res, self.actions);
            self.stack.pop_operand();
        }

        // Rename stack-resident phi-source placeholders to phi results.
        for (idx, &(phi_res, src)) in stack_phi_pairs.iter().enumerate() {
            let depth = args_prefix_len + idx;
            debug_assert_eq!(
                self.stack.item_at(depth),
                Some(&StackItem::Value(src)),
                "edge normalization failed to place phi source at depth {depth} for {pred:?}->{succ:?}"
            );
            self.stack.rename_value_at_depth(depth, phi_res);
        }
    }

    fn emit_spilled_phi_store(&mut self, phi_res: ValueId, src: ValueId) {
        if self.ctx.func.dfg.value_is_imm(src) {
            let imm = self
                .ctx
                .func
                .dfg
                .value_imm(src)
                .expect("imm value missing payload");
            self.actions.push(Action::Push(imm));
        } else if let Some(pos) = self.stack.find_reachable_value(src, self.ctx.reach.dup_max) {
            self.actions.push(Action::StackDup(pos as u8));
        } else {
            let act = self.mem.load_frame_slot_or_placeholder(src);
            self.actions.push(act);
        }
        self.mem.emit_store_for_spilled_value(phi_res, self.actions);
    }

    /// Prepare the operands and return continuation for an internal `call`.
    ///
    /// EVM internal-call ABI: at the `JUMP` into the callee the stack must read
    /// `[arg0, arg1, …, argN-1, cont, <caller values the callee cannot see>]`, where `cont` is the
    /// return-continuation address the callee jumps back to. This method arranges exactly that
    /// shape, in three pre-coordinated steps so a single `SWAP` finishes it:
    ///
    /// 1. `args` arrive already rotated left by one (see `operand_order_for_stackify`), so operand
    ///    preparation leaves `[arg1, …, argN-1, arg0, <caller values>]` on top.
    /// 2. `push_call_continuation` pushes `cont`: `[cont, arg1, …, argN-1, arg0, …]`.
    /// 3. `position_call_ret_below_operands(argc)` swaps `cont` with the bottom operand `arg0`,
    ///    yielding `[arg0, arg1, …, argN-1, cont, …]` — ABI order with the continuation directly
    ///    below the args. When `argc == 0` the continuation is already on top and the swap is
    ///    skipped.
    pub(in super::super) fn prepare_internal_call(
        &mut self,
        inst: InstId,
        args: &mut SmallVec<[ValueId; 8]>,
        consume_last_use: &BitSet<ValueId>,
        cache_preserve: &BitSet<ValueId>,
    ) {
        self.prepare_operands_for_inst(inst, args, consume_last_use, cache_preserve);
        self.stack.push_call_continuation(self.actions);
        self.stack
            .position_call_ret_below_operands(args.len(), self.actions);
    }

    pub fn plan_internal_return(&mut self, inst: InstId) {
        let ret_vals: SmallVec<[ValueId; 16]> = self
            .ctx
            .func
            .dfg
            .return_args(inst)
            .map(|args| {
                args.iter()
                    .map(|&arg| self.ctx.canonicalize_value(arg))
                    .collect()
            })
            .unwrap_or_default();
        assert!(
            ret_vals.len() <= 16,
            "stackify supports at most 16 return values for {inst:?}"
        );
        self.normalize_to_exact(ret_vals.as_slice());
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        bitset::BitSet,
        cfg_scc::CfgSccAnalysis,
        domtree::DomTree,
        liveness::Liveness,
        stackalloc::{
            Action, Actions,
            stackify::{
                builder::StackifyReachability,
                planner::{
                    MemPlan, MemState, NormalizeSearchScratch, Planner,
                    test_utils::build_stackify_test_context,
                },
                slots::{FreeSlotPools, SpillSlotPools},
                spill::SpillSet,
                sym_stack::SymStack,
                templates::BlockTemplate,
            },
        },
    };
    use cranelift_entity::SecondaryMap;
    use sonatina_ir::{BlockId, Immediate, ValueId, cfg::ControlFlowGraph};
    use sonatina_parser::parse_module;

    const ENTRY_EDGE: &str = r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i256) -> i256 {
block0:
    v1.i256 = add v0 1.i256;
    jump block1;

block1:
    v2.i256 = phi (0.i256 block0);
    v3.i256 = phi (v1 block0);
    return v3;
}
"#;

    struct EdgeFixup<'a> {
        src: &'a str,
        pred: BlockId,
        succ: BlockId,
        /// Spilled values whose scratch slots are already assigned, in slot order.
        scratch: &'a [&'a str],
        /// Spilled values whose scratch slots are assigned by their first store.
        spilled: &'a [&'a str],
        /// The predecessor stack, top first.
        stack: &'a [&'a str],
        params: &'a [&'a str],
        transfer: &'a [&'a str],
    }

    /// Plans the edge fixup into the `params ++ transfer` template of `%entry`'s `succ`, and
    /// returns the emitted actions.
    fn plan_edge_fixup(edge: EdgeFixup<'_>) -> Actions {
        let parsed = parse_module(edge.src).expect("module parses");
        let func_ref = parsed
            .module
            .funcs()
            .into_iter()
            .find(|&func| {
                parsed
                    .module
                    .ctx
                    .func_sig(func, |sig| sig.name() == "entry")
            })
            .expect("entry exists");
        let value = |name: &str| {
            parsed
                .debug
                .value(func_ref, name)
                .unwrap_or_else(|| panic!("missing {name}"))
        };

        parsed.module.func_store.view(func_ref, |func| {
            let mut cfg = ControlFlowGraph::default();
            cfg.compute(func);
            let entry = cfg.entry().expect("entry block");

            let mut liveness = Liveness::new();
            liveness.compute(func, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let mut scc = CfgSccAnalysis::new();
            scc.compute(&cfg);

            let mut ctx = build_stackify_test_context(
                func,
                &cfg,
                &dom,
                &liveness,
                entry,
                scc,
                StackifyReachability::new(16),
            );
            ctx.scratch_spill_slots = (edge.scratch.len() + edge.spilled.len()) as u32;

            let spill_set: BitSet<ValueId> = edge
                .scratch
                .iter()
                .chain(edge.spilled)
                .map(|&name| value(name))
                .collect();
            let mut free_slots = FreeSlotPools::default();
            let mut slots = SpillSlotPools::default();
            for (slot, &name) in edge.scratch.iter().enumerate() {
                let spilled = SpillSet::new(&spill_set)
                    .spilled(value(name))
                    .expect("scratch value is spilled");
                assert_eq!(
                    slots.scratch.try_ensure_slot(
                        spilled,
                        &ctx.spill_slot_interference,
                        &mut free_slots.scratch,
                        Some(ctx.scratch_spill_slots),
                    ),
                    Some(slot as u32),
                    "{name} gets its own scratch slot"
                );
            }

            let mut spill_requests = BitSet::default();
            let mut object_spill_requests = BitSet::default();
            let forced_object_spills = BitSet::default();
            let spill_obj = SecondaryMap::new();
            let mut mem_state = MemState {
                spill: SpillSet::new(&spill_set),
                spill_obj: &spill_obj,
                spill_requests: &mut spill_requests,
                object_spill_requests: &mut object_spill_requests,
                forced_object_spills: &forced_object_spills,
                slots: &mut slots,
            };
            let mem = MemPlan::new(&mut mem_state, &ctx, &ctx.remat_actions, &mut free_slots);
            let mut stack = SymStack::opaque_prefix_empty(false);
            for &name in edge.stack.iter().rev() {
                stack.push_value(value(name));
            }
            let mut actions = Actions::new();
            let mut search_scratch = NormalizeSearchScratch::default();
            let mut planner =
                Planner::new(&ctx, &mut stack, &mut actions, mem, &mut search_scratch);

            let template = BlockTemplate::new(
                edge.params.iter().map(|&name| value(name)).collect(),
                edge.transfer.iter().map(|&name| value(name)).collect(),
            );
            planner.plan_edge_fixup_to_template(&template, edge.pred, edge.succ);

            assert!(
                spill_requests.is_empty(),
                "edge fixup requested new spills: {spill_requests:?}"
            );
            actions
        })
    }

    #[test]
    fn spilled_phi_edge_slots_keep_parallel_sources_distinct() {
        let actions = plan_edge_fixup(EdgeFixup {
            src: ENTRY_EDGE,
            pred: BlockId(0),
            succ: BlockId(1),
            scratch: &["v1"],
            spilled: &["v2", "v3"],
            stack: &[],
            params: &[],
            transfer: &[],
        });

        assert_eq!(
            actions.as_slice(),
            &[
                Action::Push(Immediate::I256(0.into())),
                Action::MemStoreAbs(32),
                Action::MemLoadAbs(0),
                Action::MemStoreAbs(64),
            ],
        );
    }

    #[test]
    fn spilled_phi_store_does_not_clobber_later_stack_phi_source() {
        let actions = plan_edge_fixup(EdgeFixup {
            src: ENTRY_EDGE,
            pred: BlockId(0),
            succ: BlockId(1),
            scratch: &["v1"],
            spilled: &["v2"],
            stack: &[],
            params: &["v3"],
            transfer: &[],
        });

        assert_eq!(
            actions.as_slice(),
            &[
                Action::Push(Immediate::I256(0.into())),
                Action::MemStoreAbs(32),
                Action::MemLoadAbs(0),
            ],
        );
    }

    #[test]
    fn stack_phi_reads_spilled_phi_before_its_edge_store() {
        // Stack phi `v1` takes the old `v2`, while spilled `v2` is overwritten with `v3`.
        let actions = plan_edge_fixup(EdgeFixup {
            src: r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i256) -> i256 {
block0:
    jump block1;

block1:
    v1.i256 = phi (0.i256 block0) (v2 block2);
    v2.i256 = phi (1.i256 block0) (v3 block2);
    v4.i1 = lt v2 v0;
    br v4 block2 block3;

block2:
    v3.i256 = add v2 1.i256;
    jump block1;

block3:
    return v1;
}
"#,
            pred: BlockId(2),
            succ: BlockId(1),
            scratch: &["v2"],
            spilled: &[],
            stack: &["v3", "v0"],
            params: &["v1"],
            transfer: &["v0"],
        });

        assert_eq!(
            actions.as_slice(),
            &[
                Action::MemLoadAbs(0),
                Action::StackSwap(1),
                Action::MemStoreAbs(0),
            ],
        );
    }

    #[test]
    fn spilled_phi_swap_stages_both_sources() {
        let actions = plan_edge_fixup(EdgeFixup {
            src: r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i256) -> i256 {
block0:
    jump block1;

block1:
    v1.i256 = phi (1.i256 block0) (v2 block2);
    v2.i256 = phi (2.i256 block0) (v1 block2);
    v3.i1 = lt v1 v0;
    br v3 block2 block3;

block2:
    jump block1;

block3:
    return v2;
}
"#,
            pred: BlockId(2),
            succ: BlockId(1),
            scratch: &["v1", "v2"],
            spilled: &[],
            stack: &["v0"],
            params: &[],
            transfer: &["v0"],
        });

        assert_eq!(
            actions.as_slice(),
            &[
                Action::MemLoadAbs(0),
                Action::MemLoadAbs(32),
                Action::MemStoreAbs(0),
                Action::MemStoreAbs(32),
            ],
        );
    }

    #[test]
    fn spilled_phi_chain_stores_readers_first() {
        // `v2` reads the old `v1`, so `v2` is stored before `v1` despite the phi order, and no
        // source needs staging.
        let actions = plan_edge_fixup(EdgeFixup {
            src: r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i256) -> i256 {
block0:
    jump block1;

block1:
    v1.i256 = phi (1.i256 block0) (v3 block2);
    v2.i256 = phi (0.i256 block0) (v1 block2);
    v4.i1 = lt v1 v0;
    br v4 block2 block3;

block2:
    v3.i256 = add v1 1.i256;
    jump block1;

block3:
    return v2;
}
"#,
            pred: BlockId(2),
            succ: BlockId(1),
            scratch: &["v1", "v2"],
            spilled: &[],
            stack: &["v3", "v0"],
            params: &[],
            transfer: &["v0"],
        });

        assert_eq!(
            actions.as_slice(),
            &[
                Action::MemLoadAbs(0),
                Action::MemStoreAbs(32),
                Action::StackDup(0),
                Action::MemStoreAbs(0),
                Action::Pop,
            ],
        );
    }

    #[test]
    fn spilled_phi_self_copy_needs_no_store() {
        let actions = plan_edge_fixup(EdgeFixup {
            src: r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i256) -> i256 {
block0:
    jump block1;

block1:
    v1.i256 = phi (0.i256 block0) (v1 block2);
    v2.i1 = lt v1 v0;
    br v2 block2 block3;

block2:
    jump block1;

block3:
    return v1;
}
"#,
            pred: BlockId(2),
            succ: BlockId(1),
            scratch: &["v1"],
            spilled: &[],
            stack: &["v0"],
            params: &[],
            transfer: &["v0"],
        });

        assert_eq!(actions.as_slice(), &[]);
    }
}
