use smallvec::SmallVec;
use sonatina_ir::{BlockId, InstId, ValueId};

use super::{
    super::{
        sym_stack::StackItem,
        templates::{BlockTemplate, phi_args_for_edge},
    },
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
            if self.mem.spill_set().contains(phi_res) {
                spilled_phi_pairs.push((phi_res, src));
            } else {
                stack_phi_pairs.push((phi_res, src));
            }
        }

        // Memory-only phi results do not participate in the successor's stack template. Their
        // spill slots are assigned with phi-edge interference, so stores can be emitted directly
        // without clobbering later source loads on this edge.
        for &(phi_res, src) in &spilled_phi_pairs {
            self.emit_store_spilled_value_from_source(phi_res, src);
        }

        // Normalize the predecessor stack directly to the successor entry template:
        //
        //   StackIn(succ) = P(succ) ++ T(succ)
        //
        // Where `P(succ)` includes:
        // - function args (entry block only)
        // - stack-resident phi results (replaced here by per-edge phi sources, then renamed
        //   in-place; spilled phis were stored directly above and are omitted from `P(succ)`)
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

        let mut desired: SmallVec<[ValueId; 16]> = SmallVec::new();
        desired.extend(tmpl.params.iter().take(args_prefix_len).copied());
        desired.extend(stack_phi_pairs.iter().map(|(_, src)| *src));
        desired.extend(tmpl.transfer().iter().copied());

        self.normalize_to_exact(desired.as_slice());

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
        cfg_scc::CfgSccAnalysis,
        domtree::DomTree,
        liveness::Liveness,
        stackalloc::{
            Action, Actions,
            stackify::{
                builder::StackifyReachability,
                planner::{
                    MemPlan, NormalizeSearchScratch, Planner,
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
    use smallvec::smallvec;
    use sonatina_ir::{BlockId, ValueId, cfg::ControlFlowGraph};
    use sonatina_parser::parse_module;

    #[test]
    fn spilled_phi_edge_slots_keep_parallel_sources_distinct() {
        let parsed = parse_module(
            r#"
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
"#,
        )
        .expect("module parses");
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
            ctx.scratch_spill_slots = 3;

            let source = parsed.debug.value(func_ref, "v1").expect("v1");
            let first_phi = parsed.debug.value(func_ref, "v2").expect("v2");
            let second_phi = parsed.debug.value(func_ref, "v3").expect("v3");

            let mut spill_set = crate::bitset::BitSet::default();
            spill_set.insert(source);
            spill_set.insert(first_phi);
            spill_set.insert(second_phi);

            let mut spill_requests = crate::bitset::BitSet::default();
            let mut object_spill_requests = crate::bitset::BitSet::default();
            let forced_object_spills = crate::bitset::BitSet::default();
            let spill_obj: SecondaryMap<ValueId, Option<_>> = SecondaryMap::new();
            let mut free_slots = FreeSlotPools::default();
            let mut slots = SpillSlotPools::default();

            let spilled_source = SpillSet::new(&spill_set)
                .spilled(source)
                .expect("source is spilled");
            slots
                .scratch
                .try_ensure_slot(
                    spilled_source,
                    &ctx.spill_slot_interference,
                    &mut free_slots.scratch,
                    Some(3),
                )
                .expect("source scratch slot");

            let mem = MemPlan::new(
                SpillSet::new(&spill_set),
                &mut spill_requests,
                &ctx,
                &spill_obj,
                &ctx.exact_local_addr,
                &mut object_spill_requests,
                &forced_object_spills,
                &mut free_slots,
                &mut slots,
            );
            let mut stack = SymStack::opaque_prefix_empty(false);
            let mut actions = Actions::new();
            let mut search_scratch = NormalizeSearchScratch::default();
            let mut planner =
                Planner::new(&ctx, &mut stack, &mut actions, mem, &mut search_scratch);

            let mut template = BlockTemplate::new(smallvec![]);
            template.freeze_transfer(smallvec![]);
            planner.plan_edge_fixup_to_template(&template, BlockId(0), BlockId(1));

            assert_eq!(
                actions.as_slice(),
                &[
                    Action::Push(sonatina_ir::Immediate::I256(0.into())),
                    Action::MemStoreAbs(32),
                    Action::MemLoadAbs(0),
                    Action::MemStoreAbs(64),
                ],
            );
            assert_eq!(slots.scratch.slot_for(source), Some(0));
            assert_eq!(slots.scratch.slot_for(first_phi), Some(1));
            assert_eq!(slots.scratch.slot_for(second_phi), Some(2));
        });
    }

    #[test]
    fn spilled_phi_store_does_not_clobber_later_stack_phi_source() {
        let parsed = parse_module(
            r#"
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
"#,
        )
        .expect("module parses");
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
            ctx.scratch_spill_slots = 2;

            let source = parsed.debug.value(func_ref, "v1").expect("v1");
            let spilled_phi = parsed.debug.value(func_ref, "v2").expect("v2");
            let stack_phi = parsed.debug.value(func_ref, "v3").expect("v3");

            let mut spill_set = crate::bitset::BitSet::default();
            spill_set.insert(source);
            spill_set.insert(spilled_phi);

            let mut spill_requests = crate::bitset::BitSet::default();
            let mut object_spill_requests = crate::bitset::BitSet::default();
            let forced_object_spills = crate::bitset::BitSet::default();
            let spill_obj: SecondaryMap<ValueId, Option<_>> = SecondaryMap::new();
            let mut free_slots = FreeSlotPools::default();
            let mut slots = SpillSlotPools::default();

            let spilled_source = SpillSet::new(&spill_set)
                .spilled(source)
                .expect("source is spilled");
            slots
                .scratch
                .try_ensure_slot(
                    spilled_source,
                    &ctx.spill_slot_interference,
                    &mut free_slots.scratch,
                    Some(2),
                )
                .expect("source scratch slot");

            let mem = MemPlan::new(
                SpillSet::new(&spill_set),
                &mut spill_requests,
                &ctx,
                &spill_obj,
                &ctx.exact_local_addr,
                &mut object_spill_requests,
                &forced_object_spills,
                &mut free_slots,
                &mut slots,
            );
            let mut stack = SymStack::opaque_prefix_empty(false);
            let mut actions = Actions::new();
            let mut search_scratch = NormalizeSearchScratch::default();
            let mut planner =
                Planner::new(&ctx, &mut stack, &mut actions, mem, &mut search_scratch);

            let mut template = BlockTemplate::new(smallvec![stack_phi]);
            template.freeze_transfer(smallvec![]);
            planner.plan_edge_fixup_to_template(&template, BlockId(0), BlockId(1));

            assert_eq!(
                actions.as_slice(),
                &[
                    Action::Push(sonatina_ir::Immediate::I256(0.into())),
                    Action::MemStoreAbs(32),
                    Action::MemLoadAbs(0),
                ],
            );
            assert_eq!(slots.scratch.slot_for(source), Some(0));
            assert_eq!(slots.scratch.slot_for(spilled_phi), Some(1));
        });
    }
}
