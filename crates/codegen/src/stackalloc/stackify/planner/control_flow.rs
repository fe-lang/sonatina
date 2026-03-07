use cranelift_entity::SecondaryMap;
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
    pub(in super::super) fn plan_edge_fixup(
        &mut self,
        templates: &SecondaryMap<BlockId, BlockTemplate>,
        pred: BlockId,
        succ: BlockId,
    ) {
        let tmpl = &templates[succ];
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

        // Memory-only phi results do not participate in the successor's stack template: store
        // them directly from the incoming source, then normalize only the stack-resident prefix.
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
        desired.extend(tmpl.transfer.iter().copied());

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
        let Some(ret_val) = self
            .ctx
            .func
            .dfg
            .return_args(inst)
            .and_then(|args| match args {
                [] => None,
                [arg] => Some(*arg),
                _ => panic!("stackify does not support multi-value return {inst:?}"),
            })
        else {
            // No return value: pop everything above the function return address.
            self.stack.clear_above_func_ret(self.actions);
            return;
        };
        let ret_val = self.ctx.canonicalize_value(ret_val);

        if self.ctx.func.dfg.value_is_imm(ret_val) {
            let imm = self
                .ctx
                .func
                .dfg
                .value_imm(ret_val)
                .expect("imm value missing payload");

            // If an identical immediate is already on the stack, reuse it instead of pushing a
            // duplicate constant.
            let limit = self.stack.len_above_func_ret();
            let mut existing_pos: Option<usize> = None;
            for (idx, item) in self.stack.iter().take(limit).enumerate() {
                let StackItem::Value(v) = item else {
                    continue;
                };
                let Some(stack_imm) = self.ctx.func.dfg.value_imm(*v) else {
                    continue;
                };
                if stack_imm == imm {
                    existing_pos = Some(idx);
                    break;
                }
            }

            if let Some(pos) = existing_pos {
                self.stack.pop_n(pos, self.actions);
                self.stack.rename_top_value(ret_val);
                self.delete_between_top_and_func_ret();
                return;
            }

            // Immediate return: clear the callee stack segment, then push the immediate.
            self.stack.clear_above_func_ret(self.actions);
            self.stack.push_imm(ret_val, imm, self.actions);
            return;
        }

        // Prefer using an existing stack copy of the return value (if any) to avoid
        // forcing it into `spill_set`.
        //
        // Step 1: pop values until either the return value or the return-address barrier is on top.
        loop {
            match self.stack.top() {
                Some(StackItem::Value(v)) if *v == ret_val => break,
                Some(StackItem::FuncRetAddr) | None => break,
                Some(_) => {
                    self.stack.pop(self.actions);
                }
            }
        }

        // Step 2: if the return value wasn't present on the stack, reload it from `spill_set`.
        if self.stack.top() != Some(&StackItem::Value(ret_val)) {
            self.push_value_from_spill_slot_or_mark(ret_val, ret_val);
        }

        self.delete_between_top_and_func_ret();
    }
}
