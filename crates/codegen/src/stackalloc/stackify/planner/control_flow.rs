use crate::bitset::BitSet;
use cranelift_entity::SecondaryMap;
use smallvec::SmallVec;
use sonatina_ir::{BlockId, InstId, ValueId};
use std::collections::BTreeMap;

use super::{
    super::{
        sym_stack::StackItem,
        templates::{phi_args_for_edge, BlockTemplate},
        DUP_MAX, SWAP_MAX,
    },
    Planner,
};

impl<'a, 'ctx: 'a> Planner<'a, 'ctx> {
    pub(in super::super) fn plan_edge_fixup(
        &mut self,
        templates: &SecondaryMap<BlockId, BlockTemplate>,
        phi_results: &SecondaryMap<BlockId, SmallVec<[ValueId; 4]>>,
        pred: BlockId,
        succ: BlockId,
    ) {
        // Edge fixup:
        // 1) normalize carried transfer to successor's chosen `T(S)`
        // 2) push phi arguments so successor sees `P(S)` on entry
        let tmpl = &templates[succ];

        let phi_srcs = phi_args_for_edge(self.ctx.func, pred, succ);
        debug_assert_eq!(
            phi_srcs.len(),
            phi_results[succ].len(),
            "phi source/result arity mismatch for edge {pred:?}->{succ:?}"
        );

        // 1) Normalize carried transfer to the successor's transfer list, while
        // preserving reachable phi sources so we can forward them without forcing `spill_set`.
        let phi_count = phi_results[succ].len();
        let mut preserve_phi_srcs: BitSet<ValueId> = BitSet::default();
        for &src in phi_srcs.iter() {
            if self.ctx.func.dfg.value_is_imm(src) {
                continue;
            }
            if let Some(pos) = self.stack.find_reachable_value(src, SWAP_MAX) {
                // Conservatively ensure the source stays reachable after pushing the phi prefix.
                if pos + phi_count <= SWAP_MAX {
                    preserve_phi_srcs.insert(src);
                }
            }
        }
        self.normalize_to_transfer_with_preserve(tmpl.transfer.as_slice(), &preserve_phi_srcs);

        // 2) Push phi parameters so successor sees its parameter prefix on entry.
        let transfer_set: BitSet<ValueId> = tmpl.transfer.as_slice().into();
        let mut remaining_src_uses: BTreeMap<ValueId, u32> = BTreeMap::new();
        for &src in phi_srcs.iter() {
            if self.ctx.func.dfg.value_is_imm(src) {
                continue;
            }
            *remaining_src_uses.entry(src).or_insert(0) += 1;
        }

        for (&phi_res, &src) in phi_results[succ].iter().zip(phi_srcs.iter()).rev() {
            if self.ctx.func.dfg.value_is_imm(src) {
                let imm = self
                    .ctx
                    .func
                    .dfg
                    .value_imm(src)
                    .expect("imm value missing payload");
                self.stack.push_imm(phi_res, imm, self.actions);
            } else {
                let rem = remaining_src_uses
                    .get_mut(&src)
                    .expect("phi source missing from use-count map");
                *rem = rem.saturating_sub(1);
                let is_last_use_on_edge = *rem == 0;

                if is_last_use_on_edge && !transfer_set.contains(src) {
                    // Prefer consuming the existing stack copy (by stable-rotating it to the top)
                    // instead of duplicating/loading it. This avoids leaving an extra dead copy
                    // of `src` below the phi prefix.
                    if let Some(pos) = self.stack.find_reachable_value(src, SWAP_MAX) {
                        self.stack.stable_rotate_to_top(pos, self.actions);
                        self.stack.rename_top_value(phi_res);
                    } else {
                        self.push_value_from_spill_slot_or_mark(src, phi_res);
                    }
                } else if let Some(pos) = self.stack.find_reachable_value(src, DUP_MAX) {
                    self.stack.dup(pos, self.actions);
                    self.stack.rename_top_value(phi_res);
                } else {
                    self.push_value_from_spill_slot_or_mark(src, phi_res);
                }
            }

            // If the phi result is in `spill_set`, store it immediately while it is on top.
            self.emit_store_if_spilled(phi_res);
        }
    }

    pub fn plan_internal_return(&mut self, inst: InstId) {
        let Some(ret_val) = self.ctx.func.dfg.as_return(inst) else {
            // No return value: pop everything above the function return address.
            self.stack.clear_above_func_ret(self.actions);
            return;
        };

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
