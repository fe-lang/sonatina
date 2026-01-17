use sonatina_ir::ValueId;
use std::collections::BTreeMap;

use super::{
    super::{
        DUP_MAX, SWAP_MAX,
        sym_stack::{StackItem, SymStack},
    },
    Planner,
};

impl<'a, 'ctx: 'a> Planner<'a, 'ctx> {
    pub(super) fn normalize_to_exact(&mut self, desired: &[ValueId]) {
        // Contract: rewrite the current symbolic stack (above the function return barrier, if any)
        // so that it matches `desired` exactly (top-first).
        if matches_exact(self.stack, desired) {
            return;
        }
        if self.try_normalize_to_exact(desired) {
            return;
        }
        self.flush_rebuild(desired);
    }

    fn delete_to_match_multiset(&mut self, req: &BTreeMap<ValueId, usize>) -> bool {
        let limit = self.stack.len_above_func_ret();
        let mut keep: Vec<bool> = vec![false; limit];

        // Choose the deepest occurrences to keep. This tends to keep values that are already
        // "out of reach" (e.g. deep transfer values) while discarding dead prefixes, which helps
        // avoid long swap+pop chains when cleaning up edge stacks.
        let mut remaining: BTreeMap<ValueId, usize> = req.clone();
        for depth in (0..limit).rev() {
            let Some(StackItem::Value(v)) = self.stack.item_at(depth) else {
                return false;
            };
            let need = remaining.get(v).copied().unwrap_or(0);
            if need == 0 {
                continue;
            }
            keep[depth] = true;
            if need == 1 {
                remaining.remove(v);
            } else {
                remaining.insert(*v, need - 1);
            }
        }

        self.delete_unkept_values(&mut keep);
        true
    }

    fn delete_unkept_values(&mut self, keep: &mut Vec<bool>) {
        // Delete all values marked as "not kept" using only SWAPs + POPs.
        //
        // Key optimization: if we have a kept prefix followed by a long contiguous run of
        // deletable values (and more kept values below), we can sink the kept prefix below the
        // run with O(k) swaps and then pop the entire run without per-item swaps.
        while keep.iter().any(|k| !*k) {
            if !keep[0] {
                self.stack.pop(self.actions);
                keep.remove(0);
                continue;
            }

            let keep_prefix_len = keep.iter().take_while(|k| **k).count();
            debug_assert!(keep_prefix_len > 0);

            let mut run_len: usize = 0;
            for k in keep.iter().skip(keep_prefix_len) {
                if *k {
                    break;
                }
                run_len += 1;
            }

            let can_bulk_delete = run_len != 0
                && keep_prefix_len + run_len < keep.len()
                && run_len > keep_prefix_len.saturating_mul(2).saturating_sub(1);
            if can_bulk_delete {
                let mut prefix = keep_prefix_len;
                let mut run = run_len;
                while prefix != 0 {
                    // Swap the top kept value with the bottom of the deletable run,
                    // making a deletable value immediately available to pop.
                    let sink_depth = prefix + run - 1;
                    self.stack.swap(sink_depth, self.actions);
                    keep.swap(0, sink_depth);

                    debug_assert!(!keep[0], "bulk delete expected deletable value on top");
                    self.stack.pop(self.actions);
                    keep.remove(0);

                    run = run.saturating_sub(1);
                    prefix = prefix.saturating_sub(1);
                }

                for _ in 0..run {
                    debug_assert!(!keep[0], "bulk delete expected deletable prefix");
                    self.stack.pop(self.actions);
                    keep.remove(0);
                }
                continue;
            }

            // Fallback: swap the first deletable value to the top and pop it.
            let pos = keep
                .iter()
                .position(|k| !*k)
                .expect("keep mask had deletable values");
            debug_assert!(pos != 0);
            self.stack.swap(pos, self.actions);
            keep.swap(0, pos);
            self.stack.pop(self.actions);
            keep.remove(0);
        }
    }

    fn try_normalize_to_exact(&mut self, desired: &[ValueId]) -> bool {
        if desired.len() > SWAP_MAX {
            return false;
        }

        let mut limit = self.stack.len_above_func_ret();
        if limit > SWAP_MAX {
            return false;
        }

        // If the desired stack begins with one or more immediates, delay pushing them until after
        // the existing (non-immediate) stack prefix is normalized. This avoids permuting around
        // freshly-pushed constants (e.g. a loop-entry phi source `0`).
        let imm_prefix_len = desired
            .iter()
            .take_while(|v| self.ctx.func.dfg.value_is_imm(**v))
            .count();
        if imm_prefix_len != 0 {
            let tail = &desired[imm_prefix_len..];
            if !self.try_normalize_to_exact(tail) {
                return false;
            }

            for &v in desired[..imm_prefix_len].iter().rev() {
                let imm = self
                    .ctx
                    .func
                    .dfg
                    .value_imm(v)
                    .expect("imm value missing payload");
                self.stack.push_imm(v, imm, self.actions);
            }
            return true;
        }

        let mut req: BTreeMap<ValueId, usize> = BTreeMap::new();
        for &v in desired.iter() {
            *req.entry(v).or_insert(0) += 1;
        }

        // 1) Remove any extra values (including duplicates) so the stack multiset matches `req`.
        if !self.delete_to_match_multiset(&req) {
            return false;
        }

        // 2) Materialize any missing required multiplicities (DUP, PUSH, or MLOAD).
        limit = self.stack.len_above_func_ret();
        if limit > SWAP_MAX {
            return false;
        }

        let mut cur: BTreeMap<ValueId, usize> = BTreeMap::new();
        for item in self.stack.iter().take(limit) {
            let StackItem::Value(v) = item else {
                continue;
            };
            *cur.entry(*v).or_insert(0) += 1;
        }

        for (&v, &need) in req.iter() {
            let have = cur.get(&v).copied().unwrap_or(0);
            if have >= need {
                continue;
            }
            for _ in have..need {
                if self.ctx.func.dfg.value_is_imm(v) {
                    let imm = self
                        .ctx
                        .func
                        .dfg
                        .value_imm(v)
                        .expect("imm value missing payload");
                    self.stack.push_imm(v, imm, self.actions);
                } else if let Some(pos) = self.stack.find_reachable_value(v, DUP_MAX) {
                    self.stack.dup(pos, &mut *self.actions);
                } else {
                    self.push_value_from_spill_slot_or_mark(v, v);
                }
            }
        }

        // 3) Permute to the exact required order (bottom-up) using only SWAPs.
        if self.stack.len_above_func_ret() != desired.len() {
            return false;
        }
        let base_len = self.stack.common_suffix_len(desired);
        let permute_limit = desired.len().saturating_sub(base_len);
        for (depth, &want) in desired.iter().take(permute_limit).enumerate().rev() {
            if self.stack.item_at(depth) == Some(&StackItem::Value(want)) {
                continue;
            }

            let Some(pos) = self.stack.find_reachable_value(want, depth + 1) else {
                return false;
            };

            if pos != 0 {
                self.stack.swap(pos, self.actions);
            }
            self.stack.swap(depth, self.actions);

            debug_assert!(self.stack.item_at(depth) == Some(&StackItem::Value(want)));
        }

        true
    }

    fn flush_rebuild(&mut self, desired: &[ValueId]) {
        let base_len = self.stack.common_suffix_len(desired);

        // Pop everything above the common base suffix.
        while self.stack.len_above_func_ret() > base_len {
            self.stack.pop(self.actions);
        }

        // Rebuild the remaining prefix bottom-to-top (push reverse so final is top-first).
        for &v in desired[..desired.len().saturating_sub(base_len)]
            .iter()
            .rev()
        {
            if self.ctx.func.dfg.value_is_imm(v) {
                let imm = self
                    .ctx
                    .func
                    .dfg
                    .value_imm(v)
                    .expect("imm value missing payload");
                self.stack.push_imm(v, imm, self.actions);
            } else {
                self.push_value_from_spill_slot_or_mark(v, v);
            }
        }
    }

    /// Delete everything between the current top value and the function return barrier, preserving
    /// the top value.
    ///
    /// This is a specialized cleanup used at internal returns. When there is more than one value
    /// between `[ret_val]` and `FuncRetAddr`, we swap the return value down as close as possible
    /// (up to `SWAP16`) and then pop a run of intermediates, repeating until the barrier is
    /// directly below the top.
    pub(super) fn delete_between_top_and_func_ret(&mut self) {
        loop {
            let Some(barrier_pos) = self.stack.func_ret_index() else {
                break;
            };
            if barrier_pos <= 1 {
                break;
            }
            let between = barrier_pos.saturating_sub(1);
            let swap_depth = between.min(DUP_MAX);
            debug_assert!(swap_depth >= 1);
            self.stack.swap(swap_depth, self.actions);
            self.stack.pop_n(swap_depth, self.actions);
        }
    }
}

fn matches_exact(stack: &SymStack, desired: &[ValueId]) -> bool {
    let limit = stack.len_above_func_ret();
    limit == desired.len()
        && stack
            .iter()
            .take(limit)
            .zip(desired.iter().copied())
            .all(|(item, v)| item == &StackItem::Value(v))
}
