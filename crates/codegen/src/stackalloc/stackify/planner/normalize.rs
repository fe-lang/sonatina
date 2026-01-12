use crate::bitset::BitSet;
use smallvec::SmallVec;
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
    fn try_normalize_to_exact(&mut self, desired: &[ValueId]) -> bool {
        if desired.len() > SWAP_MAX {
            return false;
        }

        let mut limit = self.stack.len_above_func_ret();
        if limit > SWAP_MAX {
            return false;
        }

        let mut req: BTreeMap<ValueId, usize> = BTreeMap::new();
        for &v in desired.iter() {
            *req.entry(v).or_insert(0) += 1;
        }

        // 1) Remove any extra values (including duplicates) so the stack multiset matches `req`.
        loop {
            limit = self.stack.len_above_func_ret();
            debug_assert!(limit <= SWAP_MAX);

            let mut cur: BTreeMap<ValueId, usize> = BTreeMap::new();
            for item in self.stack.iter().take(limit) {
                let StackItem::Value(v) = item else {
                    continue;
                };
                *cur.entry(*v).or_insert(0) += 1;
            }

            let mut victim: Option<usize> = None;
            for (i, item) in self.stack.iter().take(limit).enumerate() {
                let StackItem::Value(v) = item else {
                    continue;
                };
                let have = cur.get(v).copied().unwrap_or(0);
                let need = req.get(v).copied().unwrap_or(0);
                if have > need || need == 0 {
                    victim = Some(i);
                    break;
                }
            }

            // If we found no removable element, our multiset already matches.
            let Some(victim) = victim else {
                break;
            };
            self.stack
                .unstable_delete_at_pos(victim, &mut *self.actions);
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

    pub(super) fn normalize_to_transfer_with_preserve(
        &mut self,
        target: &[ValueId],
        preserve: &BitSet<ValueId>,
    ) {
        // Contract: rewrite the current symbolic stack (above the function return barrier, if any)
        // so that `target` is present in-order (top-first), allowing `preserve` values to remain.
        //
        // - stable-delete reachable unwanted values within `SWAP16` reach
        // - if any unwanted remain (too deep), flush & rebuild from memory homes (dropping preserves)
        // - if the target order mismatches, flush & rebuild (dropping preserves)
        let mut wanted: BitSet<ValueId> = target.iter().copied().collect();
        wanted.union_with(preserve);

        // Step 1: delete reachable unwanted values.
        //
        // If `target` already appears as a subsequence, keep stable deletion to avoid
        // needlessly breaking the order and forcing a permutation later.
        let stable_deletes = matches_transfer_subsequence(self.stack, target);
        loop {
            if let Some(StackItem::Value(v)) = self.stack.top()
                && !wanted.contains(*v)
            {
                self.stack.pop(&mut *self.actions);
                continue;
            }

            let Some(pos) = find_deepest_reachable_unwanted(self.stack, &wanted, SWAP_MAX) else {
                break;
            };
            if stable_deletes {
                self.stack
                    .stable_delete_at_depth(pos + 1, &mut *self.actions);
            } else {
                self.stack.unstable_delete_at_pos(pos, &mut *self.actions);
            }
        }

        // Step 2: if any unwanted values remain above the function return barrier, flush & rebuild.
        if exists_unwanted(self.stack, &wanted) {
            self.flush_rebuild(target);
            return;
        }

        // Step 3: if the target order mismatches, try SWAP/DUP/POP normalization within reach
        // before falling back to flush & rebuild (which may unnecessarily grow `spill_set`).
        if preserve.is_empty() {
            if !matches_transfer_exact(self.stack, target) && !self.try_normalize_to_exact(target) {
                self.flush_rebuild(target);
            }
            return;
        }

        if matches_transfer_subsequence(self.stack, target) {
            return;
        }

        // Prefer leaving `target` as a suffix (so the preserved values are closer to the top and
        // can be forwarded into phi results), but only if it fits within `SWAP16` reach.
        let target_set: BitSet<ValueId> = target.iter().copied().collect();
        let mut preserve_prefix: SmallVec<[ValueId; 4]> = SmallVec::new();
        let mut seen: BitSet<ValueId> = BitSet::default();
        let limit = self.stack.len_above_func_ret();
        for item in self.stack.iter().take(limit) {
            let StackItem::Value(v) = item else {
                continue;
            };
            if preserve.contains(*v) && !target_set.contains(*v) && seen.insert(*v) {
                preserve_prefix.push(*v);
            }
        }

        let mut desired: SmallVec<[ValueId; 12]> = SmallVec::new();
        desired.extend(preserve_prefix.iter().copied());
        desired.extend(target.iter().copied());

        if !self.try_normalize_to_exact(desired.as_slice()) {
            self.flush_rebuild(target);
        }
    }

    fn flush_rebuild(&mut self, target: &[ValueId]) {
        let base_len = self.stack.common_suffix_len(target);

        // Pop everything above the common base suffix.
        while self.stack.len_above_func_ret() > base_len {
            self.stack.pop(self.actions);
        }

        // Rebuild the remaining prefix bottom-to-top (push reverse so final is top-first).
        for &v in target[..target.len().saturating_sub(base_len)].iter().rev() {
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

fn matches_transfer_exact(stack: &SymStack, target: &[ValueId]) -> bool {
    let limit = stack.len_above_func_ret();
    limit == target.len()
        && stack
            .iter()
            .take(limit)
            .zip(target.iter().copied())
            .all(|(item, v)| item == &StackItem::Value(v))
}

fn matches_transfer_subsequence(stack: &SymStack, target: &[ValueId]) -> bool {
    let limit = stack.len_above_func_ret();
    let mut want_idx: usize = 0;
    for item in stack.iter().take(limit) {
        if want_idx >= target.len() {
            break;
        }
        if item == &StackItem::Value(target[want_idx]) {
            want_idx += 1;
        }
    }
    want_idx == target.len()
}

fn find_deepest_reachable_unwanted(
    stack: &SymStack,
    wanted: &BitSet<ValueId>,
    max_depth: usize,
) -> Option<usize> {
    let limit = stack.len_above_func_ret().min(max_depth);
    stack
        .iter()
        .take(limit)
        .enumerate()
        .filter_map(|(i, item)| match item {
            StackItem::Value(v) if !wanted.contains(*v) => Some(i),
            _ => None,
        })
        .last()
}

fn exists_unwanted(stack: &SymStack, wanted: &BitSet<ValueId>) -> bool {
    let limit = stack.len_above_func_ret();
    for item in stack.iter().take(limit) {
        let StackItem::Value(v) = item else {
            continue;
        };
        if !wanted.contains(*v) {
            return true;
        }
    }
    false
}
