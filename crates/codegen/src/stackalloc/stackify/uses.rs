use sonatina_ir::{BlockId, I256, ValueId};
use std::collections::BTreeMap;

use crate::bitset::BitSet;

use super::{
    block::operand_order_for_stackify,
    builder::StackifyContext,
    slots::{FreeSlots, SlotPool},
    sym_stack::{StackItem, SymStack},
};

/// Per-block value-use bookkeeping threaded through the instruction walk.
///
/// Tracks how many in-block uses remain for each retained value (`remaining`) and each cached
/// immediate (`cached_imm_remaining`), the set of values still used later in the block
/// (`live_future`), and the block's live-out set unioned with phi-out sources (`live_out`).
pub(super) struct UseTracker {
    remaining: BTreeMap<ValueId, u32>,
    cached_imm_remaining: BTreeMap<I256, u32>,
    live_future: BitSet<ValueId>,
    live_out: BitSet<ValueId>,
}

impl UseTracker {
    pub(super) fn for_block(ctx: &StackifyContext<'_>, block: BlockId) -> Self {
        let mut remaining: BTreeMap<ValueId, u32> = BTreeMap::new();
        let mut cached_imm_remaining: BTreeMap<I256, u32> = BTreeMap::new();
        for inst in ctx.func.layout.iter_inst(block) {
            if ctx.func.dfg.is_phi(inst) {
                continue;
            }
            for v in operand_order_for_stackify(ctx.func, inst, &ctx.value_aliases) {
                if ctx.retains_value(v) {
                    *remaining.entry(v).or_insert(0) += 1;
                } else if ctx.stack_caches_immediate(v)
                    && let Some(imm) = ctx.func.dfg.value_imm(v)
                {
                    *cached_imm_remaining.entry(imm.as_i256()).or_insert(0) += 1;
                }
            }
        }
        let live_future: BitSet<ValueId> = remaining.keys().copied().collect();
        let mut live_out = ctx.liveness.block_live_outs(block).clone();
        live_out.union_with(&ctx.phi_out_sources[block]);
        Self {
            remaining,
            cached_imm_remaining,
            live_future,
            live_out,
        }
    }

    pub(super) fn live_future(&self) -> &BitSet<ValueId> {
        &self.live_future
    }

    pub(super) fn live_out(&self) -> &BitSet<ValueId> {
        &self.live_out
    }

    pub(super) fn is_dead(&self, v: ValueId) -> bool {
        !self.live_future.contains(v) && !self.live_out.contains(v)
    }

    /// Values in `args` whose in-block uses all end at this instruction (and which are not
    /// live-out), so they may be consumed directly from the stack.
    pub(super) fn last_uses_in(
        &self,
        ctx: &StackifyContext<'_>,
        args: &[ValueId],
    ) -> BitSet<ValueId> {
        let mut inst_counts: BTreeMap<ValueId, u32> = BTreeMap::new();
        for &v in args.iter() {
            if !ctx.retains_value(v) {
                continue;
            }
            *inst_counts.entry(v).or_insert(0) += 1;
        }

        let mut last_use: BitSet<ValueId> = BitSet::default();
        for (v, count) in inst_counts {
            let rem = self.remaining.get(&v).copied().unwrap_or(0);
            if rem == count && !self.live_out.contains(v) {
                last_use.insert(v);
            }
        }
        last_use
    }

    /// Cached immediates in `args` that have further in-block uses beyond this instruction and so
    /// should be kept on the stack rather than consumed.
    pub(super) fn cache_preserve_in(
        &self,
        ctx: &StackifyContext<'_>,
        args: &[ValueId],
    ) -> BitSet<ValueId> {
        let mut inst_counts: BTreeMap<I256, u32> = BTreeMap::new();
        for &value in args {
            if ctx.stack_caches_immediate(value)
                && let Some(imm) = ctx.func.dfg.value_imm(value)
            {
                *inst_counts.entry(imm.as_i256()).or_insert(0) += 1;
            }
        }

        let mut preserve: BitSet<ValueId> = BitSet::default();
        for &value in args {
            if ctx.stack_caches_immediate(value)
                && let Some(imm) = ctx.func.dfg.value_imm(value)
                && self
                    .cached_imm_remaining
                    .get(&imm.as_i256())
                    .copied()
                    .unwrap_or(0)
                    > inst_counts.get(&imm.as_i256()).copied().unwrap_or(0)
            {
                preserve.insert(value);
            }
        }
        preserve
    }

    /// Consume one use of each operand in `args`, releasing scratch slots for values that die here
    /// and decaying cached-immediate counts.
    pub(super) fn consume(
        &mut self,
        ctx: &StackifyContext<'_>,
        args: &[ValueId],
        scratch_slots: &SlotPool,
        free_scratch: &mut FreeSlots,
    ) {
        for &v in args {
            if ctx.retains_value(v)
                && let Some(n) = self.remaining.get_mut(&v)
            {
                let before = *n;
                *n = n.saturating_sub(1);
                if before != 0 && *n == 0 {
                    self.live_future.remove(v);
                    if !ctx.func.dfg.value_is_imm(v) && !self.live_out.contains(v) {
                        scratch_slots.release_if_assigned(v, free_scratch);
                    }
                }
            }
        }

        for &value in args {
            if ctx.stack_caches_immediate(value)
                && let Some(imm) = ctx.func.dfg.value_imm(value)
                && let Some(count) = self.cached_imm_remaining.get_mut(&imm.as_i256())
            {
                *count = count.saturating_sub(1);
            }
        }
        self.cached_imm_remaining.retain(|_, count| *count != 0);
    }

    /// `live_future`, extended with any cached immediates still on `stack` that have remaining
    /// in-block uses, so dead-prefix cleanup does not drop a reusable cached immediate.
    pub(super) fn cleanup_live(
        &self,
        ctx: &StackifyContext<'_>,
        stack: &SymStack,
    ) -> BitSet<ValueId> {
        let mut live = self.live_future.clone();
        if self.cached_imm_remaining.is_empty() {
            return live;
        }

        for item in stack.iter() {
            if let StackItem::Value(value) = item
                && ctx.stack_caches_immediate(*value)
                && let Some(imm) = ctx.func.dfg.value_imm(*value)
                && self
                    .cached_imm_remaining
                    .get(&imm.as_i256())
                    .is_some_and(|count| *count != 0)
            {
                live.insert(*value);
            }
        }
        live
    }
}
