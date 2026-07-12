use sonatina_ir::{BlockId, ValueId};
use std::collections::BTreeMap;

use crate::bitset::BitSet;

use super::{
    block::operand_order_for_stackify,
    builder::StackifyContext,
    slots::{FreeSlots, SlotPool},
};

/// Per-block value-use bookkeeping threaded through the instruction walk.
///
/// Tracks how many in-block uses remain for each use-tracked value (`remaining`) — pinned values
/// and cached immediates alike, since immediates are canonicalized to one `ValueId` per word — the
/// set of values still used later in the block (`live_future`), and the block's live-out set
/// unioned with phi-out sources (`live_out`). `live_out` never contains immediates (liveness only
/// `mark_use`s them and `phi_out_sources` filters them), so a cached immediate is live exactly
/// until its last in-block use.
pub(super) struct UseTracker {
    remaining: BTreeMap<ValueId, u32>,
    live_future: BitSet<ValueId>,
    live_out: BitSet<ValueId>,
}

impl UseTracker {
    pub(super) fn for_block(ctx: &StackifyContext<'_>, block: BlockId) -> Self {
        let mut remaining: BTreeMap<ValueId, u32> = BTreeMap::new();
        for inst in ctx.func.layout.iter_inst(block) {
            if ctx.func.dfg.is_phi(inst) {
                continue;
            }
            for v in operand_order_for_stackify(ctx.func, inst, &ctx.value_aliases) {
                if ctx.is_use_tracked(v) {
                    *remaining.entry(v).or_insert(0) += 1;
                }
            }
        }
        let live_future: BitSet<ValueId> = remaining.keys().copied().collect();
        let mut live_out = ctx.liveness.block_live_outs(block).clone();
        live_out.union_with(&ctx.phi_out_sources[block]);
        Self {
            remaining,
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
    /// live-out), so they may be consumed directly from the stack. Restricted to pinned values:
    /// cached immediates stay out of the consume-last-use search mask (they are rematerializable,
    /// and their keep-vs-consume choice is expressed through `cache_preserve_in` instead).
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

    /// Cached immediates in `args` that have further in-block uses beyond this instruction — the
    /// inverse of a last use — and so should be kept on the stack rather than consumed.
    pub(super) fn cache_preserve_in(
        &self,
        ctx: &StackifyContext<'_>,
        args: &[ValueId],
    ) -> BitSet<ValueId> {
        let mut inst_counts: BTreeMap<ValueId, u32> = BTreeMap::new();
        for &value in args {
            if ctx.stack_caches_immediate(value) {
                *inst_counts.entry(value).or_insert(0) += 1;
            }
        }

        let mut preserve: BitSet<ValueId> = BitSet::default();
        for (value, count) in inst_counts {
            if self.remaining.get(&value).copied().unwrap_or(0) > count {
                preserve.insert(value);
            }
        }
        preserve
    }

    /// Consume one use of each operand in `args`, dropping values from `live_future` at their last
    /// in-block use and releasing scratch slots for non-immediate values that die here.
    pub(super) fn consume(
        &mut self,
        ctx: &StackifyContext<'_>,
        args: &[ValueId],
        scratch_slots: &SlotPool,
        free_scratch: &mut FreeSlots,
    ) {
        for &v in args {
            if ctx.is_use_tracked(v)
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
    }
}
