mod control_flow;
mod normalize;
mod normalize_search;
mod operand_prep;

use crate::{
    bitset::BitSet,
    liveness::Liveness,
    stackalloc::{Action, Actions},
};
use cranelift_entity::{EntityRef, SecondaryMap};
use sonatina_ir::ValueId;

use super::{
    StackifyContext,
    slots::{FreeSlotPools, SpillSlotPools},
    spill::{SpillDiscovery, SpillSet},
    sym_stack::SymStack,
};

pub(super) struct MemPlan<'a> {
    scratch_live_values: &'a BitSet<ValueId>,
    scratch_spill_slots: u32,
    spill_obj: &'a SecondaryMap<ValueId, Option<crate::isa::evm::static_arena_alloc::StackObjId>>,
    free_slots: &'a mut FreeSlotPools,
    slots: &'a mut SpillSlotPools,
    liveness: &'a Liveness,
    spill: SpillDiscovery<'a>,
}

impl<'a> MemPlan<'a> {
    pub(super) fn new(
        spill: SpillSet<'a>,
        spill_requests: &'a mut BitSet<ValueId>,
        ctx: &'a StackifyContext<'_>,
        spill_obj: &'a SecondaryMap<
            ValueId,
            Option<crate::isa::evm::static_arena_alloc::StackObjId>,
        >,
        free_slots: &'a mut FreeSlotPools,
        slots: &'a mut SpillSlotPools,
    ) -> Self {
        Self {
            scratch_live_values: &ctx.scratch_live_values,
            scratch_spill_slots: ctx.scratch_spill_slots,
            spill_obj,
            free_slots,
            slots,
            liveness: ctx.liveness,
            spill: SpillDiscovery::new(spill, spill_requests),
        }
    }

    pub(super) fn spill_set(&self) -> SpillSet<'a> {
        self.spill.spill_set()
    }

    pub(super) fn spill_requests(&self) -> &BitSet<ValueId> {
        self.spill.spill_requests()
    }

    pub(super) fn free_slots(&self) -> &FreeSlotPools {
        &*self.free_slots
    }

    pub(super) fn slot_state(&self) -> &SpillSlotPools {
        &*self.slots
    }

    fn load_frame_slot_or_placeholder(&mut self, v: ValueId) -> Action {
        let Some(_) = self.spill.spilled(v) else {
            self.spill.request_spill(v);
            // This fixed-point iteration will be discarded; the real slot assignment happens at
            // `v`'s definition once it becomes part of `spill_set`.
            return Action::MemLoadObj(crate::isa::evm::static_arena_alloc::StackObjId::new(0));
        };

        if self.scratch_spill_slots != 0
            && !self.scratch_live_values.contains(v)
            && let Some(slot) = self.slots.scratch.slot_for(v)
        {
            return Action::MemLoadAbs(slot * 32);
        }

        // Invariant: every spilled value has a `StackObjId` assigned by stackify's builder
        // (should be verified when finalizing the spill set).
        Action::MemLoadObj(self.spill_obj[v].expect("spilled value missing stack object id"))
    }

    fn emit_store_if_spilled_at_depth(&mut self, v: ValueId, depth: u8, actions: &mut Actions) {
        let Some(spilled) = self.spill.spilled(v) else {
            return;
        };

        actions.push(Action::StackDup(depth));

        if self.scratch_spill_slots != 0
            && !self.scratch_live_values.contains(v)
            && let Some(slot) = self.slots.scratch.try_ensure_slot(
                spilled,
                self.liveness,
                &mut self.free_slots.scratch,
                Some(self.scratch_spill_slots),
            )
        {
            actions.push(Action::MemStoreAbs(slot * 32));
            return;
        }

        actions.push(Action::MemStoreObj(
            self.spill_obj[v].expect("spilled value missing stack object id"),
        ));
    }
}

/// Planning context for a single instruction/edge.
///
/// This bundles the symbolic stack + output action list with the current fixed-point
/// iteration's `spill_set` and frame-slot allocation state, avoiding large `&mut`
/// argument lists throughout the planner.
pub(super) struct Planner<'a, 'ctx: 'a> {
    ctx: &'a StackifyContext<'ctx>,
    stack: &'a mut SymStack,
    actions: &'a mut Actions,
    mem: MemPlan<'a>,
}

impl<'a, 'ctx: 'a> Planner<'a, 'ctx> {
    pub(super) fn new(
        ctx: &'a StackifyContext<'ctx>,
        stack: &'a mut SymStack,
        actions: &'a mut Actions,
        mem: MemPlan<'a>,
    ) -> Self {
        Self {
            ctx,
            stack,
            actions,
            mem,
        }
    }

    pub(super) fn emit_store_if_spilled(&mut self, v: ValueId) {
        self.mem.emit_store_if_spilled_at_depth(v, 0, self.actions);
    }

    pub(super) fn emit_store_if_spilled_at_depth(&mut self, v: ValueId, depth: usize) {
        if !self.mem.spill_set().contains(v) {
            return;
        }
        debug_assert!(depth < self.ctx.reach.dup_max, "DUP out of range");
        self.mem
            .emit_store_if_spilled_at_depth(v, depth as u8, self.actions);
    }

    fn push_value_from_spill_slot_or_mark(&mut self, load_from: ValueId, stack_as: ValueId) {
        debug_assert!(
            !self.ctx.func.dfg.value_is_imm(load_from),
            "immediates must be pushed via `Action::Push`"
        );

        let act = self.mem.load_frame_slot_or_placeholder(load_from);
        self.actions.push(act);
        self.stack.push_value(stack_as);
    }
}
