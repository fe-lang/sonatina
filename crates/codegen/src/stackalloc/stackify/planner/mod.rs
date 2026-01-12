mod control_flow;
mod normalize;
mod operand_prep;

use crate::{
    bitset::BitSet,
    liveness::Liveness,
    stackalloc::{Action, Actions},
};
use sonatina_ir::ValueId;

use super::{
    StackifyContext,
    slots::{FreeSlots, SlotState},
    spill::{SpillDiscovery, SpillSet},
    sym_stack::SymStack,
};

pub(super) struct MemPlan<'a> {
    free_slots: &'a mut FreeSlots,
    slots: &'a mut SlotState,
    liveness: &'a Liveness,
    spill: SpillDiscovery<'a>,
}

impl<'a> MemPlan<'a> {
    pub(super) fn new(
        spill: SpillSet<'a>,
        spill_requests: &'a mut BitSet<ValueId>,
        free_slots: &'a mut FreeSlots,
        slots: &'a mut SlotState,
        liveness: &'a Liveness,
    ) -> Self {
        Self {
            free_slots,
            slots,
            liveness,
            spill: SpillDiscovery::new(spill, spill_requests),
        }
    }

    pub(super) fn spill_set(&self) -> SpillSet<'a> {
        self.spill.spill_set()
    }

    pub(super) fn spill_requests(&self) -> &BitSet<ValueId> {
        self.spill.spill_requests()
    }

    pub(super) fn free_slots(&self) -> &FreeSlots {
        &*self.free_slots
    }

    pub(super) fn slot_state(&self) -> &SlotState {
        &*self.slots
    }

    pub(super) fn liveness(&self) -> &Liveness {
        self.liveness
    }

    fn load_frame_slot_or_placeholder(&mut self, v: ValueId) -> Action {
        let Some(spilled) = self.spill.spilled(v) else {
            self.spill.request_spill(v);
            // This fixed-point iteration will be discarded; the real slot assignment happens at
            // `v`'s definition once it becomes part of `spill_set`.
            return Action::MemLoadFrameSlot(0);
        };

        let slot = self
            .slots
            .ensure_slot(spilled, self.liveness, &mut *self.free_slots);
        Action::MemLoadFrameSlot(slot)
    }

    fn emit_store_if_spilled(&mut self, v: ValueId, actions: &mut Actions) {
        let Some(spilled) = self.spill.spilled(v) else {
            return;
        };
        let slot = self
            .slots
            .ensure_slot(spilled, self.liveness, &mut *self.free_slots);
        actions.push(Action::StackDup(0));
        actions.push(Action::MemStoreFrameSlot(slot));
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
        self.mem.emit_store_if_spilled(v, self.actions);
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
