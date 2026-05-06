mod control_flow;
mod normalize;
mod normalize_search;
mod operand_prep;
#[cfg(test)]
mod test_utils;

pub(super) use normalize_search::NormalizeSearchScratch;

use crate::{
    analysis::memory_access::ExactLocalAddr,
    bitset::BitSet,
    stackalloc::{Action, Actions},
};
use cranelift_entity::{EntityRef, SecondaryMap};
use sonatina_ir::ValueId;

use super::{
    StackifyContext,
    slots::{FreeSlotPools, SpillSlotInterference, SpillSlotPools},
    spill::{SpillDiscovery, SpillSet},
    sym_stack::SymStack,
};

#[derive(Clone)]
pub(super) struct MemPlanSnapshot {
    free_slots: FreeSlotPools,
    slots: SpillSlotPools,
    spill_requests: BitSet<ValueId>,
    object_spill_requests: BitSet<ValueId>,
}

pub(super) struct MemPlan<'a> {
    scratch_live_values: &'a BitSet<ValueId>,
    scratch_spill_slots: u32,
    spill_obj: &'a SecondaryMap<ValueId, Option<crate::isa::evm::static_arena_alloc::StackObjId>>,
    exact_local_addr: &'a SecondaryMap<ValueId, Option<ExactLocalAddr>>,
    object_spill_requests: &'a mut BitSet<ValueId>,
    forced_object_spills: &'a BitSet<ValueId>,
    free_slots: &'a mut FreeSlotPools,
    slots: &'a mut SpillSlotPools,
    spill_slot_interference: &'a SpillSlotInterference,
    spill: SpillDiscovery<'a>,
}

impl<'a> MemPlan<'a> {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn new(
        spill: SpillSet<'a>,
        spill_requests: &'a mut BitSet<ValueId>,
        ctx: &'a StackifyContext<'_>,
        spill_obj: &'a SecondaryMap<
            ValueId,
            Option<crate::isa::evm::static_arena_alloc::StackObjId>,
        >,
        exact_local_addr: &'a SecondaryMap<ValueId, Option<ExactLocalAddr>>,
        object_spill_requests: &'a mut BitSet<ValueId>,
        forced_object_spills: &'a BitSet<ValueId>,
        free_slots: &'a mut FreeSlotPools,
        slots: &'a mut SpillSlotPools,
    ) -> Self {
        Self {
            scratch_live_values: &ctx.scratch_live_values,
            scratch_spill_slots: ctx.scratch_spill_slots,
            spill_obj,
            exact_local_addr,
            object_spill_requests,
            forced_object_spills,
            free_slots,
            slots,
            spill_slot_interference: &ctx.spill_slot_interference,
            spill: SpillDiscovery::new(spill, spill_requests),
        }
    }

    pub(super) fn spill_set(&self) -> SpillSet<'a> {
        self.spill.spill_set()
    }

    pub(super) fn snapshot(&self) -> MemPlanSnapshot {
        MemPlanSnapshot {
            free_slots: self.free_slots.clone(),
            slots: self.slots.clone(),
            spill_requests: self.spill.spill_requests().clone(),
            object_spill_requests: (*self.object_spill_requests).clone(),
        }
    }

    pub(super) fn restore(&mut self, snapshot: MemPlanSnapshot) {
        *self.free_slots = snapshot.free_slots;
        *self.slots = snapshot.slots;
        self.spill.restore_spill_requests(snapshot.spill_requests);
        *self.object_spill_requests = snapshot.object_spill_requests;
    }

    fn must_use_object_storage(&self, v: ValueId) -> bool {
        self.scratch_spill_slots == 0
            || self.scratch_live_values.contains(v)
            || self.forced_object_spills.contains(v)
    }

    fn request_object_storage(&mut self, v: ValueId) {
        self.object_spill_requests.insert(v);
    }

    fn emit_store_for_spilled_value(&mut self, v: ValueId, actions: &mut Actions) {
        let Some(spilled) = self.spill.spilled(v) else {
            return;
        };
        if self.exact_local_addr[v].is_some() {
            debug_assert_eq!(
                self.spill_obj[v], None,
                "exact local addresses must not have spill objects"
            );
            actions.push(Action::Pop);
            return;
        }

        if !self.must_use_object_storage(v) {
            if let Some(slot) = self.slots.scratch.try_ensure_slot(
                spilled,
                self.spill_slot_interference,
                &mut self.free_slots.scratch,
                Some(self.scratch_spill_slots),
            ) {
                actions.push(Action::MemStoreAbs(slot * 32));
                return;
            }
            self.request_object_storage(v);
        }

        actions.push(Action::MemStoreObj(
            self.spill_obj[v].expect("spilled value missing stack object id"),
        ));
    }

    fn load_frame_slot_or_placeholder(&mut self, v: ValueId) -> Action {
        let Some(_) = self.spill.spilled(v) else {
            self.spill.request_spill(v);
            // This fixed-point iteration will be discarded; the real slot assignment happens at
            // `v`'s definition once it becomes part of `spill_set`.
            return Action::MemLoadObj(crate::isa::evm::static_arena_alloc::StackObjId::new(0));
        };

        if let Some(exact) = self.exact_local_addr[v] {
            debug_assert_eq!(
                self.spill_obj[v], None,
                "exact local addresses must not have spill objects"
            );
            return Action::MaterializeLocalAddr {
                alloca: exact.root_alloca,
                offset_bytes: exact.offset_bytes,
            };
        }

        if !self.must_use_object_storage(v) {
            if let Some(slot) = self.slots.scratch.slot_for(v) {
                return Action::MemLoadAbs(slot * 32);
            }
            self.request_object_storage(v);
        }

        // Invariant: every spilled value has a `StackObjId` assigned by stackify's builder
        // (should be verified when finalizing the spill set).
        Action::MemLoadObj(self.spill_obj[v].expect("spilled value missing stack object id"))
    }

    fn emit_store_if_spilled_at_depth(&mut self, v: ValueId, depth: u8, actions: &mut Actions) {
        if self.spill.spilled(v).is_none() {
            return;
        }

        actions.push(Action::StackDup(depth));
        self.emit_store_for_spilled_value(v, actions);
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
    search_scratch: &'a mut NormalizeSearchScratch,
}

impl<'a, 'ctx: 'a> Planner<'a, 'ctx> {
    pub(super) fn new(
        ctx: &'a StackifyContext<'ctx>,
        stack: &'a mut SymStack,
        actions: &'a mut Actions,
        mem: MemPlan<'a>,
        search_scratch: &'a mut NormalizeSearchScratch,
    ) -> Self {
        Self {
            ctx,
            stack,
            actions,
            mem,
            search_scratch,
        }
    }

    pub(super) fn emit_store_if_spilled_at_depth(&mut self, v: ValueId, depth: usize) {
        if !self.mem.spill_set().contains(v) {
            return;
        }
        debug_assert!(depth < self.ctx.reach.dup_max, "DUP out of range");
        self.mem
            .emit_store_if_spilled_at_depth(v, depth as u8, self.actions);
    }

    pub(super) fn emit_store_spilled_value_from_source(
        &mut self,
        spilled_value: ValueId,
        source: ValueId,
    ) {
        if !self.mem.spill_set().contains(spilled_value) {
            return;
        }

        if self.ctx.func.dfg.value_is_imm(source) {
            let imm = self
                .ctx
                .func
                .dfg
                .value_imm(source)
                .expect("imm value missing payload");
            self.actions.push(Action::Push(imm));
            self.mem
                .emit_store_for_spilled_value(spilled_value, self.actions);
        } else if let Some(pos) = self
            .stack
            .find_reachable_value(source, self.ctx.reach.dup_max)
        {
            self.actions.push(Action::StackDup(pos as u8));
            self.mem
                .emit_store_for_spilled_value(spilled_value, self.actions);
        } else if let Some(pos) = self
            .stack
            .find_reachable_value(source, self.ctx.reach.swap_max)
        {
            self.stack.stable_rotate_to_top(pos, self.actions);
            self.stack.dup(0, self.actions);
            self.mem
                .emit_store_for_spilled_value(spilled_value, self.actions);
            self.stack.pop_operand();
            for depth in (1..=pos).rev() {
                self.stack.swap(depth, self.actions);
            }
        } else {
            let act = self.mem.load_frame_slot_or_placeholder(source);
            self.actions.push(act);
            self.mem
                .emit_store_for_spilled_value(spilled_value, self.actions);
        }
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
