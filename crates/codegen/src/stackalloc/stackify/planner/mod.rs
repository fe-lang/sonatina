mod control_flow;
mod normalize;
mod normalize_search;
mod operand_prep;
#[cfg(test)]
mod test_utils;

pub(super) use normalize_search::NormalizeSearchScratch;
pub(crate) use normalize_search::StackifySearchCache;

use crate::{
    bitset::BitSet,
    stackalloc::{Action, Actions},
};
use cranelift_entity::{EntityRef, SecondaryMap};
use sonatina_ir::ValueId;

use super::{
    StackifyContext,
    alloc::SpillStorage,
    slots::{FreeSlotPools, SpillSlotInterference, SpillSlotPools},
    spill::{SpillDiscovery, SpillSet},
    sym_stack::SymStack,
};

/// Storage-eligibility policy, owned in one place and shared by `MemPlan` and the entry-arg
/// scratch pre-pass in the builder.
///
/// A spilled value must use arena (object) storage rather than a reusable scratch slot when every
/// scratch slot bars it (`scratch_barred` has an entry per slot), or once the plan found no free
/// slot for it (`object_spills`).
///
/// Invariant: using a scratch slot never changes what the program observes. On EVM the slots are
/// memory `[0, 64)`, which the IR may use too, so a slot bars every value live across an IR write
/// or a call that may write the slot, and every value whose spill store may run while IR data in
/// the slot is live: possibly read after the store, here, in a callee, or in a caller after a
/// return, without a write of it in between (`isa::evm::fixed_slots`).
pub(super) fn must_use_object_storage(
    scratch_barred: &[BitSet<ValueId>],
    object_spills: &BitSet<ValueId>,
    v: ValueId,
) -> bool {
    object_spills.contains(v) || scratch_barred.iter().all(|barred| barred.contains(v))
}

/// Driver-owned memory-planning state, grouped so `MemPlan::new` takes it in one reborrow rather
/// than six separate arguments. Lives in `FunctionPlanner`; a `MemPlan` borrows its fields for the
/// span of a single instruction/edge plan.
pub(super) struct MemState<'a> {
    pub(super) spill: SpillSet<'a>,
    /// Provisional per-iteration object-id assignment (`assign_spill_obj_ids`), read by `MemPlan`
    /// during planning before storage is finalized.
    pub(super) spill_obj:
        &'a SecondaryMap<ValueId, Option<crate::isa::evm::static_arena_alloc::StackObjId>>,
    pub(super) spill_requests: &'a mut BitSet<ValueId>,
    /// The values this plan loads from memory.
    pub(super) reloaded: &'a mut BitSet<ValueId>,
    /// The spilled values this plan found no free scratch slot for. Such a value has no slot yet,
    /// so every store and load of it planned from then on uses its object.
    pub(super) object_spills: &'a mut BitSet<ValueId>,
    pub(super) slots: &'a mut SpillSlotPools,
}

#[derive(Clone)]
pub(super) struct MemPlanSnapshot {
    free_slots: FreeSlotPools,
    slots: SpillSlotPools,
    spill_requests: BitSet<ValueId>,
    reloaded: BitSet<ValueId>,
    object_spills: BitSet<ValueId>,
}

pub(super) struct MemPlan<'a> {
    scratch_barred: &'a [BitSet<ValueId>],
    spill_obj: &'a SecondaryMap<ValueId, Option<crate::isa::evm::static_arena_alloc::StackObjId>>,
    remat_actions: &'a SecondaryMap<ValueId, Option<Action>>,
    object_spills: &'a mut BitSet<ValueId>,
    free_slots: &'a mut FreeSlotPools,
    slots: &'a mut SpillSlotPools,
    spill_slot_interference: &'a SpillSlotInterference,
    spill: SpillDiscovery<'a>,
}

impl<'a> MemPlan<'a> {
    pub(super) fn new(
        mem: &'a mut MemState<'_>,
        ctx: &'a StackifyContext<'_>,
        remat_actions: &'a SecondaryMap<ValueId, Option<Action>>,
        free_slots: &'a mut FreeSlotPools,
    ) -> Self {
        Self {
            scratch_barred: &ctx.scratch_barred,
            spill_obj: mem.spill_obj,
            remat_actions,
            object_spills: &mut *mem.object_spills,
            free_slots,
            slots: &mut *mem.slots,
            spill_slot_interference: &ctx.spill_slot_interference,
            spill: SpillDiscovery::new(mem.spill, &mut *mem.spill_requests, &mut *mem.reloaded),
        }
    }

    pub(super) fn spill_set(&self) -> SpillSet<'a> {
        self.spill.spill_set()
    }

    pub(super) fn snapshot(&self) -> MemPlanSnapshot {
        let (spill_requests, reloaded) = self.spill.requests();
        MemPlanSnapshot {
            free_slots: self.free_slots.clone(),
            slots: self.slots.clone(),
            spill_requests: spill_requests.clone(),
            reloaded: reloaded.clone(),
            object_spills: (*self.object_spills).clone(),
        }
    }

    pub(super) fn restore(&mut self, snapshot: MemPlanSnapshot) {
        *self.free_slots = snapshot.free_slots;
        *self.slots = snapshot.slots;
        self.spill
            .restore_requests(snapshot.spill_requests, snapshot.reloaded);
        *self.object_spills = snapshot.object_spills;
    }

    fn must_use_object_storage(&self, v: ValueId) -> bool {
        must_use_object_storage(self.scratch_barred, self.object_spills, v)
    }

    /// Stores the stack top into `v`'s memory, consuming it.
    fn emit_store_for_spilled_value(&mut self, v: ValueId, actions: &mut Actions) {
        let spilled = self
            .spill_set()
            .stored(v)
            .expect("only a stored spilled value is stored");
        if self.remat_actions[v].is_some() {
            debug_assert_eq!(
                self.spill_obj[v], None,
                "rematerialized values must not have spill objects"
            );
            actions.push(Action::Pop);
            return;
        }

        if !self.must_use_object_storage(v) {
            if let Some(slot) = self.slots.scratch.try_ensure_slot(
                spilled,
                self.spill_slot_interference,
                &mut self.free_slots.scratch,
                self.scratch_barred,
            ) {
                actions.push(
                    SpillStorage::Scratch(slot)
                        .store_action()
                        .expect("scratch storage has a store action"),
                );
                return;
            }
            self.object_spills.insert(v);
        }

        let obj = self.spill_obj[v].expect("spilled value missing stack object id");
        actions.push(
            SpillStorage::Object(obj)
                .store_action()
                .expect("object storage has a store action"),
        );
    }

    fn load_frame_slot_or_placeholder(&mut self, v: ValueId) -> Action {
        self.spill.reload(v);
        if self.spill_set().stored(v).is_none() {
            // This fixed-point iteration will be discarded; the real slot assignment happens at
            // `v`'s definition once the next iteration stores it.
            return Action::MemLoadObj(crate::isa::evm::static_arena_alloc::StackObjId::new(0));
        }

        if let Some(action) = self.remat_actions[v] {
            debug_assert_eq!(
                self.spill_obj[v], None,
                "rematerialized values must not have spill objects"
            );
            return action;
        }

        if !self.must_use_object_storage(v) {
            if let Some(slot) = self.slots.scratch.slot_for(v) {
                return Action::MemLoadAbs(slot * 32);
            }
            self.object_spills.insert(v);
        }

        // Invariant: every spilled value has a `StackObjId` assigned by stackify's builder
        // (should be verified when finalizing the spill set).
        Action::MemLoadObj(self.spill_obj[v].expect("spilled value missing stack object id"))
    }

    fn emit_store_if_stored_at_depth(&mut self, v: ValueId, depth: u8, actions: &mut Actions) {
        if self.spill_set().stored(v).is_none() {
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

    pub(super) fn emit_store_if_stored_at_depth(&mut self, v: ValueId, depth: usize) {
        debug_assert!(depth < self.ctx.reach.dup_max, "DUP out of range");
        self.mem
            .emit_store_if_stored_at_depth(v, depth as u8, self.actions);
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
