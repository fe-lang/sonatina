use cranelift_entity::SecondaryMap;
use sonatina_ir::{BlockId, Function, InstId, ValueId, cfg::ControlFlowGraph};
use std::collections::BTreeMap;

use crate::{
    bitset::BitSet,
    domtree::DomTree,
    liveness::Liveness,
    stackalloc::{Action, Actions, Allocator, SpillSlotRef},
};

use super::{builder::StackifyBuilder, trace::StackifyTrace};

#[derive(Default)]
pub struct StackifyAlloc {
    pub(super) pre_actions: SecondaryMap<InstId, Actions>,
    pub(super) post_actions: SecondaryMap<InstId, Actions>,

    /// br_table lowering uses per-case action sequences keyed by (scrutinee, case_val).
    pub(super) brtable_actions: BTreeMap<(InstId, ValueId, ValueId), Actions>,

    /// Value -> frame slot index (32-byte slots).
    ///
    /// Slots are allocated deterministically and may be shared by multiple values as long as
    /// their lifetimes do not overlap (currently: within-block reuse based on last-use tracking).
    pub(super) slot_of_value: SecondaryMap<ValueId, Option<SpillSlotRef>>,
    pub(crate) persistent_frame_slots: u32,
    pub(crate) transient_frame_slots: u32,
}

impl StackifyAlloc {
    /// Compute stack allocation for a single function using the transfer-region stackify spec.
    pub fn for_function(
        func: &Function,
        cfg: &ControlFlowGraph,
        dom: &DomTree,
        liveness: &Liveness,
        reach_depth: u8,
    ) -> Self {
        let builder = StackifyBuilder::new(func, cfg, dom, liveness, reach_depth);
        builder.compute()
    }

    pub fn for_function_with_call_live_values(
        func: &Function,
        cfg: &ControlFlowGraph,
        dom: &DomTree,
        liveness: &Liveness,
        reach_depth: u8,
        call_live_values: BitSet<ValueId>,
    ) -> Self {
        let builder = StackifyBuilder::new(func, cfg, dom, liveness, reach_depth)
            .with_call_live_values(call_live_values);
        builder.compute()
    }

    pub fn for_function_with_call_live_values_and_scratch_spills(
        func: &Function,
        cfg: &ControlFlowGraph,
        dom: &DomTree,
        liveness: &Liveness,
        reach_depth: u8,
        call_live_values: BitSet<ValueId>,
        scratch_live_values: BitSet<ValueId>,
        scratch_spill_slots: u32,
    ) -> Self {
        let builder = StackifyBuilder::new(func, cfg, dom, liveness, reach_depth)
            .with_call_live_values(call_live_values)
            .with_scratch_live_values(scratch_live_values)
            .with_scratch_spills(scratch_spill_slots);
        builder.compute()
    }

    /// Compute stack allocation for a single function and return a human-oriented trace of the
    /// planning decisions made during the final fixed-point iteration.
    pub fn for_function_with_trace(
        func: &Function,
        cfg: &ControlFlowGraph,
        dom: &DomTree,
        liveness: &Liveness,
        reach_depth: u8,
    ) -> (Self, String) {
        let builder = StackifyBuilder::new(func, cfg, dom, liveness, reach_depth);
        let mut trace = StackifyTrace::default();
        let alloc = builder.compute_with_observer(&mut trace);
        let trace = trace.render(func, &alloc);
        (alloc, trace)
    }

    pub fn for_function_with_trace_and_call_live_values(
        func: &Function,
        cfg: &ControlFlowGraph,
        dom: &DomTree,
        liveness: &Liveness,
        reach_depth: u8,
        call_live_values: BitSet<ValueId>,
    ) -> (Self, String) {
        let builder = StackifyBuilder::new(func, cfg, dom, liveness, reach_depth)
            .with_call_live_values(call_live_values);
        let mut trace = StackifyTrace::default();
        let alloc = builder.compute_with_observer(&mut trace);
        let trace = trace.render(func, &alloc);
        (alloc, trace)
    }

    pub fn for_function_with_trace_call_live_values_and_scratch_spills(
        func: &Function,
        cfg: &ControlFlowGraph,
        dom: &DomTree,
        liveness: &Liveness,
        reach_depth: u8,
        call_live_values: BitSet<ValueId>,
        scratch_live_values: BitSet<ValueId>,
        scratch_spill_slots: u32,
    ) -> (Self, String) {
        let builder = StackifyBuilder::new(func, cfg, dom, liveness, reach_depth)
            .with_call_live_values(call_live_values)
            .with_scratch_live_values(scratch_live_values)
            .with_scratch_spills(scratch_spill_slots);
        let mut trace = StackifyTrace::default();
        let alloc = builder.compute_with_observer(&mut trace);
        let trace = trace.render(func, &alloc);
        (alloc, trace)
    }

    pub(crate) fn uses_scratch_spills(&self) -> bool {
        self.slot_of_value
            .values()
            .any(|slot| matches!(*slot, Some(SpillSlotRef::Scratch(_))))
    }
}

impl Allocator for StackifyAlloc {
    fn enter_function(&self, function: &Function) -> Actions {
        let mut act = Actions::new();
        for (idx, &arg) in function.arg_values.iter().enumerate() {
            let Some(slot) = self.slot_of_value[arg] else {
                continue;
            };
            debug_assert!(
                idx < super::DUP_MAX,
                "function arg depth exceeds DUP16 reach"
            );
            act.push(Action::StackDup(idx as u8));
            match slot {
                SpillSlotRef::Persistent(slot) => act.push(Action::MemStoreFrameSlot(slot)),
                SpillSlotRef::Transient(slot) => act.push(Action::MemStoreFrameSlot(
                    self.persistent_frame_slots + slot,
                )),
                SpillSlotRef::Scratch(slot) => act.push(Action::MemStoreAbs(slot * 32)),
            }
        }
        act
    }

    fn frame_size_slots(&self) -> u32 {
        self.persistent_frame_slots + self.transient_frame_slots
    }

    fn read(&self, inst: InstId, vals: &[ValueId]) -> Actions {
        if let [scrutinee, case_val] = vals
            && let Some(act) = self.brtable_actions.get(&(inst, *scrutinee, *case_val))
        {
            return act.clone();
        }
        self.pre_actions[inst].clone()
    }

    fn write(&self, inst: InstId, _val: Option<ValueId>) -> Actions {
        self.post_actions[inst].clone()
    }

    fn traverse_edge(&self, _from: BlockId, _to: BlockId) -> Actions {
        Actions::new()
    }
}
