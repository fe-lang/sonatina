use cranelift_entity::SecondaryMap;
use sonatina_ir::{BlockId, Function, InstId, ValueId, cfg::ControlFlowGraph};
use std::collections::BTreeMap;

use crate::{
    domtree::DomTree,
    liveness::Liveness,
    stackalloc::{Action, Actions, Allocator},
};

use super::{builder::StackifyBuilder, trace::StackifyTrace};

#[derive(Default)]
pub struct StackifyAlloc {
    pub(super) pre_actions: SecondaryMap<InstId, Actions>,
    pub(super) post_actions: SecondaryMap<InstId, Actions>,

    /// br_table lowering uses per-case action sequences (keyed by the case value).
    pub(super) brtable_actions: BTreeMap<(InstId, ValueId), Actions>,

    /// Value -> frame slot index (32-byte slots).
    ///
    /// Slots are allocated deterministically and may be shared by multiple values as long as
    /// their lifetimes do not overlap (currently: within-block reuse based on last-use tracking).
    pub(super) slot_of: SecondaryMap<ValueId, Option<u32>>,
    pub(super) frame_size_slots: u32,
}

impl StackifyAlloc {
    /// Compute stack allocation for a single function using the transfer-region stackify spec.
    pub fn for_function(
        func: &Function,
        cfg: &ControlFlowGraph,
        dom: &DomTree,
        liveness: &Liveness,
        _stack_size: u8,
    ) -> Self {
        let builder = StackifyBuilder::new(func, cfg, dom, liveness);
        builder.compute()
    }

    /// Compute stack allocation for a single function and return a human-oriented trace of the
    /// planning decisions made during the final fixed-point iteration.
    pub fn for_function_with_trace(
        func: &Function,
        cfg: &ControlFlowGraph,
        dom: &DomTree,
        liveness: &Liveness,
        _stack_size: u8,
    ) -> (Self, String) {
        let builder = StackifyBuilder::new(func, cfg, dom, liveness);
        let mut trace = StackifyTrace::default();
        let alloc = builder.compute_with_observer(&mut trace);
        let trace = trace.render(func, &alloc);
        (alloc, trace)
    }
}

impl Allocator for StackifyAlloc {
    fn enter_function(&self, function: &Function) -> Actions {
        let mut act = Actions::new();
        for (idx, &arg) in function.arg_values.iter().enumerate() {
            let Some(slot) = self.slot_of[arg] else {
                continue;
            };
            debug_assert!(
                idx < super::DUP_MAX,
                "function arg depth exceeds DUP16 reach"
            );
            act.push(Action::StackDup(idx as u8));
            act.push(Action::MemStoreFrameSlot(slot));
        }
        act
    }

    fn frame_size_slots(&self) -> u32 {
        self.frame_size_slots
    }

    fn read(&self, inst: InstId, vals: &[ValueId]) -> Actions {
        if let [val] = vals
            && let Some(act) = self.brtable_actions.get(&(inst, *val))
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
