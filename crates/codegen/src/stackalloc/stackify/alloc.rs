use cranelift_entity::SecondaryMap;
use sonatina_ir::{BlockId, Function, InstId, ValueId};
use std::collections::BTreeMap;

use crate::stackalloc::{Action, Actions, Allocator};

#[derive(Clone, Default)]
pub struct StackifyAlloc {
    pub(super) pre_actions: SecondaryMap<InstId, Actions>,
    pub(super) post_actions: SecondaryMap<InstId, Actions>,

    /// br_table lowering uses per-case action sequences keyed by (scrutinee, case_val).
    pub(super) brtable_actions: BTreeMap<(InstId, ValueId, ValueId), Actions>,

    pub(crate) spill_obj:
        SecondaryMap<ValueId, Option<crate::isa::evm::static_arena_alloc::StackObjId>>,
    pub(crate) scratch_slot_of_value: SecondaryMap<ValueId, Option<u32>>,
}

impl StackifyAlloc {
    pub(crate) fn uses_scratch_spills(&self) -> bool {
        self.scratch_slot_of_value
            .values()
            .any(|slot| slot.is_some())
    }
}

impl Allocator for StackifyAlloc {
    fn enter_function(&self, function: &Function) -> Actions {
        let mut act = Actions::new();
        for (idx, &arg) in function.arg_values.iter().enumerate() {
            debug_assert!(
                idx < super::DUP_MAX,
                "function arg depth exceeds DUP16 reach"
            );
            if let Some(slot) = self.scratch_slot_of_value[arg] {
                act.push(Action::StackDup(idx as u8));
                act.push(Action::MemStoreAbs(slot * 32));
            } else if let Some(obj) = self.spill_obj[arg] {
                act.push(Action::StackDup(idx as u8));
                act.push(Action::MemStoreObj(obj));
            }
        }
        act
    }

    fn read(&self, inst: InstId, vals: &[ValueId]) -> Actions {
        if let [scrutinee, case_val] = vals
            && let Some(act) = self.brtable_actions.get(&(inst, *scrutinee, *case_val))
        {
            return act.clone();
        }
        self.pre_actions[inst].clone()
    }

    fn write(&self, inst: InstId, _vals: &[ValueId]) -> Actions {
        self.post_actions[inst].clone()
    }

    fn traverse_edge(&self, _from: BlockId, _to: BlockId) -> Actions {
        Actions::new()
    }
}
