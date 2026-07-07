use cranelift_entity::SecondaryMap;
use rustc_hash::FxHashMap;
use sonatina_ir::{Function, InstId, ValueId};

use crate::{
    analysis::memory_access::ExactLocalAddr,
    isa::evm::static_arena_alloc::StackObjId,
    stackalloc::{Action, Actions, Allocator},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SpillStorage {
    Scratch(u32),
    Object(StackObjId),
    ExactLocal(ExactLocalAddr),
}

impl SpillStorage {
    /// The action that stores a value from the stack top into this storage.
    /// `None` for storage materialized without a store (exact local addresses).
    pub(super) fn store_action(self) -> Option<Action> {
        match self {
            SpillStorage::Scratch(slot) => Some(Action::MemStoreAbs(slot * 32)),
            SpillStorage::Object(obj) => Some(Action::MemStoreObj(obj)),
            SpillStorage::ExactLocal(_) => None,
        }
    }
}

#[derive(Clone, Default)]
pub struct StackifyAlloc {
    pub(super) pre_actions: SecondaryMap<InstId, Actions>,
    pub(super) post_actions: SecondaryMap<InstId, Actions>,

    /// `br_table` lowering uses per-case action sequences stored in IR case order.
    pub(super) brtable_actions: SecondaryMap<InstId, Vec<Actions>>,

    pub(crate) spill_storage: SecondaryMap<ValueId, Option<SpillStorage>>,
    pub(crate) spill_obj: SecondaryMap<ValueId, Option<StackObjId>>,
    pub(crate) scratch_slot_of_value: SecondaryMap<ValueId, Option<u32>>,
    pub(crate) exact_local_addr: SecondaryMap<ValueId, Option<ExactLocalAddr>>,
}

impl StackifyAlloc {
    #[cfg(test)]
    pub(crate) fn set_object_spill_for_test(&mut self, value: ValueId, obj: StackObjId) {
        self.spill_obj[value] = Some(obj);
        self.spill_storage[value] = Some(SpillStorage::Object(obj));
    }

    pub(crate) fn uses_scratch_spills(&self) -> bool {
        self.scratch_slot_of_value
            .values()
            .any(|slot| slot.is_some())
    }

    pub(crate) fn storage_for_value(&self, value: ValueId) -> Option<SpillStorage> {
        self.spill_storage[value]
    }

    pub(crate) fn for_each_action(&self, mut f: impl FnMut(&Action)) {
        for actions in self.pre_actions.values() {
            for action in actions {
                f(action);
            }
        }
        for actions in self.post_actions.values() {
            for action in actions {
                f(action);
            }
        }
        for cases in self.brtable_actions.values() {
            for actions in cases {
                for action in actions {
                    f(action);
                }
            }
        }
    }

    pub(crate) fn validate_spill_storage(&self) {
        for (value, storage) in self.spill_storage.iter() {
            match storage {
                Some(SpillStorage::Scratch(slot)) => {
                    assert_eq!(
                        self.scratch_slot_of_value[value],
                        Some(*slot),
                        "scratch storage map drift for value {}",
                        value.as_u32()
                    );
                    assert_eq!(
                        self.spill_obj[value],
                        None,
                        "scratch-spilled value {} must not have object storage",
                        value.as_u32()
                    );
                }
                Some(SpillStorage::Object(obj)) => {
                    assert_eq!(
                        self.spill_obj[value],
                        Some(*obj),
                        "object storage map drift for value {}",
                        value.as_u32()
                    );
                    assert_eq!(
                        self.scratch_slot_of_value[value],
                        None,
                        "object-spilled value {} must not have scratch storage",
                        value.as_u32()
                    );
                }
                Some(SpillStorage::ExactLocal(exact)) => {
                    assert_eq!(
                        self.exact_local_addr[value],
                        Some(*exact),
                        "exact local storage map drift for value {}",
                        value.as_u32()
                    );
                }
                None => {
                    assert_eq!(
                        self.scratch_slot_of_value[value],
                        None,
                        "unspilled value {} must not have scratch storage",
                        value.as_u32()
                    );
                    assert_eq!(
                        self.spill_obj[value],
                        None,
                        "unspilled value {} must not have object storage",
                        value.as_u32()
                    );
                }
            }
        }

        self.for_each_action(|action| {
            if let Action::MemLoadObj(id) | Action::MemStoreObj(id) = action {
                assert!(
                    self.spill_storage.values().any(
                        |storage| matches!(storage, Some(SpillStorage::Object(obj)) if obj == id)
                    ),
                    "stackify emitted object action for non-object spill {}",
                    id.as_u32()
                );
            }
        });
    }
    /// Ensure `inst`'s pre/post action entries exist (empty if never planned), so that map-wide
    /// transforms like [`Self::rewrite_action_lists`] visit them.
    pub(crate) fn touch_inst_actions(&mut self, inst: InstId) {
        let _ = &mut self.pre_actions[inst];
        let _ = &mut self.post_actions[inst];
    }

    /// Replace every stored pre/post/`br_table` action list in place with the result of the
    /// given transforms (each consumes the old list and returns the rewritten one).
    pub(crate) fn rewrite_action_lists(
        &mut self,
        mut pre: impl FnMut(InstId, Actions) -> Actions,
        mut post: impl FnMut(InstId, Actions) -> Actions,
        mut br_case: impl FnMut(Actions) -> Actions,
    ) {
        for (inst, actions) in self.pre_actions.iter_mut() {
            *actions = pre(inst, std::mem::take(actions));
        }
        for (inst, actions) in self.post_actions.iter_mut() {
            *actions = post(inst, std::mem::take(actions));
        }
        for cases in self.brtable_actions.values_mut() {
            for actions in cases.iter_mut() {
                *actions = br_case(std::mem::take(actions));
            }
        }
    }

    pub(crate) fn remap_stack_objects(&mut self, remap: &FxHashMap<StackObjId, StackObjId>) {
        fn remap_actions(actions: &mut Actions, remap: &FxHashMap<StackObjId, StackObjId>) {
            for action in actions {
                match action {
                    Action::MemLoadObj(obj) | Action::MemStoreObj(obj) => {
                        if let Some(new_obj) = remap.get(obj) {
                            *obj = *new_obj;
                        }
                    }
                    _ => {}
                }
            }
        }

        for actions in self.pre_actions.values_mut() {
            remap_actions(actions, remap);
        }
        for actions in self.post_actions.values_mut() {
            remap_actions(actions, remap);
        }
        for cases in self.brtable_actions.values_mut() {
            for actions in cases {
                remap_actions(actions, remap);
            }
        }
        for storage in self.spill_storage.values_mut() {
            if let Some(SpillStorage::Object(obj)) = storage
                && let Some(new_obj) = remap.get(obj)
            {
                *obj = *new_obj;
            }
        }
        for obj in self.spill_obj.values_mut().flatten() {
            if let Some(new_obj) = remap.get(obj) {
                *obj = *new_obj;
            }
        }
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
            if let Some(store) = self
                .storage_for_value(arg)
                .and_then(SpillStorage::store_action)
            {
                act.push(Action::StackDup(idx as u8));
                act.push(store);
            }
        }
        act
    }

    fn pre_inst(&self, inst: InstId) -> &Actions {
        &self.pre_actions[inst]
    }

    fn br_table_case(&self, inst: InstId, case_index: usize) -> &Actions {
        self.brtable_actions[inst]
            .get(case_index)
            .unwrap_or_else(|| {
                panic!(
                    "missing br_table case actions for inst {} case {}",
                    inst.as_u32(),
                    case_index
                )
            })
    }

    fn post_inst(&self, inst: InstId) -> &Actions {
        &self.post_actions[inst]
    }
}
