use cranelift_entity::SecondaryMap;
use sonatina_ir::{BlockId, Function, InstId, ValueId};

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
}

impl Allocator for StackifyAlloc {
    fn enter_function(&self, function: &Function) -> Actions {
        let mut act = Actions::new();
        for (idx, &arg) in function.arg_values.iter().enumerate() {
            debug_assert!(
                idx < super::DUP_MAX,
                "function arg depth exceeds DUP16 reach"
            );
            match self.storage_for_value(arg) {
                Some(SpillStorage::Scratch(slot)) => {
                    act.push(Action::StackDup(idx as u8));
                    act.push(Action::MemStoreAbs(slot * 32));
                }
                Some(SpillStorage::Object(obj)) => {
                    act.push(Action::StackDup(idx as u8));
                    act.push(Action::MemStoreObj(obj));
                }
                Some(SpillStorage::ExactLocal(_)) | None => {}
            }
        }
        act
    }

    fn read(&self, inst: InstId, _vals: &[ValueId]) -> Actions {
        self.pre_actions[inst].clone()
    }

    fn read_br_table_case(&self, inst: InstId, case_index: usize) -> Actions {
        self.brtable_actions[inst]
            .get(case_index)
            .cloned()
            .unwrap_or_else(|| {
                panic!(
                    "missing br_table case actions for inst {} case {}",
                    inst.as_u32(),
                    case_index
                )
            })
    }

    fn write(&self, inst: InstId, _vals: &[ValueId]) -> Actions {
        self.post_actions[inst].clone()
    }

    fn traverse_edge(&self, _from: BlockId, _to: BlockId) -> Actions {
        Actions::new()
    }
}
