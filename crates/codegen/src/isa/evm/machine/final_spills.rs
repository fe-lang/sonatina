use cranelift_entity::EntityRef;
use rustc_hash::FxHashMap;
use sonatina_ir::ValueId;

use crate::stackalloc::StackifyAlloc;

use super::super::{FuncMemPlan, ObjLoc, memory_plan::StableMode, static_arena_alloc::StackObjId};

pub(crate) struct FinalSpillAllocation {
    pub(crate) alloc: StackifyAlloc,
    pub(crate) mem_plan: FuncMemPlan,
    pub(crate) peak_words: u32,
}

pub(crate) fn allocate_final_spills(
    mut alloc: StackifyAlloc,
    mut mem_plan: FuncMemPlan,
) -> FinalSpillAllocation {
    let mut next_obj = mem_plan
        .obj_loc
        .keys()
        .map(|id| id.as_u32())
        .max()
        .map_or(0, |id| id.checked_add(1).expect("stack object id overflow"));
    let mut remap: FxHashMap<StackObjId, StackObjId> = FxHashMap::default();
    let mut spilled_values: Vec<(ValueId, StackObjId)> = alloc
        .spill_obj
        .iter()
        .filter_map(|(value, obj)| {
            let obj = (*obj)?;
            alloc.scratch_slot_of_value[value]
                .is_none()
                .then_some((value, obj))
        })
        .collect();
    spilled_values.sort_unstable_by_key(|(value, _)| value.as_u32());

    let mut old_objs = Vec::new();
    for &(_, old_obj) in &spilled_values {
        if remap.contains_key(&old_obj) {
            continue;
        }
        old_objs.push(old_obj);
        remap.insert(old_obj, {
            let obj = StackObjId::new(next_obj as usize);
            next_obj = next_obj.checked_add(1).expect("stack object id overflow");
            obj
        });
    }

    let old_obj_count = u32::try_from(old_objs.len()).expect("spill count overflow");
    if old_obj_count == 0 {
        alloc.validate_spill_storage();
        return FinalSpillAllocation {
            alloc,
            peak_words: 0,
            mem_plan,
        };
    }

    let dynamic_frame_has_reserve = matches!(mem_plan.stable_mode, StableMode::DynamicFrame)
        && old_obj_count <= mem_plan.stable_words;
    let start_word = match mem_plan.stable_mode {
        StableMode::DynamicFrame if dynamic_frame_has_reserve => {
            mem_plan.stable_words - old_obj_count
        }
        StableMode::None | StableMode::StaticAbs { .. } => mem_plan.abs_words_end(),
        StableMode::DynamicFrame => mem_plan.abs_words_end(),
    };
    for (idx, old_obj) in old_objs.into_iter().enumerate() {
        let new_obj = remap[&old_obj];
        let word = start_word
            .checked_add(u32::try_from(idx).expect("spill count overflow"))
            .expect("final spill word overflow");
        let loc = match mem_plan.stable_mode {
            StableMode::DynamicFrame if dynamic_frame_has_reserve => ObjLoc::StableFrame(word),
            StableMode::None | StableMode::StaticAbs { .. } => ObjLoc::ScratchAbs(word),
            StableMode::DynamicFrame => ObjLoc::ScratchAbs(word),
        };
        mem_plan.obj_loc.insert(new_obj, loc);
    }

    alloc.remap_stack_objects(&remap);
    for (value, old_obj) in spilled_values {
        let new_obj = remap[&old_obj];
        alloc.spill_obj[value] = Some(new_obj);
        mem_plan.spill_obj[value] = Some(new_obj);
    }
    alloc.validate_spill_storage();

    let peak_words = if matches!(mem_plan.stable_mode, StableMode::DynamicFrame) {
        old_obj_count
    } else {
        start_word
            .checked_add(old_obj_count)
            .expect("final spill peak overflow")
    };
    mem_plan.scratch_words = mem_plan.scratch_words.max(peak_words);

    FinalSpillAllocation {
        alloc,
        mem_plan,
        peak_words,
    }
}

#[cfg(test)]
mod tests {
    use cranelift_entity::SecondaryMap;
    use rustc_hash::{FxHashMap, FxHashSet};

    use crate::{
        isa::evm::{
            FuncMemPlan, machine::final_spills::allocate_final_spills,
            malloc_plan::MallocEscapeKind, memory_plan::StableMode,
        },
        stackalloc::StackifyAlloc,
    };

    fn static_mem_plan(scratch_words: u32, stable_words: u32) -> FuncMemPlan {
        FuncMemPlan {
            arena_base: 0xa0,
            scratch_words,
            stable_words,
            stable_mode: StableMode::StaticAbs {
                base_word: scratch_words,
            },
            entry_abs_words: scratch_words,
            obj_loc: FxHashMap::default(),
            alloca_loc: FxHashMap::default(),
            spill_obj: SecondaryMap::new(),
            call_preserve: FxHashMap::default(),
            malloc_future_abs_words: FxHashMap::default(),
            transient_mallocs: FxHashSet::default(),
            malloc_escape_kinds: FxHashMap::<_, MallocEscapeKind>::default(),
            return_escape_caller_abs_words: 0,
        }
    }

    #[test]
    fn zero_final_spills_do_not_count_stable_words_as_scratch() {
        let final_spills = allocate_final_spills(StackifyAlloc::default(), static_mem_plan(0, 5));

        assert_eq!(final_spills.peak_words, 0);
        assert_eq!(final_spills.mem_plan.scratch_words, 0);
    }

    #[test]
    fn zero_final_spills_do_not_request_backend_spill_reserve() {
        let final_spills = allocate_final_spills(StackifyAlloc::default(), static_mem_plan(3, 5));

        assert_eq!(final_spills.peak_words, 0);
        assert_eq!(final_spills.mem_plan.scratch_words, 3);
    }
}
