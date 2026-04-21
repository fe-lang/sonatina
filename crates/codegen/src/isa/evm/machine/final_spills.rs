use cranelift_entity::EntityRef;
use rustc_hash::FxHashMap;
use sonatina_ir::ValueId;

use crate::stackalloc::StackifyAlloc;

use super::super::{FuncMemPlan, ObjLoc, static_arena_alloc::StackObjId};

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

    let start_word = mem_plan.abs_words_end();
    for (idx, old_obj) in old_objs.into_iter().enumerate() {
        let new_obj = remap[&old_obj];
        let word = start_word
            .checked_add(u32::try_from(idx).expect("spill count overflow"))
            .expect("final spill word overflow");
        mem_plan.obj_loc.insert(new_obj, ObjLoc::ScratchAbs(word));
    }

    alloc.remap_stack_objects(&remap);
    for (value, old_obj) in spilled_values {
        let new_obj = remap[&old_obj];
        alloc.spill_obj[value] = Some(new_obj);
        mem_plan.spill_obj[value] = Some(new_obj);
    }

    let peak_words = start_word
        .checked_add(u32::try_from(remap.len()).expect("spill count overflow"))
        .expect("final spill peak overflow");
    mem_plan.scratch_words = mem_plan.scratch_words.max(peak_words);

    FinalSpillAllocation {
        alloc,
        mem_plan,
        peak_words,
    }
}
