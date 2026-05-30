use cranelift_entity::EntityRef;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{Module, ValueId, module::FuncRef};

use crate::{bitset::BitSet, stackalloc::StackifyAlloc};

use super::{
    super::{
        EvmBackend, FuncMemPlan, ObjLoc,
        memory_plan::{BackendSpillReserve, FuncPreAnalysis, MachineStackifyAnalysis, StableMode},
        ptr_escape::PtrEscapeSummary,
        static_arena_alloc::StackObjId,
    },
    placement::{MemoryPlacementSection, compute_semantic_memory_placement},
};

pub(crate) struct FinalSpillAllocation {
    pub(crate) alloc: StackifyAlloc,
    pub(crate) mem_plan: FuncMemPlan,
    pub(crate) required_reserve: BackendSpillReserve,
    pub(crate) stack_obj_remap: FxHashMap<StackObjId, StackObjId>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum OptionalFinalSpillPlacement {
    Scratch,
    Stable,
}

#[derive(Default)]
pub(crate) struct FinalSpillObjects {
    spilled_values: Vec<(ValueId, StackObjId)>,
    objs: Vec<(StackObjId, bool)>,
}

impl FinalSpillObjects {
    pub(crate) fn compute(alloc: &StackifyAlloc, stable_spill_values: &BitSet<ValueId>) -> Self {
        let mut spilled_values = final_spilled_values(alloc);
        spilled_values.sort_unstable_by_key(|(value, _)| value.as_u32());
        let mut old_obj_stable: FxHashMap<StackObjId, bool> = FxHashMap::default();
        let mut old_objs = Vec::new();
        for &(value, old_obj) in &spilled_values {
            if !old_obj_stable.contains_key(&old_obj) {
                old_objs.push(old_obj);
            }
            let stable = stable_spill_values.contains(value);
            old_obj_stable
                .entry(old_obj)
                .and_modify(|known| *known |= stable)
                .or_insert(stable);
        }

        let objs = old_objs
            .into_iter()
            .map(|old_obj| (old_obj, old_obj_stable[&old_obj]))
            .collect();
        Self {
            spilled_values,
            objs,
        }
    }

    fn is_empty(&self) -> bool {
        self.objs.is_empty()
    }

    fn has_optional_spills(&self) -> bool {
        self.objs.iter().any(|obj| !obj.1)
    }

    pub(crate) fn required_reserve(
        &self,
        mem_plan: &FuncMemPlan,
        reserved: BackendSpillReserve,
        abs_spill_floor_words: u32,
        optional_placement: OptionalFinalSpillPlacement,
    ) -> BackendSpillReserve {
        if self.is_empty() {
            return BackendSpillReserve::default();
        }

        let must_stable_words = spill_count(self.objs.iter().filter(|obj| obj.1).count());
        let optional_words = spill_count(self.objs.len()) - must_stable_words;
        let optional_stable = match optional_placement {
            OptionalFinalSpillPlacement::Scratch => 0,
            OptionalFinalSpillPlacement::Stable => optional_words,
        };
        let stable_words = must_stable_words
            .checked_add(optional_stable)
            .expect("final stable spill count overflow");
        let scratch_words = optional_words - optional_stable;
        BackendSpillReserve {
            scratch_words,
            stable_words: required_stable_reserve_words(
                mem_plan,
                reserved.stable_words,
                stable_words,
                abs_spill_floor_words,
            ),
        }
    }
}

pub(crate) struct MachineFinalSpillInput {
    pub(crate) func: FuncRef,
    pub(crate) analysis: MachineStackifyAnalysis,
    pub(crate) mem_plan: FuncMemPlan,
    pub(crate) reserve: BackendSpillReserve,
    pub(crate) abs_spill_floor_words: u32,
    pub(crate) spills: FinalSpillObjects,
}

type FinalSpillChoiceScore = (u32, u32, u32, u32, u64, u64);

pub(crate) struct FinalSpillChoiceCtx<'a> {
    pub(crate) source_module: &'a Module,
    pub(crate) funcs: &'a [FuncRef],
    pub(crate) section_entry: FuncRef,
    pub(crate) section_includes: &'a [FuncRef],
    pub(crate) pre_analyses: &'a FxHashMap<FuncRef, FuncPreAnalysis>,
    pub(crate) ptr_escape: &'a FxHashMap<FuncRef, PtrEscapeSummary>,
    pub(crate) backend: &'a EvmBackend,
    pub(crate) base_scratch_effects: &'a FxHashSet<FuncRef>,
    pub(crate) inputs: &'a [MachineFinalSpillInput],
}

impl FinalSpillChoiceCtx<'_> {
    pub(crate) fn choose_optional_placements(
        &self,
    ) -> FxHashMap<FuncRef, OptionalFinalSpillPlacement> {
        let mut choices: FxHashMap<FuncRef, OptionalFinalSpillPlacement> = self
            .inputs
            .iter()
            .filter(|input| input.spills.has_optional_spills())
            .map(|input| (input.func, OptionalFinalSpillPlacement::Scratch))
            .collect();
        if choices.is_empty() {
            return choices;
        }

        let mut best_score = self.score(&choices);
        let mut all_stable = choices.clone();
        for choice in all_stable.values_mut() {
            *choice = OptionalFinalSpillPlacement::Stable;
        }
        let all_stable_score = self.score(&all_stable);
        if all_stable_score < best_score {
            choices = all_stable;
            best_score = all_stable_score;
        }

        for input in self
            .inputs
            .iter()
            .filter(|input| input.spills.has_optional_spills())
        {
            let mut trial = choices.clone();
            let next = match trial[&input.func] {
                OptionalFinalSpillPlacement::Scratch => OptionalFinalSpillPlacement::Stable,
                OptionalFinalSpillPlacement::Stable => OptionalFinalSpillPlacement::Scratch,
            };
            trial.insert(input.func, next);
            let score = self.score(&trial);
            if score < best_score {
                choices = trial;
                best_score = score;
            }
        }

        choices
    }

    fn score(
        &self,
        choices: &FxHashMap<FuncRef, OptionalFinalSpillPlacement>,
    ) -> FinalSpillChoiceScore {
        let reserves = self.final_spill_reserves(choices);
        let mut scratch_effects = self.base_scratch_effects.clone();
        for (&func, reserve) in &reserves {
            if reserve.scratch_words != 0 {
                scratch_effects.insert(func);
            }
        }

        let placement = compute_semantic_memory_placement(
            self.source_module,
            MemoryPlacementSection {
                funcs: self.funcs,
                entry: self.section_entry,
                includes: self.section_includes,
            },
            self.pre_analyses,
            self.ptr_escape,
            &scratch_effects,
            self.backend,
            &reserves,
        );

        (
            placement.global_dyn_base,
            placement.arena_base,
            placement.scratch_peak_words,
            placement.static_chain_peak_words,
            reserves
                .values()
                .map(|reserve| u64::from(reserve.stable_words))
                .sum(),
            reserves
                .values()
                .map(|reserve| u64::from(reserve.scratch_words))
                .sum(),
        )
    }

    fn final_spill_reserves(
        &self,
        choices: &FxHashMap<FuncRef, OptionalFinalSpillPlacement>,
    ) -> FxHashMap<FuncRef, BackendSpillReserve> {
        self.inputs
            .iter()
            .map(|input| {
                let choice = choices
                    .get(&input.func)
                    .copied()
                    .unwrap_or(OptionalFinalSpillPlacement::Scratch);
                (
                    input.func,
                    input.spills.required_reserve(
                        &input.mem_plan,
                        input.reserve,
                        input.abs_spill_floor_words,
                        choice,
                    ),
                )
            })
            .collect()
    }
}

pub(crate) fn allocate_final_spills(
    mut alloc: StackifyAlloc,
    mut mem_plan: FuncMemPlan,
    reserved: BackendSpillReserve,
    abs_spill_floor_words: u32,
    spills: FinalSpillObjects,
    optional_placement: OptionalFinalSpillPlacement,
) -> FinalSpillAllocation {
    if spills.is_empty() {
        alloc.validate_spill_storage();
        return FinalSpillAllocation {
            alloc,
            mem_plan,
            required_reserve: BackendSpillReserve::default(),
            stack_obj_remap: FxHashMap::default(),
        };
    }

    let mut next_obj = mem_plan
        .obj_loc
        .keys()
        .map(|id| id.as_u32())
        .max()
        .map_or(0, |id| id.checked_add(1).expect("stack object id overflow"));
    let mut remap: FxHashMap<StackObjId, StackObjId> = FxHashMap::default();
    for &(old_obj, _) in &spills.objs {
        remap.insert(old_obj, {
            let obj = StackObjId::new(next_obj as usize);
            next_obj = next_obj.checked_add(1).expect("stack object id overflow");
            obj
        });
    }

    let mut scratch_objs = Vec::new();
    let mut stable_objs = Vec::new();
    for &(old_obj, must_stable) in &spills.objs {
        let new_obj = remap[&old_obj];
        if must_stable || matches!(optional_placement, OptionalFinalSpillPlacement::Stable) {
            stable_objs.push((old_obj, new_obj));
        } else {
            scratch_objs.push((old_obj, new_obj));
        }
    }

    let required_reserve = spills.required_reserve(
        &mem_plan,
        reserved,
        abs_spill_floor_words,
        optional_placement,
    );

    place_scratch_spills(
        &mut mem_plan,
        &scratch_objs,
        reserved.scratch_words,
        required_reserve.scratch_words,
        abs_spill_floor_words,
    );
    place_stable_spills(
        &mut mem_plan,
        &stable_objs,
        reserved.stable_words,
        required_reserve.stable_words,
        abs_spill_floor_words,
    );

    alloc.remap_stack_objects(&remap);
    for (value, old_obj) in spills.spilled_values {
        let new_obj = remap[&old_obj];
        alloc.spill_obj[value] = Some(new_obj);
        mem_plan.spill_obj[value] = Some(new_obj);
    }
    alloc.validate_spill_storage();

    FinalSpillAllocation {
        alloc,
        mem_plan,
        required_reserve,
        stack_obj_remap: remap,
    }
}

fn final_spilled_values(alloc: &StackifyAlloc) -> Vec<(ValueId, StackObjId)> {
    alloc
        .spill_obj
        .iter()
        .filter_map(|(value, obj)| {
            let obj = (*obj)?;
            alloc.scratch_slot_of_value[value]
                .is_none()
                .then_some((value, obj))
        })
        .collect()
}

fn spill_count(len: usize) -> u32 {
    u32::try_from(len).expect("spill count overflow")
}

fn required_stable_reserve_words(
    mem_plan: &FuncMemPlan,
    reserved_words: u32,
    spill_words: u32,
    abs_spill_floor_words: u32,
) -> u32 {
    if spill_words == 0 {
        return 0;
    }

    let required_for_floor = match mem_plan.stable_mode {
        StableMode::StaticAbs { base_word } => {
            let semantic_stable_words = mem_plan
                .stable_words
                .checked_sub(reserved_words)
                .expect("reserved stable spill words exceed stable words");
            let min_start_offset = abs_spill_floor_words.saturating_sub(base_word);
            min_start_offset
                .checked_add(spill_words)
                .expect("final stable spill reserve overflow")
                .saturating_sub(semantic_stable_words)
        }
        StableMode::None | StableMode::DynamicFrame => spill_words,
    };

    spill_words.max(required_for_floor)
}

fn place_scratch_spills(
    mem_plan: &mut FuncMemPlan,
    objs: &[(StackObjId, StackObjId)],
    reserved_words: u32,
    required_words: u32,
    abs_spill_floor_words: u32,
) {
    let spill_words = u32::try_from(objs.len()).expect("spill count overflow");
    if spill_words == 0 {
        return;
    }

    let tail_start = mem_plan.scratch_words.checked_sub(spill_words);
    let use_reserved_tail = required_words <= reserved_words && tail_start.is_some();
    let start_word = if use_reserved_tail {
        tail_start.expect("checked above")
    } else {
        mem_plan.scratch_words.max(abs_spill_floor_words)
    };
    place_spills(mem_plan, objs, start_word, ObjLoc::ScratchAbs);
    if !use_reserved_tail {
        let scratch_peak_words = start_word
            .checked_add(spill_words)
            .expect("final scratch spill peak overflow");
        mem_plan.scratch_words = mem_plan.scratch_words.max(scratch_peak_words);
    }
}

fn place_stable_spills(
    mem_plan: &mut FuncMemPlan,
    objs: &[(StackObjId, StackObjId)],
    reserved_words: u32,
    required_words: u32,
    abs_spill_floor_words: u32,
) {
    let spill_words = u32::try_from(objs.len()).expect("spill count overflow");
    if spill_words == 0 {
        return;
    }

    let tail_start = stable_tail_start(mem_plan, spill_words);
    let use_reserved_tail = required_words <= reserved_words
        && tail_start.is_some_and(|start| {
            stable_tail_clears_abs_floor(mem_plan, start, abs_spill_floor_words)
        });
    let start_word = if use_reserved_tail {
        tail_start.expect("checked above")
    } else {
        mem_plan.abs_words_end().max(abs_spill_floor_words)
    };
    let stable_mode = mem_plan.stable_mode;
    let loc = |word| match (use_reserved_tail, stable_mode) {
        (true, StableMode::StaticAbs { .. }) => ObjLoc::StableAbs(word),
        (true, StableMode::DynamicFrame) => ObjLoc::StableFrame(word),
        (true, StableMode::None) => unreachable!("stable tail requires stable mode"),
        (false, _) => ObjLoc::ScratchAbs(word),
    };
    place_spills(mem_plan, objs, start_word, loc);
    if !use_reserved_tail {
        let scratch_peak_words = start_word
            .checked_add(spill_words)
            .expect("final stable spill fallback peak overflow");
        mem_plan.scratch_words = mem_plan.scratch_words.max(scratch_peak_words);
    }
}

fn place_spills(
    mem_plan: &mut FuncMemPlan,
    objs: &[(StackObjId, StackObjId)],
    start_word: u32,
    loc: impl Fn(u32) -> ObjLoc,
) {
    for (idx, &(_, new_obj)) in objs.iter().enumerate() {
        let word = start_word
            .checked_add(u32::try_from(idx).expect("spill count overflow"))
            .expect("final spill word overflow");
        mem_plan.obj_loc.insert(new_obj, loc(word));
    }
}

fn stable_tail_start(mem_plan: &FuncMemPlan, spill_words: u32) -> Option<u32> {
    match mem_plan.stable_mode {
        StableMode::StaticAbs { .. } | StableMode::DynamicFrame => {
            mem_plan.stable_words.checked_sub(spill_words)
        }
        StableMode::None => None,
    }
}

fn stable_tail_clears_abs_floor(
    mem_plan: &FuncMemPlan,
    start: u32,
    abs_spill_floor_words: u32,
) -> bool {
    match mem_plan.stable_mode {
        StableMode::StaticAbs { base_word } => base_word
            .checked_add(start)
            .is_some_and(|start| abs_spill_floor_words <= start),
        StableMode::DynamicFrame => true,
        StableMode::None => unreachable!("stable tail requires stable mode"),
    }
}

#[cfg(test)]
mod tests {
    use cranelift_entity::{EntityRef, SecondaryMap};
    use rustc_hash::{FxHashMap, FxHashSet};
    use sonatina_ir::ValueId;

    use super::{
        FinalSpillAllocation, FinalSpillObjects, OptionalFinalSpillPlacement,
        allocate_final_spills as alloc_final_spills,
    };
    use crate::{
        bitset::BitSet,
        isa::evm::{
            FuncMemPlan, ObjLoc,
            malloc_plan::MallocEscapeKind,
            memory_plan::{BackendSpillReserve, StableMode},
            static_arena_alloc::StackObjId,
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

    fn scratch_mem_plan(scratch_words: u32) -> FuncMemPlan {
        FuncMemPlan {
            arena_base: 0xa0,
            scratch_words,
            stable_words: 0,
            stable_mode: StableMode::None,
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

    fn alloc_with_object_spills(values: &[(u32, u32)]) -> StackifyAlloc {
        let mut alloc = StackifyAlloc::default();
        for &(value, obj) in values {
            let value = ValueId::from_u32(value);
            let obj = StackObjId::new(obj as usize);
            alloc.set_object_spill_for_test(value, obj);
        }
        alloc
    }

    fn reserve(scratch_words: u32, stable_words: u32) -> BackendSpillReserve {
        BackendSpillReserve {
            scratch_words,
            stable_words,
        }
    }

    fn stable_values(values: &[u32]) -> BitSet<ValueId> {
        values.iter().copied().map(ValueId::from_u32).collect()
    }

    fn allocate_final_spills(
        alloc: StackifyAlloc,
        mem_plan: FuncMemPlan,
        reserve: BackendSpillReserve,
        floor: u32,
        stable: &BitSet<ValueId>,
        placement: OptionalFinalSpillPlacement,
    ) -> FinalSpillAllocation {
        let spills = FinalSpillObjects::compute(&alloc, stable);
        alloc_final_spills(alloc, mem_plan, reserve, floor, spills, placement)
    }

    #[test]
    fn zero_final_spills_do_not_count_stable_words_as_scratch() {
        let final_spills = allocate_final_spills(
            StackifyAlloc::default(),
            static_mem_plan(0, 5),
            BackendSpillReserve::default(),
            0,
            &BitSet::default(),
            OptionalFinalSpillPlacement::Scratch,
        );

        assert_eq!(
            final_spills.required_reserve,
            BackendSpillReserve::default()
        );
        assert_eq!(final_spills.mem_plan.scratch_words, 0);
    }

    #[test]
    fn zero_final_spills_do_not_request_backend_spill_reserve() {
        let final_spills = allocate_final_spills(
            StackifyAlloc::default(),
            static_mem_plan(3, 5),
            BackendSpillReserve::default(),
            0,
            &BitSet::default(),
            OptionalFinalSpillPlacement::Scratch,
        );

        assert_eq!(
            final_spills.required_reserve,
            BackendSpillReserve::default()
        );
        assert_eq!(final_spills.mem_plan.scratch_words, 3);
    }

    #[test]
    fn static_final_spills_use_reserved_stable_tail() {
        let alloc = alloc_with_object_spills(&[(10, 0), (11, 1)]);
        let final_spills = allocate_final_spills(
            alloc,
            static_mem_plan(3, 7),
            reserve(0, 2),
            0,
            &stable_values(&[10, 11]),
            OptionalFinalSpillPlacement::Scratch,
        );

        assert_eq!(final_spills.required_reserve, reserve(0, 2));
        assert_eq!(final_spills.mem_plan.scratch_words, 3);
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(0)],
            ObjLoc::StableAbs(5)
        );
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(1)],
            ObjLoc::StableAbs(6)
        );
    }

    #[test]
    fn insufficient_static_reserve_reports_required_words() {
        let alloc = alloc_with_object_spills(&[(10, 0), (11, 1)]);
        let final_spills = allocate_final_spills(
            alloc,
            static_mem_plan(3, 7),
            reserve(0, 1),
            0,
            &stable_values(&[10, 11]),
            OptionalFinalSpillPlacement::Scratch,
        );

        assert_eq!(final_spills.required_reserve, reserve(0, 2));
        assert_eq!(final_spills.mem_plan.scratch_words, 12);
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(0)],
            ObjLoc::ScratchAbs(10)
        );
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(1)],
            ObjLoc::ScratchAbs(11)
        );
    }

    #[test]
    fn static_final_spills_request_padding_to_clear_fixed_memory_floor() {
        let alloc = alloc_with_object_spills(&[(10, 0), (11, 1)]);
        let final_spills = allocate_final_spills(
            alloc,
            static_mem_plan(3, 7),
            BackendSpillReserve::default(),
            13,
            &stable_values(&[10, 11]),
            OptionalFinalSpillPlacement::Scratch,
        );

        assert_eq!(final_spills.required_reserve, reserve(0, 5));
        assert_eq!(final_spills.mem_plan.scratch_words, 15);
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(0)],
            ObjLoc::ScratchAbs(13)
        );
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(1)],
            ObjLoc::ScratchAbs(14)
        );
    }

    #[test]
    fn static_final_spills_use_padded_reserve_above_fixed_memory_floor() {
        let alloc = alloc_with_object_spills(&[(10, 0), (11, 1)]);
        let final_spills = allocate_final_spills(
            alloc,
            static_mem_plan(3, 12),
            reserve(0, 5),
            13,
            &stable_values(&[10, 11]),
            OptionalFinalSpillPlacement::Scratch,
        );

        assert_eq!(final_spills.required_reserve, reserve(0, 5));
        assert_eq!(final_spills.mem_plan.scratch_words, 3);
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(0)],
            ObjLoc::StableAbs(10)
        );
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(1)],
            ObjLoc::StableAbs(11)
        );
    }

    #[test]
    fn scratch_final_spills_use_reserved_tail() {
        let alloc = alloc_with_object_spills(&[(10, 0), (11, 1)]);
        let final_spills = allocate_final_spills(
            alloc,
            scratch_mem_plan(5),
            reserve(2, 0),
            0,
            &BitSet::default(),
            OptionalFinalSpillPlacement::Scratch,
        );

        assert_eq!(final_spills.required_reserve, reserve(2, 0));
        assert_eq!(final_spills.mem_plan.scratch_words, 5);
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(0)],
            ObjLoc::ScratchAbs(3)
        );
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(1)],
            ObjLoc::ScratchAbs(4)
        );
    }

    #[test]
    fn scratch_final_spills_fallback_clears_fixed_memory_floor() {
        let alloc = alloc_with_object_spills(&[(10, 0), (11, 1)]);
        let final_spills = allocate_final_spills(
            alloc,
            scratch_mem_plan(3),
            BackendSpillReserve::default(),
            6,
            &BitSet::default(),
            OptionalFinalSpillPlacement::Scratch,
        );

        assert_eq!(final_spills.required_reserve, reserve(2, 0));
        assert_eq!(final_spills.mem_plan.scratch_words, 8);
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(0)],
            ObjLoc::ScratchAbs(6)
        );
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(1)],
            ObjLoc::ScratchAbs(7)
        );
    }

    #[test]
    fn scratch_final_spills_use_reserved_tail_even_below_fixed_memory_floor() {
        let alloc = alloc_with_object_spills(&[(10, 0), (11, 1)]);
        let final_spills = allocate_final_spills(
            alloc,
            scratch_mem_plan(5),
            reserve(2, 0),
            6,
            &BitSet::default(),
            OptionalFinalSpillPlacement::Scratch,
        );

        assert_eq!(final_spills.required_reserve, reserve(2, 0));
        assert_eq!(final_spills.mem_plan.scratch_words, 5);
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(0)],
            ObjLoc::ScratchAbs(3)
        );
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(1)],
            ObjLoc::ScratchAbs(4)
        );
    }

    #[test]
    fn mixed_final_spills_split_scratch_and_stable_reserves() {
        let alloc = alloc_with_object_spills(&[(10, 0), (11, 1), (12, 2)]);
        let final_spills = allocate_final_spills(
            alloc,
            static_mem_plan(5, 5),
            reserve(2, 1),
            0,
            &stable_values(&[12]),
            OptionalFinalSpillPlacement::Scratch,
        );

        assert_eq!(final_spills.required_reserve, reserve(2, 1));
        assert_eq!(final_spills.mem_plan.scratch_words, 5);
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(0)],
            ObjLoc::ScratchAbs(3)
        );
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(1)],
            ObjLoc::ScratchAbs(4)
        );
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(2)],
            ObjLoc::StableAbs(4)
        );
    }
}
