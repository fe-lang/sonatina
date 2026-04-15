use cranelift_entity::{EntityRef, SecondaryMap};
use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{BlockId, InstId, Module, ValueId, module::FuncRef};
use std::{
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet},
};

use crate::{
    bitset::BitSet,
    liveness::InstLiveness,
    module_analysis::{CallGraph, CallGraphSccs, SccBuilder, SccRef},
    stackalloc::StackifyAlloc,
};

use super::{
    canonicalize_alias_value,
    malloc_plan::MallocEscapeKind,
    ptr_escape::PtrEscapeSummary,
    static_arena_alloc::{
        CallSiteObjects, ExactPackItem, FuncStackObjects, LiveRegion, LocalObjIdx, ObjFacts,
        PackedObject, StableItemIdx, StackObj, StackObjId, StackObjKind, StaticArenaAllocCtx,
        pack_exact_peak, pack_exact_with_offsets, pack_objects_presorted,
    },
};
use sonatina_ir::isa::evm::Evm;

pub const WORD_BYTES: u32 = 32;
pub const FREE_PTR_SLOT: u8 = 0x40;
pub const DYN_SP_SLOT: u8 = 0x80;
pub const STATIC_BASE: u32 = 0xa0;

#[derive(Clone, Debug)]
pub struct ProgramMemoryPlan {
    pub scratch_peak_words: u32,
    pub static_chain_peak_words: u32,
    pub global_dyn_base: u32,
    pub funcs: FxHashMap<FuncRef, FuncMemPlan>,
    #[allow(dead_code)]
    pub sccs: FxHashMap<SccRef, SccMemPlan>,
}

#[derive(Clone, Debug)]
pub struct FuncMemPlan {
    pub scratch_words: u32,
    pub stable_words: u32,
    pub stable_mode: StableMode,
    pub entry_abs_words: u32,
    pub obj_loc: FxHashMap<StackObjId, ObjLoc>,
    pub alloca_loc: FxHashMap<InstId, ObjLoc>,
    pub spill_obj: SecondaryMap<ValueId, Option<StackObjId>>,
    pub call_preserve: FxHashMap<InstId, CallPreservePlan>,
    pub malloc_future_abs_words: FxHashMap<InstId, u32>,
    pub transient_mallocs: FxHashSet<InstId>,
    pub malloc_escape_kinds: FxHashMap<InstId, MallocEscapeKind>,
    pub return_escape_caller_abs_words: u32,
}

impl FuncMemPlan {
    pub fn stable_base_word(&self) -> Option<u32> {
        match self.stable_mode {
            StableMode::StaticAbs { base_word } => Some(base_word),
            StableMode::None | StableMode::DynamicFrame => None,
        }
    }

    pub fn frame_words(&self) -> u32 {
        match self.stable_mode {
            StableMode::DynamicFrame => self.stable_words,
            StableMode::None | StableMode::StaticAbs { .. } => 0,
        }
    }

    pub fn uses_dynamic_frame(&self) -> bool {
        matches!(self.stable_mode, StableMode::DynamicFrame)
    }

    pub fn frame_size_words(&self) -> u32 {
        self.frame_words()
    }

    pub fn abs_words_end(&self) -> u32 {
        let stable_end = match self.stable_mode {
            StableMode::StaticAbs { base_word } if self.stable_words != 0 => base_word
                .checked_add(self.stable_words)
                .expect("stable absolute end overflow"),
            StableMode::None | StableMode::DynamicFrame | StableMode::StaticAbs { .. } => 0,
        };
        self.scratch_words.max(stable_end)
    }

    pub fn active_abs_words(&self) -> u32 {
        self.entry_abs_words.max(self.abs_words_end())
    }

    pub fn abs_addr_for_loc(&self, loc: ObjLoc) -> Option<u32> {
        match loc {
            ObjLoc::ScratchAbs(word) => Some(abs_addr_for_word(word)),
            ObjLoc::StableAbs(word) => Some(abs_addr_for_word(
                self.stable_base_word()
                    .expect("stable absolute object missing base word")
                    .checked_add(word)
                    .expect("stable absolute word overflow"),
            )),
            ObjLoc::StableFrame(_) | ObjLoc::StackPinned(_) => None,
        }
    }

    pub fn obj_word_offset(&self, obj: StackObjId) -> Option<u32> {
        self.obj_loc.get(&obj).and_then(|loc| match *loc {
            ObjLoc::ScratchAbs(word) | ObjLoc::StableAbs(word) | ObjLoc::StableFrame(word) => {
                Some(word)
            }
            ObjLoc::StackPinned(_) => None,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::isa::evm::static_arena_alloc::BlockLiveSegment;

    fn region(block: u32, start_boundary: u32, end_boundary: u32) -> LiveRegion {
        LiveRegion {
            segments: SmallVec::from_vec(vec![BlockLiveSegment {
                block: BlockId::from_u32(block),
                start_boundary,
                end_boundary,
            }]),
            first_rank: start_boundary,
            last_rank: end_boundary,
        }
    }

    fn stack_obj(id: u32, kind: StackObjKind, size_words: u32, region: LiveRegion) -> StackObj {
        StackObj {
            id: StackObjId::new(id as usize),
            kind,
            size_words,
            region,
            access_weight: 0,
            load_count: 0,
            store_count: 0,
        }
    }

    #[test]
    fn stable_pack_conflicts_shadow_with_callee_visible_objects() {
        let real0 = stack_obj(
            1,
            StackObjKind::Alloca(InstId::from_u32(1)),
            4,
            region(0, 0, 2),
        );
        let real1 = stack_obj(
            2,
            StackObjKind::Alloca(InstId::from_u32(2)),
            4,
            region(1, 0, 2),
        );
        let shadow = ShadowPackObj {
            call_idx: 0,
            obj: stack_obj(
                3,
                StackObjKind::Shadow(InstId::from_u32(10)),
                4,
                LiveRegion::sort_only(10),
            ),
        };
        let sorted_objects = vec![&real0, &real1];
        let mut must_stable = BitSet::default();
        let _ = must_stable.insert(real0.id);
        let _ = must_stable.insert(real1.id);
        let promoted_optional = BitSet::default();
        let real_conflicts = vec![BitSet::default(), BitSet::default()];
        let mut shadow_conflicts = vec![BitSet::default(); 1];
        let _ = shadow_conflicts[0].insert(LocalObjIdx::new(0));
        let _ = shadow_conflicts[0].insert(LocalObjIdx::new(1));

        let mut items = Vec::new();
        let mut conflicts = Vec::new();
        build_stable_pack(
            &mut items,
            &mut conflicts,
            &[shadow],
            StablePackCtx {
                sorted_objects: &sorted_objects,
                must_stable: &must_stable,
                real_conflicts_by_local: &real_conflicts,
                shadow_conflicts_by_call: &shadow_conflicts,
            },
            &promoted_optional,
        );
        let packed = pack_exact_with_offsets(&items, &conflicts);

        let real0_off = packed.offsets[&real0.id];
        let real1_off = packed.offsets[&real1.id];
        let shadow_off = packed.offsets[&StackObjId::new(3)];
        assert_eq!(real0_off, 0);
        assert_eq!(real1_off, 0);
        assert_ne!(shadow_off, real0_off);
        assert_ne!(shadow_off, real1_off);
        assert_eq!(shadow_off, 4);
    }

    #[test]
    fn swap_search_uses_bounded_shortlists_once_pair_count_exceeds_limit() {
        let candidate_count = 320usize;
        let objects: Vec<_> = (0..candidate_count)
            .map(|idx| {
                stack_obj(
                    idx as u32,
                    StackObjKind::Alloca(InstId::from_u32(idx as u32)),
                    1 + (idx % 3) as u32,
                    region(0, 0, 1),
                )
            })
            .collect();
        let obj_size_words = objects.iter().map(|obj| (obj.id, obj.size_words)).collect();
        let stack = FuncStackObjects {
            objects,
            obj_facts: FxHashMap::default(),
            obj_size_words,
            alloca_ids: FxHashMap::default(),
            spill_obj: SecondaryMap::default(),
            call_sites: Vec::new(),
            next_obj_id: candidate_count as u32,
        };
        let sorted_objects: Vec<_> = stack.objects.iter().collect();
        let candidates = sorted_objects
            .iter()
            .enumerate()
            .map(|(local_idx, obj)| CandidateMeta {
                obj_id: obj.id,
                local_idx: LocalObjIdx::new(local_idx),
                size_words: obj.size_words,
                recursive_access_cost: (local_idx % 11) as u64,
                shadow_copy_words: 0,
                live_call_indices: SmallVec::new(),
            })
            .collect();
        let cost_model = ArenaCostModel::default();
        let problem = PlacementProblem {
            stack: &stack,
            sorted_objects,
            sorted_calls: Vec::new(),
            must_stable: BitSet::default(),
            must_stable_by_local: vec![false; candidate_count],
            candidates,
            base_shadow_words_by_call: Vec::new(),
            base_shadow_copy_words: 0,
            base_recursive_access_cost: 0,
            frame_setup_cost: 0,
            shadow_cost_per_word: 0,
            next_shadow_base_id: stack.next_obj_id,
            is_recursive: false,
            cost_model: &cost_model,
            real_conflicts_by_local: vec![BitSet::default(); candidate_count],
            shadow_conflicts_by_call: Vec::new(),
        };
        let mut state = PlacementState::new(&problem);
        for candidate_idx in 0..candidate_count / 2 {
            state.apply_add(&problem, candidate_idx);
        }

        let feasible_add_count = state.promoted.iter().filter(|&&promoted| !promoted).count();
        let feasible_remove_count = state.promoted_count;
        assert!(
            feasible_add_count.saturating_mul(feasible_remove_count) > SWAP_FULL_PAIR_LIMIT,
            "test must exercise the bounded swap shortlist path"
        );

        let mut lb_state = PlacementLowerBoundState::new(&problem);
        let mut search_work = SearchWorkBuffers::default();
        let current_score = FuncPlacementScore {
            scratch_words: u32::MAX,
            stable_words: u32::MAX,
            cost: u64::MAX,
        };
        let _ = find_best_exact_swap_move(
            &problem,
            &state,
            &mut lb_state,
            current_score,
            &mut FuncPlacementScoreWorkspace::default(),
            &mut search_work,
        );

        assert!(!search_work.add_shortlist.is_empty());
        assert!(!search_work.remove_shortlist.is_empty());
        assert!(search_work.add_shortlist.len() <= SWAP_SHORTLIST_PER_METRIC * 3);
        assert!(search_work.remove_shortlist.len() <= SWAP_SHORTLIST_PER_METRIC * 3);
        assert_eq!(
            search_work.swap_exact.len(),
            search_work
                .add_shortlist
                .len()
                .saturating_mul(search_work.remove_shortlist.len()),
            "bounded swap search should only exact-score the shortlist cross-product",
        );
    }
}

#[derive(Clone, Debug)]
pub struct SccMemPlan {
    pub is_recursive: bool,
    pub static_chain_prefix_words: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StableMode {
    None,
    StaticAbs { base_word: u32 },
    DynamicFrame,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ObjLoc {
    ScratchAbs(u32),
    StableAbs(u32),
    StableFrame(u32),
    #[allow(dead_code)]
    StackPinned(u8),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallPreservePlan {
    pub mode: PreserveMode,
    pub result_count: u8,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PreserveMode {
    #[allow(dead_code)]
    None,
    ShadowRuns {
        shadow_obj: StackObjId,
        runs: SmallVec<[SaveRun; 2]>,
    },
    #[allow(dead_code)]
    TinyStackLift { word_offsets: SmallVec<[u32; 4]> },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SaveRun {
    pub scratch_src_word: u32,
    pub shadow_dst_word: u32,
    pub len_words: u32,
}

#[derive(Clone, Copy, Debug)]
pub struct ArenaCostModel {
    pub w_mem: u64,
    pub w_save: u64,
    pub w_code: u64,
    pub w_stack: u64,
    pub max_save_words_per_call: u32,
}

impl Default for ArenaCostModel {
    fn default() -> Self {
        Self {
            w_mem: 3,
            w_save: 1,
            w_code: 50,
            w_stack: 1,
            max_save_words_per_call: 128,
        }
    }
}

pub(crate) struct FuncAnalysis {
    pub(crate) alloc: StackifyAlloc,
    pub(crate) inst_liveness: InstLiveness,
    pub(crate) block_order: Vec<BlockId>,
    pub(crate) value_aliases: SecondaryMap<ValueId, Option<ValueId>>,
}

impl FuncAnalysis {
    pub(crate) fn canonicalize_value(&self, value: ValueId) -> ValueId {
        canonicalize_alias_value(&self.value_aliases, value)
    }
}

#[derive(Clone, Debug)]
struct FuncPlacementEval {
    scratch_offsets: FxHashMap<StackObjId, u32>,
    scratch_words: u32,
    stable_offsets: FxHashMap<StackObjId, u32>,
    stable_words: u32,
    call_preserve: FxHashMap<InstId, CallPreservePlan>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct FuncPlacementScore {
    scratch_words: u32,
    stable_words: u32,
    cost: u64,
}

#[derive(Default)]
struct FuncPlacementWorkspace {
    scratch_pack: Vec<PackedObject>,
    shadow_objs: Vec<ShadowPackObj>,
    stable_items: Vec<ExactPackItem<StableItemIdx>>,
    stable_conflicts: Vec<BitSet<StableItemIdx>>,
}

#[derive(Default)]
struct FuncPlacementScoreWorkspace {
    stable_items: Vec<ExactPackItem<StableItemIdx>>,
    stable_conflicts: Vec<BitSet<StableItemIdx>>,
}

struct StablePackCtx<'a> {
    sorted_objects: &'a [&'a StackObj],
    must_stable: &'a BitSet<StackObjId>,
    real_conflicts_by_local: &'a [BitSet<LocalObjIdx>],
    shadow_conflicts_by_call: &'a [BitSet<LocalObjIdx>],
}

#[derive(Clone, Debug)]
struct CandidateMeta {
    obj_id: StackObjId,
    local_idx: LocalObjIdx,
    size_words: u32,
    recursive_access_cost: u64,
    shadow_copy_words: u64,
    live_call_indices: SmallVec<[u32; 4]>,
}

struct PlacementProblem<'a> {
    stack: &'a FuncStackObjects,
    sorted_objects: Vec<&'a StackObj>,
    sorted_calls: Vec<&'a CallSiteObjects>,
    must_stable: BitSet<StackObjId>,
    must_stable_by_local: Vec<bool>,
    candidates: Vec<CandidateMeta>,
    base_shadow_words_by_call: Vec<u32>,
    base_shadow_copy_words: u64,
    base_recursive_access_cost: u64,
    frame_setup_cost: u64,
    shadow_cost_per_word: u64,
    next_shadow_base_id: u32,
    is_recursive: bool,
    cost_model: &'a ArenaCostModel,
    real_conflicts_by_local: Vec<BitSet<LocalObjIdx>>,
    shadow_conflicts_by_call: Vec<BitSet<LocalObjIdx>>,
}

#[derive(Clone, Debug)]
struct PlacementState {
    promoted: Vec<bool>,
    promoted_count: usize,
    shadow_words_by_call: Vec<u32>,
    shadow_copy_words: u64,
    recursive_access_cost: u64,
    scratch_real_locals: Vec<u32>,
    stable_real_locals: Vec<u32>,
    nonzero_shadow_calls: Vec<u32>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PlacementMove {
    None,
    Add(usize),
    Remove(usize),
    Swap { add_idx: usize, remove_idx: usize },
}

#[derive(Clone, Copy, Debug)]
struct ExactMoveEval {
    mv: PlacementMove,
    exact: FuncPlacementScore,
}

#[derive(Default)]
struct SearchWorkBuffers {
    one_flip_exact: Vec<ExactMoveEval>,
    swap_exact: Vec<ExactMoveEval>,
    add_shortlist: Vec<usize>,
    remove_shortlist: Vec<usize>,
}

#[derive(Default)]
struct PlacementLowerBoundState;

#[derive(Clone, Debug)]
struct ShadowPackObj {
    call_idx: u32,
    obj: StackObj,
}

const SWAP_FULL_PAIR_LIMIT: usize = 25_000;
const SWAP_SHORTLIST_PER_METRIC: usize = 8;

impl<'a> PlacementProblem<'a> {
    fn new(
        stack: &'a FuncStackObjects,
        facts: &FxHashMap<StackObjId, ObjFacts>,
        is_recursive: bool,
        cost_model: &'a ArenaCostModel,
    ) -> Self {
        let mut sorted_objects: Vec<_> = stack.objects.iter().collect();
        sorted_objects.sort_unstable_by_key(|obj| obj.region.sort_key(obj.id));
        let sorted_calls: Vec<_> = stack.call_sites.iter().collect();
        let mut local_obj_index_by_id = vec![u32::MAX; stack.next_obj_id as usize];
        let mut must_stable_by_local = vec![false; sorted_objects.len()];
        let mut must_stable = BitSet::default();
        for (local_idx, &obj) in sorted_objects.iter().enumerate() {
            local_obj_index_by_id[obj.id.as_u32() as usize] = local_idx as u32;
            let fact = facts
                .get(&obj.id)
                .unwrap_or_else(|| panic!("missing object facts for obj {}", obj.id.as_u32()));
            must_stable_by_local[local_idx] = fact.must_stable;
            if fact.must_stable {
                let _ = must_stable.insert(obj.id);
            }
        }

        let mut candidates: Vec<_> = facts
            .values()
            .filter(|fact| !fact.must_stable && !fact.live_across_calls.is_empty())
            .map(|fact| fact.id)
            .collect();
        candidates.sort_unstable_by_key(|id| id.as_u32());

        let mut optional_idx_by_local = vec![u32::MAX; sorted_objects.len()];
        let mut candidate_meta = Vec::with_capacity(candidates.len());
        for obj_id in candidates {
            let fact = facts
                .get(&obj_id)
                .unwrap_or_else(|| panic!("missing object facts for obj {}", obj_id.as_u32()));
            let local_idx = *local_obj_index_by_id
                .get(obj_id.as_u32() as usize)
                .unwrap_or(&u32::MAX);
            assert_ne!(
                local_idx,
                u32::MAX,
                "missing sorted object index for obj {}",
                obj_id.as_u32()
            );
            optional_idx_by_local[local_idx as usize] = candidate_meta.len() as u32;
            candidate_meta.push(CandidateMeta {
                obj_id,
                local_idx: LocalObjIdx::new(local_idx as usize),
                size_words: fact.size_words,
                recursive_access_cost: recursive_access_cost(cost_model, is_recursive, fact),
                shadow_copy_words: 0,
                live_call_indices: SmallVec::new(),
            });
        }

        let mut real_conflicts_by_local = vec![BitSet::default(); sorted_objects.len()];
        for (lhs_idx, &lhs) in sorted_objects.iter().enumerate() {
            for (rhs_idx, &rhs) in sorted_objects.iter().enumerate().skip(lhs_idx + 1) {
                if lhs.size_words == 0 || rhs.size_words == 0 || !lhs.region.overlaps(&rhs.region) {
                    continue;
                }
                let lhs_idx = LocalObjIdx::new(lhs_idx);
                let rhs_idx = LocalObjIdx::new(rhs_idx);
                let _ = real_conflicts_by_local[lhs_idx.index()].insert(rhs_idx);
                let _ = real_conflicts_by_local[rhs_idx.index()].insert(lhs_idx);
            }
        }

        let mut shadow_conflicts_by_call = vec![BitSet::default(); sorted_calls.len()];
        let mut base_shadow_words_by_call = vec![0u32; sorted_calls.len()];
        let mut base_shadow_copy_words = 0u64;
        for (call_idx, &call) in sorted_calls.iter().enumerate() {
            for &obj in &call.callee_visible_objs {
                let local_idx = *local_obj_index_by_id
                    .get(obj.as_u32() as usize)
                    .unwrap_or(&u32::MAX);
                assert_ne!(
                    local_idx,
                    u32::MAX,
                    "missing sorted object index for obj {}",
                    obj.as_u32()
                );
                let _ =
                    shadow_conflicts_by_call[call_idx].insert(LocalObjIdx::new(local_idx as usize));
            }
            for &obj in &call.live_across_objs {
                let size = stack
                    .obj_size_words
                    .get(&obj)
                    .copied()
                    .unwrap_or_else(|| panic!("missing object size for obj {}", obj.as_u32()));
                if size == 0 {
                    continue;
                }
                let local_idx = *local_obj_index_by_id
                    .get(obj.as_u32() as usize)
                    .unwrap_or(&u32::MAX);
                assert_ne!(
                    local_idx,
                    u32::MAX,
                    "missing sorted object index for obj {}",
                    obj.as_u32()
                );
                let _ =
                    shadow_conflicts_by_call[call_idx].insert(LocalObjIdx::new(local_idx as usize));
                if must_stable_by_local[local_idx as usize] {
                    continue;
                }
                base_shadow_words_by_call[call_idx] = base_shadow_words_by_call[call_idx]
                    .checked_add(size)
                    .expect("shadow words overflow");
                base_shadow_copy_words = base_shadow_copy_words
                    .checked_add(u64::from(size))
                    .expect("shadow copy words overflow");
                let optional_idx = optional_idx_by_local[local_idx as usize];
                if optional_idx != u32::MAX {
                    let candidate = &mut candidate_meta[optional_idx as usize];
                    candidate.shadow_copy_words = candidate
                        .shadow_copy_words
                        .checked_add(u64::from(size))
                        .expect("candidate shadow copy words overflow");
                    candidate.live_call_indices.push(call_idx as u32);
                }
            }
        }

        let base_recursive_access_cost = facts
            .values()
            .filter(|fact| fact.must_stable)
            .try_fold(0u64, |acc, fact| {
                acc.checked_add(recursive_access_cost(cost_model, is_recursive, fact))
            })
            .expect("recursive access cost overflow");

        Self {
            stack,
            sorted_objects,
            sorted_calls,
            must_stable,
            must_stable_by_local,
            candidates: candidate_meta,
            base_shadow_words_by_call,
            base_shadow_copy_words,
            base_recursive_access_cost,
            frame_setup_cost: frame_setup_cost(cost_model),
            shadow_cost_per_word: shadow_cost_per_word(cost_model, is_recursive),
            next_shadow_base_id: stack.next_obj_id,
            is_recursive,
            cost_model,
            real_conflicts_by_local,
            shadow_conflicts_by_call,
        }
    }

    fn promoted_optional(&self, state: &PlacementState) -> BitSet<StackObjId> {
        self.candidates
            .iter()
            .zip(&state.promoted)
            .filter_map(|(candidate, &promoted)| promoted.then_some(candidate.obj_id))
            .collect()
    }
}

impl PlacementState {
    fn new(problem: &PlacementProblem<'_>) -> Self {
        Self {
            promoted: vec![false; problem.candidates.len()],
            promoted_count: 0,
            shadow_words_by_call: problem.base_shadow_words_by_call.clone(),
            shadow_copy_words: problem.base_shadow_copy_words,
            recursive_access_cost: problem.base_recursive_access_cost,
            scratch_real_locals: problem
                .sorted_objects
                .iter()
                .enumerate()
                .filter_map(|(local_idx, obj)| {
                    (!problem.must_stable_by_local[local_idx] && obj.size_words != 0)
                        .then_some(local_idx as u32)
                })
                .collect(),
            stable_real_locals: problem
                .sorted_objects
                .iter()
                .enumerate()
                .filter_map(|(local_idx, obj)| {
                    (problem.must_stable_by_local[local_idx] && obj.size_words != 0)
                        .then_some(local_idx as u32)
                })
                .collect(),
            nonzero_shadow_calls: problem
                .base_shadow_words_by_call
                .iter()
                .enumerate()
                .filter_map(|(call_idx, &shadow_words)| {
                    (shadow_words != 0).then_some(call_idx as u32)
                })
                .collect(),
        }
    }

    fn apply_add(&mut self, problem: &PlacementProblem<'_>, candidate_idx: usize) {
        assert!(
            !self.promoted[candidate_idx],
            "candidate {} already promoted",
            problem.candidates[candidate_idx].obj_id.as_u32()
        );
        self.promoted[candidate_idx] = true;
        self.promoted_count += 1;
        let candidate = &problem.candidates[candidate_idx];
        if candidate.size_words != 0 {
            remove_sorted_u32(&mut self.scratch_real_locals, candidate.local_idx.as_u32());
            insert_sorted_u32(&mut self.stable_real_locals, candidate.local_idx.as_u32());
        }
        self.shadow_copy_words = self
            .shadow_copy_words
            .checked_sub(candidate.shadow_copy_words)
            .expect("shadow copy words underflow");
        self.recursive_access_cost = self
            .recursive_access_cost
            .checked_add(candidate.recursive_access_cost)
            .expect("recursive access cost overflow");
        for &call_idx in &candidate.live_call_indices {
            let shadow_words = &mut self.shadow_words_by_call[call_idx as usize];
            let was_nonzero = *shadow_words != 0;
            *shadow_words = shadow_words
                .checked_sub(candidate.size_words)
                .expect("shadow words underflow");
            if was_nonzero && *shadow_words == 0 {
                remove_sorted_u32(&mut self.nonzero_shadow_calls, call_idx);
            }
        }
    }

    fn apply_remove(&mut self, problem: &PlacementProblem<'_>, candidate_idx: usize) {
        assert!(
            self.promoted[candidate_idx],
            "candidate {} is not promoted",
            problem.candidates[candidate_idx].obj_id.as_u32()
        );
        self.promoted[candidate_idx] = false;
        self.promoted_count = self
            .promoted_count
            .checked_sub(1)
            .expect("promoted count underflow");
        let candidate = &problem.candidates[candidate_idx];
        if candidate.size_words != 0 {
            remove_sorted_u32(&mut self.stable_real_locals, candidate.local_idx.as_u32());
            insert_sorted_u32(&mut self.scratch_real_locals, candidate.local_idx.as_u32());
        }
        self.shadow_copy_words = self
            .shadow_copy_words
            .checked_add(candidate.shadow_copy_words)
            .expect("shadow copy words overflow");
        self.recursive_access_cost = self
            .recursive_access_cost
            .checked_sub(candidate.recursive_access_cost)
            .expect("recursive access cost underflow");
        for &call_idx in &candidate.live_call_indices {
            let shadow_words = &mut self.shadow_words_by_call[call_idx as usize];
            let was_nonzero = *shadow_words != 0;
            *shadow_words = shadow_words
                .checked_add(candidate.size_words)
                .expect("shadow words overflow");
            if !was_nonzero && *shadow_words != 0 {
                insert_sorted_u32(&mut self.nonzero_shadow_calls, call_idx);
            }
        }
    }

    fn apply_swap(&mut self, problem: &PlacementProblem<'_>, add_idx: usize, remove_idx: usize) {
        assert_ne!(add_idx, remove_idx, "swap requires distinct candidates");
        self.apply_remove(problem, remove_idx);
        self.apply_add(problem, add_idx);
    }
}

impl PlacementLowerBoundState {
    fn new(problem: &PlacementProblem<'_>) -> Self {
        let _ = problem;
        Self
    }

    fn apply_add(&mut self, problem: &PlacementProblem<'_>, candidate_idx: usize) {
        let _ = (problem, candidate_idx);
    }

    fn apply_remove(&mut self, problem: &PlacementProblem<'_>, candidate_idx: usize) {
        let _ = (problem, candidate_idx);
    }

    fn apply_swap(&mut self, problem: &PlacementProblem<'_>, add_idx: usize, remove_idx: usize) {
        let _ = (problem, add_idx, remove_idx);
    }
}

pub(crate) fn compute_program_memory_plan(
    module: &Module,
    funcs: &[FuncRef],
    analyses: &FxHashMap<FuncRef, FuncAnalysis>,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
    isa: &Evm,
    cost_model: &ArenaCostModel,
) -> ProgramMemoryPlan {
    let funcs_set: FxHashSet<FuncRef> = funcs.iter().copied().collect();

    for &func in funcs {
        module.func_store.view(func, |function| {
            for block in function.layout.iter_block() {
                for inst in function.layout.iter_inst(block) {
                    let Some(call) = function.dfg.call_info(inst) else {
                        continue;
                    };
                    let callee = call.callee();
                    assert!(
                        funcs_set.contains(&callee),
                        "missing memory plan for callee {} (called from {})",
                        callee.as_u32(),
                        func.as_u32()
                    );
                }
            }
        });
    }

    let call_graph = CallGraph::build_graph_subset(module, &funcs_set);
    let scc = SccBuilder::new().compute_scc(&call_graph);
    let topo = topo_sort_sccs(&funcs_set, &call_graph, &scc);
    let scc_edges = build_scc_edges(&funcs_set, &call_graph, &scc, &topo);
    let alloc_ctx = StaticArenaAllocCtx::new(&module.ctx, isa, ptr_escape);

    let mut stack_results: Vec<_> = funcs
        .par_iter()
        .copied()
        .map(|func| {
            let analysis = analyses.get(&func).expect("missing FuncAnalysis");
            let stack = module.func_store.view(func, |function| {
                alloc_ctx.compute_func_stack_objects(func, function, analysis)
            });
            (func, stack)
        })
        .collect();
    stack_results.sort_unstable_by_key(|(func, _)| func.as_u32());

    let mut stacks: FxHashMap<FuncRef, FuncStackObjects> = FxHashMap::default();
    for (func, stack) in stack_results {
        stacks.insert(func, stack);
    }

    let mut placement_results: Vec<_> = funcs
        .par_iter()
        .copied()
        .map(|func| {
            let stack = stacks
                .get(&func)
                .unwrap_or_else(|| panic!("missing object facts for func {}", func.as_u32()));
            let scc_ref = scc.scc_ref(func);
            let is_recursive = scc.scc_info(scc_ref).is_cycle;
            let facts = build_planner_facts(stack, &scc, scc_ref, is_recursive);
            (
                func,
                solve_func_placement(stack, &facts, is_recursive, cost_model),
            )
        })
        .collect();
    placement_results.sort_unstable_by_key(|(func, _)| func.as_u32());

    let mut placements: FxHashMap<FuncRef, FuncPlacementEval> = FxHashMap::default();
    for (func, placement) in placement_results {
        placements.insert(func, placement);
    }

    let scratch_peak_words = placements
        .values()
        .map(|placement| placement.scratch_words)
        .max()
        .unwrap_or(0);

    let mut scc_weights: FxHashMap<SccRef, u32> = FxHashMap::default();
    for &scc_ref in &topo {
        let mut weight = 0;
        if !scc.scc_info(scc_ref).is_cycle {
            for &func in scc
                .scc_info(scc_ref)
                .components
                .iter()
                .filter(|func| funcs_set.contains(func))
            {
                weight = weight.max(placements[&func].stable_words);
            }
        }
        scc_weights.insert(scc_ref, weight);
    }

    let mut scc_prefix: FxHashMap<SccRef, u32> = FxHashMap::default();
    for &scc_ref in &topo {
        scc_prefix.entry(scc_ref).or_insert(0);
    }
    for &scc_ref in &topo {
        let carry = scc_prefix[&scc_ref]
            .checked_add(scc_weights[&scc_ref])
            .expect("static chain prefix overflow");
        if let Some(callees) = scc_edges.get(&scc_ref) {
            for &callee_scc in callees {
                scc_prefix
                    .entry(callee_scc)
                    .and_modify(|prefix| *prefix = (*prefix).max(carry))
                    .or_insert(carry);
            }
        }
    }

    let static_chain_peak_words = topo
        .iter()
        .map(|scc_ref| {
            scc_prefix[scc_ref]
                .checked_add(scc_weights[scc_ref])
                .expect("static chain peak overflow")
        })
        .max()
        .unwrap_or(0);

    let global_dyn_base = abs_addr_for_word(
        scratch_peak_words
            .checked_add(static_chain_peak_words)
            .expect("global dynamic base word overflow"),
    );
    let global_dyn_base_words = scratch_peak_words
        .checked_add(static_chain_peak_words)
        .expect("global dynamic base word overflow");

    let mut scc_plans: FxHashMap<SccRef, SccMemPlan> = FxHashMap::default();
    for &scc_ref in &topo {
        scc_plans.insert(
            scc_ref,
            SccMemPlan {
                is_recursive: scc.scc_info(scc_ref).is_cycle,
                static_chain_prefix_words: scc_prefix[&scc_ref],
            },
        );
    }

    let mut funcs_plan: FxHashMap<FuncRef, FuncMemPlan> = FxHashMap::default();
    for &func in funcs {
        let stack = stacks
            .get(&func)
            .unwrap_or_else(|| panic!("missing object facts for func {}", func.as_u32()));
        let placement = placements
            .remove(&func)
            .unwrap_or_else(|| panic!("missing placement for func {}", func.as_u32()));
        let scc_ref = scc.scc_ref(func);
        let scc_plan = scc_plans
            .get(&scc_ref)
            .unwrap_or_else(|| panic!("missing SCC plan for scc {}", scc_ref.as_u32()));
        let stable_base_word = scratch_peak_words
            .checked_add(scc_plan.static_chain_prefix_words)
            .expect("stable base word overflow");
        let stable_mode = if scc_plan.is_recursive {
            StableMode::DynamicFrame
        } else if placement.stable_words != 0 {
            StableMode::StaticAbs {
                base_word: stable_base_word,
            }
        } else {
            StableMode::None
        };
        let entry_abs_words = if scc_plan.is_recursive {
            global_dyn_base_words
        } else {
            stable_base_word
        };

        let mut obj_loc: FxHashMap<StackObjId, ObjLoc> = FxHashMap::default();
        for (&obj, &word) in &placement.scratch_offsets {
            obj_loc.insert(obj, ObjLoc::ScratchAbs(word));
        }
        for (&obj, &word) in &placement.stable_offsets {
            let loc = match stable_mode {
                StableMode::None => panic!("stable offsets present without stable mode"),
                StableMode::StaticAbs { .. } => ObjLoc::StableAbs(word),
                StableMode::DynamicFrame => ObjLoc::StableFrame(word),
            };
            obj_loc.insert(obj, loc);
        }

        let mut alloca_loc: FxHashMap<InstId, ObjLoc> = FxHashMap::default();
        for (inst, id) in &stack.alloca_ids {
            let loc = obj_loc.get(id).copied().unwrap_or_else(|| {
                panic!(
                    "missing object location for alloca inst {} in func {}",
                    inst.as_u32(),
                    func.as_u32()
                )
            });
            alloca_loc.insert(*inst, loc);
        }

        funcs_plan.insert(
            func,
            FuncMemPlan {
                scratch_words: placement.scratch_words,
                stable_words: placement.stable_words,
                stable_mode,
                entry_abs_words,
                obj_loc,
                alloca_loc,
                spill_obj: stack.spill_obj.clone(),
                call_preserve: placement.call_preserve,
                malloc_future_abs_words: FxHashMap::default(),
                transient_mallocs: FxHashSet::default(),
                malloc_escape_kinds: FxHashMap::default(),
                return_escape_caller_abs_words: 0,
            },
        );
    }

    let plan = ProgramMemoryPlan {
        scratch_peak_words,
        static_chain_peak_words,
        global_dyn_base,
        funcs: funcs_plan,
        sccs: scc_plans,
    };

    #[cfg(debug_assertions)]
    verify_program_memory_plan(module, funcs, analyses, ptr_escape, isa, &scc, &plan);

    plan
}

pub(crate) fn compute_abs_clobber_words(
    module: &Module,
    funcs: &[FuncRef],
    plan: &ProgramMemoryPlan,
) -> FxHashMap<FuncRef, u32> {
    let funcs_set: FxHashSet<FuncRef> = funcs.iter().copied().collect();
    let mut out: FxHashMap<FuncRef, u32> = FxHashMap::default();
    for &func in funcs {
        let local = plan
            .funcs
            .get(&func)
            .map(FuncMemPlan::abs_words_end)
            .unwrap_or(0);
        out.insert(func, local);
    }

    let mut changed = true;
    while changed {
        changed = false;
        for &func in funcs {
            let mut next = out.get(&func).copied().unwrap_or(0);
            module.func_store.view(func, |function| {
                for block in function.layout.iter_block() {
                    for inst in function.layout.iter_inst(block) {
                        let Some(call) = function.dfg.call_info(inst) else {
                            continue;
                        };
                        let callee = call.callee();
                        if funcs_set.contains(&callee) {
                            next = next.max(out.get(&callee).copied().unwrap_or(0));
                        }
                    }
                }
            });

            let cur = out.get(&func).copied().unwrap_or(0);
            if next > cur {
                out.insert(func, next);
                changed = true;
            }
        }
    }

    out
}

fn build_planner_facts(
    stack: &FuncStackObjects,
    scc: &CallGraphSccs,
    scc_ref: SccRef,
    is_recursive_scc: bool,
) -> FxHashMap<StackObjId, ObjFacts> {
    let mut facts = stack.obj_facts.clone();
    for call in &stack.call_sites {
        let is_recursive_call = is_recursive_scc && scc.scc_ref(call.callee) == scc_ref;
        if !is_recursive_call {
            continue;
        }
        for &obj in &call.live_across_objs {
            let fact = facts
                .get_mut(&obj)
                .unwrap_or_else(|| panic!("missing object facts for obj {}", obj.as_u32()));
            fact.live_across_recursive_call = true;
        }
        for &obj in &call.callee_visible_objs {
            let fact = facts
                .get_mut(&obj)
                .unwrap_or_else(|| panic!("missing object facts for obj {}", obj.as_u32()));
            fact.live_across_recursive_call = true;
            fact.must_stable = true;
            fact.stable_reason = super::static_arena_alloc::StableReason::RecursiveVisibility;
        }
    }
    facts
}

fn solve_func_placement(
    stack: &FuncStackObjects,
    facts: &FxHashMap<StackObjId, ObjFacts>,
    is_recursive: bool,
    cost_model: &ArenaCostModel,
) -> FuncPlacementEval {
    let problem = PlacementProblem::new(stack, facts, is_recursive, cost_model);
    let mut state = PlacementState::new(&problem);
    let mut lb_state = PlacementLowerBoundState::new(&problem);
    let mut workspace = FuncPlacementWorkspace {
        scratch_pack: Vec::with_capacity(problem.sorted_objects.len()),
        shadow_objs: Vec::with_capacity(problem.sorted_calls.len()),
        stable_items: Vec::with_capacity(
            problem
                .sorted_objects
                .len()
                .saturating_add(problem.sorted_calls.len()),
        ),
        stable_conflicts: Vec::with_capacity(
            problem
                .sorted_objects
                .len()
                .saturating_add(problem.sorted_calls.len()),
        ),
    };
    let mut score_workspace = FuncPlacementScoreWorkspace::default();
    let mut search_work = SearchWorkBuffers::default();
    let mut best_score =
        evaluate_func_placement_score(&problem, &state, PlacementMove::None, &mut score_workspace);
    let mut iteration = 0usize;

    loop {
        iteration += 1;
        debug_assert!(
            iteration <= 1_000_000,
            "placement local search did not converge"
        );

        if let Some(best_move) = find_best_exact_one_flip_move(
            &problem,
            &state,
            &mut lb_state,
            best_score,
            &mut score_workspace,
            &mut search_work,
        ) {
            apply_placement_move(&problem, &mut state, &mut lb_state, best_move.mv);
            best_score = best_move.exact;
            continue;
        }

        if let Some(best_move) = find_best_exact_swap_move(
            &problem,
            &state,
            &mut lb_state,
            best_score,
            &mut score_workspace,
            &mut search_work,
        ) {
            apply_placement_move(&problem, &mut state, &mut lb_state, best_move.mv);
            best_score = best_move.exact;
            continue;
        }

        break;
    }

    let promoted_optional = problem.promoted_optional(&state);
    evaluate_func_placement(&problem, &promoted_optional, &state, &mut workspace)
}

fn apply_placement_move(
    problem: &PlacementProblem<'_>,
    state: &mut PlacementState,
    lb_state: &mut PlacementLowerBoundState,
    mv: PlacementMove,
) {
    match mv {
        PlacementMove::None => {}
        PlacementMove::Add(candidate_idx) => {
            state.apply_add(problem, candidate_idx);
            lb_state.apply_add(problem, candidate_idx);
        }
        PlacementMove::Remove(candidate_idx) => {
            state.apply_remove(problem, candidate_idx);
            lb_state.apply_remove(problem, candidate_idx);
        }
        PlacementMove::Swap {
            add_idx,
            remove_idx,
        } => {
            state.apply_swap(problem, add_idx, remove_idx);
            lb_state.apply_swap(problem, add_idx, remove_idx);
        }
    }
}

fn evaluate_func_placement(
    problem: &PlacementProblem<'_>,
    promoted_optional: &BitSet<StackObjId>,
    state: &PlacementState,
    workspace: &mut FuncPlacementWorkspace,
) -> FuncPlacementEval {
    build_scratch_pack(
        &mut workspace.scratch_pack,
        &problem.sorted_objects,
        &problem.must_stable,
        promoted_optional,
    );
    let (scratch_offsets, scratch_words) = pack_objects_presorted(&workspace.scratch_pack);

    workspace.shadow_objs.clear();
    let mut call_preserve =
        FxHashMap::with_capacity_and_hasher(problem.sorted_calls.len(), Default::default());
    let mut next_obj_id = problem.next_shadow_base_id;
    for (call_idx, &call) in problem.sorted_calls.iter().enumerate() {
        let Some((shadow_obj, plan)) = build_shadow_preserve_for_call(
            problem.stack,
            call,
            &problem.must_stable,
            promoted_optional,
            &scratch_offsets,
            next_obj_id,
        ) else {
            continue;
        };
        next_obj_id = next_obj_id
            .checked_add(1)
            .expect("shadow object id overflow");
        workspace.shadow_objs.push(ShadowPackObj {
            call_idx: call_idx as u32,
            obj: shadow_obj,
        });
        call_preserve.insert(call.inst, plan);
    }

    build_stable_pack(
        &mut workspace.stable_items,
        &mut workspace.stable_conflicts,
        &workspace.shadow_objs,
        StablePackCtx {
            sorted_objects: &problem.sorted_objects,
            must_stable: &problem.must_stable,
            real_conflicts_by_local: &problem.real_conflicts_by_local,
            shadow_conflicts_by_call: &problem.shadow_conflicts_by_call,
        },
        promoted_optional,
    );
    let stable_pack = pack_exact_with_offsets(&workspace.stable_items, &workspace.stable_conflicts);
    let stable_offsets = stable_pack.offsets;
    let stable_words = stable_pack.max_used;

    let shadow_copy_words = shadow_copy_words(&call_preserve);
    debug_assert_eq!(shadow_copy_words, state.shadow_copy_words);
    let cost = placement_cost(
        problem,
        state.recursive_access_cost,
        shadow_copy_words,
        scratch_words,
        stable_words,
    );
    debug_assert_eq!(
        FuncPlacementScore {
            scratch_words,
            stable_words,
            cost,
        },
        evaluate_func_placement_score(
            problem,
            state,
            PlacementMove::None,
            &mut FuncPlacementScoreWorkspace::default(),
        )
    );

    FuncPlacementEval {
        scratch_offsets,
        scratch_words,
        stable_offsets,
        stable_words,
        call_preserve,
    }
}

fn evaluate_func_placement_score(
    problem: &PlacementProblem<'_>,
    state: &PlacementState,
    mv: PlacementMove,
    workspace: &mut FuncPlacementScoreWorkspace,
) -> FuncPlacementScore {
    let (shadow_copy_words, recursive_access_cost) = additive_terms_with_move(problem, state, mv);
    let scratch_words = scratch_peak_with_move(problem, state, mv, workspace);
    let stable_words = stable_peak_with_move(problem, state, mv, workspace);
    score_from_words(
        problem,
        recursive_access_cost,
        shadow_copy_words,
        scratch_words,
        stable_words,
    )
}

fn score_from_words(
    problem: &PlacementProblem<'_>,
    recursive_access_cost: u64,
    shadow_copy_words: u64,
    scratch_words: u32,
    stable_words: u32,
) -> FuncPlacementScore {
    FuncPlacementScore {
        scratch_words,
        stable_words,
        cost: placement_cost(
            problem,
            recursive_access_cost,
            shadow_copy_words,
            scratch_words,
            stable_words,
        ),
    }
}

fn scratch_peak_with_move(
    problem: &PlacementProblem<'_>,
    state: &PlacementState,
    mv: PlacementMove,
    workspace: &mut FuncPlacementScoreWorkspace,
) -> u32 {
    let _ = workspace;
    let (insert_idx, skip_idx) = scratch_local_indices_for_move(problem, mv);
    let items: Vec<_> = TrialLocalIter::new(&state.scratch_real_locals, insert_idx, skip_idx)
        .map(|local_idx| {
            let obj = problem.sorted_objects[local_idx as usize];
            ExactPackItem {
                id: obj.id,
                idx: LocalObjIdx::new(local_idx as usize),
                size_words: obj.size_words,
                min_offset_words: 0,
            }
        })
        .collect();
    pack_exact_peak(&items, &problem.real_conflicts_by_local)
}

fn stable_peak_with_move(
    problem: &PlacementProblem<'_>,
    state: &PlacementState,
    mv: PlacementMove,
    workspace: &mut FuncPlacementScoreWorkspace,
) -> u32 {
    let promoted_optional = promoted_optional_with_move(problem, state, mv);
    let shadow_objs = shadow_pack_objs_for_move(problem, state, mv);
    build_stable_pack(
        &mut workspace.stable_items,
        &mut workspace.stable_conflicts,
        &shadow_objs,
        StablePackCtx {
            sorted_objects: &problem.sorted_objects,
            must_stable: &problem.must_stable,
            real_conflicts_by_local: &problem.real_conflicts_by_local,
            shadow_conflicts_by_call: &problem.shadow_conflicts_by_call,
        },
        &promoted_optional,
    );
    pack_exact_peak(&workspace.stable_items, &workspace.stable_conflicts)
}

fn promoted_optional_with_move(
    problem: &PlacementProblem<'_>,
    state: &PlacementState,
    mv: PlacementMove,
) -> BitSet<StackObjId> {
    let mut promoted = problem.promoted_optional(state);
    match mv {
        PlacementMove::None => {}
        PlacementMove::Add(candidate_idx) => {
            let _ = promoted.insert(problem.candidates[candidate_idx].obj_id);
        }
        PlacementMove::Remove(candidate_idx) => {
            promoted.remove(problem.candidates[candidate_idx].obj_id);
        }
        PlacementMove::Swap {
            add_idx,
            remove_idx,
        } => {
            promoted.remove(problem.candidates[remove_idx].obj_id);
            let _ = promoted.insert(problem.candidates[add_idx].obj_id);
        }
    }
    promoted
}

fn shadow_words_for_call_after_move(
    problem: &PlacementProblem<'_>,
    state: &PlacementState,
    mv: PlacementMove,
    call_idx: usize,
) -> u32 {
    let mut shadow_words = state.shadow_words_by_call[call_idx];
    let mut apply_candidate = |candidate_idx: usize, sign: i64| {
        let candidate = &problem.candidates[candidate_idx];
        if !candidate.live_call_indices.contains(&(call_idx as u32)) || candidate.size_words == 0 {
            return;
        }
        if sign.is_negative() {
            shadow_words = shadow_words
                .checked_sub(candidate.size_words)
                .expect("shadow words underflow");
        } else {
            shadow_words = shadow_words
                .checked_add(candidate.size_words)
                .expect("shadow words overflow");
        }
    };
    match mv {
        PlacementMove::None => {}
        PlacementMove::Add(candidate_idx) => apply_candidate(candidate_idx, -1),
        PlacementMove::Remove(candidate_idx) => apply_candidate(candidate_idx, 1),
        PlacementMove::Swap {
            add_idx,
            remove_idx,
        } => {
            apply_candidate(add_idx, -1);
            apply_candidate(remove_idx, 1);
        }
    }
    shadow_words
}

fn shadow_pack_objs_for_move(
    problem: &PlacementProblem<'_>,
    state: &PlacementState,
    mv: PlacementMove,
) -> Vec<ShadowPackObj> {
    let mut shadow_objs = Vec::new();
    for (call_idx, &call) in problem.sorted_calls.iter().enumerate() {
        let shadow_words = shadow_words_for_call_after_move(problem, state, mv, call_idx);
        if shadow_words == 0 {
            continue;
        }
        shadow_objs.push(ShadowPackObj {
            call_idx: call_idx as u32,
            obj: StackObj {
                id: StackObjId::new(
                    problem_shadow_order_id(problem.next_shadow_base_id, call_idx) as usize,
                ),
                kind: StackObjKind::Shadow(call.inst),
                size_words: shadow_words,
                region: LiveRegion::sort_only(call.call_rank),
                access_weight: 0,
                load_count: 0,
                store_count: 0,
            },
        });
    }
    shadow_objs
}

fn find_best_exact_one_flip_move(
    problem: &PlacementProblem<'_>,
    state: &PlacementState,
    lb_state: &mut PlacementLowerBoundState,
    current_score: FuncPlacementScore,
    exact_ws: &mut FuncPlacementScoreWorkspace,
    work: &mut SearchWorkBuffers,
) -> Option<ExactMoveEval> {
    let _ = lb_state;
    work.one_flip_exact.clear();
    for candidate_idx in 0..problem.candidates.len() {
        let mv = if state.promoted[candidate_idx] {
            PlacementMove::Remove(candidate_idx)
        } else {
            PlacementMove::Add(candidate_idx)
        };
        let exact = evaluate_func_placement_score(problem, state, mv, exact_ws);
        if is_better_score(exact, current_score) {
            work.one_flip_exact.push(ExactMoveEval { mv, exact });
        }
    }
    work.one_flip_exact.sort_unstable_by(|a, b| {
        cmp_func_placement_score(a.exact, b.exact)
            .then_with(|| {
                resulting_promoted_count(state, a.mv).cmp(&resulting_promoted_count(state, b.mv))
            })
            .then_with(|| cmp_move_tie_key(problem, a.mv, b.mv))
    });
    work.one_flip_exact.first().copied()
}

fn find_best_exact_swap_move(
    problem: &PlacementProblem<'_>,
    state: &PlacementState,
    lb_state: &mut PlacementLowerBoundState,
    current_score: FuncPlacementScore,
    exact_ws: &mut FuncPlacementScoreWorkspace,
    work: &mut SearchWorkBuffers,
) -> Option<ExactMoveEval> {
    let feasible_add_count = state.promoted.iter().filter(|&&promoted| !promoted).count();
    let feasible_remove_count = state.promoted_count;
    if feasible_add_count == 0 || feasible_remove_count == 0 {
        return None;
    }

    let _ = lb_state;
    work.swap_exact.clear();
    if feasible_add_count.saturating_mul(feasible_remove_count) <= SWAP_FULL_PAIR_LIMIT {
        for add_idx in 0..problem.candidates.len() {
            if state.promoted[add_idx] {
                continue;
            }
            for remove_idx in 0..problem.candidates.len() {
                if !state.promoted[remove_idx] {
                    continue;
                }
                let mv = PlacementMove::Swap {
                    add_idx,
                    remove_idx,
                };
                let exact = evaluate_func_placement_score(problem, state, mv, exact_ws);
                if is_better_score(exact, current_score) {
                    work.swap_exact.push(ExactMoveEval { mv, exact });
                }
            }
        }
    } else {
        collect_swap_shortlists(problem, state, work);
        for &add_idx in &work.add_shortlist {
            for &remove_idx in &work.remove_shortlist {
                let mv = PlacementMove::Swap {
                    add_idx,
                    remove_idx,
                };
                let exact = evaluate_func_placement_score(problem, state, mv, exact_ws);
                if is_better_score(exact, current_score) {
                    work.swap_exact.push(ExactMoveEval { mv, exact });
                }
            }
        }
    }

    work.swap_exact.sort_unstable_by(|a, b| {
        cmp_func_placement_score(a.exact, b.exact)
            .then_with(|| {
                resulting_promoted_count(state, a.mv).cmp(&resulting_promoted_count(state, b.mv))
            })
            .then_with(|| cmp_move_tie_key(problem, a.mv, b.mv))
    });
    work.swap_exact.first().copied()
}

fn collect_swap_shortlists(
    problem: &PlacementProblem<'_>,
    state: &PlacementState,
    work: &mut SearchWorkBuffers,
) {
    work.add_shortlist.clear();
    work.remove_shortlist.clear();
    collect_metric_shortlist(problem, state, false, work);
    collect_metric_shortlist(problem, state, true, work);

    work.add_shortlist
        .sort_unstable_by_key(|&candidate_idx| problem.candidates[candidate_idx].obj_id.as_u32());
    work.remove_shortlist
        .sort_unstable_by_key(|&candidate_idx| problem.candidates[candidate_idx].obj_id.as_u32());
}

fn collect_metric_shortlist(
    problem: &PlacementProblem<'_>,
    state: &PlacementState,
    promoted: bool,
    work: &mut SearchWorkBuffers,
) {
    for metric in 0..3 {
        let mut candidates: Vec<_> = problem
            .candidates
            .iter()
            .enumerate()
            .filter_map(|(candidate_idx, _)| {
                (state.promoted[candidate_idx] == promoted).then_some(candidate_idx)
            })
            .collect();
        candidates.sort_unstable_by(|&lhs, &rhs| {
            candidate_metric(problem, rhs, metric)
                .cmp(&candidate_metric(problem, lhs, metric))
                .then_with(|| {
                    problem.candidates[lhs]
                        .obj_id
                        .as_u32()
                        .cmp(&problem.candidates[rhs].obj_id.as_u32())
                })
        });
        for &candidate_idx in candidates.iter().take(SWAP_SHORTLIST_PER_METRIC) {
            if promoted {
                push_unique_candidate(&mut work.remove_shortlist, candidate_idx);
            } else {
                push_unique_candidate(&mut work.add_shortlist, candidate_idx);
            }
        }
    }
}

fn candidate_metric(problem: &PlacementProblem<'_>, candidate_idx: usize, metric: usize) -> u64 {
    let candidate = &problem.candidates[candidate_idx];
    match metric {
        0 => u64::from(candidate.size_words),
        1 => candidate.shadow_copy_words,
        2 => candidate.recursive_access_cost,
        _ => panic!("unknown candidate metric {metric}"),
    }
}

fn push_unique_candidate(shortlist: &mut Vec<usize>, candidate_idx: usize) {
    if !shortlist.contains(&candidate_idx) {
        shortlist.push(candidate_idx);
    }
}

fn build_shadow_preserve_for_call(
    stack: &FuncStackObjects,
    call: &CallSiteObjects,
    must_stable: &BitSet<StackObjId>,
    promoted_optional: &BitSet<StackObjId>,
    scratch_offsets: &FxHashMap<StackObjId, u32>,
    next_obj_id: u32,
) -> Option<(StackObj, CallPreservePlan)> {
    let mut ranges = SmallVec::<[(u32, u32); 8]>::new();
    for &obj in &call.live_across_objs {
        if is_stable_real(must_stable, promoted_optional, obj) {
            continue;
        }
        let Some(&size) = stack.obj_size_words.get(&obj) else {
            panic!("missing object size for obj {}", obj.as_u32());
        };
        if size == 0 {
            continue;
        }
        let start = *scratch_offsets.get(&obj).unwrap_or_else(|| {
            panic!(
                "missing scratch offset for obj {} at call {}",
                obj.as_u32(),
                call.inst.as_u32()
            )
        });
        ranges.push((start, size));
    }

    if ranges.is_empty() {
        return None;
    }

    ranges.sort_unstable_by_key(|(start, _)| *start);
    let mut shadow_words: u32 = 0;
    let mut runs: SmallVec<[SaveRun; 2]> = smallvec![];
    for (start, len) in ranges {
        if let Some(last) = runs.last_mut() {
            let last_end = last
                .scratch_src_word
                .checked_add(last.len_words)
                .expect("shadow run end overflow");
            if last_end == start {
                last.len_words = last
                    .len_words
                    .checked_add(len)
                    .expect("shadow run merge overflow");
                shadow_words = shadow_words
                    .checked_add(len)
                    .expect("shadow object size overflow");
                continue;
            }
        }
        runs.push(SaveRun {
            scratch_src_word: start,
            shadow_dst_word: shadow_words,
            len_words: len,
        });
        shadow_words = shadow_words
            .checked_add(len)
            .expect("shadow object size overflow");
    }
    if shadow_words == 0 {
        return None;
    }

    let shadow_obj = StackObj {
        id: StackObjId::new(next_obj_id as usize),
        kind: StackObjKind::Shadow(call.inst),
        size_words: shadow_words,
        region: LiveRegion::sort_only(call.call_rank),
        access_weight: 0,
        load_count: 0,
        store_count: 0,
    };
    let plan = CallPreservePlan {
        mode: PreserveMode::ShadowRuns {
            shadow_obj: shadow_obj.id,
            runs,
        },
        result_count: call.result_count,
    };
    Some((shadow_obj, plan))
}

fn build_scratch_pack(
    scratch_pack: &mut Vec<PackedObject>,
    sorted_objects: &[&StackObj],
    must_stable: &BitSet<StackObjId>,
    promoted_optional: &BitSet<StackObjId>,
) {
    scratch_pack.clear();
    for &obj in sorted_objects {
        if is_stable_real(must_stable, promoted_optional, obj.id) {
            continue;
        }
        scratch_pack.push(PackedObject {
            id: obj.id,
            size_words: obj.size_words,
            region: obj.region.clone(),
            min_offset_words: 0,
        });
    }
}

fn build_stable_pack(
    stable_items: &mut Vec<ExactPackItem<StableItemIdx>>,
    stable_conflicts: &mut Vec<BitSet<StableItemIdx>>,
    shadow_objs: &[ShadowPackObj],
    ctx: StablePackCtx<'_>,
    promoted_optional: &BitSet<StackObjId>,
) {
    #[derive(Clone, Copy)]
    enum StablePackMember {
        Real(LocalObjIdx),
        Shadow(u32),
    }

    stable_items.clear();
    stable_conflicts.clear();
    let mut members = Vec::new();
    for (local_idx, &obj) in ctx.sorted_objects.iter().enumerate() {
        if !is_stable_real(ctx.must_stable, promoted_optional, obj.id) || obj.size_words == 0 {
            continue;
        }
        members.push((
            obj.region.sort_key(obj.id),
            StablePackMember::Real(LocalObjIdx::new(local_idx)),
            obj.id,
            obj.size_words,
        ));
    }
    for shadow in shadow_objs {
        if shadow.obj.size_words == 0 {
            continue;
        }
        members.push((
            shadow.obj.region.sort_key(shadow.obj.id),
            StablePackMember::Shadow(shadow.call_idx),
            shadow.obj.id,
            shadow.obj.size_words,
        ));
    }
    members.sort_unstable_by_key(|(sort_key, _, _, _)| *sort_key);

    for (item_idx, (_sort_key, member, id, size_words)) in members.iter().enumerate() {
        stable_items.push(ExactPackItem {
            id: *id,
            idx: StableItemIdx::new(item_idx),
            size_words: *size_words,
            min_offset_words: 0,
        });
        stable_conflicts.push(BitSet::default());
        let _ = member;
    }

    for lhs_idx in 0..members.len() {
        for rhs_idx in lhs_idx + 1..members.len() {
            let conflicts = match (members[lhs_idx].1, members[rhs_idx].1) {
                (StablePackMember::Real(lhs), StablePackMember::Real(rhs)) => {
                    ctx.real_conflicts_by_local[lhs.index()].contains(rhs)
                }
                (StablePackMember::Real(local), StablePackMember::Shadow(call_idx))
                | (StablePackMember::Shadow(call_idx), StablePackMember::Real(local)) => {
                    ctx.shadow_conflicts_by_call[call_idx as usize].contains(local)
                }
                (StablePackMember::Shadow(_), StablePackMember::Shadow(_)) => false,
            };
            if !conflicts {
                continue;
            }
            let lhs = StableItemIdx::new(lhs_idx);
            let rhs = StableItemIdx::new(rhs_idx);
            let _ = stable_conflicts[lhs.index()].insert(rhs);
            let _ = stable_conflicts[rhs.index()].insert(lhs);
        }
    }
}

fn cmp_func_placement_score(a: FuncPlacementScore, b: FuncPlacementScore) -> Ordering {
    a.cost
        .cmp(&b.cost)
        .then_with(|| a.stable_words.cmp(&b.stable_words))
        .then_with(|| a.scratch_words.cmp(&b.scratch_words))
}

fn resulting_promoted_count(state: &PlacementState, mv: PlacementMove) -> usize {
    match mv {
        PlacementMove::None => state.promoted_count,
        PlacementMove::Add(_) => state.promoted_count + 1,
        PlacementMove::Remove(_) => state
            .promoted_count
            .checked_sub(1)
            .expect("promoted count underflow"),
        PlacementMove::Swap { .. } => state.promoted_count,
    }
}

fn move_tie_key(problem: &PlacementProblem<'_>, mv: PlacementMove) -> (u8, u32, u32) {
    match mv {
        PlacementMove::Add(candidate_idx) => {
            (0, problem.candidates[candidate_idx].obj_id.as_u32(), 0)
        }
        PlacementMove::Remove(candidate_idx) => {
            (1, problem.candidates[candidate_idx].obj_id.as_u32(), 0)
        }
        PlacementMove::Swap {
            add_idx,
            remove_idx,
        } => (
            2,
            problem.candidates[add_idx].obj_id.as_u32(),
            problem.candidates[remove_idx].obj_id.as_u32(),
        ),
        PlacementMove::None => (3, u32::MAX, u32::MAX),
    }
}

fn cmp_move_tie_key(
    problem: &PlacementProblem<'_>,
    a: PlacementMove,
    b: PlacementMove,
) -> Ordering {
    move_tie_key(problem, a).cmp(&move_tie_key(problem, b))
}

fn placement_cost(
    problem: &PlacementProblem<'_>,
    recursive_access_cost: u64,
    shadow_copy_words: u64,
    scratch_words: u32,
    stable_words: u32,
) -> u64 {
    let mut cost = evaluate_memory_cost(problem.cost_model, scratch_words, stable_words);
    if problem.is_recursive && stable_words != 0 {
        cost = cost
            .checked_add(problem.frame_setup_cost)
            .expect("frame setup total cost overflow");
    }
    cost = cost
        .checked_add(recursive_access_cost)
        .expect("frame access total cost overflow");
    cost.checked_add(
        problem
            .shadow_cost_per_word
            .checked_mul(shadow_copy_words)
            .expect("shadow copy total cost overflow"),
    )
    .expect("shadow copy total cost overflow")
}

fn shadow_copy_words(call_preserve: &FxHashMap<InstId, CallPreservePlan>) -> u64 {
    call_preserve
        .values()
        .map(|plan| match &plan.mode {
            PreserveMode::ShadowRuns { runs, .. } => {
                runs.iter().map(|run| u64::from(run.len_words)).sum()
            }
            PreserveMode::None | PreserveMode::TinyStackLift { .. } => 0,
        })
        .sum()
}

struct TrialLocalIter<'a> {
    base: &'a [u32],
    pos: usize,
    insert_idx: Option<u32>,
    skip_idx: Option<u32>,
}

impl<'a> TrialLocalIter<'a> {
    fn new(base: &'a [u32], insert_idx: Option<u32>, skip_idx: Option<u32>) -> Self {
        Self {
            base,
            pos: 0,
            insert_idx,
            skip_idx,
        }
    }
}

impl Iterator for TrialLocalIter<'_> {
    type Item = u32;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let base_idx = self.base.get(self.pos).copied();
            if let Some(insert_idx) = self.insert_idx
                && base_idx.is_none_or(|base_idx| insert_idx < base_idx)
            {
                self.insert_idx = None;
                return Some(insert_idx);
            }

            let Some(base_idx) = base_idx else {
                return self.insert_idx.take();
            };
            self.pos += 1;
            if self.skip_idx == Some(base_idx) {
                continue;
            }
            return Some(base_idx);
        }
    }
}

fn scratch_local_indices_for_move(
    problem: &PlacementProblem<'_>,
    mv: PlacementMove,
) -> (Option<u32>, Option<u32>) {
    match mv {
        PlacementMove::None => (None, None),
        PlacementMove::Add(candidate_idx) => (
            None,
            Some(problem.candidates[candidate_idx].local_idx.as_u32()),
        ),
        PlacementMove::Remove(candidate_idx) => (
            Some(problem.candidates[candidate_idx].local_idx.as_u32()),
            None,
        ),
        PlacementMove::Swap {
            add_idx,
            remove_idx,
        } => (
            Some(problem.candidates[remove_idx].local_idx.as_u32()),
            Some(problem.candidates[add_idx].local_idx.as_u32()),
        ),
    }
}

fn additive_terms_with_move(
    problem: &PlacementProblem<'_>,
    state: &PlacementState,
    mv: PlacementMove,
) -> (u64, u64) {
    match mv {
        PlacementMove::None => (state.shadow_copy_words, state.recursive_access_cost),
        PlacementMove::Add(candidate_idx) => {
            let candidate = &problem.candidates[candidate_idx];
            (
                state
                    .shadow_copy_words
                    .checked_sub(candidate.shadow_copy_words)
                    .expect("shadow copy words underflow"),
                state
                    .recursive_access_cost
                    .checked_add(candidate.recursive_access_cost)
                    .expect("recursive access cost overflow"),
            )
        }
        PlacementMove::Remove(candidate_idx) => {
            let candidate = &problem.candidates[candidate_idx];
            (
                state
                    .shadow_copy_words
                    .checked_add(candidate.shadow_copy_words)
                    .expect("shadow copy words overflow"),
                state
                    .recursive_access_cost
                    .checked_sub(candidate.recursive_access_cost)
                    .expect("recursive access cost underflow"),
            )
        }
        PlacementMove::Swap {
            add_idx,
            remove_idx,
        } => {
            let add_candidate = &problem.candidates[add_idx];
            let remove_candidate = &problem.candidates[remove_idx];
            (
                state
                    .shadow_copy_words
                    .checked_sub(add_candidate.shadow_copy_words)
                    .expect("shadow copy words underflow")
                    .checked_add(remove_candidate.shadow_copy_words)
                    .expect("shadow copy words overflow"),
                state
                    .recursive_access_cost
                    .checked_add(add_candidate.recursive_access_cost)
                    .expect("recursive access cost overflow")
                    .checked_sub(remove_candidate.recursive_access_cost)
                    .expect("recursive access cost underflow"),
            )
        }
    }
}

fn insert_sorted_u32(values: &mut Vec<u32>, value: u32) {
    match values.binary_search(&value) {
        Ok(_) => {}
        Err(index) => values.insert(index, value),
    }
}

fn remove_sorted_u32(values: &mut Vec<u32>, value: u32) {
    let index = values
        .binary_search(&value)
        .unwrap_or_else(|_| panic!("missing sorted value {value}"));
    let _ = values.remove(index);
}

fn recursive_access_cost(cost_model: &ArenaCostModel, is_recursive: bool, fact: &ObjFacts) -> u64 {
    if !is_recursive {
        return 0;
    }
    cost_model
        .w_stack
        .checked_mul(fact.access_weight.saturating_mul(4))
        .expect("frame access cost overflow")
}

fn frame_setup_cost(cost_model: &ArenaCostModel) -> u64 {
    cost_model
        .w_save
        .checked_mul(32)
        .expect("frame setup cost overflow")
        .checked_add(
            cost_model
                .w_code
                .checked_mul(16)
                .expect("frame setup code cost overflow"),
        )
        .expect("frame setup total cost overflow")
}

fn shadow_cost_per_word(cost_model: &ArenaCostModel, is_recursive: bool) -> u64 {
    let copy_units = if is_recursive { 16 } else { 12 };
    cost_model
        .w_save
        .checked_mul(copy_units)
        .expect("shadow copy gas cost overflow")
        .checked_add(
            cost_model
                .w_code
                .checked_mul(copy_units)
                .expect("shadow copy code cost overflow"),
        )
        .expect("shadow copy total cost overflow")
}

fn is_stable_real(
    must_stable: &BitSet<StackObjId>,
    promoted_optional: &BitSet<StackObjId>,
    obj: StackObjId,
) -> bool {
    must_stable.contains(obj) || promoted_optional.contains(obj)
}

fn is_better_score(candidate: FuncPlacementScore, current: FuncPlacementScore) -> bool {
    cmp_func_placement_score(candidate, current) == Ordering::Less
}

fn evaluate_memory_cost(cost_model: &ArenaCostModel, scratch_words: u32, stable_words: u32) -> u64 {
    let words = scratch_words
        .checked_add(stable_words)
        .expect("memory words overflow");
    let total_words = (STATIC_BASE / WORD_BYTES)
        .checked_add(words)
        .expect("memory expansion words overflow");
    cost_model
        .w_mem
        .checked_mul(mem_expansion_gas(total_words))
        .expect("memory cost overflow")
}

fn mem_expansion_gas(words: u32) -> u64 {
    let words = u128::from(words);
    let lin = words.saturating_mul(3);
    let quad = words.saturating_mul(words) / 512;
    u64::try_from(lin.saturating_add(quad)).expect("memory expansion gas overflow")
}

fn abs_addr_for_word(word: u32) -> u32 {
    STATIC_BASE
        .checked_add(
            word.checked_mul(WORD_BYTES)
                .expect("absolute address overflow"),
        )
        .expect("absolute address overflow")
}

fn problem_shadow_order_id(next_shadow_base_id: u32, call_idx: usize) -> u32 {
    next_shadow_base_id
        .checked_add(call_idx as u32)
        .expect("shadow order id overflow")
}

#[cfg(debug_assertions)]
fn verify_program_memory_plan(
    module: &Module,
    funcs: &[FuncRef],
    analyses: &FxHashMap<FuncRef, FuncAnalysis>,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
    isa: &Evm,
    scc: &CallGraphSccs,
    plan: &ProgramMemoryPlan,
) {
    let alloc_ctx = StaticArenaAllocCtx::new(&module.ctx, isa, ptr_escape);

    for &func in funcs {
        let Some(func_plan) = plan.funcs.get(&func) else {
            continue;
        };
        let analysis = analyses.get(&func).expect("missing analysis");
        let scc_ref = scc.scc_ref(func);
        let is_recursive = scc.scc_info(scc_ref).is_cycle;

        module.func_store.view(func, |function| {
            let stack = alloc_ctx.compute_func_stack_objects(func, function, analysis);

            let mut scratch_offsets: FxHashMap<StackObjId, u32> = FxHashMap::default();
            let mut stable_offsets: FxHashMap<StackObjId, u32> = FxHashMap::default();
            for (obj, loc) in &func_plan.obj_loc {
                match *loc {
                    ObjLoc::ScratchAbs(word) => {
                        scratch_offsets.insert(*obj, word);
                    }
                    ObjLoc::StableAbs(word) | ObjLoc::StableFrame(word) => {
                        stable_offsets.insert(*obj, word);
                    }
                    ObjLoc::StackPinned(_) => panic!("stack-pinned objects are not implemented"),
                }
            }

            let scratch_subset = subset_objects(&stack.objects, scratch_offsets.keys().copied());
            verify_subset_packing(
                func,
                &scratch_subset,
                &scratch_offsets,
                func_plan.scratch_words,
            );

            let mut stable_subset = subset_objects(&stack.objects, stable_offsets.keys().copied());
            for call in func_plan.call_preserve.values() {
                let PreserveMode::ShadowRuns { shadow_obj, runs } = &call.mode else {
                    continue;
                };
                let size_words: u32 = runs.iter().map(|run| run.len_words).sum();
                stable_subset.push(StackObj {
                    id: *shadow_obj,
                    kind: StackObjKind::Shadow(InstId::from_u32(0)),
                    size_words,
                    region: LiveRegion::sort_only(0),
                    access_weight: 0,
                    load_count: 0,
                    store_count: 0,
                });
            }
            let _ = &stable_subset;

            if !is_recursive {
                for fact in stack.obj_facts.values() {
                    if fact.must_stable {
                        let loc = func_plan.obj_loc.get(&fact.id).copied().unwrap_or_else(|| {
                            panic!("missing object location for obj {}", fact.id.as_u32())
                        });
                        assert!(
                            !matches!(loc, ObjLoc::ScratchAbs(_)),
                            "callee-visible object {} in func {} was placed in scratch",
                            fact.id.as_u32(),
                            func.as_u32()
                        );
                    }
                }
            }

            for call in &stack.call_sites {
                let saved = func_plan
                    .call_preserve
                    .get(&call.inst)
                    .map(|plan| &plan.mode);
                for &obj in &call.callee_visible_objs {
                    let loc = func_plan.obj_loc.get(&obj).copied().unwrap_or_else(|| {
                        panic!("missing object location for obj {}", obj.as_u32())
                    });
                    assert!(
                        !matches!(loc, ObjLoc::ScratchAbs(_)),
                        "callee-visible object {} in func {} at call {} was placed in scratch",
                        obj.as_u32(),
                        func.as_u32(),
                        call.inst.as_u32()
                    );
                }
                for &obj in &call.live_across_objs {
                    let loc = func_plan.obj_loc.get(&obj).copied().unwrap_or_else(|| {
                        panic!("missing object location for obj {}", obj.as_u32())
                    });
                    if matches!(loc, ObjLoc::ScratchAbs(_)) {
                        let Some(PreserveMode::ShadowRuns { runs, .. }) = saved else {
                            panic!(
                                "scratch object {} in func {} at call {} is not preserved",
                                obj.as_u32(),
                                func.as_u32(),
                                call.inst.as_u32()
                            );
                        };
                        let Some(src_word) =
                            func_plan.obj_loc.get(&obj).and_then(|loc| match loc {
                                ObjLoc::ScratchAbs(word) => Some(*word),
                                ObjLoc::StableAbs(_)
                                | ObjLoc::StableFrame(_)
                                | ObjLoc::StackPinned(_) => None,
                            })
                        else {
                            continue;
                        };
                        let size = stack.obj_size_words[&obj];
                        for word in src_word..src_word + size {
                            assert!(
                                runs.iter().any(|run| {
                                    let end = run
                                        .scratch_src_word
                                        .checked_add(run.len_words)
                                        .expect("shadow run end overflow");
                                    (run.scratch_src_word..end).contains(&word)
                                }),
                                "scratch object {} in func {} at call {} missing preserved word {}",
                                obj.as_u32(),
                                func.as_u32(),
                                call.inst.as_u32(),
                                word
                            );
                        }
                    }
                }
            }

            if !stable_subset.is_empty() {
                verify_subset_packing(
                    func,
                    &stable_subset,
                    &stable_offsets,
                    func_plan.stable_words,
                );
            }
        });
    }
}

#[cfg(debug_assertions)]
fn subset_objects(
    objects: &[StackObj],
    ids: impl IntoIterator<Item = StackObjId>,
) -> Vec<StackObj> {
    let wanted: FxHashSet<StackObjId> = ids.into_iter().collect();
    objects
        .iter()
        .filter(|obj| wanted.contains(&obj.id))
        .cloned()
        .collect()
}

#[cfg(debug_assertions)]
fn verify_subset_packing(
    func_ref: FuncRef,
    objects: &[StackObj],
    obj_offset_words: &FxHashMap<StackObjId, u32>,
    locals_words: u32,
) {
    let mut max_end: u32 = 0;
    for obj in objects {
        let off = obj_offset_words
            .get(&obj.id)
            .copied()
            .unwrap_or_else(|| panic!("missing offset for obj {}", obj.id.as_u32()));
        let end = off
            .checked_add(obj.size_words)
            .unwrap_or_else(|| panic!("obj {} end overflows", obj.id.as_u32()));
        max_end = max_end.max(end);
        assert!(
            end <= locals_words,
            "object {} in func {} ends at {} > locals_words={}",
            obj.id.as_u32(),
            func_ref.as_u32(),
            end,
            locals_words
        );
    }
    assert_eq!(
        max_end,
        locals_words,
        "locals_words mismatch in func {}",
        func_ref.as_u32()
    );

    for (idx, left) in objects.iter().enumerate() {
        for right in objects.iter().skip(idx + 1) {
            if left.size_words == 0 || right.size_words == 0 || !left.region.overlaps(&right.region)
            {
                continue;
            }

            let left_off = obj_offset_words[&left.id];
            let right_off = obj_offset_words[&right.id];
            let left_end = left_off + left.size_words;
            let right_end = right_off + right.size_words;
            assert!(
                left_end <= right_off || right_end <= left_off,
                "packing overlap in func {}: {:?}@[{left_off},{left_end}) vs {:?}@[{right_off},{right_end})",
                func_ref.as_u32(),
                left.kind,
                right.kind,
            );
        }
    }
}

pub(crate) fn topo_sort_sccs(
    funcs: &FxHashSet<FuncRef>,
    call_graph: &CallGraph,
    scc: &CallGraphSccs,
) -> Vec<SccRef> {
    let mut sccs: BTreeSet<SccRef> = BTreeSet::new();
    for &func in funcs {
        sccs.insert(scc.scc_ref(func));
    }

    let mut edges: BTreeMap<SccRef, BTreeSet<SccRef>> = BTreeMap::new();
    let mut indegree: BTreeMap<SccRef, usize> = BTreeMap::new();
    for &scc_ref in &sccs {
        edges.insert(scc_ref, BTreeSet::new());
        indegree.insert(scc_ref, 0);
    }

    for &func in funcs {
        let from = scc.scc_ref(func);
        for &callee in call_graph.callee_of(func) {
            let to = scc.scc_ref(callee);
            if from == to {
                continue;
            }
            let tos = edges.get_mut(&from).expect("missing SCC edge set");
            if tos.insert(to) {
                *indegree.get_mut(&to).expect("missing SCC indegree") += 1;
            }
        }
    }

    let mut ready: BTreeSet<SccRef> = BTreeSet::new();
    for (&scc_ref, &deg) in &indegree {
        if deg == 0 {
            ready.insert(scc_ref);
        }
    }

    let mut topo: Vec<SccRef> = Vec::with_capacity(sccs.len());
    while let Some(&scc_ref) = ready.first() {
        ready.remove(&scc_ref);
        topo.push(scc_ref);

        let tos: Vec<SccRef> = edges
            .get(&scc_ref)
            .expect("missing SCC edge set")
            .iter()
            .copied()
            .collect();
        for to in tos {
            let deg = indegree.get_mut(&to).expect("missing SCC indegree");
            *deg = deg.checked_sub(1).expect("SCC indegree underflow");
            if *deg == 0 {
                ready.insert(to);
            }
        }
    }

    debug_assert_eq!(topo.len(), sccs.len(), "SCC topo sort incomplete");
    topo
}

pub(crate) fn build_scc_edges(
    funcs: &FxHashSet<FuncRef>,
    call_graph: &CallGraph,
    scc: &CallGraphSccs,
    topo: &[SccRef],
) -> BTreeMap<SccRef, Vec<SccRef>> {
    let mut edges: BTreeMap<SccRef, BTreeSet<SccRef>> = BTreeMap::new();
    for &scc_ref in topo {
        edges.insert(scc_ref, BTreeSet::new());
    }

    for &func in funcs {
        let from = scc.scc_ref(func);
        for &callee in call_graph.callee_of(func) {
            let to = scc.scc_ref(callee);
            if from != to {
                edges
                    .get_mut(&from)
                    .expect("missing SCC edge set")
                    .insert(to);
            }
        }
    }

    let mut out: BTreeMap<SccRef, Vec<SccRef>> = BTreeMap::new();
    for (scc_ref, tos) in edges {
        out.insert(scc_ref, tos.into_iter().collect());
    }
    out
}
