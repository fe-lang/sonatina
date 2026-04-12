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
        CallSiteObjects, FuncStackObjects, LiveInterval, ObjFacts, PackedObject, PeakPackWorkspace,
        RankedPeakPackItem, ReleaseSchedule, StackObj, StackObjId, StackObjKind,
        StaticArenaAllocCtx, pack_objects_presorted, pack_zero_min_offset_peak_ranked,
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
    shadow_objs: Vec<StackObj>,
    stable_pack: Vec<PackedObject>,
}

#[derive(Default)]
struct FuncPlacementScoreWorkspace {
    scratch_peak: PeakPackWorkspace,
    stable_peak: PeakPackWorkspace,
}

#[derive(Clone, Copy, Debug)]
struct EventRange {
    start_order: u32,
    end_order: u32,
}

#[derive(Clone, Debug)]
struct CandidateMeta {
    obj_id: StackObjId,
    local_idx: u32,
    size_words: u32,
    scratch_lb_range: EventRange,
    stable_lb_range: EventRange,
    recursive_access_cost: u64,
    shadow_copy_words: u64,
    live_call_indices: SmallVec<[u32; 4]>,
    live_call_order_indices: SmallVec<[u32; 4]>,
}

struct PlacementProblem<'a> {
    stack: &'a FuncStackObjects,
    sorted_objects: Vec<&'a StackObj>,
    sorted_calls: Vec<&'a CallSiteObjects>,
    scratch_release: ReleaseSchedule,
    scratch_lb_range_by_local: Vec<EventRange>,
    stable_order_by_local: Vec<u32>,
    stable_order_by_call: Vec<u32>,
    stable_release: ReleaseSchedule,
    stable_lb_range_by_local: Vec<EventRange>,
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
struct MoveLocalDelta {
    local_idx: u32,
    scratch_delta: i64,
    stable_delta: i64,
}

#[derive(Clone, Copy, Debug)]
struct MoveCallDelta {
    call_idx: u32,
    stable_shadow_delta: i64,
}

struct PlacementLowerBoundState {
    scratch_tree: MaxAddSegTree,
    stable_tree: MaxAddSegTree,
}

struct MaxAddSegTree {
    len: usize,
    max: Vec<i64>,
    lazy: Vec<i64>,
}

#[derive(Clone, Copy, Debug)]
struct BoundMoveEval {
    mv: PlacementMove,
    lower_bound: FuncPlacementScore,
}

#[derive(Clone, Copy, Debug)]
struct ExactMoveEval {
    mv: PlacementMove,
    exact: FuncPlacementScore,
}

#[derive(Default)]
struct SearchWorkBuffers {
    one_flip_bounds: Vec<BoundMoveEval>,
    swap_bounds: Vec<BoundMoveEval>,
    add_shortlist: Vec<usize>,
    remove_shortlist: Vec<usize>,
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
        sorted_objects.sort_unstable_by_key(|obj| pack_sort_key(obj.id, obj.interval));
        let mut sorted_calls: Vec<_> = stack.call_sites.iter().collect();
        sorted_calls.sort_unstable_by_key(|call| (call.inst_pos, call.inst.as_u32()));
        let scratch_start_ranks: Vec<u32> = sorted_objects
            .iter()
            .map(|obj| obj.interval.start)
            .collect();
        let scratch_end_ranks: Vec<u32> =
            sorted_objects.iter().map(|obj| obj.interval.end).collect();
        let scratch_release = ReleaseSchedule::from_end_ranks(
            &scratch_end_ranks,
            rank_count(scratch_end_ranks.iter().copied().max()),
        );
        let scratch_lb_range_by_local: Vec<EventRange> =
            build_lb_end_order_by_order(&scratch_start_ranks, &scratch_end_ranks)
                .into_iter()
                .enumerate()
                .map(|(local_idx, end_order)| EventRange {
                    start_order: local_idx as u32,
                    end_order,
                })
                .collect();
        let mut stable_order_by_local = vec![u32::MAX; sorted_objects.len()];
        let mut stable_order_by_call = vec![u32::MAX; sorted_calls.len()];
        let mut stable_start_ranks =
            Vec::with_capacity(sorted_objects.len().saturating_add(sorted_calls.len()));
        let mut stable_end_ranks =
            Vec::with_capacity(sorted_objects.len().saturating_add(sorted_calls.len()));
        let mut local_pos = 0usize;
        let mut call_pos = 0usize;
        while local_pos < sorted_objects.len() || call_pos < sorted_calls.len() {
            let take_local = match (sorted_objects.get(local_pos), sorted_calls.get(call_pos)) {
                (Some(obj), Some(call)) => {
                    let shadow_order = problem_shadow_order_id(stack.next_obj_id, call_pos);
                    pack_sort_key(obj.id, obj.interval)
                        <= (call.inst_pos, call.inst_pos, shadow_order)
                }
                (Some(_), None) => true,
                (None, Some(_)) => false,
                (None, None) => break,
            };
            let order_idx = stable_end_ranks.len() as u32;
            if take_local {
                stable_order_by_local[local_pos] = order_idx;
                stable_start_ranks.push(sorted_objects[local_pos].interval.start);
                stable_end_ranks.push(sorted_objects[local_pos].interval.end);
                local_pos += 1;
            } else {
                stable_order_by_call[call_pos] = order_idx;
                stable_start_ranks.push(sorted_calls[call_pos].inst_pos);
                stable_end_ranks.push(sorted_calls[call_pos].inst_pos);
                call_pos += 1;
            }
        }
        let stable_release = ReleaseSchedule::from_end_ranks(
            &stable_end_ranks,
            rank_count(
                sorted_objects
                    .iter()
                    .map(|obj| obj.interval.end)
                    .chain(sorted_calls.iter().map(|call| call.inst_pos))
                    .max(),
            ),
        );
        let stable_lb_end_by_order =
            build_lb_end_order_by_order(&stable_start_ranks, &stable_end_ranks);
        let stable_lb_range_by_local: Vec<EventRange> = stable_order_by_local
            .iter()
            .map(|&order_idx| EventRange {
                start_order: order_idx,
                end_order: stable_lb_end_by_order[order_idx as usize],
            })
            .collect();

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
                local_idx,
                size_words: fact.size_words,
                scratch_lb_range: scratch_lb_range_by_local[local_idx as usize],
                stable_lb_range: stable_lb_range_by_local[local_idx as usize],
                recursive_access_cost: recursive_access_cost(cost_model, is_recursive, fact),
                shadow_copy_words: 0,
                live_call_indices: SmallVec::new(),
                live_call_order_indices: SmallVec::new(),
            });
        }

        let mut base_shadow_words_by_call = vec![0u32; sorted_calls.len()];
        let mut base_shadow_copy_words = 0u64;
        for (call_idx, &call) in sorted_calls.iter().enumerate() {
            for &obj in &call.live_out_objs {
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
                    candidate
                        .live_call_order_indices
                        .push(stable_order_by_call[call_idx]);
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
            scratch_release,
            scratch_lb_range_by_local,
            stable_order_by_local,
            stable_order_by_call,
            stable_release,
            stable_lb_range_by_local,
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
            remove_sorted_u32(&mut self.scratch_real_locals, candidate.local_idx);
            insert_sorted_u32(&mut self.stable_real_locals, candidate.local_idx);
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
            remove_sorted_u32(&mut self.stable_real_locals, candidate.local_idx);
            insert_sorted_u32(&mut self.scratch_real_locals, candidate.local_idx);
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

impl MaxAddSegTree {
    fn new() -> Self {
        Self {
            len: 0,
            max: Vec::new(),
            lazy: Vec::new(),
        }
    }

    fn reset(&mut self, len: usize) {
        self.len = len;
        let tree_len = len.saturating_mul(4).max(1);
        if self.max.len() < tree_len {
            self.max.resize(tree_len, 0);
            self.lazy.resize(tree_len, 0);
        } else {
            self.max[..tree_len].fill(0);
            self.lazy[..tree_len].fill(0);
        }
    }

    fn add_range_nolog(&mut self, start: u32, end: u32, delta: i64) {
        self.add_range_impl(start as usize, end as usize, delta, 1, 0, self.len);
    }

    fn add_point_nolog(&mut self, idx: u32, delta: i64) {
        self.add_point_impl(idx as usize, delta);
    }

    fn max_value(&self) -> u32 {
        if self.len == 0 {
            return 0;
        }
        debug_assert!(self.max[1] >= 0, "negative committed lower-bound load");
        self.max[1] as u32
    }

    fn add_range_impl(
        &mut self,
        start: usize,
        end: usize,
        delta: i64,
        idx: usize,
        seg_start: usize,
        seg_end: usize,
    ) {
        if self.len == 0
            || start > end
            || seg_start == seg_end
            || end < seg_start
            || seg_end - 1 < start
        {
            return;
        }
        if start <= seg_start && seg_end - 1 <= end {
            self.apply_delta(idx, delta);
            return;
        }
        let mid = seg_start + (seg_end - seg_start) / 2;
        if start < mid {
            self.add_range_impl(start, end, delta, idx * 2, seg_start, mid);
        }
        if end >= mid && mid < seg_end {
            self.add_range_impl(start, end, delta, idx * 2 + 1, mid, seg_end);
        }
        self.recompute(idx);
    }

    fn add_point_impl(&mut self, pos: usize, delta: i64) {
        if self.len == 0 || pos >= self.len {
            return;
        }

        let mut idx = 1usize;
        let mut seg_start = 0usize;
        let mut seg_end = self.len;
        let mut path = SmallVec::<[usize; 32]>::new();
        while seg_end - seg_start > 1 {
            path.push(idx);
            let mid = seg_start + (seg_end - seg_start) / 2;
            if pos < mid {
                idx *= 2;
                seg_end = mid;
            } else {
                idx = idx * 2 + 1;
                seg_start = mid;
            }
        }
        self.apply_delta(idx, delta);
        while let Some(parent) = path.pop() {
            self.recompute(parent);
        }
    }

    fn apply_delta(&mut self, idx: usize, delta: i64) {
        self.max[idx] += delta;
        self.lazy[idx] += delta;
    }

    fn recompute(&mut self, idx: usize) {
        self.max[idx] = self.max[idx * 2].max(self.max[idx * 2 + 1]) + self.lazy[idx];
    }
}

impl Default for MaxAddSegTree {
    fn default() -> Self {
        Self::new()
    }
}

impl PlacementLowerBoundState {
    fn new(problem: &PlacementProblem<'_>) -> Self {
        let mut scratch_tree = MaxAddSegTree::new();
        scratch_tree.reset(problem.sorted_objects.len());
        for (local_idx, obj) in problem.sorted_objects.iter().enumerate() {
            if problem.must_stable_by_local[local_idx] || obj.size_words == 0 {
                continue;
            }
            let range = problem.scratch_lb_range_by_local[local_idx];
            scratch_tree.add_range_nolog(
                range.start_order,
                range.end_order,
                i64::from(obj.size_words),
            );
        }

        let mut stable_tree = MaxAddSegTree::new();
        stable_tree.reset(problem.sorted_objects.len() + problem.sorted_calls.len());
        for (local_idx, obj) in problem.sorted_objects.iter().enumerate() {
            if !problem.must_stable_by_local[local_idx] || obj.size_words == 0 {
                continue;
            }
            let range = problem.stable_lb_range_by_local[local_idx];
            stable_tree.add_range_nolog(
                range.start_order,
                range.end_order,
                i64::from(obj.size_words),
            );
        }
        for (call_idx, &shadow_words) in problem.base_shadow_words_by_call.iter().enumerate() {
            if shadow_words == 0 {
                continue;
            }
            stable_tree.add_point_nolog(
                problem.stable_order_by_call[call_idx],
                i64::from(shadow_words),
            );
        }

        Self {
            scratch_tree,
            stable_tree,
        }
    }

    fn apply_add(&mut self, problem: &PlacementProblem<'_>, candidate_idx: usize) {
        self.apply_move(problem, PlacementMove::Add(candidate_idx));
    }

    fn apply_remove(&mut self, problem: &PlacementProblem<'_>, candidate_idx: usize) {
        self.apply_move(problem, PlacementMove::Remove(candidate_idx));
    }

    fn apply_swap(&mut self, problem: &PlacementProblem<'_>, add_idx: usize, remove_idx: usize) {
        self.apply_move(
            problem,
            PlacementMove::Swap {
                add_idx,
                remove_idx,
            },
        );
    }

    fn apply_move(&mut self, problem: &PlacementProblem<'_>, mv: PlacementMove) {
        apply_lower_bound_move(
            problem,
            &mut self.scratch_tree,
            &mut self.stable_tree,
            mv,
            1,
        );
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
        for &obj in &call.live_out_objs {
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
        stable_pack: Vec::with_capacity(
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
    for &call in &problem.sorted_calls {
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
        workspace.shadow_objs.push(shadow_obj);
        call_preserve.insert(call.inst, plan);
    }

    build_stable_pack(
        &mut workspace.stable_pack,
        &problem.sorted_objects,
        &workspace.shadow_objs,
        &problem.must_stable,
        promoted_optional,
    );
    let (stable_offsets, stable_words) = pack_objects_presorted(&workspace.stable_pack);

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
    let scratch_words = scratch_peak_with_move(problem, state, mv, workspace);
    let stable_words = stable_peak_with_move(problem, state, mv, workspace);
    let (shadow_copy_words, recursive_access_cost) = additive_terms_with_move(problem, state, mv);

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

fn evaluate_func_placement_lower_bound(
    problem: &PlacementProblem<'_>,
    state: &PlacementState,
    lb_state: &mut PlacementLowerBoundState,
    mv: PlacementMove,
) -> FuncPlacementScore {
    apply_lower_bound_move(
        problem,
        &mut lb_state.scratch_tree,
        &mut lb_state.stable_tree,
        mv,
        1,
    );
    let scratch_words = lb_state.scratch_tree.max_value();
    let stable_words = lb_state.stable_tree.max_value();
    apply_lower_bound_move(
        problem,
        &mut lb_state.scratch_tree,
        &mut lb_state.stable_tree,
        mv,
        -1,
    );

    let (shadow_copy_words, recursive_access_cost) = additive_terms_with_move(problem, state, mv);
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
    let (insert_idx, skip_idx) = scratch_local_indices_for_move(problem, mv);
    let count = state.scratch_real_locals.len() + usize::from(insert_idx.is_some())
        - usize::from(skip_idx.is_some());
    pack_zero_min_offset_peak_ranked(
        &mut workspace.scratch_peak,
        &problem.scratch_release,
        TrialLocalIter::new(&state.scratch_real_locals, insert_idx, skip_idx)
            .map(|local_idx| ranked_scratch_item_for_local(problem, local_idx)),
        count,
    )
}

fn stable_peak_with_move(
    problem: &PlacementProblem<'_>,
    state: &PlacementState,
    mv: PlacementMove,
    workspace: &mut FuncPlacementScoreWorkspace,
) -> u32 {
    let (insert_idx, skip_idx) = stable_local_indices_for_move(problem, mv);
    let mut real_iter = TrialLocalIter::new(&state.stable_real_locals, insert_idx, skip_idx)
        .map(|local_idx| ranked_stable_real_item_for_local(problem, local_idx))
        .peekable();
    let mut local_deltas = SmallVec::<[MoveLocalDelta; 2]>::new();
    let mut call_deltas = SmallVec::<[MoveCallDelta; 8]>::new();
    build_move_deltas(problem, mv, &mut local_deltas, &mut call_deltas);
    let mut shadow_iter = MoveShadowCallIter::new(problem, state, &call_deltas).peekable();
    let count = state.stable_real_locals.len() + usize::from(insert_idx.is_some())
        - usize::from(skip_idx.is_some())
        + state.nonzero_shadow_calls.len()
        + call_deltas.len();

    pack_zero_min_offset_peak_ranked(
        &mut workspace.stable_peak,
        &problem.stable_release,
        std::iter::from_fn(move || match (real_iter.peek(), shadow_iter.peek()) {
            (Some(real), Some(shadow)) => {
                if real.order_idx < shadow.order_idx {
                    real_iter.next()
                } else {
                    shadow_iter.next()
                }
            }
            (Some(_), None) => real_iter.next(),
            (None, Some(_)) => shadow_iter.next(),
            (None, None) => None,
        }),
        count,
    )
}

fn find_best_exact_one_flip_move(
    problem: &PlacementProblem<'_>,
    state: &PlacementState,
    lb_state: &mut PlacementLowerBoundState,
    current_score: FuncPlacementScore,
    exact_ws: &mut FuncPlacementScoreWorkspace,
    work: &mut SearchWorkBuffers,
) -> Option<ExactMoveEval> {
    work.one_flip_bounds.clear();
    for candidate_idx in 0..problem.candidates.len() {
        let mv = if state.promoted[candidate_idx] {
            PlacementMove::Remove(candidate_idx)
        } else {
            PlacementMove::Add(candidate_idx)
        };
        let lower_bound = evaluate_func_placement_lower_bound(problem, state, lb_state, mv);
        if is_better_score(lower_bound, current_score) {
            work.one_flip_bounds.push(BoundMoveEval { mv, lower_bound });
        }
    }
    work.one_flip_bounds.sort_unstable_by(|a, b| {
        cmp_func_placement_score(a.lower_bound, b.lower_bound)
            .then_with(|| {
                resulting_promoted_count(state, a.mv).cmp(&resulting_promoted_count(state, b.mv))
            })
            .then_with(|| cmp_move_tie_key(problem, a.mv, b.mv))
    });

    let mut best_exact: Option<ExactMoveEval> = None;
    for bound in &work.one_flip_bounds {
        if let Some(current_best) = best_exact
            && cmp_func_placement_score(bound.lower_bound, current_best.exact) != Ordering::Less
        {
            break;
        }
        let exact = evaluate_func_placement_score(problem, state, bound.mv, exact_ws);
        if !is_better_score(exact, current_score) {
            continue;
        }
        if best_exact.is_none_or(|current_best| {
            is_preferred_exact_move(
                problem,
                state,
                bound.mv,
                exact,
                current_best.mv,
                current_best.exact,
            )
        }) {
            best_exact = Some(ExactMoveEval {
                mv: bound.mv,
                exact,
            });
        }
    }
    best_exact
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

    work.swap_bounds.clear();
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
                let lower_bound = evaluate_func_placement_lower_bound(problem, state, lb_state, mv);
                if is_better_score(lower_bound, current_score) {
                    work.swap_bounds.push(BoundMoveEval { mv, lower_bound });
                }
            }
        }
    } else {
        collect_swap_shortlists(problem, state, lb_state, work);
        let add_shortlist = work.add_shortlist.clone();
        let remove_shortlist = work.remove_shortlist.clone();
        for add_idx in add_shortlist {
            for &remove_idx in &remove_shortlist {
                let mv = PlacementMove::Swap {
                    add_idx,
                    remove_idx,
                };
                let lower_bound = evaluate_func_placement_lower_bound(problem, state, lb_state, mv);
                if is_better_score(lower_bound, current_score) {
                    work.swap_bounds.push(BoundMoveEval { mv, lower_bound });
                }
            }
        }
    }

    work.swap_bounds.sort_unstable_by(|a, b| {
        cmp_func_placement_score(a.lower_bound, b.lower_bound)
            .then_with(|| {
                resulting_promoted_count(state, a.mv).cmp(&resulting_promoted_count(state, b.mv))
            })
            .then_with(|| cmp_move_tie_key(problem, a.mv, b.mv))
    });

    let mut best_exact: Option<ExactMoveEval> = None;
    for bound in &work.swap_bounds {
        if let Some(current_best) = best_exact
            && cmp_func_placement_score(bound.lower_bound, current_best.exact) != Ordering::Less
        {
            break;
        }
        let exact = evaluate_func_placement_score(problem, state, bound.mv, exact_ws);
        if !is_better_score(exact, current_score) {
            continue;
        }
        if best_exact.is_none_or(|current_best| {
            is_preferred_exact_move(
                problem,
                state,
                bound.mv,
                exact,
                current_best.mv,
                current_best.exact,
            )
        }) {
            best_exact = Some(ExactMoveEval {
                mv: bound.mv,
                exact,
            });
        }
    }
    best_exact
}

fn collect_swap_shortlists(
    problem: &PlacementProblem<'_>,
    state: &PlacementState,
    lb_state: &mut PlacementLowerBoundState,
    work: &mut SearchWorkBuffers,
) {
    work.add_shortlist.clear();
    work.remove_shortlist.clear();

    let mut add_lb_scores = Vec::new();
    let mut remove_lb_scores = Vec::new();
    for candidate_idx in 0..problem.candidates.len() {
        if state.promoted[candidate_idx] {
            remove_lb_scores.push((
                candidate_idx,
                evaluate_func_placement_lower_bound(
                    problem,
                    state,
                    lb_state,
                    PlacementMove::Remove(candidate_idx),
                ),
            ));
        } else {
            add_lb_scores.push((
                candidate_idx,
                evaluate_func_placement_lower_bound(
                    problem,
                    state,
                    lb_state,
                    PlacementMove::Add(candidate_idx),
                ),
            ));
        }
    }

    add_lb_scores.sort_unstable_by(|a, b| {
        cmp_func_placement_score(a.1, b.1).then_with(|| {
            problem.candidates[a.0]
                .obj_id
                .as_u32()
                .cmp(&problem.candidates[b.0].obj_id.as_u32())
        })
    });
    remove_lb_scores.sort_unstable_by(|a, b| {
        cmp_func_placement_score(a.1, b.1).then_with(|| {
            problem.candidates[a.0]
                .obj_id
                .as_u32()
                .cmp(&problem.candidates[b.0].obj_id.as_u32())
        })
    });
    for &(candidate_idx, _) in add_lb_scores.iter().take(SWAP_SHORTLIST_PER_METRIC) {
        push_unique_candidate(&mut work.add_shortlist, candidate_idx);
    }
    for &(candidate_idx, _) in remove_lb_scores.iter().take(SWAP_SHORTLIST_PER_METRIC) {
        push_unique_candidate(&mut work.remove_shortlist, candidate_idx);
    }

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
        let mut candidates: Vec<usize> = problem
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
    for &obj in &call.live_out_objs {
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
        interval: LiveInterval {
            start: call.inst_pos,
            end: call.inst_pos,
        },
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
            interval: obj.interval,
            min_offset_words: 0,
        });
    }
}

fn build_stable_pack(
    stable_pack: &mut Vec<PackedObject>,
    sorted_objects: &[&StackObj],
    shadow_objs: &[StackObj],
    must_stable: &BitSet<StackObjId>,
    promoted_optional: &BitSet<StackObjId>,
) {
    stable_pack.clear();
    let mut shadow_iter = shadow_objs.iter().peekable();
    for &obj in sorted_objects {
        if !is_stable_real(must_stable, promoted_optional, obj.id) {
            continue;
        }
        let obj_key = pack_sort_key(obj.id, obj.interval);
        while let Some(shadow) = shadow_iter.peek()
            && pack_sort_key(shadow.id, shadow.interval) <= obj_key
        {
            stable_pack.push(PackedObject {
                id: shadow.id,
                size_words: shadow.size_words,
                interval: shadow.interval,
                min_offset_words: 0,
            });
            let _ = shadow_iter.next();
        }
        stable_pack.push(PackedObject {
            id: obj.id,
            size_words: obj.size_words,
            interval: obj.interval,
            min_offset_words: 0,
        });
    }
    for shadow in shadow_iter {
        stable_pack.push(PackedObject {
            id: shadow.id,
            size_words: shadow.size_words,
            interval: shadow.interval,
            min_offset_words: 0,
        });
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

fn move_arity_rank(mv: PlacementMove) -> u8 {
    match mv {
        PlacementMove::Add(_) | PlacementMove::Remove(_) => 0,
        PlacementMove::Swap { .. } => 1,
        PlacementMove::None => 2,
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

fn is_preferred_exact_move(
    problem: &PlacementProblem<'_>,
    state: &PlacementState,
    mv_a: PlacementMove,
    score_a: FuncPlacementScore,
    mv_b: PlacementMove,
    score_b: FuncPlacementScore,
) -> bool {
    cmp_func_placement_score(score_a, score_b) == Ordering::Less
        || (score_a == score_b
            && resulting_promoted_count(state, mv_a)
                .cmp(&resulting_promoted_count(state, mv_b))
                .then_with(|| move_arity_rank(mv_a).cmp(&move_arity_rank(mv_b)))
                .then_with(|| cmp_move_tie_key(problem, mv_a, mv_b))
                == Ordering::Less)
}

fn build_lb_end_order_by_order(
    start_ranks_by_order: &[u32],
    end_ranks_by_order: &[u32],
) -> Vec<u32> {
    assert_eq!(
        start_ranks_by_order.len(),
        end_ranks_by_order.len(),
        "lower-bound order arrays must have matching lengths"
    );
    let mut out = Vec::with_capacity(start_ranks_by_order.len());
    for (order_idx, &end_rank) in end_ranks_by_order.iter().enumerate() {
        let last_before = start_ranks_by_order.partition_point(|&start_rank| start_rank < end_rank);
        out.push(order_idx.max(last_before.saturating_sub(1)) as u32);
    }
    out
}

fn push_local_delta(
    local_deltas: &mut SmallVec<[MoveLocalDelta; 2]>,
    local_idx: u32,
    scratch_delta: i64,
    stable_delta: i64,
) {
    if scratch_delta == 0 && stable_delta == 0 {
        return;
    }
    if let Some(delta) = local_deltas
        .iter_mut()
        .find(|delta| delta.local_idx == local_idx)
    {
        delta.scratch_delta += scratch_delta;
        delta.stable_delta += stable_delta;
        return;
    }
    local_deltas.push(MoveLocalDelta {
        local_idx,
        scratch_delta,
        stable_delta,
    });
}

fn push_call_delta(
    call_deltas: &mut SmallVec<[MoveCallDelta; 8]>,
    call_idx: u32,
    stable_shadow_delta: i64,
) {
    if stable_shadow_delta == 0 {
        return;
    }
    if let Some(delta) = call_deltas
        .iter_mut()
        .find(|delta| delta.call_idx == call_idx)
    {
        delta.stable_shadow_delta += stable_shadow_delta;
        return;
    }
    call_deltas.push(MoveCallDelta {
        call_idx,
        stable_shadow_delta,
    });
}

fn add_candidate_move_deltas(
    problem: &PlacementProblem<'_>,
    candidate_idx: usize,
    sign: i64,
    local_deltas: &mut SmallVec<[MoveLocalDelta; 2]>,
    call_deltas: &mut SmallVec<[MoveCallDelta; 8]>,
) {
    let candidate = &problem.candidates[candidate_idx];
    let size = i64::from(candidate.size_words);
    push_local_delta(local_deltas, candidate.local_idx, -sign * size, sign * size);
    for &call_idx in &candidate.live_call_indices {
        push_call_delta(call_deltas, call_idx, -sign * size);
    }
}

fn build_move_deltas(
    problem: &PlacementProblem<'_>,
    mv: PlacementMove,
    local_deltas: &mut SmallVec<[MoveLocalDelta; 2]>,
    call_deltas: &mut SmallVec<[MoveCallDelta; 8]>,
) {
    local_deltas.clear();
    call_deltas.clear();
    match mv {
        PlacementMove::None => {}
        PlacementMove::Add(candidate_idx) => {
            add_candidate_move_deltas(problem, candidate_idx, 1, local_deltas, call_deltas);
        }
        PlacementMove::Remove(candidate_idx) => {
            add_candidate_move_deltas(problem, candidate_idx, -1, local_deltas, call_deltas);
        }
        PlacementMove::Swap {
            add_idx,
            remove_idx,
        } => {
            add_candidate_move_deltas(problem, add_idx, 1, local_deltas, call_deltas);
            add_candidate_move_deltas(problem, remove_idx, -1, local_deltas, call_deltas);
        }
    }
    local_deltas.retain(|delta| delta.scratch_delta != 0 || delta.stable_delta != 0);
    call_deltas.retain(|delta| delta.stable_shadow_delta != 0);
    call_deltas.sort_unstable_by_key(|delta| delta.call_idx);
}

fn apply_candidate_local_lower_bound_delta(
    candidate: &CandidateMeta,
    scratch_tree: &mut MaxAddSegTree,
    stable_tree: &mut MaxAddSegTree,
    sign: i64,
) {
    if candidate.size_words == 0 {
        return;
    }
    let size = i64::from(candidate.size_words);
    scratch_tree.add_range_nolog(
        candidate.scratch_lb_range.start_order,
        candidate.scratch_lb_range.end_order,
        -sign * size,
    );
    stable_tree.add_range_nolog(
        candidate.stable_lb_range.start_order,
        candidate.stable_lb_range.end_order,
        sign * size,
    );
}

fn apply_candidate_shadow_lower_bound_delta(
    candidate: &CandidateMeta,
    stable_tree: &mut MaxAddSegTree,
    sign: i64,
) {
    if candidate.size_words == 0 {
        return;
    }
    let shadow_delta = -sign * i64::from(candidate.size_words);
    for &order_idx in &candidate.live_call_order_indices {
        stable_tree.add_point_nolog(order_idx, shadow_delta);
    }
}

fn apply_swap_shadow_lower_bound_delta(
    add_candidate: &CandidateMeta,
    remove_candidate: &CandidateMeta,
    stable_tree: &mut MaxAddSegTree,
    scale: i64,
) {
    let add_size = i64::from(add_candidate.size_words);
    let remove_size = i64::from(remove_candidate.size_words);
    let mut add_pos = 0usize;
    let mut remove_pos = 0usize;
    while add_pos < add_candidate.live_call_order_indices.len()
        || remove_pos < remove_candidate.live_call_order_indices.len()
    {
        let add_order = add_candidate.live_call_order_indices.get(add_pos).copied();
        let remove_order = remove_candidate
            .live_call_order_indices
            .get(remove_pos)
            .copied();
        let Some(order_idx) = (match (add_order, remove_order) {
            (Some(add_order), Some(remove_order)) => Some(add_order.min(remove_order)),
            (Some(add_order), None) => Some(add_order),
            (None, Some(remove_order)) => Some(remove_order),
            (None, None) => None,
        }) else {
            break;
        };

        let mut delta = 0i64;
        if add_order == Some(order_idx) {
            delta -= scale * add_size;
            add_pos += 1;
        }
        if remove_order == Some(order_idx) {
            delta += scale * remove_size;
            remove_pos += 1;
        }
        if delta != 0 {
            stable_tree.add_point_nolog(order_idx, delta);
        }
    }
}

fn apply_lower_bound_move(
    problem: &PlacementProblem<'_>,
    scratch_tree: &mut MaxAddSegTree,
    stable_tree: &mut MaxAddSegTree,
    mv: PlacementMove,
    scale: i64,
) {
    match mv {
        PlacementMove::None => {}
        PlacementMove::Add(candidate_idx) => {
            let candidate = &problem.candidates[candidate_idx];
            apply_candidate_local_lower_bound_delta(candidate, scratch_tree, stable_tree, scale);
            apply_candidate_shadow_lower_bound_delta(candidate, stable_tree, scale);
        }
        PlacementMove::Remove(candidate_idx) => {
            let candidate = &problem.candidates[candidate_idx];
            apply_candidate_local_lower_bound_delta(candidate, scratch_tree, stable_tree, -scale);
            apply_candidate_shadow_lower_bound_delta(candidate, stable_tree, -scale);
        }
        PlacementMove::Swap {
            add_idx,
            remove_idx,
        } => {
            let add_candidate = &problem.candidates[add_idx];
            let remove_candidate = &problem.candidates[remove_idx];
            apply_candidate_local_lower_bound_delta(
                add_candidate,
                scratch_tree,
                stable_tree,
                scale,
            );
            apply_candidate_local_lower_bound_delta(
                remove_candidate,
                scratch_tree,
                stable_tree,
                -scale,
            );
            apply_swap_shadow_lower_bound_delta(
                add_candidate,
                remove_candidate,
                stable_tree,
                scale,
            );
        }
    }
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
        PlacementMove::Add(candidate_idx) => {
            (None, Some(problem.candidates[candidate_idx].local_idx))
        }
        PlacementMove::Remove(candidate_idx) => {
            (Some(problem.candidates[candidate_idx].local_idx), None)
        }
        PlacementMove::Swap {
            add_idx,
            remove_idx,
        } => (
            Some(problem.candidates[remove_idx].local_idx),
            Some(problem.candidates[add_idx].local_idx),
        ),
    }
}

fn stable_local_indices_for_move(
    problem: &PlacementProblem<'_>,
    mv: PlacementMove,
) -> (Option<u32>, Option<u32>) {
    match mv {
        PlacementMove::None => (None, None),
        PlacementMove::Add(candidate_idx) => {
            (Some(problem.candidates[candidate_idx].local_idx), None)
        }
        PlacementMove::Remove(candidate_idx) => {
            (None, Some(problem.candidates[candidate_idx].local_idx))
        }
        PlacementMove::Swap {
            add_idx,
            remove_idx,
        } => (
            Some(problem.candidates[add_idx].local_idx),
            Some(problem.candidates[remove_idx].local_idx),
        ),
    }
}

struct MoveShadowCallIter<'a> {
    problem: &'a PlacementProblem<'a>,
    state: &'a PlacementState,
    base_pos: usize,
    delta_pos: usize,
    deltas: &'a [MoveCallDelta],
}

impl<'a> MoveShadowCallIter<'a> {
    fn new(
        problem: &'a PlacementProblem<'a>,
        state: &'a PlacementState,
        deltas: &'a [MoveCallDelta],
    ) -> Self {
        Self {
            problem,
            state,
            base_pos: 0,
            delta_pos: 0,
            deltas,
        }
    }
}

impl Iterator for MoveShadowCallIter<'_> {
    type Item = RankedPeakPackItem;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let base_idx = self.state.nonzero_shadow_calls.get(self.base_pos).copied();
            let delta_idx = self.deltas.get(self.delta_pos).map(|delta| delta.call_idx);
            let idx = match (base_idx, delta_idx) {
                (Some(base_idx), Some(delta_idx)) => base_idx.min(delta_idx),
                (Some(base_idx), None) => base_idx,
                (None, Some(delta_idx)) => delta_idx,
                (None, None) => return None,
            };
            let from_base = base_idx == Some(idx);
            let from_delta = delta_idx == Some(idx);
            if from_base {
                self.base_pos += 1;
            }
            if from_delta {
                self.delta_pos += 1;
            }

            let mut shadow_words = if from_base {
                i64::from(self.state.shadow_words_by_call[idx as usize])
            } else {
                0
            };
            if from_delta {
                shadow_words += self.deltas[self.delta_pos - 1].stable_shadow_delta;
            }
            assert!(shadow_words >= 0, "shadow words underflow");
            if shadow_words == 0 {
                continue;
            }

            let call = self.problem.sorted_calls[idx as usize];
            return Some(RankedPeakPackItem {
                order_idx: self.problem.stable_order_by_call[idx as usize],
                start_rank: call.inst_pos,
                size_words: shadow_words as u32,
            });
        }
    }
}

fn ranked_scratch_item_for_local(
    problem: &PlacementProblem<'_>,
    local_idx: u32,
) -> RankedPeakPackItem {
    let obj = problem.sorted_objects[local_idx as usize];
    RankedPeakPackItem {
        order_idx: local_idx,
        start_rank: obj.interval.start,
        size_words: obj.size_words,
    }
}

fn ranked_stable_real_item_for_local(
    problem: &PlacementProblem<'_>,
    local_idx: u32,
) -> RankedPeakPackItem {
    let obj = problem.sorted_objects[local_idx as usize];
    RankedPeakPackItem {
        order_idx: problem.stable_order_by_local[local_idx as usize],
        start_rank: obj.interval.start,
        size_words: obj.size_words,
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

fn rank_count(max_rank: Option<u32>) -> usize {
    max_rank.map_or(0, |rank| rank as usize + 1)
}

fn pack_sort_key(id: StackObjId, interval: LiveInterval) -> (u32, u32, u32) {
    (interval.start, interval.end, id.as_u32())
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
                    interval: LiveInterval { start: 0, end: 0 },
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
                for &obj in &call.live_out_objs {
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
            if left.size_words == 0
                || right.size_words == 0
                || left.interval.end <= right.interval.start
                || right.interval.end <= left.interval.start
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        critical_edge::CriticalEdgeSplitter,
        domtree::DomTree,
        liveness::{InstLiveness, Liveness},
        stackalloc::StackifyBuilder,
    };
    use sonatina_ir::{
        Function, cfg::ControlFlowGraph, inst::evm::inst_set::EvmInstKind, isa::Isa,
    };
    use sonatina_parser::parse_module;
    use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

    struct PlanCtx {
        module: Module,
        plan: ProgramMemoryPlan,
        names: FxHashMap<String, FuncRef>,
        isa: Evm,
    }

    fn test_isa() -> Evm {
        Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        })
    }

    fn build_analysis(function: &mut Function, reach_depth: u8) -> FuncAnalysis {
        let mut cfg = ControlFlowGraph::new();
        cfg.compute(function);

        let mut splitter = CriticalEdgeSplitter::new();
        splitter.run(function, &mut cfg);

        let mut liveness = Liveness::new();
        liveness.compute(function, &cfg);

        let mut inst_liveness = InstLiveness::new();
        inst_liveness.compute(function, &cfg, &liveness);

        let mut dom = DomTree::new();
        dom.compute(&cfg);

        let block_order = dom.rpo().to_owned();
        let alloc = StackifyBuilder::new(function, &cfg, &dom, &liveness, reach_depth).compute();

        FuncAnalysis {
            alloc,
            inst_liveness,
            block_order,
            value_aliases: {
                let mut value_aliases: SecondaryMap<ValueId, Option<ValueId>> = SecondaryMap::new();
                for value in function.dfg.value_ids() {
                    value_aliases[value] = Some(value);
                }
                value_aliases
            },
        }
    }

    fn plan_ctx_from_src(src: &str, cost_model: &ArenaCostModel) -> PlanCtx {
        let parsed = parse_module(src).unwrap();
        let module = parsed.module;
        let funcs = module.funcs();
        let isa = test_isa();
        let ptr_escape =
            super::super::ptr_escape::compute_ptr_escape_summaries(&module, &funcs, &isa);

        let mut analyses: FxHashMap<FuncRef, FuncAnalysis> = FxHashMap::default();
        for &func in &funcs {
            module.func_store.modify(func, |function| {
                analyses.insert(func, build_analysis(function, 16));
            });
        }

        let plan =
            compute_program_memory_plan(&module, &funcs, &analyses, &ptr_escape, &isa, cost_model);

        let mut names: FxHashMap<String, FuncRef> = FxHashMap::default();
        for &func in &funcs {
            let name = module.ctx.func_sig(func, |sig| sig.name().to_string());
            names.insert(name, func);
        }

        PlanCtx {
            module,
            plan,
            names,
            isa,
        }
    }

    fn stable_mode_summary(mode: StableMode) -> (u8, u32) {
        match mode {
            StableMode::None => (0, 0),
            StableMode::StaticAbs { base_word } => (1, base_word),
            StableMode::DynamicFrame => (2, 0),
        }
    }

    fn obj_loc_summary(loc: ObjLoc) -> (u8, u32) {
        match loc {
            ObjLoc::ScratchAbs(word) => (0, word),
            ObjLoc::StableAbs(word) => (1, word),
            ObjLoc::StableFrame(word) => (2, word),
            ObjLoc::StackPinned(slot) => (3, u32::from(slot)),
        }
    }

    fn call_preserve_summary(plan: &CallPreservePlan) -> (u8, u8, u32, Vec<(u32, u32, u32)>) {
        match &plan.mode {
            PreserveMode::None => (0, plan.result_count, 0, Vec::new()),
            PreserveMode::ShadowRuns { shadow_obj, runs } => (
                1,
                plan.result_count,
                shadow_obj.as_u32(),
                runs.iter()
                    .map(|run| (run.scratch_src_word, run.shadow_dst_word, run.len_words))
                    .collect(),
            ),
            PreserveMode::TinyStackLift { word_offsets } => (
                2,
                plan.result_count,
                0,
                word_offsets
                    .iter()
                    .copied()
                    .map(|word| (word, 0, 0))
                    .collect(),
            ),
        }
    }

    type ObjLocSummary = (u8, u32);
    type PreserveRunSummary = (u32, u32, u32);
    type CallPreserveSummary = (u8, u8, u32, Vec<PreserveRunSummary>);
    type FuncPlanSummary = (
        String,
        Vec<(u32, ObjLocSummary)>,
        Vec<(u32, ObjLocSummary)>,
        Vec<(u32, CallPreserveSummary)>,
        u32,
        u32,
        (u8, u32),
        u32,
    );
    type PlanSummary = (u32, u32, u32, Vec<FuncRef>, Vec<FuncPlanSummary>);

    fn plan_summary(ctx: &PlanCtx) -> PlanSummary {
        let mut funcs = ctx.module.funcs();
        funcs.sort_unstable_by_key(|func| func.as_u32());
        let per_func = funcs
            .iter()
            .copied()
            .map(|func| {
                let name = ctx.module.ctx.func_sig(func, |sig| sig.name().to_string());
                let func_plan = ctx.plan.funcs.get(&func).expect("missing function plan");

                let mut obj_loc: Vec<_> = func_plan
                    .obj_loc
                    .iter()
                    .map(|(obj, loc)| (obj.as_u32(), obj_loc_summary(*loc)))
                    .collect();
                obj_loc.sort_unstable_by_key(|(obj, _)| *obj);

                let mut alloca_loc: Vec<_> = func_plan
                    .alloca_loc
                    .iter()
                    .map(|(inst, loc)| (inst.as_u32(), obj_loc_summary(*loc)))
                    .collect();
                alloca_loc.sort_unstable_by_key(|(inst, _)| *inst);

                let mut call_preserve: Vec<_> = func_plan
                    .call_preserve
                    .iter()
                    .map(|(inst, plan)| (inst.as_u32(), call_preserve_summary(plan)))
                    .collect();
                call_preserve.sort_unstable_by_key(|(inst, _)| *inst);

                (
                    name,
                    obj_loc,
                    alloca_loc,
                    call_preserve,
                    func_plan.scratch_words,
                    func_plan.stable_words,
                    stable_mode_summary(func_plan.stable_mode),
                    func_plan.entry_abs_words,
                )
            })
            .collect();

        (
            ctx.plan.scratch_peak_words,
            ctx.plan.static_chain_peak_words,
            ctx.plan.global_dyn_base,
            funcs,
            per_func,
        )
    }

    fn alloca_insts(module: &Module, isa: &Evm, func: FuncRef) -> Vec<InstId> {
        module.func_store.view(func, |function| {
            let mut allocas: Vec<InstId> = Vec::new();
            for block in function.layout.iter_block() {
                for inst in function.layout.iter_inst(block) {
                    if matches!(
                        sonatina_ir::InstSetExt::resolve_inst(
                            isa.inst_set(),
                            function.dfg.inst(inst)
                        ),
                        EvmInstKind::Alloca(_)
                    ) {
                        allocas.push(inst);
                    }
                }
            }
            allocas.sort_unstable_by_key(|inst| inst.as_u32());
            allocas
        })
    }

    fn first_call_inst(module: &Module, func: FuncRef) -> InstId {
        module.func_store.view(func, |function| {
            for block in function.layout.iter_block() {
                for inst in function.layout.iter_inst(block) {
                    if function.dfg.call_info(inst).is_some() {
                        return inst;
                    }
                }
            }
            panic!("missing call in func {}", func.as_u32());
        })
    }

    fn problem_from_src(
        src: &str,
        func_name: &str,
        cost_model: &ArenaCostModel,
    ) -> (PlacementProblem<'static>, bool) {
        let parsed = parse_module(src).unwrap();
        let module = Box::leak(Box::new(parsed.module));
        let funcs = module.funcs();
        let isa = Box::leak(Box::new(test_isa()));
        let cost_model = Box::leak(Box::new(*cost_model));
        let ptr_escape = Box::leak(Box::new(
            super::super::ptr_escape::compute_ptr_escape_summaries(module, &funcs, isa),
        ));

        let mut analyses: FxHashMap<FuncRef, FuncAnalysis> = FxHashMap::default();
        for &func in &funcs {
            module.func_store.modify(func, |function| {
                analyses.insert(func, build_analysis(function, 16));
            });
        }

        let funcs_set: FxHashSet<FuncRef> = funcs.iter().copied().collect();
        let call_graph = CallGraph::build_graph_subset(module, &funcs_set);
        let scc = SccBuilder::new().compute_scc(&call_graph);

        let mut names: FxHashMap<String, FuncRef> = FxHashMap::default();
        for &func in &funcs {
            let name = module.ctx.func_sig(func, |sig| sig.name().to_string());
            names.insert(name, func);
        }
        let func = names[func_name];
        let analysis = analyses.remove(&func).expect("missing analysis");
        let alloc_ctx = StaticArenaAllocCtx::new(&module.ctx, isa, ptr_escape);
        let stack = Box::leak(Box::new(module.func_store.view(func, |function| {
            alloc_ctx.compute_func_stack_objects(func, function, &analysis)
        })));
        let scc_ref = scc.scc_ref(func);
        let is_recursive = scc.scc_info(scc_ref).is_cycle;
        let facts = Box::leak(Box::new(build_planner_facts(
            stack,
            &scc,
            scc_ref,
            is_recursive,
        )));
        (
            PlacementProblem::new(stack, facts, is_recursive, cost_model),
            is_recursive,
        )
    }

    fn score_from_full_eval(
        problem: &PlacementProblem<'_>,
        state: &PlacementState,
        eval: &FuncPlacementEval,
    ) -> FuncPlacementScore {
        FuncPlacementScore {
            scratch_words: eval.scratch_words,
            stable_words: eval.stable_words,
            cost: placement_cost(
                problem,
                state.recursive_access_cost,
                shadow_copy_words(&eval.call_preserve),
                eval.scratch_words,
                eval.stable_words,
            ),
        }
    }

    fn state_from_mask(problem: &PlacementProblem<'_>, mask: usize) -> PlacementState {
        let mut state = PlacementState::new(problem);
        for candidate_idx in 0..problem.candidates.len() {
            if mask & (1 << candidate_idx) != 0 {
                state.apply_add(problem, candidate_idx);
            }
        }
        state
    }

    fn eval_state_score(
        problem: &PlacementProblem<'_>,
        state: &PlacementState,
        workspace: &mut FuncPlacementWorkspace,
    ) -> FuncPlacementScore {
        let promoted_optional = problem.promoted_optional(state);
        let eval = evaluate_func_placement(problem, &promoted_optional, state, workspace);
        score_from_full_eval(problem, state, &eval)
    }

    fn next_state_for_move(
        problem: &PlacementProblem<'_>,
        state: &PlacementState,
        mv: PlacementMove,
    ) -> PlacementState {
        let mut next_state = state.clone();
        match mv {
            PlacementMove::None => {}
            PlacementMove::Add(candidate_idx) => next_state.apply_add(problem, candidate_idx),
            PlacementMove::Remove(candidate_idx) => next_state.apply_remove(problem, candidate_idx),
            PlacementMove::Swap {
                add_idx,
                remove_idx,
            } => {
                next_state.apply_swap(problem, add_idx, remove_idx);
            }
        }
        next_state
    }

    fn solve_problem_score(problem: &PlacementProblem<'_>) -> FuncPlacementScore {
        let mut state = PlacementState::new(problem);
        let mut lb_state = PlacementLowerBoundState::new(problem);
        let mut score_workspace = FuncPlacementScoreWorkspace::default();
        let mut search_work = SearchWorkBuffers::default();
        let mut current_score = evaluate_func_placement_score(
            problem,
            &state,
            PlacementMove::None,
            &mut score_workspace,
        );

        loop {
            if let Some(best_move) = find_best_exact_one_flip_move(
                problem,
                &state,
                &mut lb_state,
                current_score,
                &mut score_workspace,
                &mut search_work,
            ) {
                apply_placement_move(problem, &mut state, &mut lb_state, best_move.mv);
                current_score = best_move.exact;
                continue;
            }
            if let Some(best_move) = find_best_exact_swap_move(
                problem,
                &state,
                &mut lb_state,
                current_score,
                &mut score_workspace,
                &mut search_work,
            ) {
                apply_placement_move(problem, &mut state, &mut lb_state, best_move.mv);
                current_score = best_move.exact;
                continue;
            }
            return current_score;
        }
    }

    #[test]
    fn visible_alloca_uses_static_stable_abs() {
        let ctx = plan_ctx_from_src(
            r#"
target = "evm-ethereum-osaka"

func public %callee(v0.*i256) -> i256 {
block0:
    mstore v0 1.i256 i256;
    return 0.i256;
}

func public %caller() -> i256 {
block0:
    v0.*i256 = alloca i256;
    v1.i256 = call %callee v0;
    v2.i256 = mload v0 i256;
    return v2;
}
"#,
            &ArenaCostModel::default(),
        );

        let caller = ctx.names["caller"];
        let alloca = alloca_insts(&ctx.module, &ctx.isa, caller)[0];
        let func_plan = &ctx.plan.funcs[&caller];
        assert!(matches!(
            func_plan.stable_mode,
            StableMode::StaticAbs { .. }
        ));
        assert!(matches!(
            func_plan.alloca_loc[&alloca],
            ObjLoc::StableAbs(_)
        ));

        let call_inst = first_call_inst(&ctx.module, caller);
        assert!(
            !func_plan.call_preserve.contains_key(&call_inst),
            "callee-visible alloca should not use fallback preservation"
        );
    }

    #[test]
    fn non_recursive_cross_call_local_prefers_static_stable_abs() {
        let ctx = plan_ctx_from_src(
            r#"
target = "evm-ethereum-osaka"

func public %callee(v0.i256, v1.i256) -> i256 {
block0:
    v2.*i256 = alloca i256;
    mstore v2 v0 i256;
    v3.i256 = mload v2 i256;
    v4.i256 = add v3 v1;
    return v4;
}

func public %caller() -> i256 {
block0:
    v0.*i256 = alloca i256;
    mstore v0 1.i256 i256;
    v1.i256 = call %callee 11.i256 22.i256;
    v2.i256 = mload v0 i256;
    v3.i256 = add v1 v2;
    return v3;
}
"#,
            &ArenaCostModel::default(),
        );

        let caller = ctx.names["caller"];
        let alloca = alloca_insts(&ctx.module, &ctx.isa, caller)[0];
        let func_plan = &ctx.plan.funcs[&caller];
        assert!(matches!(
            func_plan.stable_mode,
            StableMode::StaticAbs { .. }
        ));
        assert!(matches!(
            func_plan.alloca_loc[&alloca],
            ObjLoc::StableAbs(_)
        ));
        assert!(
            func_plan.call_preserve.is_empty(),
            "stable non-recursive local should not need fallback preserve"
        );
    }

    #[test]
    fn recursive_scratch_preserve_uses_dynamic_frame_only_for_shadow() {
        let cost_model = ArenaCostModel {
            w_save: 0,
            w_code: 0,
            ..ArenaCostModel::default()
        };
        let ctx = plan_ctx_from_src(
            r#"
target = "evm-ethereum-osaka"

func public %f() -> i256 {
block0:
    v0.*i256 = alloca i256;
    mstore v0 1.i256 i256;
    v1.i256 = call %f;
    v2.i256 = mload v0 i256;
    v3.i256 = add v1 v2;
    return v3;
}
"#,
            &cost_model,
        );

        let f = ctx.names["f"];
        let alloca = alloca_insts(&ctx.module, &ctx.isa, f)[0];
        let func_plan = &ctx.plan.funcs[&f];
        assert!(matches!(func_plan.stable_mode, StableMode::DynamicFrame));
        assert!(matches!(
            func_plan.alloca_loc[&alloca],
            ObjLoc::ScratchAbs(_)
        ));

        let call_inst = first_call_inst(&ctx.module, f);
        let preserve = func_plan
            .call_preserve
            .get(&call_inst)
            .expect("expected recursive shadow preserve plan");
        let PreserveMode::ShadowRuns { shadow_obj, .. } = &preserve.mode else {
            panic!("expected recursive shadow preserve plan");
        };
        assert!(matches!(
            func_plan.obj_loc[shadow_obj],
            ObjLoc::StableFrame(_)
        ));
    }

    #[test]
    fn recursive_visible_alloca_uses_stable_frame() {
        let ctx = plan_ctx_from_src(
            r#"
target = "evm-ethereum-osaka"

func public %f(v0.*i256) -> i256 {
block0:
    v1.*i256 = alloca i256;
    mstore v1 0.i256 i256;
    v2.i256 = call %f v1;
    return v2;
}
"#,
            &ArenaCostModel::default(),
        );

        let f = ctx.names["f"];
        let alloca = alloca_insts(&ctx.module, &ctx.isa, f)[0];
        let func_plan = &ctx.plan.funcs[&f];
        assert!(matches!(func_plan.stable_mode, StableMode::DynamicFrame));
        assert!(matches!(
            func_plan.alloca_loc[&alloca],
            ObjLoc::StableFrame(_)
        ));
    }

    #[test]
    fn static_chain_prefixes_accumulate_across_calls() {
        let ctx = plan_ctx_from_src(
            r#"
target = "evm-ethereum-osaka"

func public %d(v0.*i256) -> i256 {
block0:
    mstore v0 1.i256 i256;
    return 0.i256;
}

func public %c(v0.*i256) -> i256 {
block0:
    v1.*i256 = alloca i256;
    v2.i256 = call %d v1;
    return v2;
}

func public %b(v0.*i256) -> i256 {
block0:
    v1.*i256 = alloca i256;
    v2.i256 = call %c v1;
    return v2;
}

func public %a(v0.*i256) -> i256 {
block0:
    v1.*i256 = alloca i256;
    v2.i256 = call %b v1;
    return v2;
}
"#,
            &ArenaCostModel::default(),
        );

        let a = ctx.names["a"];
        let b = ctx.names["b"];
        let c = ctx.names["c"];
        let a_plan = &ctx.plan.funcs[&a];
        let b_plan = &ctx.plan.funcs[&b];
        let c_plan = &ctx.plan.funcs[&c];
        let a_base = a_plan.stable_base_word().expect("missing a base");
        let b_base = b_plan.stable_base_word().expect("missing b base");
        let c_base = c_plan.stable_base_word().expect("missing c base");
        assert!(b_base >= a_base + a_plan.stable_words);
        assert!(c_base >= b_base + b_plan.stable_words);
    }

    #[test]
    fn compute_program_memory_plan_is_deterministic_across_runs() {
        let src = r#"
target = "evm-ethereum-osaka"

func public %leaf(v0.*i256) -> i256 {
block0:
    mstore v0 1.i256 i256;
    return 0.i256;
}

func public %chain(v0.*i256) -> i256 {
block0:
    v1.*i256 = alloca i256;
    v2.i256 = call %leaf v1;
    return v2;
}

func public %recur(v0.*i256, v1.i256) -> i256 {
block0:
    v2.i1 = eq v1 0.i256;
    br v2 block1 block2;

block1:
    return 0.i256;

block2:
    v3.*i256 = alloca i256;
    mstore v3 v1 i256;
    v4.i256 = sub v1 1.i256;
    v5.i256 = call %recur v3 v4;
    v6.i256 = call %chain v3;
    v7.i256 = add v5 v6;
    return v7;
}
"#;

        let cost_model = ArenaCostModel::default();
        let expected = plan_summary(&plan_ctx_from_src(src, &cost_model));
        for _ in 0..8 {
            let actual = plan_summary(&plan_ctx_from_src(src, &cost_model));
            assert_eq!(actual, expected, "memory plan changed across runs");
        }
    }

    #[test]
    fn streamed_func_placement_score_matches_full_eval() {
        let cost_model = ArenaCostModel::default();
        let (problem, is_recursive) = problem_from_src(
            r#"
target = "evm-ethereum-osaka"

func public %f() -> i256 {
block0:
    v0.*i256 = alloca i256;
    v1.*i256 = alloca i256;
    mstore v0 1.i256 i256;
    mstore v1 2.i256 i256;
    v2.i256 = call %f;
    v3.i256 = mload v0 i256;
    v4.i256 = mload v1 i256;
    v5.i256 = add v2 v3;
    v6.i256 = add v5 v4;
    return v6;
}
"#,
            "f",
            &cost_model,
        );
        assert!(is_recursive, "test expects a recursive function");
        assert_eq!(problem.candidates.len(), 2, "test expects two candidates");

        for mask in 0..(1usize << problem.candidates.len()) {
            let state = state_from_mask(&problem, mask);
            let mut score_workspace = FuncPlacementScoreWorkspace::default();

            let promoted_optional = problem.promoted_optional(&state);
            let mut workspace = FuncPlacementWorkspace {
                scratch_pack: Vec::with_capacity(problem.sorted_objects.len()),
                shadow_objs: Vec::with_capacity(problem.sorted_calls.len()),
                stable_pack: Vec::with_capacity(
                    problem
                        .sorted_objects
                        .len()
                        .saturating_add(problem.sorted_calls.len()),
                ),
            };
            let eval =
                evaluate_func_placement(&problem, &promoted_optional, &state, &mut workspace);
            assert_eq!(
                evaluate_func_placement_score(
                    &problem,
                    &state,
                    PlacementMove::None,
                    &mut score_workspace,
                ),
                score_from_full_eval(&problem, &state, &eval),
                "baseline streamed score mismatch for promoted mask {mask:b}"
            );

            for candidate_idx in 0..problem.candidates.len() {
                if state.promoted[candidate_idx] {
                    let mut next_state = state.clone();
                    next_state.apply_remove(&problem, candidate_idx);
                    let next_promoted = problem.promoted_optional(&next_state);
                    let next_eval = evaluate_func_placement(
                        &problem,
                        &next_promoted,
                        &next_state,
                        &mut workspace,
                    );
                    assert_eq!(
                        evaluate_func_placement_score(
                            &problem,
                            &state,
                            PlacementMove::Remove(candidate_idx),
                            &mut score_workspace,
                        ),
                        score_from_full_eval(&problem, &next_state, &next_eval),
                        "remove-trial streamed score mismatch for candidate {candidate_idx} in mask {mask:b}"
                    );
                } else {
                    let mut next_state = state.clone();
                    next_state.apply_add(&problem, candidate_idx);
                    let next_promoted = problem.promoted_optional(&next_state);
                    let next_eval = evaluate_func_placement(
                        &problem,
                        &next_promoted,
                        &next_state,
                        &mut workspace,
                    );
                    assert_eq!(
                        evaluate_func_placement_score(
                            &problem,
                            &state,
                            PlacementMove::Add(candidate_idx),
                            &mut score_workspace,
                        ),
                        score_from_full_eval(&problem, &next_state, &next_eval),
                        "add-trial streamed score mismatch for candidate {candidate_idx} in mask {mask:b}"
                    );
                }
            }

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
                    let next_state = next_state_for_move(&problem, &state, mv);
                    let next_promoted = problem.promoted_optional(&next_state);
                    let next_eval = evaluate_func_placement(
                        &problem,
                        &next_promoted,
                        &next_state,
                        &mut workspace,
                    );
                    assert_eq!(
                        evaluate_func_placement_score(&problem, &state, mv, &mut score_workspace),
                        score_from_full_eval(&problem, &next_state, &next_eval),
                        "swap streamed score mismatch for add {add_idx} remove {remove_idx} in mask {mask:b}"
                    );
                }
            }
        }
    }

    #[test]
    fn placement_lower_bound_is_safe_for_all_moves() {
        let cost_model = ArenaCostModel::default();
        let (problem, is_recursive) = problem_from_src(
            r#"
target = "evm-ethereum-osaka"

func public %f() -> i256 {
block0:
    v0.*i256 = alloca i256;
    v1.*i256 = alloca i256;
    v2.*i256 = alloca i256;
    mstore v0 1.i256 i256;
    mstore v1 2.i256 i256;
    mstore v2 3.i256 i256;
    v3.i256 = call %f;
    v4.i256 = mload v0 i256;
    v5.i256 = mload v1 i256;
    v6.i256 = mload v2 i256;
    v7.i256 = add v3 v4;
    v8.i256 = add v7 v5;
    v9.i256 = add v8 v6;
    return v9;
}
"#,
            "f",
            &cost_model,
        );
        assert!(is_recursive, "test expects a recursive function");

        let mut score_workspace = FuncPlacementScoreWorkspace::default();
        for mask in 0..(1usize << problem.candidates.len()) {
            let state = state_from_mask(&problem, mask);
            let mut lb_state = PlacementLowerBoundState::new(&problem);
            for candidate_idx in 0..problem.candidates.len() {
                if state.promoted[candidate_idx] {
                    lb_state.apply_add(&problem, candidate_idx);
                }
            }

            let mut moves = vec![PlacementMove::None];
            for candidate_idx in 0..problem.candidates.len() {
                if state.promoted[candidate_idx] {
                    moves.push(PlacementMove::Remove(candidate_idx));
                } else {
                    moves.push(PlacementMove::Add(candidate_idx));
                }
            }
            for add_idx in 0..problem.candidates.len() {
                if state.promoted[add_idx] {
                    continue;
                }
                for remove_idx in 0..problem.candidates.len() {
                    if state.promoted[remove_idx] {
                        moves.push(PlacementMove::Swap {
                            add_idx,
                            remove_idx,
                        });
                    }
                }
            }

            for mv in moves {
                let lower_bound =
                    evaluate_func_placement_lower_bound(&problem, &state, &mut lb_state, mv);
                let exact =
                    evaluate_func_placement_score(&problem, &state, mv, &mut score_workspace);
                assert!(
                    lower_bound.scratch_words <= exact.scratch_words,
                    "scratch lower bound exceeded exact score for move {:?} in mask {mask:b}",
                    mv
                );
                assert!(
                    lower_bound.stable_words <= exact.stable_words,
                    "stable lower bound exceeded exact score for move {:?} in mask {mask:b}",
                    mv
                );
                assert!(
                    lower_bound.cost <= exact.cost,
                    "cost lower bound exceeded exact score for move {:?} in mask {mask:b}",
                    mv
                );
            }
        }
    }

    #[test]
    fn local_search_matches_exhaustive_optimum_on_small_problem() {
        let cost_model = ArenaCostModel::default();
        let (problem, is_recursive) = problem_from_src(
            r#"
target = "evm-ethereum-osaka"

func public %f() -> i256 {
block0:
    v0.*i256 = alloca i256;
    v1.*i256 = alloca i256;
    v2.*i256 = alloca i256;
    mstore v0 1.i256 i256;
    mstore v1 2.i256 i256;
    mstore v2 3.i256 i256;
    v3.i256 = call %f;
    v4.i256 = mload v0 i256;
    v5.i256 = mload v1 i256;
    v6.i256 = mload v2 i256;
    v7.i256 = add v3 v4;
    v8.i256 = add v7 v5;
    v9.i256 = add v8 v6;
    return v9;
}
"#,
            "f",
            &cost_model,
        );
        assert!(is_recursive, "test expects a recursive function");
        assert_eq!(problem.candidates.len(), 3, "test expects three candidates");

        let mut workspace = FuncPlacementWorkspace {
            scratch_pack: Vec::with_capacity(problem.sorted_objects.len()),
            shadow_objs: Vec::with_capacity(problem.sorted_calls.len()),
            stable_pack: Vec::with_capacity(
                problem
                    .sorted_objects
                    .len()
                    .saturating_add(problem.sorted_calls.len()),
            ),
        };
        let mut best = None;
        for mask in 0..(1usize << problem.candidates.len()) {
            let state = state_from_mask(&problem, mask);
            let score = eval_state_score(&problem, &state, &mut workspace);
            if best.is_none_or(|current| is_better_score(score, current)) {
                best = Some(score);
            }
        }

        assert_eq!(
            solve_problem_score(&problem),
            best.expect("missing exhaustive optimum"),
        );
    }
}
