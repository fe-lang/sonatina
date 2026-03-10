use cranelift_entity::{EntityRef, SecondaryMap};
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{BlockId, InstId, Module, ValueId, module::FuncRef};
use std::collections::{BTreeMap, BTreeSet};

use crate::{
    liveness::InstLiveness,
    module_analysis::{CallGraph, CallGraphSccs, SccBuilder, SccRef},
    stackalloc::StackifyAlloc,
};

use super::{
    malloc_plan::MallocEscapeKind,
    ptr_escape::PtrEscapeSummary,
    static_arena_alloc::{
        CallSiteObjects, FuncStackObjects, LiveInterval, ObjFacts, PackedObject, StackObj,
        StackObjId, StackObjKind, StaticArenaAllocCtx, pack_objects,
    },
};
use sonatina_ir::isa::evm::Evm;

pub const WORD_BYTES: u32 = 32;
pub const FREE_PTR_SLOT: u8 = 0x40;
pub const DYN_SP_SLOT: u8 = 0x80;
pub const DYN_FP_SLOT: u8 = 0xa0;
pub const STATIC_BASE: u32 = 0xc0;

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
}

#[derive(Clone, Debug)]
struct FuncPlacementEval {
    promoted_optional: FxHashSet<StackObjId>,
    scratch_offsets: FxHashMap<StackObjId, u32>,
    scratch_words: u32,
    stable_offsets: FxHashMap<StackObjId, u32>,
    stable_words: u32,
    call_preserve: FxHashMap<InstId, CallPreservePlan>,
    cost: u64,
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

    let mut stacks: FxHashMap<FuncRef, FuncStackObjects> = FxHashMap::default();
    for &func in funcs {
        let analysis = analyses.get(&func).expect("missing FuncAnalysis");
        let stack = module.func_store.view(func, |function| {
            alloc_ctx.compute_func_stack_objects(func, function, analysis)
        });
        stacks.insert(func, stack);
    }

    let mut placements: FxHashMap<FuncRef, FuncPlacementEval> = FxHashMap::default();
    for &func in funcs {
        let stack = stacks
            .get(&func)
            .unwrap_or_else(|| panic!("missing object facts for func {}", func.as_u32()));
        let scc_ref = scc.scc_ref(func);
        let is_recursive = scc.scc_info(scc_ref).is_cycle;
        let facts = build_planner_facts(stack, &scc, scc_ref, is_recursive);
        placements.insert(
            func,
            solve_func_placement(stack, &facts, is_recursive, cost_model),
        );
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
    let mut candidates: Vec<StackObjId> = facts
        .values()
        .filter(|fact| !fact.must_stable && !fact.live_across_calls.is_empty())
        .map(|fact| fact.id)
        .collect();
    candidates.sort_unstable_by_key(|id| id.as_u32());

    let mut promoted_optional: FxHashSet<StackObjId> = FxHashSet::default();
    let mut best =
        evaluate_func_placement(stack, facts, is_recursive, cost_model, &promoted_optional);

    loop {
        let mut best_candidate: Option<StackObjId> = None;
        let mut best_eval: Option<FuncPlacementEval> = None;
        for &candidate in &candidates {
            if promoted_optional.contains(&candidate) {
                continue;
            }

            let mut next = promoted_optional.clone();
            next.insert(candidate);
            let eval = evaluate_func_placement(stack, facts, is_recursive, cost_model, &next);
            if !is_better_eval(&eval, &best) {
                continue;
            }

            let replace = match (&best_candidate, &best_eval) {
                (None, None) => true,
                (Some(prev), Some(cur)) => {
                    is_better_eval(&eval, cur)
                        || (eval.cost == cur.cost && candidate.as_u32() < prev.as_u32())
                }
                _ => false,
            };
            if replace {
                best_candidate = Some(candidate);
                best_eval = Some(eval);
            }
        }

        let Some(candidate) = best_candidate else {
            break;
        };
        promoted_optional.insert(candidate);
        best = best_eval.expect("missing best eval for promoted candidate");
    }

    let promoted: Vec<StackObjId> = promoted_optional.iter().copied().collect();
    for candidate in promoted {
        if !promoted_optional.contains(&candidate) {
            continue;
        }
        let mut next = promoted_optional.clone();
        next.remove(&candidate);
        let eval = evaluate_func_placement(stack, facts, is_recursive, cost_model, &next);
        if is_better_eval(&eval, &best) {
            promoted_optional = next;
            best = eval;
        }
    }

    best.promoted_optional = promoted_optional;
    best
}

fn evaluate_func_placement(
    stack: &FuncStackObjects,
    facts: &FxHashMap<StackObjId, ObjFacts>,
    is_recursive: bool,
    cost_model: &ArenaCostModel,
    promoted_optional: &FxHashSet<StackObjId>,
) -> FuncPlacementEval {
    let mut stable_real: FxHashSet<StackObjId> = FxHashSet::default();
    for fact in facts.values() {
        if fact.must_stable || promoted_optional.contains(&fact.id) {
            stable_real.insert(fact.id);
        }
    }

    let mut scratch_pack: Vec<PackedObject> = stack
        .objects
        .iter()
        .filter(|obj| !stable_real.contains(&obj.id))
        .map(|obj| PackedObject {
            id: obj.id,
            size_words: obj.size_words,
            interval: obj.interval,
            min_offset_words: 0,
        })
        .collect();
    let (scratch_offsets, scratch_words) = pack_objects(&mut scratch_pack);

    let mut shadow_objs: Vec<StackObj> = Vec::new();
    let mut call_preserve: FxHashMap<InstId, CallPreservePlan> = FxHashMap::default();
    let mut next_obj_id = stack.next_obj_id;
    for call in &stack.call_sites {
        let Some((shadow_obj, plan)) = build_shadow_preserve_for_call(
            stack,
            call,
            &stable_real,
            &scratch_offsets,
            next_obj_id,
        ) else {
            continue;
        };
        next_obj_id = next_obj_id
            .checked_add(1)
            .expect("shadow object id overflow");
        shadow_objs.push(shadow_obj);
        call_preserve.insert(call.inst, plan);
    }

    let mut stable_pack: Vec<PackedObject> = stack
        .objects
        .iter()
        .filter(|obj| stable_real.contains(&obj.id))
        .map(|obj| PackedObject {
            id: obj.id,
            size_words: obj.size_words,
            interval: obj.interval,
            min_offset_words: 0,
        })
        .collect();
    stable_pack.extend(shadow_objs.iter().map(|obj| PackedObject {
        id: obj.id,
        size_words: obj.size_words,
        interval: obj.interval,
        min_offset_words: 0,
    }));
    let (stable_offsets, stable_words) = pack_objects(&mut stable_pack);

    let mut cost = evaluate_memory_cost(cost_model, scratch_words, stable_words);
    if is_recursive && stable_words != 0 {
        cost = cost
            .checked_add(
                cost_model
                    .w_save
                    .checked_mul(32)
                    .expect("frame setup cost overflow"),
            )
            .and_then(|cost| {
                cost.checked_add(
                    cost_model
                        .w_code
                        .checked_mul(16)
                        .expect("frame setup code cost overflow"),
                )
            })
            .expect("frame setup total cost overflow");
    }
    if is_recursive {
        for fact in facts.values() {
            if !stable_real.contains(&fact.id) {
                continue;
            }
            let access_penalty = fact.access_weight.saturating_mul(4);
            cost = cost
                .checked_add(
                    cost_model
                        .w_stack
                        .checked_mul(access_penalty)
                        .expect("frame access cost overflow"),
                )
                .expect("frame access total cost overflow");
        }
    }
    for plan in call_preserve.values() {
        let PreserveMode::ShadowRuns { runs, .. } = &plan.mode else {
            continue;
        };
        let words: u64 = runs.iter().map(|run| u64::from(run.len_words)).sum();
        let (copy_gas, copy_bytes) = if is_recursive {
            (words.saturating_mul(16), words.saturating_mul(16))
        } else {
            (words.saturating_mul(12), words.saturating_mul(12))
        };
        cost = cost
            .checked_add(
                cost_model
                    .w_save
                    .checked_mul(copy_gas)
                    .expect("shadow copy gas cost overflow"),
            )
            .and_then(|cost| {
                cost.checked_add(
                    cost_model
                        .w_code
                        .checked_mul(copy_bytes)
                        .expect("shadow copy code cost overflow"),
                )
            })
            .expect("shadow copy total cost overflow");
    }

    FuncPlacementEval {
        promoted_optional: promoted_optional.clone(),
        scratch_offsets,
        scratch_words,
        stable_offsets,
        stable_words,
        call_preserve,
        cost,
    }
}

fn build_shadow_preserve_for_call(
    stack: &FuncStackObjects,
    call: &CallSiteObjects,
    stable_real: &FxHashSet<StackObjId>,
    scratch_offsets: &FxHashMap<StackObjId, u32>,
    next_obj_id: u32,
) -> Option<(StackObj, CallPreservePlan)> {
    let mut ranges: Vec<(u32, u32)> = Vec::new();
    for &obj in &call.live_out_objs {
        if stable_real.contains(&obj) {
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
    let mut merged: Vec<(u32, u32)> = Vec::new();
    for (start, len) in ranges {
        if let Some((last_start, last_len)) = merged.last_mut() {
            let last_end = last_start
                .checked_add(*last_len)
                .expect("shadow run end overflow");
            if last_end == start {
                *last_len = last_len
                    .checked_add(len)
                    .expect("shadow run merge overflow");
                continue;
            }
        }
        merged.push((start, len));
    }

    let mut shadow_words: u32 = 0;
    let mut runs: SmallVec<[SaveRun; 2]> = smallvec![];
    for (start, len) in merged {
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

fn is_better_eval(candidate: &FuncPlacementEval, current: &FuncPlacementEval) -> bool {
    candidate.cost < current.cost
        || (candidate.cost == current.cost
            && (candidate.stable_words < current.stable_words
                || (candidate.stable_words == current.stable_words
                    && candidate.scratch_words < current.scratch_words)))
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

fn topo_sort_sccs(
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

fn build_scc_edges(
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
}
