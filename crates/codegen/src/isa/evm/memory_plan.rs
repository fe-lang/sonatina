use cranelift_entity::SecondaryMap;
use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use sonatina_ir::{BlockId, InstId, Module, ValueId, module::FuncRef};
use std::collections::{BTreeMap, BTreeSet};

use crate::{
    bitset::BitSet,
    liveness::InstLiveness,
    module_analysis::{CallGraph, CallGraphSccs, SccBuilder, SccRef},
    stackalloc::{StackifyAlloc, StackifyTrace},
};

use super::{
    frame_layout::DynamicFrameLayout,
    malloc_plan::MallocEscapeKind,
    placement_search::{FuncPlacementEval, solve_func_placement},
    ptr_escape::PtrEscapeSummary,
    static_arena_alloc::{
        FuncStackObjects, LiveRegion, ObjFacts, StackObj, StackObjId, StackObjKind,
        StaticArenaAllocCtx,
    },
};
use sonatina_ir::isa::evm::Evm;

pub use super::placement_search::ArenaCostModel;

pub const WORD_BYTES: u32 = 32;
pub const FREE_PTR_SLOT: u8 = 0x40;
pub const DYN_SP_SLOT: u8 = 0x80;
pub const STATIC_BASE: u32 = 0xa0;

#[derive(Clone, Debug)]
pub struct ProgramMemoryPlan {
    pub arena_base: u32,
    pub scratch_peak_words: u32,
    pub stable_chain_peak_words: u32,
    pub global_dyn_base: u32,
    pub funcs: FxHashMap<FuncRef, FuncMemPlan>,
    #[allow(dead_code)]
    pub sccs: FxHashMap<SccRef, SccMemPlan>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct BackendSpillReserve {
    pub(crate) scratch_words: u32,
    pub(crate) stable_words: u32,
}

impl BackendSpillReserve {
    pub(crate) fn is_empty(self) -> bool {
        self.scratch_words == 0 && self.stable_words == 0
    }

    pub(crate) fn pointwise_max(self, other: Self) -> Self {
        Self {
            scratch_words: self.scratch_words.max(other.scratch_words),
            stable_words: self.stable_words.max(other.stable_words),
        }
    }

    pub(crate) fn max_words(self) -> u32 {
        self.scratch_words.max(self.stable_words)
    }

    pub(crate) fn satisfies(self, required: Self) -> bool {
        self.scratch_words >= required.scratch_words && self.stable_words >= required.stable_words
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct FinalScratchReserveRange {
    pub(crate) start_word: u32,
    pub(crate) words: u32,
}

impl FinalScratchReserveRange {
    pub(crate) fn contains(self, start_word: u32, words: u32) -> bool {
        let Some(end_word) = start_word.checked_add(words) else {
            return false;
        };
        let Some(reserve_end) = self.start_word.checked_add(self.words) else {
            return false;
        };
        self.start_word <= start_word && end_word <= reserve_end
    }
}

#[derive(Clone, Debug)]
pub struct FuncMemPlan {
    pub arena_base: u32,
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
    pub fn abs_addr_for_word(&self, word: u32) -> u32 {
        abs_addr_for_word(self.arena_base, word)
    }

    pub fn stable_base_word(&self) -> Option<u32> {
        match self.stable_mode {
            StableMode::StableAbs { base_word } => Some(base_word),
            StableMode::None | StableMode::DynamicFrame => None,
        }
    }

    pub fn dynamic_frame_layout(&self) -> Option<DynamicFrameLayout> {
        matches!(self.stable_mode, StableMode::DynamicFrame)
            .then(|| DynamicFrameLayout::new(self.stable_words))
            .flatten()
    }

    pub fn uses_dynamic_frame(&self) -> bool {
        matches!(self.stable_mode, StableMode::DynamicFrame)
    }

    pub fn abs_words_end(&self) -> u32 {
        let stable_end = match self.stable_mode {
            StableMode::StableAbs { base_word } if self.stable_words != 0 => base_word
                .checked_add(self.stable_words)
                .expect("stable absolute end overflow"),
            StableMode::None | StableMode::DynamicFrame | StableMode::StableAbs { .. } => 0,
        };
        self.scratch_words.max(stable_end)
    }

    pub fn active_abs_words(&self) -> u32 {
        self.entry_abs_words.max(self.abs_words_end())
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

impl ProgramMemoryPlan {
    pub(crate) fn set_arena_base(&mut self, arena_base: u32) {
        self.arena_base = arena_base;
        let global_dyn_base_words = self
            .scratch_peak_words
            .checked_add(self.stable_chain_peak_words)
            .expect("global dynamic base word overflow");
        self.global_dyn_base = abs_addr_for_word(arena_base, global_dyn_base_words);

        for func_plan in self.funcs.values_mut() {
            func_plan.arena_base = arena_base;
            if func_plan.uses_dynamic_frame() {
                func_plan.entry_abs_words = global_dyn_base_words;
            }
        }
    }

    pub(crate) fn apply_backend_spill_reserves(
        &mut self,
        module: &Module,
        funcs: &[FuncRef],
        reserves: &FxHashMap<FuncRef, BackendSpillReserve>,
    ) {
        if reserves.values().all(|reserve| reserve.is_empty()) {
            return;
        }

        for (&func, &reserve) in reserves {
            if !reserve.is_empty()
                && let Some(func_plan) = self.funcs.get_mut(&func)
            {
                func_plan.scratch_words = func_plan
                    .scratch_words
                    .checked_add(reserve.scratch_words)
                    .expect("backend scratch spill reserve overflow");
                func_plan.stable_words = func_plan
                    .stable_words
                    .checked_add(reserve.stable_words)
                    .expect("backend stable spill reserve overflow");
            }
        }

        self.scratch_peak_words = self
            .funcs
            .values()
            .map(|func_plan| func_plan.scratch_words)
            .max()
            .unwrap_or(0);

        let funcs_set: FxHashSet<FuncRef> = funcs.iter().copied().collect();
        let call_graph = CallGraph::build_graph_subset(module, &funcs_set);
        let scc = SccBuilder::new().compute_scc(&call_graph);
        let topo = topo_sort_sccs(&funcs_set, &call_graph, &scc);
        let scc_edges = build_scc_edges(&funcs_set, &call_graph, &scc, &topo);

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
                    weight = weight.max(self.funcs[&func].stable_words);
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

        self.stable_chain_peak_words = topo
            .iter()
            .map(|scc_ref| {
                scc_prefix[scc_ref]
                    .checked_add(scc_weights[scc_ref])
                    .expect("static chain peak overflow")
            })
            .max()
            .unwrap_or(0);
        let global_dyn_base_words = self
            .scratch_peak_words
            .checked_add(self.stable_chain_peak_words)
            .expect("global dynamic base word overflow");
        self.global_dyn_base = abs_addr_for_word(self.arena_base, global_dyn_base_words);

        for &scc_ref in &topo {
            self.sccs.insert(
                scc_ref,
                SccMemPlan {
                    is_recursive: scc.scc_info(scc_ref).is_cycle,
                    static_chain_prefix_words: scc_prefix[&scc_ref],
                },
            );
        }

        for &func in funcs {
            let scc_ref = scc.scc_ref(func);
            let scc_plan = self
                .sccs
                .get(&scc_ref)
                .unwrap_or_else(|| panic!("missing SCC plan for scc {}", scc_ref.as_u32()));
            let stable_base_word = self
                .scratch_peak_words
                .checked_add(scc_plan.static_chain_prefix_words)
                .expect("stable base word overflow");
            let func_plan = self
                .funcs
                .get_mut(&func)
                .unwrap_or_else(|| panic!("missing memory plan for func {}", func.as_u32()));
            func_plan.stable_mode = if scc_plan.is_recursive {
                StableMode::DynamicFrame
            } else if func_plan.stable_words != 0 {
                StableMode::StableAbs {
                    base_word: stable_base_word,
                }
            } else {
                StableMode::None
            };
            func_plan.entry_abs_words = if scc_plan.is_recursive {
                global_dyn_base_words
            } else {
                stable_base_word
            };
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use sonatina_parser::parse_module;

    fn empty_func_plan(scratch_words: u32, stable_mode: StableMode) -> FuncMemPlan {
        FuncMemPlan {
            arena_base: STATIC_BASE,
            scratch_words,
            stable_words: 0,
            stable_mode,
            entry_abs_words: scratch_words,
            obj_loc: FxHashMap::default(),
            alloca_loc: FxHashMap::default(),
            spill_obj: SecondaryMap::new(),
            call_preserve: FxHashMap::default(),
            malloc_future_abs_words: FxHashMap::default(),
            transient_mallocs: FxHashSet::default(),
            malloc_escape_kinds: FxHashMap::default(),
            return_escape_caller_abs_words: 0,
        }
    }

    #[test]
    fn backend_spill_reserve_creates_stable_frame_for_functions_without_stable_frame() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func public %entry() {
block0:
    return;
}
"#,
        )
        .expect("module parses");
        let func = parsed.module.funcs()[0];
        let mut plan = ProgramMemoryPlan {
            arena_base: STATIC_BASE,
            scratch_peak_words: 3,
            stable_chain_peak_words: 0,
            global_dyn_base: abs_addr_for_word(STATIC_BASE, 3),
            funcs: FxHashMap::from_iter([(func, empty_func_plan(3, StableMode::None))]),
            sccs: FxHashMap::default(),
        };
        let reserve_words = FxHashMap::from_iter([(
            func,
            BackendSpillReserve {
                scratch_words: 0,
                stable_words: 2,
            },
        )]);

        plan.apply_backend_spill_reserves(&parsed.module, &[func], &reserve_words);

        let func_plan = &plan.funcs[&func];
        assert_eq!(func_plan.scratch_words, 3);
        assert_eq!(func_plan.stable_words, 2);
        assert_eq!(
            func_plan.stable_mode,
            StableMode::StableAbs { base_word: 3 }
        );
        assert_eq!(plan.scratch_peak_words, 3);
        assert_eq!(plan.global_dyn_base, abs_addr_for_word(STATIC_BASE, 5));
    }

    #[test]
    fn backend_spill_reserve_extends_scratch_without_static_frame() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func public %entry() {
block0:
    return;
}
"#,
        )
        .expect("module parses");
        let func = parsed.module.funcs()[0];
        let mut plan = ProgramMemoryPlan {
            arena_base: STATIC_BASE,
            scratch_peak_words: 3,
            stable_chain_peak_words: 0,
            global_dyn_base: abs_addr_for_word(STATIC_BASE, 3),
            funcs: FxHashMap::from_iter([(func, empty_func_plan(3, StableMode::None))]),
            sccs: FxHashMap::default(),
        };
        let reserve_words = FxHashMap::from_iter([(
            func,
            BackendSpillReserve {
                scratch_words: 2,
                stable_words: 0,
            },
        )]);

        plan.apply_backend_spill_reserves(&parsed.module, &[func], &reserve_words);

        let func_plan = &plan.funcs[&func];
        assert_eq!(func_plan.scratch_words, 5);
        assert_eq!(func_plan.stable_words, 0);
        assert_eq!(func_plan.stable_mode, StableMode::None);
        assert_eq!(plan.scratch_peak_words, 5);
        assert_eq!(plan.global_dyn_base, abs_addr_for_word(STATIC_BASE, 5));
    }

    #[test]
    fn abs_clobber_extra_reserve_extends_scratch_end() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func public %entry() {
block0:
    return;
}
"#,
        )
        .expect("module parses");
        let func = parsed.module.funcs()[0];
        let plan = ProgramMemoryPlan {
            arena_base: STATIC_BASE,
            scratch_peak_words: 3,
            stable_chain_peak_words: 0,
            global_dyn_base: abs_addr_for_word(STATIC_BASE, 3),
            funcs: FxHashMap::from_iter([(func, empty_func_plan(3, StableMode::None))]),
            sccs: FxHashMap::default(),
        };
        let reserve_words = FxHashMap::from_iter([(
            func,
            BackendSpillReserve {
                scratch_words: 2,
                stable_words: 0,
            },
        )]);
        let clobber_words =
            compute_abs_clobber_words_with_extra(&parsed.module, &[func], &plan, &reserve_words);

        assert_eq!(clobber_words[&func], 5);
    }

    #[test]
    fn abs_clobber_extra_reserve_extends_static_stable_end() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func public %entry() {
block0:
    return;
}
"#,
        )
        .expect("module parses");
        let func = parsed.module.funcs()[0];
        let mut func_plan = empty_func_plan(1, StableMode::StableAbs { base_word: 4 });
        func_plan.stable_words = 4;
        let plan = ProgramMemoryPlan {
            arena_base: STATIC_BASE,
            scratch_peak_words: 1,
            stable_chain_peak_words: 4,
            global_dyn_base: abs_addr_for_word(STATIC_BASE, 5),
            funcs: FxHashMap::from_iter([(func, func_plan)]),
            sccs: FxHashMap::default(),
        };
        let reserve_words = FxHashMap::from_iter([(
            func,
            BackendSpillReserve {
                scratch_words: 0,
                stable_words: 2,
            },
        )]);
        let clobber_words =
            compute_abs_clobber_words_with_extra(&parsed.module, &[func], &plan, &reserve_words);

        assert_eq!(clobber_words[&func], 10);
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
    StableAbs { base_word: u32 },
    DynamicFrame,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ObjLoc {
    ScratchAbs(u32),
    StableAbs(u32),
    /// Local dynamic-frame word offset, excluding backend metadata such as the
    /// hidden caller-SP link slot.
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

pub(crate) struct FuncPreAnalysis {
    pub(crate) inst_liveness: InstLiveness,
    pub(crate) block_order: Vec<BlockId>,
    pub(crate) value_aliases: SecondaryMap<ValueId, Option<ValueId>>,
}

pub(crate) struct MachineStackifyAnalysis {
    pub(crate) alloc: StackifyAlloc,
    pub(crate) block_order: Vec<BlockId>,
    pub(crate) stable_final_spill_values: BitSet<ValueId>,
    pub(crate) trace: Option<StackifyTrace>,
}

pub(crate) fn compute_semantic_program_memory_plan(
    module: &Module,
    funcs: &[FuncRef],
    analyses: &FxHashMap<FuncRef, FuncPreAnalysis>,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
    isa: &Evm,
    cost_model: &ArenaCostModel,
) -> ProgramMemoryPlan {
    let alloc_ctx = StaticArenaAllocCtx::new(&module.ctx, isa, ptr_escape);
    let mut stack_results: Vec<_> = funcs
        .par_iter()
        .copied()
        .map(|func| {
            let analysis = analyses.get(&func).expect("missing FuncPreAnalysis");
            let stack = module.func_store.view(func, |function| {
                alloc_ctx.compute_func_semantic_stack_objects(func, function, analysis)
            });
            (func, stack)
        })
        .collect();
    stack_results.sort_unstable_by_key(|(func, _)| func.as_u32());

    let mut stacks: FxHashMap<FuncRef, FuncStackObjects> = FxHashMap::default();
    for (func, stack) in stack_results {
        stacks.insert(func, stack);
    }

    let plan = compute_program_memory_plan_from_stacks(module, funcs, &stacks, cost_model);

    #[cfg(debug_assertions)]
    {
        let funcs_set: FxHashSet<FuncRef> = funcs.iter().copied().collect();
        let call_graph = CallGraph::build_graph_subset(module, &funcs_set);
        let scc = SccBuilder::new().compute_scc(&call_graph);
        verify_program_memory_plan(funcs, &stacks, &scc, &plan);
    }

    plan
}

fn compute_program_memory_plan_from_stacks(
    module: &Module,
    funcs: &[FuncRef],
    stacks: &FxHashMap<FuncRef, FuncStackObjects>,
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

    let stable_chain_peak_words = topo
        .iter()
        .map(|scc_ref| {
            scc_prefix[scc_ref]
                .checked_add(scc_weights[scc_ref])
                .expect("static chain peak overflow")
        })
        .max()
        .unwrap_or(0);

    let arena_base = STATIC_BASE;
    let global_dyn_base = abs_addr_for_word(
        arena_base,
        scratch_peak_words
            .checked_add(stable_chain_peak_words)
            .expect("global dynamic base word overflow"),
    );
    let global_dyn_base_words = scratch_peak_words
        .checked_add(stable_chain_peak_words)
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
            StableMode::StableAbs {
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
                StableMode::StableAbs { .. } => ObjLoc::StableAbs(word),
                StableMode::DynamicFrame => ObjLoc::StableFrame(word),
            };
            obj_loc.insert(obj, loc);
        }

        let mut alloca_loc: FxHashMap<InstId, ObjLoc> = FxHashMap::default();
        for (inst, id) in &stack.alloca_ids {
            let loc = obj_loc.get(id).copied().unwrap_or_else(|| {
                if stack.obj_size_words.get(id).copied() == Some(0) {
                    ObjLoc::ScratchAbs(0)
                } else {
                    panic!(
                        "missing object location for alloca inst {} in func {}",
                        inst.as_u32(),
                        func.as_u32()
                    )
                }
            });
            alloca_loc.insert(*inst, loc);
        }

        funcs_plan.insert(
            func,
            FuncMemPlan {
                arena_base,
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

    ProgramMemoryPlan {
        arena_base,
        scratch_peak_words,
        stable_chain_peak_words,
        global_dyn_base,
        funcs: funcs_plan,
        sccs: scc_plans,
    }
}

pub(crate) fn compute_abs_clobber_words_with_extra(
    module: &Module,
    funcs: &[FuncRef],
    plan: &ProgramMemoryPlan,
    extra_reserves: &FxHashMap<FuncRef, BackendSpillReserve>,
) -> FxHashMap<FuncRef, u32> {
    let funcs_set: FxHashSet<FuncRef> = funcs.iter().copied().collect();
    let mut out: FxHashMap<FuncRef, u32> = FxHashMap::default();
    for &func in funcs {
        let extra_reserve = extra_reserves.get(&func).copied().unwrap_or_default();
        let Some(func_plan) = plan.funcs.get(&func) else {
            out.insert(func, extra_reserve.max_words());
            continue;
        };
        let local = abs_words_end_with_extra_reserve(func_plan, extra_reserve);
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

fn abs_words_end_with_extra_reserve(
    func_plan: &FuncMemPlan,
    extra_reserve: BackendSpillReserve,
) -> u32 {
    let scratch_end = func_plan
        .scratch_words
        .checked_add(extra_reserve.scratch_words)
        .expect("scratch reserve overflow");
    let stable_end = match func_plan.stable_mode {
        StableMode::None => extra_reserve.stable_words,
        StableMode::StableAbs { base_word } => {
            if func_plan.stable_words == 0 && extra_reserve.stable_words == 0 {
                0
            } else {
                base_word
                    .checked_add(func_plan.stable_words)
                    .and_then(|end| end.checked_add(extra_reserve.stable_words))
                    .expect("stable reserve overflow")
            }
        }
        StableMode::DynamicFrame => 0,
    };

    scratch_end.max(stable_end)
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

fn abs_addr_for_word(arena_base: u32, word: u32) -> u32 {
    arena_base
        .checked_add(
            word.checked_mul(WORD_BYTES)
                .expect("absolute address overflow"),
        )
        .expect("absolute address overflow")
}

#[cfg(debug_assertions)]
fn verify_program_memory_plan(
    funcs: &[FuncRef],
    stacks: &FxHashMap<FuncRef, FuncStackObjects>,
    scc: &CallGraphSccs,
    plan: &ProgramMemoryPlan,
) {
    for &func in funcs {
        let Some(func_plan) = plan.funcs.get(&func) else {
            continue;
        };
        let stack = stacks.get(&func).expect("missing stack objects");
        let scc_ref = scc.scc_ref(func);
        let is_recursive = scc.scc_info(scc_ref).is_cycle;

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
                if fact.size_words == 0 {
                    continue;
                }
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
                if stack.obj_size_words.get(&obj).copied() == Some(0) {
                    continue;
                }
                let loc =
                    func_plan.obj_loc.get(&obj).copied().unwrap_or_else(|| {
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
                let loc =
                    func_plan.obj_loc.get(&obj).copied().unwrap_or_else(|| {
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
                    let Some(src_word) = func_plan.obj_loc.get(&obj).and_then(|loc| match loc {
                        ObjLoc::ScratchAbs(word) => Some(*word),
                        ObjLoc::StableAbs(_) | ObjLoc::StableFrame(_) | ObjLoc::StackPinned(_) => {
                            None
                        }
                    }) else {
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
