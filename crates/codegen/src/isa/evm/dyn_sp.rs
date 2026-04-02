use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{InstId, Module, module::FuncRef};

use crate::module_analysis::{CallGraph, SccBuilder};

use super::{
    Evm,
    emit::FinalAlloc,
    lazy_frame::{FrameSummary, compute_frame_summary},
    memory_plan::{self, ProgramMemoryPlan, topo_sort_sccs},
};

#[derive(Clone, Default)]
pub(crate) struct DynSpPlan {
    pub(crate) entry_init: bool,
    pub(crate) frontier_init_calls: FxHashMap<FuncRef, FxHashSet<InstId>>,
    pub(crate) checked_frontier_init_calls: FxHashMap<FuncRef, FxHashSet<InstId>>,
    pub(crate) entry_live_frame: FxHashMap<FuncRef, bool>,
    pub(crate) frame_summaries: FxHashMap<FuncRef, FrameSummary>,
}

#[derive(Clone, Default)]
pub(crate) struct FuncDynSpPlan {
    pub(crate) entry_init: bool,
    pub(crate) frontier_init_calls: FxHashSet<InstId>,
    pub(crate) checked_frontier_init_calls: FxHashSet<InstId>,
    pub(crate) entry_live_frame: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FrontierInitKind {
    Always,
    Checked,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct EntryFrameState {
    maybe_no_live_frame: bool,
    maybe_live_frame: bool,
}

impl EntryFrameState {
    fn no_live() -> Self {
        Self {
            maybe_no_live_frame: true,
            maybe_live_frame: false,
        }
    }

    fn live() -> Self {
        Self {
            maybe_no_live_frame: false,
            maybe_live_frame: true,
        }
    }

    fn is_reachable(self) -> bool {
        self.maybe_no_live_frame || self.maybe_live_frame
    }

    fn merge(&mut self, other: Self) -> bool {
        let next = Self {
            maybe_no_live_frame: self.maybe_no_live_frame || other.maybe_no_live_frame,
            maybe_live_frame: self.maybe_live_frame || other.maybe_live_frame,
        };
        let changed = next != *self;
        *self = next;
        changed
    }
}

pub(crate) fn compute_dyn_sp_plan(
    module: &Module,
    funcs: &[FuncRef],
    section_entry: FuncRef,
    plan: &ProgramMemoryPlan,
    analyses: &FxHashMap<FuncRef, memory_plan::FuncAnalysis>,
    isa: &Evm,
) -> DynSpPlan {
    let mut frame_summaries: FxHashMap<FuncRef, FrameSummary> = FxHashMap::default();
    for &func in funcs {
        let analysis = analyses
            .get(&func)
            .unwrap_or_else(|| panic!("missing analysis for func {}", func.as_u32()));
        let mem_plan = plan
            .funcs
            .get(&func)
            .cloned()
            .unwrap_or_else(|| panic!("missing memory plan for func {}", func.as_u32()));
        let summary = module.func_store.view(func, |function| {
            let alloc = FinalAlloc::new(analysis.alloc.clone(), mem_plan.clone());
            compute_frame_summary(function, &alloc, &mem_plan, isa)
        });
        frame_summaries.insert(func, summary);
    }

    let funcs_set: FxHashSet<FuncRef> = funcs.iter().copied().collect();
    let call_graph = CallGraph::build_graph_subset(module, &funcs_set);
    let mut reachable_funcs: FxHashSet<FuncRef> = FxHashSet::default();
    let mut worklist = vec![section_entry];
    while let Some(func) = worklist.pop() {
        if !reachable_funcs.insert(func) {
            continue;
        }
        for &callee in call_graph.callee_of(func) {
            worklist.push(callee);
        }
    }

    let mut ordered_funcs: Vec<FuncRef> = funcs.to_vec();
    ordered_funcs.sort_unstable_by_key(|func| func.as_u32());
    let mut ordered_reachable: Vec<FuncRef> = reachable_funcs.iter().copied().collect();
    ordered_reachable.sort_unstable_by_key(|func| func.as_u32());

    let scc = SccBuilder::new().compute_scc(&call_graph);
    let topo = topo_sort_sccs(&reachable_funcs, &call_graph, &scc);
    let mut ready_sccs: FxHashSet<_> = FxHashSet::default();
    for &scc_ref in &topo {
        if scc
            .scc_info(scc_ref)
            .components
            .iter()
            .copied()
            .filter(|func| reachable_funcs.contains(func))
            .any(|func| {
                plan.funcs
                    .get(&func)
                    .is_some_and(|func_plan| func_plan.frame_size_words() != 0)
            })
        {
            ready_sccs.insert(scc_ref);
        }
    }

    let mut entry_states: FxHashMap<FuncRef, EntryFrameState> = FxHashMap::default();
    entry_states.insert(section_entry, EntryFrameState::no_live());
    let mut changed = true;
    while changed {
        changed = false;
        for &caller in &ordered_reachable {
            let caller_state = entry_states.get(&caller).copied().unwrap_or_default();
            if !caller_state.is_reachable() {
                continue;
            }
            let caller_summary = frame_summaries
                .get(&caller)
                .unwrap_or_else(|| panic!("missing frame summary for func {}", caller.as_u32()));
            module.func_store.view(caller, |function| {
                for block in function.layout.iter_block() {
                    for inst in function.layout.iter_inst(block) {
                        let Some(call) = function.dfg.call_info(inst) else {
                            continue;
                        };
                        let callee = call.callee();
                        if !reachable_funcs.contains(&callee) {
                            continue;
                        }

                        let edge_state = if caller_summary.local_frame_active_before_inst(inst) {
                            EntryFrameState::live()
                        } else {
                            caller_state
                        };
                        changed |= entry_states.entry(callee).or_default().merge(edge_state);
                    }
                }
            });
        }
    }

    let entry_init = ready_sccs.contains(&scc.scc_ref(section_entry));
    let mut frontier_init_calls: FxHashMap<FuncRef, FxHashSet<InstId>> = FxHashMap::default();
    let mut checked_frontier_init_calls: FxHashMap<FuncRef, FxHashSet<InstId>> =
        FxHashMap::default();
    for &caller in &ordered_reachable {
        let caller_scc = scc.scc_ref(caller);
        if ready_sccs.contains(&caller_scc) {
            continue;
        }

        let caller_summary = frame_summaries
            .get(&caller)
            .unwrap_or_else(|| panic!("missing frame summary for func {}", caller.as_u32()));
        let caller_state = entry_states.get(&caller).copied().unwrap_or_default();
        module.func_store.view(caller, |function| {
            for block in function.layout.iter_block() {
                for inst in function.layout.iter_inst(block) {
                    let Some(call) = function.dfg.call_info(inst) else {
                        continue;
                    };
                    let callee = call.callee();
                    if !reachable_funcs.contains(&callee) {
                        continue;
                    }
                    let callee_scc = scc.scc_ref(callee);
                    if caller_scc == callee_scc || !ready_sccs.contains(&callee_scc) {
                        continue;
                    }
                    if caller_summary.local_frame_active_before_inst(inst) {
                        continue;
                    }

                    match (
                        caller_state.maybe_no_live_frame,
                        caller_state.maybe_live_frame,
                    ) {
                        (true, false) => {
                            frontier_init_calls.entry(caller).or_default().insert(inst);
                        }
                        (true, true) => {
                            frontier_init_calls.entry(caller).or_default().insert(inst);
                            checked_frontier_init_calls
                                .entry(caller)
                                .or_default()
                                .insert(inst);
                        }
                        (false, true) | (false, false) => {}
                    }
                }
            }
        });
    }

    let mut entry_live_frame: FxHashMap<FuncRef, bool> = FxHashMap::default();
    for func in ordered_funcs {
        let state = entry_states.get(&func).copied().unwrap_or_default();
        entry_live_frame.insert(func, state.maybe_live_frame);
    }

    DynSpPlan {
        entry_init,
        frontier_init_calls,
        checked_frontier_init_calls,
        entry_live_frame,
        frame_summaries,
    }
}
