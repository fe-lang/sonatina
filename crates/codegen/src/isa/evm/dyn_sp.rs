use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{InstId, Module, module::FuncRef};

use crate::module_analysis::{CallGraph, SccBuilder};

use super::{
    machine::lazy_frame::FrameSummary,
    memory_plan::{self, FuncMemPlan},
};

#[derive(Clone, Default)]
pub(crate) struct FuncDynSpPlan {
    pub(crate) entry_init: Option<DynSpInitKind>,
    pub(crate) frontier_init_calls: FxHashSet<InstId>,
    pub(crate) checked_frontier_init_calls: FxHashSet<InstId>,
    pub(crate) entry_live_frame: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DynSpInitKind {
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

pub(crate) fn compute_machine_dyn_sp_plan(
    module: &Module,
    funcs: &[FuncRef],
    section_entry: FuncRef,
    mem_plans: &FxHashMap<FuncRef, FuncMemPlan>,
    frame_summaries: &FxHashMap<FuncRef, FrameSummary>,
) -> FxHashMap<FuncRef, FuncDynSpPlan> {
    let funcs_set: FxHashSet<FuncRef> = funcs.iter().copied().collect();
    let call_graph = CallGraph::build_graph_subset(module, &funcs_set);
    let mut reachable_funcs = FxHashSet::default();
    let mut worklist = vec![section_entry];
    while let Some(func) = worklist.pop() {
        if !reachable_funcs.insert(func) {
            continue;
        }
        for &callee in call_graph.callee_of(func) {
            worklist.push(callee);
        }
    }

    let mut ordered_funcs = funcs.to_vec();
    ordered_funcs.sort_unstable_by_key(|func| func.as_u32());
    let mut ordered_reachable: Vec<FuncRef> = reachable_funcs.iter().copied().collect();
    ordered_reachable.sort_unstable_by_key(|func| func.as_u32());

    let scc = SccBuilder::new().compute_scc(&call_graph);
    let topo = memory_plan::topo_sort_sccs(&reachable_funcs, &call_graph, &scc);
    let mut ready_sccs = FxHashSet::default();
    for &scc_ref in &topo {
        if scc
            .scc_info(scc_ref)
            .components
            .iter()
            .copied()
            .filter(|func| reachable_funcs.contains(func))
            .any(|func| {
                mem_plans
                    .get(&func)
                    .is_some_and(FuncMemPlan::uses_dynamic_frame)
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

    let mut plans: FxHashMap<FuncRef, FuncDynSpPlan> = ordered_funcs
        .iter()
        .copied()
        .map(|func| {
            let state = entry_states.get(&func).copied().unwrap_or_default();
            (
                func,
                FuncDynSpPlan {
                    entry_init: None,
                    frontier_init_calls: FxHashSet::default(),
                    checked_frontier_init_calls: FxHashSet::default(),
                    entry_live_frame: state.maybe_live_frame,
                },
            )
        })
        .collect();

    if ready_sccs.contains(&scc.scc_ref(section_entry)) {
        let entry_live_frame = plans
            .get(&section_entry)
            .is_some_and(|plan| plan.entry_live_frame);
        plans
            .get_mut(&section_entry)
            .expect("section entry plan missing")
            .entry_init = Some(if entry_live_frame {
            DynSpInitKind::Checked
        } else {
            DynSpInitKind::Always
        });
    }

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
                    if caller_scc == callee_scc
                        || !ready_sccs.contains(&callee_scc)
                        || caller_summary.local_frame_active_before_inst(inst)
                    {
                        continue;
                    }

                    let plan = plans
                        .get_mut(&caller)
                        .unwrap_or_else(|| panic!("missing dyn-sp plan for {}", caller.as_u32()));
                    match (
                        caller_state.maybe_no_live_frame,
                        caller_state.maybe_live_frame,
                    ) {
                        (true, false) => {
                            plan.frontier_init_calls.insert(inst);
                        }
                        (true, true) => {
                            plan.frontier_init_calls.insert(inst);
                            plan.checked_frontier_init_calls.insert(inst);
                        }
                        (false, true) | (false, false) => {}
                    }
                }
            }
        });
    }

    plans
}
