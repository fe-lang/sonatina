use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    BlockId, Function, InstId, InstSetExt, Module,
    cfg::ControlFlowGraph,
    inst::evm::inst_set::EvmInstKind,
    isa::{Isa, evm::Evm},
    module::FuncRef,
};
use std::collections::{BTreeMap, BTreeSet};

use crate::module_analysis::{CallGraph, CallGraphSccs, SccBuilder, SccRef};

use super::memory_plan::{FuncLocalMemInfo, MemScheme, ProgramMemoryPlan, STATIC_BASE, WORD_BYTES};

pub(crate) fn compute_malloc_future_static_words(
    module: &Module,
    funcs: &[FuncRef],
    plan: &ProgramMemoryPlan,
    local_mem: &FxHashMap<FuncRef, FuncLocalMemInfo>,
    isa: &Evm,
) -> FxHashMap<FuncRef, FxHashMap<InstId, u32>> {
    let funcs_set: FxHashSet<FuncRef> = funcs.iter().copied().collect();
    let call_graph = CallGraph::build_graph_subset(module, &funcs_set);
    let scc = SccBuilder::new().compute_scc(&call_graph);

    let static_max_words = plan
        .dyn_base
        .checked_sub(STATIC_BASE)
        .expect("dyn base below static base")
        / WORD_BYTES;

    let mut self_bound_words: FxHashMap<FuncRef, u32> = FxHashMap::default();
    for &f in funcs {
        let scheme = plan.funcs.get(&f).map(|p| &p.scheme);
        let bound = match scheme {
            Some(MemScheme::StaticTree(st)) => local_mem.get(&f).map_or(0, |mem| {
                st.base_words
                    .checked_add(mem.persistent_words)
                    .and_then(|w| w.checked_add(mem.transient_words))
                    .expect("self static bound overflow")
            }),
            _ => 0,
        };
        self_bound_words.insert(f, bound);
    }

    let entry_bound_words = compute_entry_bounds(
        &funcs_set,
        &call_graph,
        &scc,
        &self_bound_words,
        static_max_words,
    );

    let mut out: FxHashMap<FuncRef, FxHashMap<InstId, u32>> = FxHashMap::default();
    for &f in funcs {
        let self_bound = self_bound_words.get(&f).copied().unwrap_or(0);
        let map = module.func_store.view(f, |function| {
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(function);
            compute_future_bounds_for_func(
                function,
                &cfg,
                isa,
                &entry_bound_words,
                self_bound,
                static_max_words,
            )
        });
        out.insert(f, map);
    }

    out
}

fn compute_entry_bounds(
    funcs: &FxHashSet<FuncRef>,
    call_graph: &CallGraph,
    scc: &CallGraphSccs,
    self_bounds: &FxHashMap<FuncRef, u32>,
    unknown_callee_bound: u32,
) -> FxHashMap<FuncRef, u32> {
    let topo = topo_sort_sccs(funcs, call_graph, scc);

    let mut entry: FxHashMap<FuncRef, u32> = FxHashMap::default();
    for &f in funcs {
        entry.insert(f, self_bounds.get(&f).copied().unwrap_or(0));
    }

    for scc_ref in topo.into_iter().rev() {
        let mut component: Vec<FuncRef> = scc
            .scc_info(scc_ref)
            .components
            .iter()
            .copied()
            .filter(|f| funcs.contains(f))
            .collect();
        component.sort_unstable_by_key(|f| f.as_u32());

        loop {
            let mut changed = false;

            for &f in &component {
                let mut bound = self_bounds.get(&f).copied().unwrap_or(0);
                for &callee in call_graph.callee_of(f) {
                    bound = bound.max(entry.get(&callee).copied().unwrap_or(unknown_callee_bound));
                }

                let cur = entry.get_mut(&f).expect("missing entry bound");
                if bound > *cur {
                    *cur = bound;
                    changed = true;
                }
            }

            if !changed {
                break;
            }
        }
    }

    entry
}

fn topo_sort_sccs(
    funcs: &FxHashSet<FuncRef>,
    call_graph: &CallGraph,
    scc: &CallGraphSccs,
) -> Vec<SccRef> {
    let mut sccs: BTreeSet<SccRef> = BTreeSet::new();
    for &f in funcs {
        sccs.insert(scc.scc_ref(f));
    }

    let mut edges: BTreeMap<SccRef, BTreeSet<SccRef>> = BTreeMap::new();
    let mut indegree: BTreeMap<SccRef, usize> = BTreeMap::new();
    for &s in &sccs {
        edges.insert(s, BTreeSet::new());
        indegree.insert(s, 0);
    }

    for &f in funcs {
        let from = scc.scc_ref(f);
        for &callee in call_graph.callee_of(f) {
            let to = scc.scc_ref(callee);
            if from == to {
                continue;
            }

            let tos = edges.get_mut(&from).expect("missing scc");
            if tos.insert(to) {
                *indegree.get_mut(&to).expect("missing scc") += 1;
            }
        }
    }

    let mut ready: BTreeSet<SccRef> = BTreeSet::new();
    for (&s, &deg) in &indegree {
        if deg == 0 {
            ready.insert(s);
        }
    }

    let mut topo: Vec<SccRef> = Vec::with_capacity(sccs.len());
    while let Some(&s) = ready.first() {
        ready.remove(&s);
        topo.push(s);

        let tos: Vec<SccRef> = edges
            .get(&s)
            .expect("missing scc")
            .iter()
            .copied()
            .collect();
        for to in tos {
            let deg = indegree.get_mut(&to).expect("missing scc");
            *deg = deg.checked_sub(1).expect("indegree underflow");
            if *deg == 0 {
                ready.insert(to);
            }
        }
    }

    debug_assert_eq!(topo.len(), sccs.len(), "SCC topo sort incomplete");
    topo
}

fn compute_future_bounds_for_func(
    function: &Function,
    cfg: &ControlFlowGraph,
    isa: &Evm,
    entry_bounds: &FxHashMap<FuncRef, u32>,
    self_bound_words: u32,
    unknown_callee_bound: u32,
) -> FxHashMap<InstId, u32> {
    let mut block_in: SecondaryMap<BlockId, u32> = SecondaryMap::new();
    for block in function.layout.iter_block() {
        let _ = &mut block_in[block];
    }

    let blocks: Vec<BlockId> = cfg.post_order().collect();

    let mut changed = true;
    while changed {
        changed = false;

        for &block in &blocks {
            let out = cfg.succs_of(block).map(|b| block_in[*b]).max().unwrap_or(0);

            let mut bound = out.max(self_bound_words);

            let insts: Vec<InstId> = function.layout.iter_inst(block).collect();
            for inst in insts.into_iter().rev() {
                if let Some(call) = function.dfg.call_info(inst) {
                    let callee = call.callee();
                    bound = bound.max(
                        entry_bounds
                            .get(&callee)
                            .copied()
                            .unwrap_or(unknown_callee_bound),
                    );
                }
            }

            if bound > block_in[block] {
                block_in[block] = bound;
                changed = true;
            }
        }
    }

    let mut malloc_bounds: FxHashMap<InstId, u32> = FxHashMap::default();
    for block in function.layout.iter_block() {
        let out = cfg.succs_of(block).map(|b| block_in[*b]).max().unwrap_or(0);
        let mut bound = out.max(self_bound_words);

        let insts: Vec<InstId> = function.layout.iter_inst(block).collect();
        for inst in insts.into_iter().rev() {
            let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));
            if matches!(data, EvmInstKind::EvmMalloc(_)) {
                malloc_bounds.insert(inst, bound);
            }

            if let Some(call) = function.dfg.call_info(inst) {
                let callee = call.callee();
                bound = bound.max(
                    entry_bounds
                        .get(&callee)
                        .copied()
                        .unwrap_or(unknown_callee_bound),
                );
            }
        }
    }

    malloc_bounds
}
