use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    Function, InstSetExt, Module,
    inst::evm::inst_set::EvmInstKind,
    isa::{Isa, evm::Evm},
    module::FuncRef,
};
use std::collections::{BTreeMap, BTreeSet};

use crate::module_analysis::{CallGraph, CallGraphSccs, SccBuilder, SccRef};

use super::memory_plan::{FuncLocalMemInfo, MemScheme, ProgramMemoryPlan};

#[derive(Clone, Copy, Default)]
pub(crate) struct FuncMemEffects {
    pub(crate) touches_static_arena: bool,
    pub(crate) touches_scratch: bool,
    pub(crate) touches_dyn_frame: bool,
    pub(crate) touches_heap_meta: bool,
}

impl FuncMemEffects {
    fn union_with(&mut self, other: FuncMemEffects) {
        self.touches_static_arena |= other.touches_static_arena;
        self.touches_scratch |= other.touches_scratch;
        self.touches_dyn_frame |= other.touches_dyn_frame;
        self.touches_heap_meta |= other.touches_heap_meta;
    }
}

pub(crate) fn compute_func_mem_effects(
    module: &Module,
    funcs: &[FuncRef],
    plan: &ProgramMemoryPlan,
    local_mem: &FxHashMap<FuncRef, FuncLocalMemInfo>,
    isa: &Evm,
) -> FxHashMap<FuncRef, FuncMemEffects> {
    let funcs_set: FxHashSet<FuncRef> = funcs.iter().copied().collect();
    let call_graph = CallGraph::build_graph_subset(module, &funcs_set);
    let scc = SccBuilder::new().compute_scc(&call_graph);

    let topo = topo_sort_sccs(&funcs_set, &call_graph, &scc);
    let edges = build_scc_edges(&funcs_set, &call_graph, &scc, &topo);

    let mut local_effects: FxHashMap<FuncRef, FuncMemEffects> = FxHashMap::default();
    for &func in funcs {
        let scheme = plan.funcs.get(&func).map(|p| &p.scheme);
        let mem = local_mem.get(&func).copied().unwrap_or(FuncLocalMemInfo {
            persistent_words: 0,
            transient_words: 0,
            alloca_words: 0,
            persistent_alloca_words: 0,
        });

        let touches_static_arena = matches!(scheme, Some(MemScheme::StaticTree(_)))
            && (mem.persistent_words != 0 || mem.transient_words != 0);
        let touches_dyn_frame = matches!(scheme, Some(MemScheme::DynamicFrame))
            && (mem.persistent_words != 0 || mem.transient_words != 0);

        let touches_heap_meta = module
            .func_store
            .view(func, |function| func_uses_malloc(function, isa));

        local_effects.insert(
            func,
            FuncMemEffects {
                touches_static_arena,
                touches_scratch: false,
                touches_dyn_frame,
                touches_heap_meta,
            },
        );
    }

    let mut scc_effects: FxHashMap<SccRef, FuncMemEffects> = FxHashMap::default();
    for scc_ref in &topo {
        scc_effects.insert(*scc_ref, FuncMemEffects::default());
    }

    for scc_ref in &topo {
        let mut eff = FuncMemEffects::default();
        for &f in scc
            .scc_info(*scc_ref)
            .components
            .iter()
            .filter(|f| funcs_set.contains(f))
        {
            eff.union_with(local_effects.get(&f).copied().unwrap_or_default());
        }
        scc_effects.insert(*scc_ref, eff);
    }

    for &scc_ref in topo.iter().rev() {
        let mut eff = scc_effects.get(&scc_ref).copied().unwrap_or_default();
        for &callee in edges.get(&scc_ref).into_iter().flatten() {
            eff.union_with(scc_effects.get(&callee).copied().unwrap_or_default());
        }
        scc_effects.insert(scc_ref, eff);
    }

    let mut out: FxHashMap<FuncRef, FuncMemEffects> = FxHashMap::default();
    for &f in funcs {
        out.insert(f, scc_effects[&scc.scc_ref(f)]);
    }
    out
}

fn func_uses_malloc(function: &Function, isa: &Evm) -> bool {
    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            if matches!(
                isa.inst_set().resolve_inst(function.dfg.inst(inst)),
                EvmInstKind::EvmMalloc(_)
            ) {
                return true;
            }
        }
    }
    false
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

fn build_scc_edges(
    funcs: &FxHashSet<FuncRef>,
    call_graph: &CallGraph,
    scc: &CallGraphSccs,
    topo: &[SccRef],
) -> BTreeMap<SccRef, Vec<SccRef>> {
    let mut edges: BTreeMap<SccRef, BTreeSet<SccRef>> = BTreeMap::new();
    for &s in topo {
        edges.insert(s, BTreeSet::new());
    }

    for &f in funcs {
        let from = scc.scc_ref(f);
        for &callee in call_graph.callee_of(f) {
            let to = scc.scc_ref(callee);
            if from == to {
                continue;
            }
            edges.get_mut(&from).expect("missing scc").insert(to);
        }
    }

    let mut out: BTreeMap<SccRef, Vec<SccRef>> = BTreeMap::new();
    for (s, tos) in edges {
        out.insert(s, tos.into_iter().collect());
    }
    out
}
