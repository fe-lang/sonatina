use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{BlockId, InstId, Module, ValueId, module::FuncRef};
use std::collections::{BTreeMap, BTreeSet};

use crate::{
    liveness::InstLiveness,
    module_analysis::{CallGraph, CallGraphSccs, SccBuilder, SccRef},
    stackalloc::StackifyAlloc,
};

use super::{
    ptr_escape::PtrEscapeSummary,
    static_arena_alloc::{FuncObjectLayout, StackObjId, plan_func_objects},
};
use sonatina_ir::isa::evm::Evm;

pub const WORD_BYTES: u32 = 32;
pub const FREE_PTR_SLOT: u8 = 0x40;
pub const DYN_SP_SLOT: u8 = 0x80;
pub const DYN_FP_SLOT: u8 = 0xa0;
pub const STATIC_BASE: u32 = 0xc0;

#[derive(Clone, Debug)]
pub struct ProgramMemoryPlan {
    pub dyn_base: u32,
    pub funcs: FxHashMap<FuncRef, FuncMemPlan>,
}

#[derive(Clone, Debug)]
pub struct FuncMemPlan {
    pub scheme: MemScheme,

    /// Word offsets for all stack objects in this function.
    ///
    /// For `StaticArena`, offsets are relative to `STATIC_BASE`.
    /// For `DynamicFrame`, offsets are relative to `fp`.
    pub obj_offset_words: FxHashMap<StackObjId, u32>,

    /// Convenience map for `Alloca` lowering.
    pub alloca_offset_words: FxHashMap<InstId, u32>,

    /// Convenience map for spill rewriting: ValueId -> obj id (non-scratch spills).
    pub spill_obj: SecondaryMap<ValueId, Option<StackObjId>>,

    /// Total local object extent (max offset + size), in words.
    pub locals_words: u32,

    pub malloc_future_static_words: FxHashMap<InstId, u32>,
    pub transient_mallocs: FxHashSet<InstId>,
}

#[derive(Clone, Debug)]
pub enum MemScheme {
    StaticArena(StaticArenaFuncPlan),
    DynamicFrame,
}

#[derive(Clone, Debug)]
pub struct StaticArenaFuncPlan {
    pub need_words: u32,
}

pub(crate) struct FuncAnalysis {
    pub(crate) alloc: StackifyAlloc,
    pub(crate) inst_liveness: InstLiveness,
    pub(crate) block_order: Vec<BlockId>,
}

pub(crate) fn compute_program_memory_plan(
    module: &Module,
    funcs: &[FuncRef],
    analyses: &FxHashMap<FuncRef, FuncAnalysis>,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
    isa: &Evm,
) -> ProgramMemoryPlan {
    let funcs_set: FxHashSet<FuncRef> = funcs.iter().copied().collect();
    let call_graph = CallGraph::build_graph_subset(module, &funcs_set);
    let scc = SccBuilder::new().compute_scc(&call_graph);

    let topo = topo_sort_sccs(&funcs_set, &call_graph, &scc);

    let mut static_arena_funcs: FxHashSet<FuncRef> = FxHashSet::default();
    for &f in &funcs_set {
        if !scc.scc_of(f).is_cycle {
            static_arena_funcs.insert(f);
        }
    }

    let mut need_words: FxHashMap<FuncRef, u32> = FxHashMap::default();
    let mut static_max_words: u32 = 0;
    let mut plans: FxHashMap<FuncRef, FuncMemPlan> = FxHashMap::default();

    for &scc_ref in topo.iter().rev() {
        let mut component: Vec<FuncRef> = scc
            .scc_info(scc_ref)
            .components
            .iter()
            .copied()
            .filter(|f| funcs_set.contains(f))
            .collect();
        component.sort_unstable_by_key(|f| f.as_u32());

        for func in component {
            let analysis = analyses.get(&func).expect("missing FuncAnalysis");

            let is_static = static_arena_funcs.contains(&func);
            let layout: FuncObjectLayout = module.func_store.view(func, |function| {
                let callee_need_words = |callee: FuncRef| {
                    (is_static && static_arena_funcs.contains(&callee)).then(|| {
                        need_words
                            .get(&callee)
                            .copied()
                            .expect("callee need_words missing")
                    })
                };

                plan_func_objects(
                    func,
                    function,
                    &module.ctx,
                    isa,
                    ptr_escape,
                    &analysis.alloc,
                    &analysis.inst_liveness,
                    &analysis.block_order,
                    callee_need_words,
                )
            });

            let scheme = if static_arena_funcs.contains(&func) {
                let child_need = call_graph
                    .callee_of(func)
                    .iter()
                    .filter(|c| static_arena_funcs.contains(c))
                    .map(|c| {
                        need_words
                            .get(c)
                            .copied()
                            .expect("callee need_words missing")
                    })
                    .max()
                    .unwrap_or(0);
                let need = layout.locals_words.max(child_need);

                #[cfg(debug_assertions)]
                if std::env::var_os("SONATINA_EVM_MEM_VERIFY").is_some()
                    && (need < layout.locals_words || need < child_need)
                {
                    panic!(
                        "StaticArena need_words violated in func {}: need_words={need}, locals_words={}, child_need={child_need}",
                        func.as_u32(),
                        layout.locals_words
                    );
                }

                need_words.insert(func, need);
                static_max_words = static_max_words.max(need);
                MemScheme::StaticArena(StaticArenaFuncPlan { need_words: need })
            } else {
                MemScheme::DynamicFrame
            };

            plans.insert(
                func,
                FuncMemPlan {
                    scheme,
                    obj_offset_words: layout.obj_offset_words,
                    alloca_offset_words: layout.alloca_offset_words,
                    spill_obj: layout.spill_obj,
                    locals_words: layout.locals_words,
                    malloc_future_static_words: FxHashMap::default(),
                    transient_mallocs: FxHashSet::default(),
                },
            );
        }
    }

    let static_max_bytes = static_max_words
        .checked_mul(WORD_BYTES)
        .expect("static max bytes overflow");
    let dyn_base = STATIC_BASE
        .checked_add(static_max_bytes)
        .expect("dyn base overflow");

    ProgramMemoryPlan {
        dyn_base,
        funcs: plans,
    }
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{critical_edge::CriticalEdgeSplitter, domtree::DomTree, liveness::Liveness};
    use sonatina_ir::cfg::ControlFlowGraph;
    use sonatina_parser::parse_module;
    use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

    fn plan_from_src(src: &str) -> (ProgramMemoryPlan, FxHashMap<String, FuncRef>) {
        let parsed = parse_module(src).unwrap();
        let funcs: Vec<FuncRef> = parsed.module.funcs();

        let isa = Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        });

        let mut analyses: FxHashMap<FuncRef, FuncAnalysis> = FxHashMap::default();
        for &func in &funcs {
            parsed.module.func_store.modify(func, |function| {
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
                let alloc = StackifyAlloc::for_function(function, &cfg, &dom, &liveness, 16);

                analyses.insert(
                    func,
                    FuncAnalysis {
                        alloc,
                        inst_liveness,
                        block_order,
                    },
                );
            });
        }

        let plan = compute_program_memory_plan(
            &parsed.module,
            &funcs,
            &analyses,
            &FxHashMap::default(),
            &isa,
        );

        let mut names: FxHashMap<String, FuncRef> = FxHashMap::default();
        for f in funcs {
            let name = parsed.module.ctx.func_sig(f, |sig| sig.name().to_string());
            names.insert(name, f);
        }

        (plan, names)
    }

    #[test]
    fn static_arena_chain_has_no_base_stacking() {
        let (plan, names) = plan_from_src(
            r#"
target = "evm-ethereum-osaka"

func public %c() -> i256 {
block0:
    v0.*i256 = alloca i256;
    return 0.i256;
}

func public %b() -> i256 {
block0:
    v0.*i256 = alloca i256;
    v1.i256 = call %c;
    return v1;
}

func public %a() -> i256 {
block0:
    v0.*i256 = alloca i256;
    v1.i256 = call %b;
    return v1;
}
"#,
        );

        assert_eq!(plan.dyn_base, STATIC_BASE + WORD_BYTES);

        for name in ["a", "b", "c"] {
            let func = names[name];
            let MemScheme::StaticArena(p) = &plan.funcs[&func].scheme else {
                panic!("expected {name} to be StaticArena");
            };
            assert_eq!(p.need_words, 1);
        }
    }

    #[test]
    fn call_live_alloca_is_placed_above_callee_need() {
        let (plan, names) = plan_from_src(
            r#"
target = "evm-ethereum-osaka"

func public %callee() -> i256 {
block0:
    v0.*i256 = alloca i256;
    v1.*i256 = alloca i256;
    v2.*i256 = alloca i256;
    v3.*i256 = alloca i256;
    v4.*i256 = alloca i256;
    mstore v0 0.i256 i256;
    mstore v1 0.i256 i256;
    mstore v2 0.i256 i256;
    mstore v3 0.i256 i256;
    mstore v4 0.i256 i256;
    v5.i256 = mload v0 i256;
    v6.i256 = mload v1 i256;
    v7.i256 = mload v2 i256;
    v8.i256 = mload v3 i256;
    v9.i256 = mload v4 i256;
    v10.i256 = add v5 v6;
    v11.i256 = add v10 v7;
    v12.i256 = add v11 v8;
    v13.i256 = add v12 v9;
    return v13;
}

func public %caller() -> i256 {
block0:
    v0.*i256 = alloca i256;
    mstore v0 1.i256 i256;
    v1.i256 = call %callee;
    mstore v0 v1 i256;
    v2.i256 = mload v0 i256;
    return v2;
}
"#,
        );

        let callee = names["callee"];
        let caller = names["caller"];

        let MemScheme::StaticArena(callee_plan) = &plan.funcs[&callee].scheme else {
            panic!("expected callee to be StaticArena");
        };
        let MemScheme::StaticArena(_) = &plan.funcs[&caller].scheme else {
            panic!("expected caller to be StaticArena");
        };

        let mut allocas: Vec<InstId> = Vec::new();
        plan.funcs[&caller]
            .alloca_offset_words
            .keys()
            .for_each(|i| allocas.push(*i));
        allocas.sort_unstable_by_key(|i| i.as_u32());
        assert_eq!(allocas.len(), 1);

        let off = plan.funcs[&caller].alloca_offset_words[&allocas[0]];
        assert!(off >= callee_plan.need_words);
    }

    #[test]
    fn self_recursion_uses_dynamic_frame() {
        let (plan, names) = plan_from_src(
            r#"
target = "evm-ethereum-osaka"

func public %f() -> i256 {
block0:
    v0.*i256 = alloca i256;
    v1.i256 = call %f;
    return v1;
}
"#,
        );

        let f = names["f"];
        assert!(matches!(plan.funcs[&f].scheme, MemScheme::DynamicFrame));
        assert_eq!(plan.dyn_base, STATIC_BASE);
    }
}
