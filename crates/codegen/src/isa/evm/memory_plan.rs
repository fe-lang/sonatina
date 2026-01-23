use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{InstId, Module, module::FuncRef};
use std::collections::BTreeSet;

use crate::module_analysis::{CallGraph, CallGraphSccs, SccBuilder, SccRef};

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
    pub alloca: FxHashMap<InstId, StackObjectPlan>,
    pub alloca_words: u32,
    pub persistent_alloca_words: u32,
    pub malloc_future_static_words: FxHashMap<InstId, u32>,
    pub transient_mallocs: FxHashSet<InstId>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AllocaClass {
    Persistent,
    Transient,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StackObjectPlan {
    pub class: AllocaClass,
    pub offset_words: u32,
}

#[derive(Clone, Debug)]
pub enum MemScheme {
    StaticTree(StaticTreeFuncPlan),
    DynamicFrame,
}

#[derive(Clone, Debug)]
pub struct StaticTreeFuncPlan {
    pub base_words: u32,
    pub persistent_words: u32,
}

#[derive(Clone, Copy, Debug)]
pub struct FuncLocalMemInfo {
    pub persistent_words: u32,
    pub transient_words: u32,
    pub alloca_words: u32,
    pub persistent_alloca_words: u32,
}

pub fn compute_program_memory_plan(
    module: &Module,
    funcs: &[FuncRef],
    local_mem: &FxHashMap<FuncRef, FuncLocalMemInfo>,
    alloca_offsets: &FxHashMap<FuncRef, FxHashMap<InstId, StackObjectPlan>>,
) -> ProgramMemoryPlan {
    let funcs_set: FxHashSet<FuncRef> = funcs.iter().copied().collect();
    let call_graph = CallGraph::build_graph_subset(module, &funcs_set);
    let scc = SccBuilder::new().compute_scc(&call_graph);

    let callers = compute_callers(&funcs_set, &call_graph);

    let mut eligible: FxHashSet<FuncRef> = FxHashSet::default();
    for &f in funcs_set.iter() {
        let caller_count = callers.get(&f).map_or(0, |cs| cs.len());
        if !scc.scc_of(f).is_cycle && caller_count <= 1 {
            eligible.insert(f);
        }
    }

    let (children, roots) = build_forest(&eligible, &callers);

    let static_enter_words =
        compute_static_enter_words(&funcs_set, &call_graph, &scc, &eligible, local_mem);

    let mut need_words: FxHashMap<FuncRef, u32> = FxHashMap::default();
    let mut static_max_words: u32 = 0;
    for &root in &roots {
        let need = compute_need_words(root, local_mem, &children, &mut need_words);
        let base_words = static_enter_words.get(&root).copied().unwrap_or(0);
        let total = base_words
            .checked_add(need)
            .expect("static max words overflow");
        static_max_words = static_max_words.max(total);
    }

    let static_max_bytes = static_max_words
        .checked_mul(WORD_BYTES)
        .expect("static max bytes overflow");
    let dyn_base = STATIC_BASE
        .checked_add(static_max_bytes)
        .expect("dyn base overflow");

    let mut plans: FxHashMap<FuncRef, FuncMemPlan> = FxHashMap::default();
    for &f in funcs {
        let Some(mem) = local_mem.get(&f) else {
            continue;
        };

        let alloca = alloca_offsets.get(&f).cloned().unwrap_or_default();

        let scheme = if eligible.contains(&f) {
            let base_words = static_enter_words.get(&f).copied().unwrap_or(0);
            MemScheme::StaticTree(StaticTreeFuncPlan {
                base_words,
                persistent_words: mem.persistent_words,
            })
        } else {
            MemScheme::DynamicFrame
        };

        plans.insert(
            f,
            FuncMemPlan {
                scheme,
                alloca,
                alloca_words: mem.alloca_words,
                persistent_alloca_words: mem.persistent_alloca_words,
                malloc_future_static_words: FxHashMap::default(),
                transient_mallocs: FxHashSet::default(),
            },
        );
    }

    ProgramMemoryPlan {
        dyn_base,
        funcs: plans,
    }
}

fn compute_callers(
    funcs: &FxHashSet<FuncRef>,
    call_graph: &CallGraph,
) -> FxHashMap<FuncRef, Vec<FuncRef>> {
    let mut callers: FxHashMap<FuncRef, Vec<FuncRef>> = FxHashMap::default();
    for &f in funcs {
        callers.entry(f).or_default();
    }

    for &f in funcs {
        for &callee in call_graph.callee_of(f) {
            debug_assert!(funcs.contains(&callee), "subset call graph invariant");
            callers.entry(callee).or_default().push(f);
        }
    }

    for cs in callers.values_mut() {
        cs.sort_unstable_by_key(|f| f.as_u32());
    }

    callers
}

fn build_forest(
    eligible: &FxHashSet<FuncRef>,
    callers: &FxHashMap<FuncRef, Vec<FuncRef>>,
) -> (FxHashMap<FuncRef, Vec<FuncRef>>, Vec<FuncRef>) {
    let mut children: FxHashMap<FuncRef, Vec<FuncRef>> = FxHashMap::default();
    let mut roots: Vec<FuncRef> = Vec::new();

    for &f in eligible {
        let p = match callers.get(&f).map(Vec::as_slice).unwrap_or_default() {
            [only] if eligible.contains(only) => Some(*only),
            _ => None,
        };
        children.entry(f).or_default();
        if let Some(p) = p {
            children.entry(p).or_default().push(f);
        } else {
            roots.push(f);
        }
    }

    for cs in children.values_mut() {
        cs.sort_unstable_by_key(|f| f.as_u32());
    }

    roots.sort_unstable_by_key(|f| f.as_u32());

    (children, roots)
}

fn compute_static_enter_words(
    funcs: &FxHashSet<FuncRef>,
    call_graph: &CallGraph,
    scc: &CallGraphSccs,
    eligible: &FxHashSet<FuncRef>,
    local_mem: &FxHashMap<FuncRef, FuncLocalMemInfo>,
) -> FxHashMap<FuncRef, u32> {
    let mut sccs: BTreeSet<SccRef> = BTreeSet::new();
    for &f in funcs {
        sccs.insert(scc.scc_ref(f));
    }

    let mut edges: FxHashMap<SccRef, BTreeSet<SccRef>> = FxHashMap::default();
    let mut indegree: FxHashMap<SccRef, usize> = FxHashMap::default();
    for &s in &sccs {
        edges.insert(s, BTreeSet::new());
        indegree.insert(s, 0);
    }

    for &f in funcs {
        let from = scc.scc_ref(f);
        for &callee in call_graph.callee_of(f) {
            debug_assert!(funcs.contains(&callee), "subset call graph invariant");
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

    let mut enter_words: FxHashMap<SccRef, u32> = FxHashMap::default();
    for &s in &sccs {
        enter_words.insert(s, 0);
    }

    for &s in &topo {
        let base = enter_words.get(&s).copied().unwrap_or(0);
        let push_words = scc_push_words(scc, s, eligible, local_mem);

        for &to in edges.get(&s).expect("missing scc") {
            let next = base
                .checked_add(push_words)
                .expect("static enter words overflow");
            let dest = enter_words.get_mut(&to).expect("missing scc");
            *dest = (*dest).max(next);
        }
    }

    let mut out: FxHashMap<FuncRef, u32> = FxHashMap::default();
    for &f in funcs {
        let s = scc.scc_ref(f);
        out.insert(f, enter_words.get(&s).copied().unwrap_or(0));
    }

    out
}

fn scc_push_words(
    scc: &CallGraphSccs,
    scc_ref: SccRef,
    eligible: &FxHashSet<FuncRef>,
    local_mem: &FxHashMap<FuncRef, FuncLocalMemInfo>,
) -> u32 {
    let info = scc.scc_info(scc_ref);
    if info.is_cycle {
        return 0;
    }

    let Some(&func) = info.components.iter().min_by_key(|f| f.as_u32()) else {
        return 0;
    };

    if eligible.contains(&func) {
        local_mem.get(&func).map_or(0, |m| m.persistent_words)
    } else {
        0
    }
}

fn compute_need_words(
    f: FuncRef,
    local_mem: &FxHashMap<FuncRef, FuncLocalMemInfo>,
    children: &FxHashMap<FuncRef, Vec<FuncRef>>,
    memo: &mut FxHashMap<FuncRef, u32>,
) -> u32 {
    if let Some(&cached) = memo.get(&f) {
        return cached;
    }

    let Some(mem) = local_mem.get(&f) else {
        memo.insert(f, 0);
        return 0;
    };

    let child_need = children
        .get(&f)
        .map(Vec::as_slice)
        .unwrap_or_default()
        .iter()
        .map(|&c| compute_need_words(c, local_mem, children, memo))
        .max()
        .unwrap_or(0);

    let need = mem
        .persistent_words
        .checked_add(mem.transient_words.max(child_need))
        .expect("need words overflow");
    memo.insert(f, need);
    need
}

#[cfg(test)]
mod tests {
    use super::*;
    use sonatina_parser::parse_module;

    fn plan_from_src(src: &str) -> (ProgramMemoryPlan, FxHashMap<String, FuncRef>) {
        let parsed = parse_module(src).unwrap();
        let funcs: Vec<FuncRef> = parsed.module.funcs();

        let mut local_mem: FxHashMap<FuncRef, FuncLocalMemInfo> = FxHashMap::default();
        let mut alloca_offsets: FxHashMap<FuncRef, FxHashMap<InstId, StackObjectPlan>> =
            FxHashMap::default();
        for f in &funcs {
            local_mem.insert(
                *f,
                FuncLocalMemInfo {
                    persistent_words: 1,
                    transient_words: 0,
                    alloca_words: 0,
                    persistent_alloca_words: 0,
                },
            );
            alloca_offsets.insert(*f, FxHashMap::default());
        }

        let plan = compute_program_memory_plan(&parsed.module, &funcs, &local_mem, &alloca_offsets);

        let mut names: FxHashMap<String, FuncRef> = FxHashMap::default();
        for f in funcs {
            let name = parsed.module.ctx.func_sig(f, |sig| sig.name().to_string());
            names.insert(name, f);
        }

        (plan, names)
    }

    #[test]
    fn static_tree_chain() {
        let (plan, names) = plan_from_src(
            r#"
target = "evm-ethereum-osaka"

func public %c() -> i256 {
block0:
    return 0.i256;
}

func public %b() -> i256 {
block0:
    v0.i256 = call %c;
    return v0;
}

func public %a() -> i256 {
block0:
    v0.i256 = call %b;
    return v0;
}
"#,
        );

        assert_eq!(plan.dyn_base, STATIC_BASE + 3 * WORD_BYTES);

        let a = names["a"];
        let b = names["b"];
        let c = names["c"];

        let MemScheme::StaticTree(a_plan) = &plan.funcs[&a].scheme else {
            panic!("expected a to be StaticTree");
        };
        let MemScheme::StaticTree(b_plan) = &plan.funcs[&b].scheme else {
            panic!("expected b to be StaticTree");
        };
        let MemScheme::StaticTree(c_plan) = &plan.funcs[&c].scheme else {
            panic!("expected c to be StaticTree");
        };

        assert_eq!(a_plan.base_words, 0);
        assert_eq!(b_plan.base_words, 1);
        assert_eq!(c_plan.base_words, 2);
    }

    #[test]
    fn static_tree_diamond_marks_multi_parent_ineligible() {
        let (plan, names) = plan_from_src(
            r#"
target = "evm-ethereum-osaka"

func public %d() -> i256 {
block0:
    return 0.i256;
}

func public %b() -> i256 {
block0:
    v0.i256 = call %d;
    return v0;
}

func public %c() -> i256 {
block0:
    v0.i256 = call %d;
    return v0;
}

func public %a() -> i256 {
block0:
    v0.i256 = call %b;
    v1.i256 = call %c;
    return v1;
}
"#,
        );

        let a = names["a"];
        let b = names["b"];
        let c = names["c"];
        let d = names["d"];

        assert!(matches!(plan.funcs[&d].scheme, MemScheme::DynamicFrame));

        let MemScheme::StaticTree(a_plan) = &plan.funcs[&a].scheme else {
            panic!("expected a to be StaticTree");
        };
        let MemScheme::StaticTree(b_plan) = &plan.funcs[&b].scheme else {
            panic!("expected b to be StaticTree");
        };
        let MemScheme::StaticTree(c_plan) = &plan.funcs[&c].scheme else {
            panic!("expected c to be StaticTree");
        };

        assert_eq!(a_plan.base_words, 0);
        assert_eq!(b_plan.base_words, 1);
        assert_eq!(c_plan.base_words, 1);
        assert_eq!(plan.dyn_base, STATIC_BASE + 2 * WORD_BYTES);
    }

    #[test]
    fn static_tree_self_recursion_ineligible() {
        let (plan, names) = plan_from_src(
            r#"
target = "evm-ethereum-osaka"

func public %a() -> i256 {
block0:
    v0.i256 = call %a;
    return v0;
}
"#,
        );

        let a = names["a"];
        assert!(matches!(plan.funcs[&a].scheme, MemScheme::DynamicFrame));
        assert_eq!(plan.dyn_base, STATIC_BASE);
    }

    #[test]
    fn static_tree_base_propagates_through_dynamic_parent() {
        let (plan, names) = plan_from_src(
            r#"
target = "evm-ethereum-osaka"

func public %b() -> i256 {
block0:
    return 0.i256;
}

func public %d() -> i256 {
block0:
    v0.i256 = call %d;
    v1.i256 = call %b;
    return v1;
}

func public %a() -> i256 {
block0:
    v0.i256 = call %d;
    return v0;
}
"#,
        );

        let a = names["a"];
        let b = names["b"];
        let d = names["d"];

        assert!(matches!(plan.funcs[&d].scheme, MemScheme::DynamicFrame));

        let MemScheme::StaticTree(a_plan) = &plan.funcs[&a].scheme else {
            panic!("expected a to be StaticTree");
        };
        let MemScheme::StaticTree(b_plan) = &plan.funcs[&b].scheme else {
            panic!("expected b to be StaticTree");
        };

        assert_eq!(a_plan.base_words, 0);
        assert_eq!(b_plan.base_words, 1);
        assert_eq!(plan.dyn_base, STATIC_BASE + 2 * WORD_BYTES);
    }
}
