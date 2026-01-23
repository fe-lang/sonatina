use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    BlockId, Function, InstId, InstSetExt, Module, ValueId,
    cfg::ControlFlowGraph,
    inst::evm::inst_set::EvmInstKind,
    isa::{Isa, evm::Evm},
    module::{FuncRef, ModuleCtx},
};
use std::collections::{BTreeMap, BTreeSet};

use crate::{
    module_analysis::{CallGraph, CallGraphSccs, SccBuilder, SccRef},
    stackalloc::{Action, Allocator, StackifyAlloc},
};

use super::{
    memory_plan::{
        AllocaClass, FuncLocalMemInfo, FuncMemPlan, MemScheme, ProgramMemoryPlan, STATIC_BASE,
        WORD_BYTES,
    },
    provenance::compute_value_provenance,
};

pub(crate) fn compute_malloc_future_static_words(
    module: &Module,
    funcs: &[FuncRef],
    plan: &ProgramMemoryPlan,
    local_mem: &FxHashMap<FuncRef, FuncLocalMemInfo>,
    allocs: &FxHashMap<FuncRef, StackifyAlloc>,
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
        let func_plan = plan.funcs.get(&f);
        let func_alloc = allocs.get(&f);
        let ctx = FutureBoundsCtx {
            module: &module.ctx,
            isa,
            entry_bounds: &entry_bound_words,
            unknown_callee_bound: static_max_words,
            func_plan,
            alloc: func_alloc,
        };
        let map = module.func_store.view(f, |function| {
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(function);
            compute_future_bounds_for_func(function, &cfg, &ctx)
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
    ctx: &FutureBoundsCtx<'_>,
) -> FxHashMap<InstId, u32> {
    #[derive(Clone, Copy)]
    struct StaticCtx {
        base_words: u32,
        persistent_words: u32,
        alloca_words: u32,
        persistent_alloca_words: u32,
    }

    impl StaticCtx {
        fn persistent_spills(self) -> u32 {
            self.persistent_words
                .checked_sub(self.persistent_alloca_words)
                .expect("persistent spill words underflow")
        }

        fn spill_slot_end_words(self, spill_slot: u32) -> u32 {
            let persistent_spills = self.persistent_spills();
            let spill_words = if spill_slot >= persistent_spills {
                spill_slot
                    .checked_add(self.alloca_words)
                    .expect("spill slot words overflow")
            } else {
                spill_slot
            };

            let addr_words = self
                .base_words
                .checked_add(spill_words)
                .expect("spill addr words overflow");
            addr_words
                .checked_add(1)
                .expect("spill addr words overflow")
        }
    }

    let static_ctx = match ctx.func_plan.map(|p| &p.scheme) {
        Some(MemScheme::StaticTree(st)) => ctx.func_plan.map(|p| StaticCtx {
            base_words: st.base_words,
            persistent_words: st.persistent_words,
            alloca_words: p.alloca_words,
            persistent_alloca_words: p.persistent_alloca_words,
        }),
        _ => None,
    };

    let mut value_alloca_bound: SecondaryMap<ValueId, u32> = SecondaryMap::new();
    for value in function.dfg.values.keys() {
        let _ = &mut value_alloca_bound[value];
    }

    if let (Some(static_ctx), Some(func_plan)) = (static_ctx, ctx.func_plan) {
        let prov = compute_value_provenance(function, ctx.module, ctx.isa, |callee| {
            let arg_count = ctx.module.func_sig(callee, |sig| sig.args().len());
            vec![true; arg_count]
        });

        let persistent_spills = static_ctx.persistent_spills();
        let mut alloca_end_words: FxHashMap<InstId, u32> = FxHashMap::default();
        for (&inst, plan) in &func_plan.alloca {
            let data = ctx.isa.inst_set().resolve_inst(function.dfg.inst(inst));
            let EvmInstKind::Alloca(alloca) = data else {
                continue;
            };

            let size_bytes: u32 = ctx
                .isa
                .type_layout()
                .size_of(*alloca.ty(), ctx.module)
                .expect("alloca has invalid type") as u32;
            let size_words = size_bytes.div_ceil(WORD_BYTES);

            let start_words = match plan.class {
                AllocaClass::Persistent => static_ctx
                    .base_words
                    .checked_add(persistent_spills)
                    .and_then(|w| w.checked_add(plan.offset_words))
                    .expect("alloca addr words overflow"),
                AllocaClass::Transient => static_ctx
                    .base_words
                    .checked_add(static_ctx.persistent_words)
                    .and_then(|w| w.checked_add(plan.offset_words))
                    .expect("alloca addr words overflow"),
            };

            let end_words = start_words
                .checked_add(size_words)
                .expect("alloca end words overflow");
            alloca_end_words.insert(inst, end_words);
        }

        for value in function.dfg.values.keys() {
            let mut max_end = 0;
            for base in prov[value].alloca_insts() {
                if let Some(end) = alloca_end_words.get(&base) {
                    max_end = max_end.max(*end);
                }
            }
            value_alloca_bound[value] = max_end;
        }
    }

    fn action_static_bound(action: &Action, static_ctx: Option<StaticCtx>) -> u32 {
        match action {
            Action::MemLoadAbs(offset) | Action::MemStoreAbs(offset) => {
                if *offset < STATIC_BASE {
                    return 0;
                }
                let delta = offset
                    .checked_sub(STATIC_BASE)
                    .expect("abs addr below static base");
                delta / WORD_BYTES + 1
            }
            Action::MemLoadFrameSlot(slot) | Action::MemStoreFrameSlot(slot) => {
                static_ctx.map_or(0, |ctx| ctx.spill_slot_end_words(*slot))
            }
            _ => 0,
        }
    }

    fn actions_static_bound(actions: &[Action], static_ctx: Option<StaticCtx>) -> u32 {
        actions
            .iter()
            .map(|a| action_static_bound(a, static_ctx))
            .max()
            .unwrap_or(0)
    }

    fn inst_alloca_bound(
        data: &EvmInstKind,
        value_alloca_bound: &SecondaryMap<ValueId, u32>,
    ) -> u32 {
        match data {
            EvmInstKind::Mload(mload) => value_alloca_bound[*mload.addr()],
            EvmInstKind::Mstore(mstore) => value_alloca_bound[*mstore.addr()],
            EvmInstKind::EvmMstore8(mstore8) => value_alloca_bound[*mstore8.addr()],
            EvmInstKind::EvmMcopy(mcopy) => {
                value_alloca_bound[*mcopy.dest()].max(value_alloca_bound[*mcopy.addr()])
            }
            EvmInstKind::EvmKeccak256(keccak) => value_alloca_bound[*keccak.addr()],
            EvmInstKind::EvmCalldataCopy(copy) => value_alloca_bound[*copy.dst_addr()],
            EvmInstKind::EvmCodeCopy(copy) => value_alloca_bound[*copy.dst_addr()],
            EvmInstKind::EvmExtCodeCopy(copy) => value_alloca_bound[*copy.dst_addr()],
            EvmInstKind::EvmReturnDataCopy(copy) => value_alloca_bound[*copy.dst_addr()],
            EvmInstKind::EvmReturn(ret) => value_alloca_bound[*ret.addr()],
            EvmInstKind::EvmRevert(rev) => value_alloca_bound[*rev.addr()],
            EvmInstKind::EvmLog0(log) => value_alloca_bound[*log.addr()],
            EvmInstKind::EvmLog1(log) => value_alloca_bound[*log.addr()],
            EvmInstKind::EvmLog2(log) => value_alloca_bound[*log.addr()],
            EvmInstKind::EvmLog3(log) => value_alloca_bound[*log.addr()],
            EvmInstKind::EvmLog4(log) => value_alloca_bound[*log.addr()],
            EvmInstKind::EvmCreate(create) => value_alloca_bound[*create.addr()],
            EvmInstKind::EvmCreate2(create) => value_alloca_bound[*create.addr()],
            EvmInstKind::EvmCall(call) => {
                value_alloca_bound[*call.arg_addr()].max(value_alloca_bound[*call.ret_addr()])
            }
            EvmInstKind::EvmCallCode(call) => {
                value_alloca_bound[*call.arg_addr()].max(value_alloca_bound[*call.ret_addr()])
            }
            EvmInstKind::EvmDelegateCall(call) => {
                value_alloca_bound[*call.arg_addr()].max(value_alloca_bound[*call.ret_addr()])
            }
            EvmInstKind::EvmStaticCall(call) => {
                value_alloca_bound[*call.arg_addr()].max(value_alloca_bound[*call.ret_addr()])
            }
            EvmInstKind::Call(call) => call
                .args()
                .iter()
                .map(|v| value_alloca_bound[*v])
                .max()
                .unwrap_or(0),
            _ => 0,
        }
    }

    let mut block_in: SecondaryMap<BlockId, u32> = SecondaryMap::new();
    for block in function.layout.iter_block() {
        let _ = &mut block_in[block];
    }

    let blocks: Vec<BlockId> = cfg.post_order().collect();

    let mut block_local: SecondaryMap<BlockId, u32> = SecondaryMap::new();
    for block in function.layout.iter_block() {
        let _ = &mut block_local[block];
    }

    for block in function.layout.iter_block() {
        let mut bound = 0;

        for inst in function.layout.iter_inst(block) {
            let data = ctx.isa.inst_set().resolve_inst(function.dfg.inst(inst));

            if let Some(call) = function.dfg.call_info(inst) {
                let callee = call.callee();
                bound = bound.max(
                    ctx.entry_bounds
                        .get(&callee)
                        .copied()
                        .unwrap_or(ctx.unknown_callee_bound),
                );
            }

            bound = bound.max(inst_alloca_bound(&data, &value_alloca_bound));

            if let Some(alloc) = ctx.alloc {
                let args = function.dfg.inst(inst).collect_values();
                let pre = alloc.read(inst, &args);
                let post = alloc.write(inst, function.dfg.inst_result(inst));
                bound = bound.max(actions_static_bound(&pre, static_ctx));
                bound = bound.max(actions_static_bound(&post, static_ctx));
            }
        }

        block_local[block] = bound;
    }

    let mut changed = true;
    while changed {
        changed = false;

        for &block in &blocks {
            let out = cfg.succs_of(block).map(|b| block_in[*b]).max().unwrap_or(0);
            let bound = out.max(block_local[block]);

            if bound > block_in[block] {
                block_in[block] = bound;
                changed = true;
            }
        }
    }

    let mut malloc_bounds: FxHashMap<InstId, u32> = FxHashMap::default();
    for block in function.layout.iter_block() {
        let out = cfg.succs_of(block).map(|b| block_in[*b]).max().unwrap_or(0);
        let mut bound = out;

        let insts: Vec<InstId> = function.layout.iter_inst(block).collect();
        for inst in insts.into_iter().rev() {
            if let Some(alloc) = ctx.alloc {
                let post = alloc.write(inst, function.dfg.inst_result(inst));
                bound = bound.max(actions_static_bound(&post, static_ctx));
            }

            let data = ctx.isa.inst_set().resolve_inst(function.dfg.inst(inst));
            bound = bound.max(inst_alloca_bound(&data, &value_alloca_bound));

            if matches!(data, EvmInstKind::EvmMalloc(_)) {
                malloc_bounds.insert(inst, bound);
            }

            if let Some(call) = function.dfg.call_info(inst) {
                let callee = call.callee();
                bound = bound.max(
                    ctx.entry_bounds
                        .get(&callee)
                        .copied()
                        .unwrap_or(ctx.unknown_callee_bound),
                );
            }

            if let Some(alloc) = ctx.alloc {
                let args = function.dfg.inst(inst).collect_values();
                let pre = alloc.read(inst, &args);
                bound = bound.max(actions_static_bound(&pre, static_ctx));
            }
        }
    }

    malloc_bounds
}

struct FutureBoundsCtx<'a> {
    module: &'a ModuleCtx,
    isa: &'a Evm,
    entry_bounds: &'a FxHashMap<FuncRef, u32>,
    unknown_callee_bound: u32,
    func_plan: Option<&'a FuncMemPlan>,
    alloc: Option<&'a StackifyAlloc>,
}
