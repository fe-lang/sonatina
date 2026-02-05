use std::collections::BTreeSet;

use cranelift_entity::SecondaryMap;
use rustc_hash::FxHashSet;
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, Module,
    inst::SideEffect,
    module::{FuncAttrs, FuncRef},
};

use crate::{cfg_scc::CfgSccAnalysis, module_analysis};

#[derive(Debug, Default, Clone)]
struct LocalFacts {
    local_mem: FuncAttrs,
    callees: Vec<FuncRef>,
    has_body: bool,
    cfg_has_cycle: bool,
    exits_all_return_like: bool,
    exits_all_terminate_like: bool,
    has_any_return_like_exit: bool,
}

pub fn analyze_module(module: &Module) {
    FuncBehaviorAnalyzer::new(module).analyze();
}

struct FuncBehaviorAnalyzer<'a> {
    module: &'a Module,
    is_external: SecondaryMap<FuncRef, bool>,
    locals: SecondaryMap<FuncRef, LocalFacts>,
    attrs: SecondaryMap<FuncRef, FuncAttrs>,
    info: module_analysis::ModuleInfo,
    topo: Vec<module_analysis::SccRef>,
    succ_sccs: SecondaryMap<module_analysis::SccRef, Vec<module_analysis::SccRef>>,
}

impl<'a> FuncBehaviorAnalyzer<'a> {
    fn new(module: &'a Module) -> Self {
        let mut funcs = module.func_store.funcs();
        funcs.sort_unstable_by_key(|f| f.as_u32());

        let mut is_external = SecondaryMap::<FuncRef, bool>::new();
        let mut locals = SecondaryMap::<FuncRef, LocalFacts>::new();
        let mut attrs = SecondaryMap::<FuncRef, FuncAttrs>::new();

        for &func_ref in &funcs {
            is_external[func_ref] = module.ctx.func_linkage(func_ref).is_external();
            locals[func_ref] = module.func_store.view(func_ref, compute_local_facts);

            let facts = &locals[func_ref];
            attrs[func_ref] = if is_external[func_ref] || !facts.has_body {
                FuncAttrs::MEM_READ | FuncAttrs::MEM_WRITE
            } else {
                FuncAttrs::empty()
            };

            if !is_external[func_ref] && facts.has_body && !facts.has_any_return_like_exit {
                attrs[func_ref].insert(FuncAttrs::NORETURN);
            }
        }

        let info = module_analysis::analyze_module(module);

        let mut scc_refs: Vec<_> = funcs.iter().map(|&f| info.scc.scc_ref(f)).collect();
        scc_refs.sort_unstable_by_key(|s| s.as_u32());
        scc_refs.dedup();

        let mut succ_sccs =
            SecondaryMap::<module_analysis::SccRef, Vec<module_analysis::SccRef>>::new();
        for &func_ref in &funcs {
            let from_scc = info.scc.scc_ref(func_ref);
            for &callee in info.call_graph.callee_of(func_ref) {
                let to_scc = info.scc.scc_ref(callee);
                if from_scc != to_scc {
                    succ_sccs[from_scc].push(to_scc);
                }
            }
        }
        for &scc in &scc_refs {
            succ_sccs[scc].sort_unstable_by_key(|s| s.as_u32());
            succ_sccs[scc].dedup();
        }

        let topo = topo_sort_sccs(&scc_refs, &succ_sccs);

        Self {
            module,
            is_external,
            locals,
            attrs,
            info,
            topo,
            succ_sccs,
        }
    }

    fn analyze(mut self) {
        self.propagate_mem();
        self.propagate_noreturn_and_will();
        self.module.ctx.set_all_func_attrs(self.attrs);
    }

    fn propagate_mem(&mut self) {
        let mut scc_mem = SecondaryMap::<module_analysis::SccRef, FuncAttrs>::new();
        for &scc in self.topo.iter().rev() {
            let scc_info = self.info.scc.scc_info(scc);
            let mut comps: Vec<_> = scc_info.components.iter().copied().collect();
            comps.sort_unstable_by_key(|f| f.as_u32());

            let mut mem = FuncAttrs::empty();
            for &func_ref in &comps {
                mem |= if self.is_external[func_ref] || !self.locals[func_ref].has_body {
                    FuncAttrs::MEM_READ | FuncAttrs::MEM_WRITE
                } else {
                    self.locals[func_ref].local_mem
                };
            }
            for &succ in &self.succ_sccs[scc] {
                mem |= scc_mem[succ];
            }

            scc_mem[scc] = mem;
            for func_ref in comps {
                self.attrs[func_ref].remove(FuncAttrs::MEM_READ | FuncAttrs::MEM_WRITE);
                self.attrs[func_ref].insert(mem);
            }
        }
    }

    fn propagate_noreturn_and_will(&mut self) {
        for &scc in self.topo.iter().rev() {
            let scc_info = self.info.scc.scc_info(scc);
            if scc_info.is_cycle {
                continue;
            }

            let mut comps: Vec<_> = scc_info.components.iter().copied().collect();
            comps.sort_unstable_by_key(|f| f.as_u32());

            for func_ref in comps {
                if self.is_external[func_ref] || !self.locals[func_ref].has_body {
                    continue;
                }

                let facts = &self.locals[func_ref];

                if !self.attrs[func_ref].contains(FuncAttrs::NORETURN) {
                    let attrs = &self.attrs;
                    let has_return = self
                        .module
                        .func_store
                        .view(func_ref, |func| has_reachable_return(func, attrs));
                    if !has_return {
                        self.attrs[func_ref].insert(FuncAttrs::NORETURN);
                    }
                }

                if facts.cfg_has_cycle {
                    continue;
                }

                let mut can_terminate = facts.exits_all_terminate_like;
                let mut can_return = facts.exits_all_return_like;
                for &callee in &facts.callees {
                    can_terminate &= self.attrs[callee].contains(FuncAttrs::WILLTERMINATE);
                    can_return &= self.attrs[callee].contains(FuncAttrs::WILLRETURN);
                    if !can_terminate && !can_return {
                        break;
                    }
                }

                if can_return {
                    self.attrs[func_ref].insert(FuncAttrs::WILLRETURN | FuncAttrs::WILLTERMINATE);
                } else if can_terminate {
                    self.attrs[func_ref].insert(FuncAttrs::WILLTERMINATE);
                }
            }
        }
    }
}

fn has_reachable_return(func: &Function, attrs: &SecondaryMap<FuncRef, FuncAttrs>) -> bool {
    let Some(entry) = func.layout.entry_block() else {
        return false;
    };

    let mut cfg = ControlFlowGraph::new();
    cfg.compute(func);

    let mut visited = FxHashSet::default();
    let mut stack = vec![entry];
    while let Some(block) = stack.pop() {
        if !visited.insert(block) || has_noreturn_call(func, block, attrs) {
            continue;
        }

        if func
            .layout
            .last_inst_of(block)
            .is_some_and(|term| func.dfg.is_return(term))
        {
            return true;
        }

        for &succ in cfg.succs_of(block) {
            stack.push(succ);
        }
    }

    false
}

fn has_noreturn_call(
    func: &Function,
    block: BlockId,
    attrs: &SecondaryMap<FuncRef, FuncAttrs>,
) -> bool {
    for inst in func.layout.iter_inst(block) {
        if func
            .dfg
            .call_info(inst)
            .is_some_and(|call| attrs[call.callee()].contains(FuncAttrs::NORETURN))
        {
            return true;
        }

        if func.dfg.is_terminator(inst) {
            break;
        }
    }

    false
}

fn compute_local_facts(func: &Function) -> LocalFacts {
    let Some(entry) = func.layout.entry_block() else {
        return LocalFacts {
            has_body: false,
            ..Default::default()
        };
    };

    let mut cfg = ControlFlowGraph::new();
    cfg.compute(func);

    let reachable = compute_reachable(&cfg, entry);

    let mut cfg_scc = CfgSccAnalysis::new();
    cfg_scc.compute(&cfg);

    let cfg_has_cycle = cfg_scc
        .topo_order()
        .iter()
        .any(|&scc| cfg_scc.scc_data(scc).is_cycle);

    let mut local_mem = FuncAttrs::empty();
    let mut callees = FxHashSet::default();

    for block in func.layout.iter_block() {
        if !reachable.contains(&block) {
            continue;
        }

        for inst in func.layout.iter_inst(block) {
            if let Some(call_info) = func.dfg.call_info(inst) {
                callees.insert(call_info.callee());
                continue;
            }

            match func.dfg.inst(inst).side_effect() {
                SideEffect::Read => local_mem.insert(FuncAttrs::MEM_READ),
                SideEffect::Write => local_mem.insert(FuncAttrs::MEM_WRITE),
                SideEffect::None | SideEffect::Control => {}
            }
        }
    }

    let mut callees: Vec<_> = callees.into_iter().collect();
    callees.sort_unstable_by_key(|f| f.as_u32());

    let mut reachable_exit_count = 0;
    let mut exits_all_return_like = true;
    let mut exits_all_terminate_like = true;
    let mut has_any_return_like_exit = false;

    for &exit in &cfg.exits {
        if !reachable.contains(&exit) {
            continue;
        }
        reachable_exit_count += 1;

        let term = func
            .layout
            .last_inst_of(exit)
            .expect("exit block has no terminator");
        let is_return_like = func.dfg.is_return(term);

        exits_all_return_like &= is_return_like;
        has_any_return_like_exit |= is_return_like;
    }

    if reachable_exit_count == 0 {
        exits_all_return_like = false;
        exits_all_terminate_like = false;
    }

    LocalFacts {
        local_mem,
        callees,
        has_body: true,
        cfg_has_cycle,
        exits_all_return_like,
        exits_all_terminate_like,
        has_any_return_like_exit,
    }
}

fn compute_reachable(cfg: &ControlFlowGraph, entry: BlockId) -> BTreeSet<BlockId> {
    let mut reachable = BTreeSet::new();
    let mut stack = vec![entry];

    while let Some(block) = stack.pop() {
        if !reachable.insert(block) {
            continue;
        }
        for &succ in cfg.succs_of(block) {
            stack.push(succ);
        }
    }

    reachable
}

fn topo_sort_sccs(
    sccs: &[module_analysis::SccRef],
    succ_sccs: &SecondaryMap<module_analysis::SccRef, Vec<module_analysis::SccRef>>,
) -> Vec<module_analysis::SccRef> {
    let mut indegree = SecondaryMap::<module_analysis::SccRef, u32>::new();
    for &scc in sccs {
        indegree[scc] = 0;
    }
    for &scc in sccs {
        for &succ in &succ_sccs[scc] {
            indegree[succ] += 1;
        }
    }

    let mut ready = BTreeSet::new();
    for &scc in sccs {
        if indegree[scc] == 0 {
            ready.insert(scc);
        }
    }

    let mut topo = Vec::with_capacity(sccs.len());
    while let Some(scc) = ready.pop_first() {
        topo.push(scc);
        for &succ in &succ_sccs[scc] {
            indegree[succ] -= 1;
            if indegree[succ] == 0 {
                ready.insert(succ);
            }
        }
    }

    topo
}
