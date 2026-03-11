use std::collections::BTreeSet;

use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    BlockId, ControlFlowGraph, FuncEffectSummary, Function, InstDowncast, Module,
    inst::{
        control_flow,
        evm::{EvmInvalid, EvmReturn, EvmRevert, EvmSelfDestruct, EvmStop},
    },
    module::FuncRef,
};

use crate::{cfg_scc::CfgSccAnalysis, module_analysis};

#[derive(Debug, Default, Clone)]
struct LocalFacts {
    local_effects: FuncEffectSummary,
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
    effects: SecondaryMap<FuncRef, FuncEffectSummary>,
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
        let mut effects = SecondaryMap::<FuncRef, FuncEffectSummary>::new();

        for &func_ref in &funcs {
            is_external[func_ref] = module.ctx.func_linkage(func_ref).is_external();
            locals[func_ref] = module.func_store.view(func_ref, compute_local_facts);

            let facts = &locals[func_ref];
            effects[func_ref] = if is_external[func_ref] || !facts.has_body {
                FuncEffectSummary::unknown_call()
            } else {
                FuncEffectSummary::default()
            };

            if !is_external[func_ref] && facts.has_body && !facts.has_any_return_like_exit {
                effects[func_ref].noreturn = true;
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
            effects,
            info,
            topo,
            succ_sccs,
        }
    }

    fn analyze(mut self) {
        self.propagate_effects();
        self.propagate_terminal_behavior();
        self.propagate_may_commit_visible_writes();

        let mut effects = FxHashMap::default();
        for func_ref in self.module.func_store.funcs() {
            effects.insert(func_ref, self.effects[func_ref].clone());
        }
        self.module.ctx.set_all_func_effects(effects);
    }

    fn propagate_effects(&mut self) {
        let mut scc_effects = SecondaryMap::<module_analysis::SccRef, FuncEffectSummary>::new();
        for &scc in self.topo.iter().rev() {
            let scc_info = self.info.scc.scc_info(scc);
            let mut comps: Vec<_> = scc_info.components.iter().copied().collect();
            comps.sort_unstable_by_key(|f| f.as_u32());

            let mut summary = FuncEffectSummary::default();
            for &func_ref in &comps {
                let local = if self.is_external[func_ref] || !self.locals[func_ref].has_body {
                    FuncEffectSummary::unknown_call()
                } else {
                    self.locals[func_ref].local_effects.clone()
                };
                summary.union_with(&local);
            }
            for &succ in &self.succ_sccs[scc] {
                summary.union_with(&scc_effects[succ]);
            }

            scc_effects[scc] = summary.clone();
            for func_ref in comps {
                let mut merged = summary.clone();
                merged.noreturn = self.effects[func_ref].noreturn;
                merged.will_return = self.effects[func_ref].will_return;
                merged.will_terminate = self.effects[func_ref].will_terminate;
                self.effects[func_ref] = merged;
            }
        }
    }

    fn propagate_terminal_behavior(&mut self) {
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

                if !self.effects[func_ref].noreturn {
                    let effects = &self.effects;
                    let has_return = self
                        .module
                        .func_store
                        .view(func_ref, |func| has_reachable_return(func, effects));
                    if !has_return {
                        self.effects[func_ref].noreturn = true;
                    }
                }

                if facts.cfg_has_cycle {
                    continue;
                }

                let mut can_terminate = facts.exits_all_terminate_like;
                let mut can_return = facts.exits_all_return_like;
                for &callee in &facts.callees {
                    can_terminate &= self.effects[callee].will_terminate;
                    can_return &= self.effects[callee].will_return;
                    if !can_terminate && !can_return {
                        break;
                    }
                }

                if can_return {
                    self.effects[func_ref].noreturn = false;
                    self.effects[func_ref].will_return = true;
                    self.effects[func_ref].will_terminate = true;
                } else if can_terminate {
                    self.effects[func_ref].will_terminate = true;
                }
            }
        }
    }

    fn propagate_may_commit_visible_writes(&mut self) {
        for &scc in self.topo.iter().rev() {
            let scc_info = self.info.scc.scc_info(scc);
            let mut comps: Vec<_> = scc_info.components.iter().copied().collect();
            comps.sort_unstable_by_key(|f| f.as_u32());

            let mut changed = true;
            while changed {
                changed = false;

                for &func_ref in &comps {
                    if self.is_external[func_ref] || !self.locals[func_ref].has_body {
                        continue;
                    }

                    let effects = &self.effects;
                    let may_commit = self.module.func_store.view(func_ref, |func| {
                        has_reachable_committing_exit(func, effects)
                    });
                    if may_commit != self.effects[func_ref].may_commit_visible_writes {
                        self.effects[func_ref].may_commit_visible_writes = may_commit;
                        changed = true;
                    }
                }

                if !scc_info.is_cycle {
                    break;
                }
            }
        }
    }
}

fn has_reachable_committing_exit(
    func: &Function,
    effects: &SecondaryMap<FuncRef, FuncEffectSummary>,
) -> bool {
    let Some(entry) = func.layout.entry_block() else {
        return false;
    };

    let mut cfg = ControlFlowGraph::new();
    cfg.compute(func);
    let reachable = cfg.reachable_blocks();
    let reachable_exit_blocks: FxHashSet<BlockId> = cfg
        .exits
        .iter()
        .copied()
        .filter(|&block| reachable[block])
        .collect();

    let mut visited = FxHashSet::default();
    let mut stack = vec![entry];
    while let Some(block) = stack.pop() {
        if !visited.insert(block) {
            continue;
        }

        match block_terminal_call_commits_visible_writes(func, block, effects) {
            Some(true) => return true,
            Some(false) => continue,
            None => {}
        }

        if reachable_exit_blocks.contains(&block)
            && func
                .layout
                .last_inst_of(block)
                .is_some_and(|term| is_committing_exit(func, term))
        {
            return true;
        }

        for &succ in cfg.succs_of(block) {
            stack.push(succ);
        }
    }

    false
}

fn has_reachable_return(
    func: &Function,
    effects: &SecondaryMap<FuncRef, FuncEffectSummary>,
) -> bool {
    let Some(entry) = func.layout.entry_block() else {
        return false;
    };

    let mut cfg = ControlFlowGraph::new();
    cfg.compute(func);

    let mut visited = FxHashSet::default();
    let mut stack = vec![entry];
    while let Some(block) = stack.pop() {
        if !visited.insert(block) || has_noreturn_call(func, block, effects) {
            continue;
        }

        if func
            .layout
            .last_inst_of(block)
            .is_some_and(|term| is_return_like_exit(func, term))
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
    effects: &SecondaryMap<FuncRef, FuncEffectSummary>,
) -> bool {
    for inst in func.layout.iter_inst(block) {
        if func
            .dfg
            .call_info(inst)
            .is_some_and(|call| effects[call.callee()].noreturn)
        {
            return true;
        }

        if func.dfg.is_terminator(inst) {
            break;
        }
    }

    false
}

fn block_terminal_call_commits_visible_writes(
    func: &Function,
    block: BlockId,
    effects: &SecondaryMap<FuncRef, FuncEffectSummary>,
) -> Option<bool> {
    for inst in func.layout.iter_inst(block) {
        if let Some(call) = func.dfg.call_info(inst)
            && effects[call.callee()].noreturn
        {
            return Some(effects[call.callee()].may_commit_visible_writes);
        }

        if func.dfg.is_terminator(inst) {
            break;
        }
    }

    None
}

fn compute_local_facts(func: &Function) -> LocalFacts {
    if func.layout.entry_block().is_none() {
        return LocalFacts {
            has_body: false,
            ..Default::default()
        };
    }

    let mut cfg = ControlFlowGraph::new();
    cfg.compute(func);

    let reachable = cfg.reachable_blocks();

    let mut cfg_scc = CfgSccAnalysis::new();
    cfg_scc.compute(&cfg);

    let cfg_has_cycle = cfg_scc
        .topo_order()
        .iter()
        .any(|&scc| cfg_scc.scc_data(scc).is_cycle);

    let mut local_effects = FuncEffectSummary::default();
    let mut callees = FxHashSet::default();

    for block in func.layout.iter_block() {
        if !reachable[block] {
            continue;
        }

        for inst in func.layout.iter_inst(block) {
            if let Some(call_info) = func.dfg.call_info(inst) {
                callees.insert(call_info.callee());
                continue;
            }

            local_effects.summarize_inst_effects(&func.dfg.effects(inst));
        }
    }

    let mut callees: Vec<_> = callees.into_iter().collect();
    callees.sort_unstable_by_key(|f| f.as_u32());

    let mut reachable_exit_count = 0;
    let mut exits_all_return_like = true;
    let mut exits_all_terminate_like = true;
    let mut has_any_return_like_exit = false;

    for &exit in &cfg.exits {
        if !reachable[exit] {
            continue;
        }
        reachable_exit_count += 1;

        let term = func
            .layout
            .last_inst_of(exit)
            .expect("exit block has no terminator");
        let is_return_like = is_return_like_exit(func, term);

        exits_all_return_like &= is_return_like;
        has_any_return_like_exit |= is_return_like;
    }

    if reachable_exit_count == 0 {
        exits_all_return_like = false;
        exits_all_terminate_like = false;
    }

    LocalFacts {
        local_effects,
        callees,
        has_body: true,
        cfg_has_cycle,
        exits_all_return_like,
        exits_all_terminate_like,
        has_any_return_like_exit,
    }
}

fn is_return_like_exit(func: &Function, inst: sonatina_ir::InstId) -> bool {
    let inst_data = func.dfg.inst(inst);
    let is = func.inst_set();
    <&control_flow::Return as InstDowncast>::downcast(is, inst_data).is_some()
}

fn is_committing_exit(func: &Function, inst: sonatina_ir::InstId) -> bool {
    let inst_data = func.dfg.inst(inst);
    let is = func.inst_set();

    if <&control_flow::Return as InstDowncast>::downcast(is, inst_data).is_some()
        || <&EvmReturn as InstDowncast>::downcast(is, inst_data).is_some()
        || <&EvmSelfDestruct as InstDowncast>::downcast(is, inst_data).is_some()
        || <&EvmStop as InstDowncast>::downcast(is, inst_data).is_some()
    {
        return true;
    }

    <&EvmRevert as InstDowncast>::downcast(is, inst_data).is_none()
        && <&EvmInvalid as InstDowncast>::downcast(is, inst_data).is_none()
        && <&control_flow::Unreachable as InstDowncast>::downcast(is, inst_data).is_none()
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

#[cfg(test)]
mod tests {
    use super::*;
    use sonatina_ir::{
        OtherEffects,
        isa::evm::space::{MEMORY, RETURNDATA, STORAGE, TRANSIENT},
    };
    use sonatina_parser::parse_module;

    fn parse(src: &str) -> Module {
        parse_module(src)
            .unwrap_or_else(|errs| panic!("parse failed: {errs:?}"))
            .module
    }

    fn find_func(module: &Module, name: &str) -> FuncRef {
        module
            .func_store
            .funcs()
            .into_iter()
            .find(|func_ref| module.ctx.func_sig(*func_ref, |sig| sig.name() == name))
            .expect("function should exist")
    }

    #[test]
    fn propagates_storage_reads_through_internal_calls() {
        let module = parse(
            r#"
target = "evm-ethereum-osaka"

func private %read_storage() -> i256 {
    block0:
        v0.i256 = evm_sload 1.i256;
        return v0;
}

func private %caller() -> i256 {
    block0:
        v0.i256 = call %read_storage;
        return v0;
}
"#,
        );

        analyze_module(&module);

        let caller = find_func(&module, "caller");
        let effects = module.ctx.func_effects(caller);
        assert!(effects.may_read_spaces.contains(STORAGE));
        assert!(!effects.may_write_spaces.contains(STORAGE));
        assert!(!effects.noreturn);
    }

    #[test]
    fn evm_return_exit_marks_functions_as_noreturn() {
        let module = parse(
            r#"
target = "evm-ethereum-osaka"

func private %return_unit() {
    block0:
        evm_return 0.i256 0.i256;
}

func private %caller() {
    block0:
        call %return_unit;
        return;
}
"#,
        );

        analyze_module(&module);

        let callee = find_func(&module, "return_unit");
        let callee_effects = module.ctx.func_effects(callee);
        assert!(callee_effects.noreturn);
        assert!(!callee_effects.will_return);
        assert!(callee_effects.will_terminate);

        let caller = find_func(&module, "caller");
        let caller_effects = module.ctx.func_effects(caller);
        assert!(caller_effects.noreturn);
        assert!(!caller_effects.will_return);
        assert!(caller_effects.will_terminate);
        assert!(caller_effects.may_commit_visible_writes);
    }

    #[test]
    fn distinguishes_committing_noreturn_helpers_from_reverting_helpers() {
        let module = parse(
            r#"
target = "evm-ethereum-osaka"

func private %commit() {
    block0:
        evm_return 0.i256 0.i256;
}

func private %revert_now() {
    block0:
        evm_revert 0.i256 0.i256;
}

func private %caller_commit() {
    block0:
        call %commit;
        unreachable;
}

func private %caller_revert() {
    block0:
        call %revert_now;
        unreachable;
}
"#,
        );

        analyze_module(&module);

        let commit = find_func(&module, "commit");
        let commit_effects = module.ctx.func_effects(commit);
        assert!(commit_effects.noreturn);
        assert!(commit_effects.may_commit_visible_writes);

        let revert_now = find_func(&module, "revert_now");
        let revert_effects = module.ctx.func_effects(revert_now);
        assert!(revert_effects.noreturn);
        assert!(!revert_effects.may_commit_visible_writes);

        let caller_commit = find_func(&module, "caller_commit");
        let caller_commit_effects = module.ctx.func_effects(caller_commit);
        assert!(caller_commit_effects.noreturn);
        assert!(caller_commit_effects.may_commit_visible_writes);

        let caller_revert = find_func(&module, "caller_revert");
        let caller_revert_effects = module.ctx.func_effects(caller_revert);
        assert!(caller_revert_effects.noreturn);
        assert!(!caller_revert_effects.may_commit_visible_writes);
    }

    #[test]
    fn internal_branches_do_not_mark_noreturn_loops_as_committing() {
        let module = parse(
            r#"
target = "evm-ethereum-osaka"

func private %spin(v0.i1) {
    block0:
        br v0 block1 block2;

    block1:
        jump block0;

    block2:
        jump block0;
}
"#,
        );

        analyze_module(&module);

        let spin = find_func(&module, "spin");
        let effects = module.ctx.func_effects(spin);
        assert!(effects.noreturn);
        assert!(!effects.may_commit_visible_writes);
    }

    #[test]
    fn propagates_create2_state_and_returndata_barriers_through_internal_calls() {
        let module = parse(
            r#"
target = "evm-ethereum-osaka"

func private %spawn(v0.i256, v1.i256) -> i256 {
    block0:
        v2.i256 = evm_create2 0.i256 v0 v1 0.i256;
        return v2;
}

func private %caller(v0.i256, v1.i256) -> i256 {
    block0:
        v2.i256 = call %spawn v0 v1;
        return v2;
}
"#,
        );

        analyze_module(&module);

        let caller = find_func(&module, "caller");
        let effects = module.ctx.func_effects(caller);
        assert!(effects.may_read_spaces.contains(STORAGE));
        assert!(effects.may_write_spaces.contains(STORAGE));
        assert!(effects.may_read_spaces.contains(TRANSIENT));
        assert!(effects.may_write_spaces.contains(TRANSIENT));
        assert!(effects.may_write_spaces.contains(RETURNDATA));
    }

    #[test]
    fn propagates_malloc_memory_barriers_through_internal_calls() {
        let module = parse(
            r#"
target = "evm-ethereum-osaka"

func private %alloc() -> *i8 {
    block0:
        v0.*i8 = evm_malloc 32.i256;
        return v0;
}

func private %caller() -> *i8 {
    block0:
        v0.*i8 = call %alloc;
        return v0;
}
"#,
        );

        analyze_module(&module);

        let caller = find_func(&module, "caller");
        let effects = module.ctx.func_effects(caller);
        assert!(effects.may_read_spaces.contains(MEMORY));
        assert!(effects.may_write_spaces.contains(MEMORY));
        assert!(effects.other.contains(OtherEffects::ALLOC));
    }
}
