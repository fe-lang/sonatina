use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use sonatina_ir::{
    Function, InstId, Type, Value, ValueId,
    inst::{control_flow, control_flow::BranchKind, downcast},
    module::{FuncRef, Module},
};

use crate::{analysis::func_behavior, module_analysis::CallGraph};

use super::signature_rewrite::{
    SignatureRewritePlan, propagate_signature_rewrite_types, retain_higher_order_safe_plans,
    rewrite_declared_signatures,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DeadArgElimConfig {
    pub private_only: bool,
    pub require_higher_order_safe: bool,
}

impl Default for DeadArgElimConfig {
    fn default() -> Self {
        Self {
            private_only: true,
            require_higher_order_safe: true,
        }
    }
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct DeadArgElimStats {
    pub eligible_funcs: usize,
    pub rewritten_funcs: usize,
    pub removed_args: usize,
    pub rewritten_calls: usize,
    pub blocked_higher_order_funcs: usize,
    pub rounds: usize,
}

#[derive(Clone)]
struct FuncPlan {
    keep_args: Vec<bool>,
    new_arg_tys: SmallVec<[Type; 8]>,
    new_ret_tys: SmallVec<[Type; 2]>,
}

impl SignatureRewritePlan for FuncPlan {
    fn new_arg_tys(&self) -> &[Type] {
        &self.new_arg_tys
    }

    fn new_ret_tys(&self) -> &[Type] {
        &self.new_ret_tys
    }

    fn is_higher_order_compatible(&self, other: &Self) -> bool {
        self.keep_args == other.keep_args && self.new_ret_tys == other.new_ret_tys
    }
}

pub fn run_dead_arg_elim(module: &Module, config: DeadArgElimConfig) -> DeadArgElimStats {
    func_behavior::analyze_module(module);
    let initial_candidate = collect_candidate_funcs(module, config);
    let mut stats = DeadArgElimStats {
        eligible_funcs: initial_candidate.len(),
        ..DeadArgElimStats::default()
    };
    if initial_candidate.is_empty() {
        return stats;
    }

    let mut candidate = initial_candidate;
    let mut blocked = FxHashSet::default();
    let final_plans = loop {
        stats.rounds += 1;
        let call_graph = CallGraph::build_graph_subset(module, &candidate);
        let reverse_callers = build_reverse_callers(&call_graph);
        let live_args = solve_live_arg_fixpoint(module, &candidate, &reverse_callers);
        let mut plans = collect_plans(module, &candidate, &live_args);
        if config.require_higher_order_safe {
            let before: FxHashSet<_> = plans.keys().copied().collect();
            retain_higher_order_safe_plans(module, &mut plans);
            for func in before {
                if !plans.contains_key(&func) {
                    blocked.insert(func);
                }
            }
        }

        let next_candidate: FxHashSet<_> = plans.keys().copied().collect();
        if next_candidate == candidate {
            break plans;
        }
        if next_candidate.is_empty() {
            break FxHashMap::default();
        }
        candidate = next_candidate;
    };

    stats.blocked_higher_order_funcs = blocked.len();
    stats.rewritten_funcs = final_plans.len();
    stats.removed_args = final_plans
        .values()
        .map(|plan| plan.keep_args.iter().filter(|keep| !**keep).count())
        .sum();

    if final_plans.is_empty() {
        return stats;
    }

    let old_sigs = rewrite_declared_signatures(module, &final_plans);
    for (&func_ref, plan) in &final_plans {
        module.func_store.modify(func_ref, |function| {
            rewrite_function(function, plan);
        });
    }

    let funcs = module.funcs();
    for func_ref in funcs {
        stats.rewritten_calls += module
            .func_store
            .modify(func_ref, |function| rewrite_calls(function, &final_plans));
    }

    propagate_signature_rewrite_types(module, &old_sigs);
    stats
}

fn is_dead_arg_root_inst(function: &Function, inst: InstId) -> bool {
    function.dfg.is_terminator(inst) || function.dfg.effect_summary(inst).has_effect()
}

fn collect_candidate_funcs(module: &Module, config: DeadArgElimConfig) -> FxHashSet<FuncRef> {
    module
        .funcs()
        .into_iter()
        .filter(|&func_ref| {
            let linkage = module.ctx.func_linkage(func_ref);
            linkage.has_definition() && (!config.private_only || linkage.is_private())
        })
        .collect()
}

fn build_reverse_callers(call_graph: &CallGraph) -> FxHashMap<FuncRef, Vec<FuncRef>> {
    let mut reverse = FxHashMap::<FuncRef, Vec<FuncRef>>::default();
    for func in call_graph.funcs() {
        reverse.entry(func).or_default();
        for &callee in call_graph.callee_of(func) {
            reverse.entry(callee).or_default().push(func);
        }
    }
    for callers in reverse.values_mut() {
        callers.sort_unstable_by_key(|func| func.as_u32());
        callers.dedup();
    }
    reverse
}

fn solve_live_arg_fixpoint(
    module: &Module,
    candidate: &FxHashSet<FuncRef>,
    reverse_callers: &FxHashMap<FuncRef, Vec<FuncRef>>,
) -> FxHashMap<FuncRef, Vec<bool>> {
    let mut live_args: FxHashMap<FuncRef, Vec<bool>> = candidate
        .iter()
        .copied()
        .map(|func_ref| {
            let arg_len = module
                .ctx
                .get_sig(func_ref)
                .map(|sig| sig.args().len())
                .unwrap_or_default();
            (func_ref, vec![false; arg_len])
        })
        .collect();
    let mut worklist: Vec<_> = candidate.iter().copied().collect();
    worklist.sort_unstable_by_key(|func| func.as_u32());

    while let Some(func_ref) = worklist.pop() {
        let new_mask = analyze_func(module, func_ref, candidate, &live_args);
        let Some(current) = live_args.get_mut(&func_ref) else {
            continue;
        };
        let mut changed = false;
        for (slot, new_live) in current.iter_mut().zip(new_mask) {
            if new_live && !*slot {
                *slot = true;
                changed = true;
            }
        }
        if changed && let Some(callers) = reverse_callers.get(&func_ref) {
            worklist.extend(callers.iter().copied());
        }
    }

    live_args
}

fn analyze_func(
    module: &Module,
    func_ref: FuncRef,
    candidate: &FxHashSet<FuncRef>,
    live_args: &FxHashMap<FuncRef, Vec<bool>>,
) -> Vec<bool> {
    let Some(sig) = module.ctx.get_sig(func_ref) else {
        return Vec::new();
    };
    let mut live_mask = vec![false; sig.args().len()];
    module.func_store.view(func_ref, |function| {
        let mut visited_insts = FxHashSet::default();
        let mut value_worklist = Vec::new();

        for block in function.layout.iter_block() {
            for inst in function.layout.iter_inst(block) {
                if is_dead_arg_root_inst(function, inst) {
                    collect_inst_inputs(
                        function,
                        inst,
                        candidate,
                        live_args,
                        &mut visited_insts,
                        &mut value_worklist,
                    );
                }
            }
        }

        while let Some(value) = value_worklist.pop() {
            match function.dfg.value(value) {
                Value::Arg { idx, .. } => {
                    if let Some(slot) = live_mask.get_mut(*idx) {
                        *slot = true;
                    }
                }
                Value::Inst { inst, .. } => collect_inst_inputs(
                    function,
                    *inst,
                    candidate,
                    live_args,
                    &mut visited_insts,
                    &mut value_worklist,
                ),
                Value::Immediate { .. } | Value::Global { .. } | Value::Undef { .. } => {}
            }
        }
    });
    live_mask
}

fn collect_inst_inputs(
    function: &Function,
    inst: InstId,
    candidate: &FxHashSet<FuncRef>,
    live_args: &FxHashMap<FuncRef, Vec<bool>>,
    visited_insts: &mut FxHashSet<InstId>,
    value_worklist: &mut Vec<ValueId>,
) {
    if !visited_insts.insert(inst) {
        return;
    }

    if let Some(call) = function.dfg.cast_call(inst) {
        let callee = *call.callee();
        if candidate.contains(&callee)
            && let Some(mask) = live_args.get(&callee)
        {
            for (&arg, &is_live) in call.args().iter().zip(mask.iter()) {
                if is_live {
                    value_worklist.push(arg);
                }
            }
            return;
        }
        value_worklist.extend(call.args().iter().copied());
        return;
    }

    if let Some(phi) = function.dfg.cast_phi(inst) {
        value_worklist.extend(phi.args().iter().map(|(value, _)| *value));
        return;
    }

    if let Some(branch) = function.dfg.branch_info(inst) {
        match branch.branch_kind() {
            BranchKind::Jump(_) => return,
            BranchKind::Br(br) => {
                value_worklist.push(*br.cond());
                return;
            }
            BranchKind::BrTable(br_table) => {
                value_worklist.push(*br_table.scrutinee());
                value_worklist.extend(br_table.table().iter().map(|(value, _)| *value));
                return;
            }
        }
    }

    if let Some(ret) =
        downcast::<&control_flow::Return>(function.inst_set(), function.dfg.inst(inst))
    {
        value_worklist.extend(ret.args().iter().copied());
        return;
    }

    function
        .dfg
        .inst(inst)
        .for_each_value(&mut |value| value_worklist.push(value));
}

fn collect_plans(
    module: &Module,
    candidate: &FxHashSet<FuncRef>,
    live_args: &FxHashMap<FuncRef, Vec<bool>>,
) -> FxHashMap<FuncRef, FuncPlan> {
    let mut plans = FxHashMap::default();
    for &func_ref in candidate {
        let Some(sig) = module.ctx.get_sig(func_ref) else {
            continue;
        };
        let Some(mask) = live_args.get(&func_ref) else {
            continue;
        };
        if mask.iter().all(|live| *live) {
            continue;
        }
        let new_arg_tys = sig
            .args()
            .iter()
            .zip(mask.iter())
            .filter_map(|(&ty, &keep)| keep.then_some(ty))
            .collect();
        plans.insert(
            func_ref,
            FuncPlan {
                keep_args: mask.clone(),
                new_arg_tys,
                new_ret_tys: SmallVec::from_slice(sig.ret_tys()),
            },
        );
    }
    plans
}

fn rewrite_function(function: &mut Function, plan: &FuncPlan) {
    let old_args = function.arg_values.clone();
    let old_arg_tys: Vec<_> = old_args
        .iter()
        .map(|&arg| function.dfg.value_ty(arg))
        .collect();
    let mut new_args = SmallVec::new();
    for ((&arg, &keep), ty) in old_args.iter().zip(plan.keep_args.iter()).zip(old_arg_tys) {
        if keep {
            let idx = new_args.len();
            function.dfg.values[arg] = Value::Arg { ty, idx };
            new_args.push(arg);
        } else {
            function.dfg.values[arg] = Value::Undef { ty };
        }
    }
    function.arg_values = new_args;
}

fn rewrite_calls(function: &mut Function, plans: &FxHashMap<FuncRef, FuncPlan>) -> usize {
    let mut rewritten = 0;
    let blocks: Vec<_> = function.layout.iter_block().collect();
    for block in blocks {
        let insts: Vec<_> = function.layout.iter_inst(block).collect();
        for inst in insts {
            let Some(call) = function.dfg.cast_call(inst).cloned() else {
                continue;
            };
            let Some(plan) = plans.get(call.callee()) else {
                continue;
            };
            let new_args = call
                .args()
                .iter()
                .zip(plan.keep_args.iter())
                .filter_map(|(&arg, &keep)| keep.then_some(arg))
                .collect();
            function.dfg.replace_inst_preserving_results(
                inst,
                Box::new(control_flow::Call::new(
                    function
                        .inst_set()
                        .has_call()
                        .expect("target ISA must support `call`"),
                    *call.callee(),
                    new_args,
                )),
            );
            rewritten += 1;
        }
    }
    rewritten
}

#[cfg(test)]
mod tests {
    use sonatina_ir::{
        Module,
        ir_writer::{FuncWriter, ModuleWriter},
    };
    use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

    use super::{DeadArgElimConfig, run_dead_arg_elim};

    fn parse_module(input: &str) -> sonatina_parser::ParsedModule {
        sonatina_parser::parse_module(input).unwrap_or_else(|errs| panic!("parse failed: {errs:?}"))
    }

    fn dump_module(module: &Module) -> String {
        ModuleWriter::new(module).dump_string()
    }

    fn dump_function(module: &Module, name: &str) -> String {
        let func_ref = find_func(module, name);
        module.func_store.view(func_ref, |function| {
            FuncWriter::new(func_ref, function).dump_string()
        })
    }

    fn find_func(module: &Module, name: &str) -> sonatina_ir::module::FuncRef {
        module
            .funcs()
            .into_iter()
            .find(|&func_ref| module.ctx.func_sig(func_ref, |sig| sig.name() == name))
            .unwrap_or_else(|| panic!("missing function {name}"))
    }

    fn assert_verified(module: &Module) {
        let verifier = VerifierConfig::for_level(VerificationLevel::Fast);
        let report = verify_module(module, &verifier);
        assert!(!report.has_errors(), "verification failed: {report:?}");
    }

    fn assert_sig(module: &Module, name: &str, arg_len: usize, ret_len: usize) {
        let sig = module
            .ctx
            .get_sig(find_func(module, name))
            .unwrap_or_else(|| panic!("missing signature for {name}"));
        assert_eq!(sig.args().len(), arg_len, "{name} arg count");
        assert_eq!(sig.ret_tys().len(), ret_len, "{name} ret count");
    }

    #[test]
    fn removes_simple_acyclic_unused_param() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func private %id(v0.i256, v1.i256) -> i256 {
    block0:
        return v1;
}

func public %entry(v0.i256) -> i256 {
    block0:
        v1.i256 = call %id 0.i256 v0;
        return v1;
}
"#,
        );

        let stats = run_dead_arg_elim(&parsed.module, DeadArgElimConfig::default());

        assert_eq!(stats.rewritten_funcs, 1);
        assert_eq!(stats.removed_args, 1);
        assert_sig(&parsed.module, "id", 1, 1);
        let dumped = dump_module(&parsed.module);
        assert!(dumped.contains("v1.i256 = call %id v0;"));
        assert_verified(&parsed.module);
    }

    #[test]
    fn removes_dead_arg_through_call_chain() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func private %sink(v0.i256, v1.i256) -> i256 {
    block0:
        return v1;
}

func private %mid(v0.i256, v1.i256) -> i256 {
    block0:
        v2.i256 = add v0 1.i256;
        v3.i256 = call %sink v2 v1;
        return v3;
}

func public %entry(v0.i256) -> i256 {
    block0:
        v1.i256 = call %mid 7.i256 v0;
        return v1;
}
"#,
        );

        let stats = run_dead_arg_elim(&parsed.module, DeadArgElimConfig::default());

        assert_eq!(stats.rewritten_funcs, 2);
        assert_eq!(stats.removed_args, 2);
        assert_sig(&parsed.module, "sink", 1, 1);
        assert_sig(&parsed.module, "mid", 1, 1);
        let dumped = dump_module(&parsed.module);
        assert!(dumped.contains("v3.i256 = call %sink v1;"));
        assert!(dumped.contains("v1.i256 = call %mid v0;"));
        assert_verified(&parsed.module);
    }

    #[test]
    fn removes_dead_arg_in_self_recursive_cycle() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func private %self(v0.i1, v1.i256) -> i256 {
    block0:
        br v0 block1 block2;

    block1:
        return 0.i256;

    block2:
        v2.i256 = call %self 1.i1 99.i256;
        return v2;
}

func public %entry() -> i256 {
    block0:
        v0.i256 = call %self 0.i1 7.i256;
        return v0;
}
"#,
        );

        let stats = run_dead_arg_elim(&parsed.module, DeadArgElimConfig::default());

        assert_eq!(stats.rewritten_funcs, 1);
        assert_sig(&parsed.module, "self", 1, 1);
        let dumped = dump_module(&parsed.module);
        assert!(dumped.contains("v2.i256 = call %self 1.i1;"));
        assert!(dumped.contains("v0.i256 = call %self 0.i1;"));
        assert_verified(&parsed.module);
    }

    #[test]
    fn removes_dead_arg_in_mutual_recursion() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func private %even(v0.i1, v1.i256) -> i256 {
    block0:
        br v0 block1 block2;

    block1:
        return 0.i256;

    block2:
        v2.i256 = call %odd 1.i1 41.i256;
        return v2;
}

func private %odd(v0.i1, v1.i256) -> i256 {
    block0:
        br v0 block1 block2;

    block1:
        return 1.i256;

    block2:
        v2.i256 = call %even 1.i1 42.i256;
        return v2;
}

func public %entry() -> i256 {
    block0:
        v0.i256 = call %even 0.i1 7.i256;
        return v0;
}
"#,
        );

        let stats = run_dead_arg_elim(&parsed.module, DeadArgElimConfig::default());

        assert_eq!(stats.rewritten_funcs, 2);
        assert_sig(&parsed.module, "even", 1, 1);
        assert_sig(&parsed.module, "odd", 1, 1);
        let dumped = dump_module(&parsed.module);
        assert!(dumped.contains("v2.i256 = call %odd 1.i1;"));
        assert!(dumped.contains("v2.i256 = call %even 1.i1;"));
        assert_verified(&parsed.module);
    }

    #[test]
    fn pure_dead_call_does_not_keep_caller_arg_live() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func private %pure(v0.i256) -> i256 {
    block0:
        return v0;
}

func private %caller(v0.i256) -> i256 {
    block0:
        v1.i256 = call %pure v0;
        return 0.i256;
}

func public %entry(v0.i256) -> i256 {
    block0:
        v1.i256 = call %caller v0;
        return v1;
}
"#,
        );

        let stats = run_dead_arg_elim(&parsed.module, DeadArgElimConfig::default());

        assert_eq!(stats.rewritten_funcs, 1);
        assert_eq!(stats.removed_args, 1);
        assert_sig(&parsed.module, "caller", 0, 1);
        let dumped = dump_module(&parsed.module);
        assert!(dumped.contains("v1.i256 = call %pure undef.i256;"));
        assert!(dumped.contains("v1.i256 = call %caller;"));
        assert_verified(&parsed.module);
    }

    #[test]
    fn impure_call_keeps_only_callee_live_actuals() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func private %writer(v0.i256, v1.i256) {
    block0:
        evm_sstore 0.i256 v1;
        return;
}

func private %caller(v0.i256, v1.i256) -> i256 {
    block0:
        call %writer v0 v1;
        return v1;
}

func public %entry(v0.i256) -> i256 {
    block0:
        v1.i256 = call %caller 9.i256 v0;
        return v1;
}
"#,
        );

        let stats = run_dead_arg_elim(&parsed.module, DeadArgElimConfig::default());

        assert_eq!(stats.rewritten_funcs, 2);
        assert_eq!(stats.removed_args, 2);
        assert_sig(&parsed.module, "writer", 1, 0);
        assert_sig(&parsed.module, "caller", 1, 1);
        let caller = dump_function(&parsed.module, "caller");
        assert!(caller.contains("call %writer v1;"));
        let dumped = dump_module(&parsed.module);
        assert!(dumped.contains("v1.i256 = call %caller v0;"));
        assert_verified(&parsed.module);
    }

    #[test]
    fn read_side_effect_keeps_arg_live() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func private %reader(v0.i256) -> i256 {
    block0:
        v1.i256 = evm_sload v0;
        return 0.i256;
}

func public %entry(v0.i256) -> i256 {
    block0:
        v1.i256 = call %reader v0;
        return v1;
}
"#,
        );

        let stats = run_dead_arg_elim(&parsed.module, DeadArgElimConfig::default());

        assert_eq!(stats.rewritten_funcs, 0);
        assert_eq!(stats.removed_args, 0);
        assert_sig(&parsed.module, "reader", 1, 1);
        let dumped = dump_function(&parsed.module, "reader");
        assert!(dumped.contains("v1.i256 = evm_sload v0;"));
        assert_verified(&parsed.module);
    }

    #[test]
    fn unused_read_only_call_keeps_caller_arg_live() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func private %reader(v0.i256) -> i256 {
    block0:
        v1.i256 = evm_sload v0;
        return 0.i256;
}

func private %caller(v0.i256) -> i256 {
    block0:
        v1.i256 = call %reader v0;
        return 0.i256;
}

func public %entry(v0.i256) -> i256 {
    block0:
        v1.i256 = call %caller v0;
        return v1;
}
"#,
        );

        let stats = run_dead_arg_elim(&parsed.module, DeadArgElimConfig::default());

        assert_eq!(stats.rewritten_funcs, 0);
        assert_eq!(stats.removed_args, 0);
        assert_sig(&parsed.module, "caller", 1, 1);
        let caller = dump_function(&parsed.module, "caller");
        assert!(caller.contains("v1.i256 = call %reader v0;"));
        let dumped = dump_module(&parsed.module);
        assert!(dumped.contains("v1.i256 = call %caller v0;"));
        assert_verified(&parsed.module);
    }

    #[test]
    fn skips_public_and_external_functions() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

declare external %ext(i256, i256) -> i256;

func public %pub(v0.i256, v1.i256) -> i256 {
    block0:
        return v1;
}

func private %priv(v0.i256, v1.i256) -> i256 {
    block0:
        return v1;
}

func public %entry(v0.i256) -> i256 {
    block0:
        v1.i256 = call %priv 0.i256 v0;
        v2.i256 = call %pub 0.i256 v1;
        v3.i256 = call %ext 0.i256 v2;
        return v3;
}
"#,
        );

        let stats = run_dead_arg_elim(&parsed.module, DeadArgElimConfig::default());

        assert_eq!(stats.eligible_funcs, 1);
        assert_eq!(stats.rewritten_funcs, 1);
        assert_sig(&parsed.module, "priv", 1, 1);
        assert_sig(&parsed.module, "pub", 2, 1);
        let dumped = dump_module(&parsed.module);
        assert!(dumped.contains("declare external %ext(i256, i256) -> i256"));
        assert!(dumped.contains("v2.i256 = call %pub 0.i256 v1;"));
        assert_verified(&parsed.module);
    }

    #[test]
    fn live_get_function_ptr_blocks_unsafe_partial_rewrite() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

type @cb_box = { *(i256, i256) -> i256 };

func private %a(v0.i256, v1.i256) -> i256 {
    block0:
        return v1;
}

func private %b(v0.i256, v1.i256) -> i256 {
    block0:
        return v0;
}

func private %register() {
    block0:
        v0.*(i256, i256) -> i256 = get_function_ptr %a;
        v1.@cb_box = insert_value undef.@cb_box 0.i8 v0;
        return;
}

func public %entry(v0.i256) -> i256 {
    block0:
        call %register;
        v1.i256 = call %a 0.i256 v0;
        return v1;
}
"#,
        );

        let stats = run_dead_arg_elim(&parsed.module, DeadArgElimConfig::default());

        assert_eq!(stats.rewritten_funcs, 0);
        assert_sig(&parsed.module, "a", 2, 1);
        let dumped = dump_module(&parsed.module);
        assert!(dumped.contains("v1.i256 = call %a 0.i256 v0;"));
        assert_verified(&parsed.module);
    }

    #[test]
    fn exposed_non_private_function_types_block_rewrite() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

type @cb_box = { *(i256, i256) -> i256 };

func public %consume(v0.@cb_box) {
    block0:
        return;
}

func private %a(v0.i256, v1.i256) -> i256 {
    block0:
        return v1;
}

func private %register() {
    block0:
        v0.*(i256, i256) -> i256 = get_function_ptr %a;
        v1.@cb_box = insert_value undef.@cb_box 0.i8 v0;
        call %consume v1;
        return;
}

func public %entry(v0.i256) -> i256 {
    block0:
        call %register;
        v1.i256 = call %a 0.i256 v0;
        return v1;
}
"#,
        );

        let stats = run_dead_arg_elim(&parsed.module, DeadArgElimConfig::default());

        assert_eq!(stats.blocked_higher_order_funcs, 1);
        assert_eq!(stats.rewritten_funcs, 0);
        assert_sig(&parsed.module, "a", 2, 1);
        assert_verified(&parsed.module);
    }

    #[test]
    fn preserves_multi_result_callsites() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func private %pair(v0.i256, v1.i256) -> (i256, i256) {
    block0:
        v2.i256 = add v1 1.i256;
        return (v1, v2);
}

func public %entry(v0.i256) -> i256 {
    block0:
        (v1.i256, v2.i256) = call %pair 0.i256 v0;
        v3.i256 = add v1 v2;
        return v3;
}
"#,
        );

        let stats = run_dead_arg_elim(&parsed.module, DeadArgElimConfig::default());

        assert_eq!(stats.rewritten_funcs, 1);
        assert_sig(&parsed.module, "pair", 1, 2);
        let dumped = dump_module(&parsed.module);
        assert!(dumped.contains("(v1.i256, v2.i256) = call %pair v0;"));
        assert_verified(&parsed.module);
    }

    #[test]
    fn rewrites_removed_formal_to_undef_in_body() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func private %drop_first(v0.i256, v1.i256) -> i256 {
    block0:
        v2.i256 = add v0 1.i256;
        return v1;
}
"#,
        );

        run_dead_arg_elim(&parsed.module, DeadArgElimConfig::default());

        let dumped = dump_function(&parsed.module, "drop_first");
        assert!(dumped.contains("v2.i256 = add undef.i256 1.i256;"));
        assert_verified(&parsed.module);
    }
}
