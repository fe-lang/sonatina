use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    Function, Immediate, Type,
    module::{FuncRef, Module},
};

use super::signature_rewrite::collect_live_get_function_ptr_funcs;

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub(crate) struct UniformConstArgStats {
    pub(crate) changed: bool,
    pub(crate) eligible_funcs: usize,
    pub(crate) rewritten_funcs: usize,
    pub(crate) bound_args: usize,
    pub(crate) analyzed_callsites: usize,
    pub(crate) blocked_get_function_ptr_funcs: usize,
}

#[derive(Clone)]
struct Candidate {
    arg_tys: Vec<Type>,
    bindable_args: Vec<usize>,
}

#[derive(Clone)]
struct FuncPlan {
    bindings: Vec<ArgBinding>,
}

#[derive(Clone)]
struct ArgBinding {
    arg_idx: usize,
    imm: Immediate,
}

pub(crate) fn run_uniform_const_arg_binding(
    module: &Module,
    funcs: &[FuncRef],
) -> UniformConstArgStats {
    let funcs: FxHashSet<_> = funcs.iter().copied().collect();
    let live_get_fn_funcs = collect_live_get_function_ptr_funcs(module);
    let candidates = collect_candidates(module, &funcs, &live_get_fn_funcs);
    let mut stats = UniformConstArgStats {
        eligible_funcs: candidates.len(),
        blocked_get_function_ptr_funcs: live_get_fn_funcs
            .iter()
            .filter(|&&func| funcs.contains(&func))
            .count(),
        ..UniformConstArgStats::default()
    };
    if candidates.is_empty() {
        return stats;
    }

    let callsites = collect_callsites(module, &candidates);
    stats.analyzed_callsites = callsites.values().map(Vec::len).sum();
    let plans = collect_plans(&candidates, &callsites);
    if plans.is_empty() {
        return stats;
    }

    stats.rewritten_funcs = plans.len();
    stats.bound_args = plans.values().map(|plan| plan.bindings.len()).sum();
    stats.changed = stats.bound_args != 0;

    for (&func, plan) in &plans {
        module.func_store.modify(func, |function| {
            bind_args(function, plan);
        });
    }

    stats
}

fn collect_candidates(
    module: &Module,
    funcs: &FxHashSet<FuncRef>,
    live_get_fn_funcs: &FxHashSet<FuncRef>,
) -> FxHashMap<FuncRef, Candidate> {
    funcs
        .iter()
        .copied()
        .filter_map(|func| {
            if live_get_fn_funcs.contains(&func) || !module.func_store.contains(func) {
                return None;
            }

            let sig = module.ctx.get_sig(func)?;
            if !sig.linkage().is_private() {
                return None;
            }

            let arg_tys = sig.args().to_vec();
            let bindable_args = arg_tys
                .iter()
                .enumerate()
                .filter_map(|(idx, ty)| ty.is_integral().then_some(idx))
                .collect::<Vec<_>>();
            (!bindable_args.is_empty()).then_some((
                func,
                Candidate {
                    arg_tys,
                    bindable_args,
                },
            ))
        })
        .collect()
}

fn collect_callsites(
    module: &Module,
    candidates: &FxHashMap<FuncRef, Candidate>,
) -> FxHashMap<FuncRef, Vec<Vec<Option<Immediate>>>> {
    let mut callsites = FxHashMap::<FuncRef, Vec<Vec<Option<Immediate>>>>::default();

    for caller in module.funcs() {
        module.func_store.view(caller, |function| {
            for block in function.layout.iter_block() {
                for inst in function.layout.iter_inst(block) {
                    let Some(call) = function.dfg.cast_call(inst) else {
                        continue;
                    };
                    let callee = *call.callee();
                    let Some(candidate) = candidates.get(&callee) else {
                        continue;
                    };
                    let actuals = candidate
                        .bindable_args
                        .iter()
                        .map(|&arg_idx| {
                            call.args()
                                .get(arg_idx)
                                .and_then(|&arg| function.dfg.value_imm(arg))
                        })
                        .collect();
                    callsites.entry(callee).or_default().push(actuals);
                }
            }
        });
    }

    callsites
}

fn collect_plans(
    candidates: &FxHashMap<FuncRef, Candidate>,
    callsites: &FxHashMap<FuncRef, Vec<Vec<Option<Immediate>>>>,
) -> FxHashMap<FuncRef, FuncPlan> {
    let mut plans = FxHashMap::default();
    for (&func, candidate) in candidates {
        let Some(sites) = callsites.get(&func) else {
            continue;
        };
        if sites.len() < 2 {
            continue;
        }

        let bindings = candidate
            .bindable_args
            .iter()
            .enumerate()
            .filter_map(|(slot, &arg_idx)| {
                let arg_ty = candidate.arg_tys[arg_idx];
                let first = sites.first()?.get(slot).copied().flatten()?;
                if first.ty() != arg_ty {
                    return None;
                }
                sites
                    .iter()
                    .all(|site| site.get(slot).copied().flatten() == Some(first))
                    .then_some(ArgBinding {
                        arg_idx,
                        imm: first,
                    })
            })
            .collect::<Vec<_>>();
        if !bindings.is_empty() {
            plans.insert(func, FuncPlan { bindings });
        }
    }
    plans
}

fn bind_args(function: &mut Function, plan: &FuncPlan) {
    for binding in &plan.bindings {
        let arg = function.arg_values[binding.arg_idx];
        debug_assert_eq!(function.dfg.value_ty(arg), binding.imm.ty());
        let replacement = function.dfg.make_imm_value(binding.imm);
        function.dfg.change_to_alias(arg, replacement);
    }
}

#[cfg(test)]
mod tests {
    use sonatina_ir::{
        ControlFlowGraph, Module,
        ir_writer::{FuncWriter, ModuleWriter},
        module::FuncRef,
    };
    use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

    use super::run_uniform_const_arg_binding;
    use crate::optim::{
        dead_arg::{DeadArgElimConfig, run_dead_arg_elim},
        sccp::SccpSolver,
    };

    fn parse_module(input: &str) -> sonatina_parser::ParsedModule {
        sonatina_parser::parse_module(input).unwrap()
    }

    fn find_func(module: &Module, name: &str) -> FuncRef {
        module
            .ctx
            .declared_funcs
            .iter()
            .find_map(|entry| (entry.value().name() == name).then_some(*entry.key()))
            .unwrap_or_else(|| panic!("missing function {name}"))
    }

    fn assert_sig(module: &Module, name: &str, args: usize, rets: usize) {
        let func = find_func(module, name);
        let sig = module
            .ctx
            .get_sig(func)
            .unwrap_or_else(|| panic!("missing signature for {name}"));
        assert_eq!(sig.args().len(), args, "arg count changed for {name}");
        assert_eq!(sig.ret_tys().len(), rets, "return count changed for {name}");
    }

    fn dump_module(module: &Module) -> String {
        let mut writer = ModuleWriter::new(module);
        writer.dump_string()
    }

    fn dump_func(module: &Module, name: &str) -> String {
        let func = find_func(module, name);
        module.func_store.view(func, |function| {
            FuncWriter::new(func, function).dump_string()
        })
    }

    fn run_sccp(module: &Module) {
        let funcs = module.funcs();
        for func in funcs {
            let mut cfg = ControlFlowGraph::default();
            module.func_store.modify(func, |function| {
                cfg.compute(function);
                SccpSolver::new().run(function, &mut cfg);
            });
        }
    }

    fn assert_verified(module: &Module) {
        let verifier = VerifierConfig::for_level(VerificationLevel::Fast);
        let report = verify_module(module, &verifier);
        assert!(!report.has_errors(), "verification failed: {report:?}");
    }

    #[test]
    fn binds_private_arg_when_all_calls_pass_same_sccp_folded_constant() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func private %helper(v0.i256, v1.i256) -> i256 {
block0:
    v2.i256 = add v0 v1;
    return v2;
}

func public %entry(v0.i256) -> i256 {
block0:
    v1.i256 = add 1.i256 2.i256;
    v2.i256 = call %helper v1 v0;
    v3.i256 = call %helper 3.i256 v2;
    return v3;
}
"#,
        );
        run_sccp(&parsed.module);

        let stats = run_uniform_const_arg_binding(&parsed.module, &parsed.module.funcs());
        assert_eq!(stats.rewritten_funcs, 1);
        assert_eq!(stats.bound_args, 1);

        let dead_arg = run_dead_arg_elim(&parsed.module, DeadArgElimConfig::default());
        assert_eq!(dead_arg.removed_args, 1);
        assert_sig(&parsed.module, "helper", 1, 1);

        let dumped = dump_module(&parsed.module);
        assert!(
            !dumped.contains("call %helper 3.i256"),
            "bound constant should be removed from callsites:\n{dumped}"
        );
        assert_verified(&parsed.module);
    }

    #[test]
    fn skips_one_callsite_helpers() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func private %helper(v0.i256, v1.i256) -> i256 {
block0:
    v2.i256 = add v0 v1;
    return v2;
}

func public %entry(v0.i256) -> i256 {
block0:
    v1.i256 = call %helper 3.i256 v0;
    return v1;
}
"#,
        );

        let stats = run_uniform_const_arg_binding(&parsed.module, &parsed.module.funcs());
        assert!(!stats.changed);
        assert_sig(&parsed.module, "helper", 2, 1);
        assert_verified(&parsed.module);
    }

    #[test]
    fn skips_differing_constants() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func private %helper(v0.i256, v1.i256) -> i256 {
block0:
    v2.i256 = add v0 v1;
    return v2;
}

func public %entry(v0.i256) -> i256 {
block0:
    v1.i256 = call %helper 3.i256 v0;
    v2.i256 = call %helper 4.i256 v1;
    return v2;
}
"#,
        );

        let stats = run_uniform_const_arg_binding(&parsed.module, &parsed.module.funcs());
        assert!(!stats.changed);
        assert_sig(&parsed.module, "helper", 2, 1);
        assert_verified(&parsed.module);
    }

    #[test]
    fn skips_non_immediate_actuals() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func private %helper(v0.i256, v1.i256) -> i256 {
block0:
    v2.i256 = add v0 v1;
    return v2;
}

func public %entry(v0.i256, v1.i256) -> i256 {
block0:
    v2.i256 = call %helper v0 v1;
    v3.i256 = call %helper v1 v2;
    return v3;
}
"#,
        );

        let stats = run_uniform_const_arg_binding(&parsed.module, &parsed.module.funcs());
        assert!(!stats.changed);
        assert_sig(&parsed.module, "helper", 2, 1);
        assert_verified(&parsed.module);
    }

    #[test]
    fn skips_live_get_function_ptr_callees() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

type @cb_box = { *(i256, i256) -> i256 };

func private %helper(v0.i256, v1.i256) -> i256 {
block0:
    v2.i256 = add v0 v1;
    return v2;
}

func private %register() -> @cb_box {
block0:
    v0.*(i256, i256) -> i256 = get_function_ptr %helper;
    v1.@cb_box = insert_value undef.@cb_box 0.i8 v0;
    return v1;
}

func public %entry(v0.i256) -> i256 {
block0:
    v1.@cb_box = call %register;
    v2.i256 = call %helper 3.i256 v0;
    v3.i256 = call %helper 3.i256 v2;
    return v3;
}
"#,
        );

        let stats = run_uniform_const_arg_binding(&parsed.module, &parsed.module.funcs());
        assert!(!stats.changed);
        assert_eq!(stats.blocked_get_function_ptr_funcs, 1);
        assert_sig(&parsed.module, "helper", 2, 1);
        assert_verified(&parsed.module);
    }

    #[test]
    fn binds_multiple_uniform_args_on_one_callee() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func private %helper(v0.i256, v1.i256, v2.i256) -> i256 {
block0:
    v3.i256 = add v0 v1;
    v4.i256 = add v3 v2;
    return v4;
}

func public %entry(v0.i256) -> i256 {
block0:
    v1.i256 = call %helper 3.i256 4.i256 v0;
    v2.i256 = call %helper 3.i256 4.i256 v1;
    return v2;
}
"#,
        );

        let stats = run_uniform_const_arg_binding(&parsed.module, &parsed.module.funcs());
        assert_eq!(stats.rewritten_funcs, 1);
        assert_eq!(stats.bound_args, 2);

        let dead_arg = run_dead_arg_elim(&parsed.module, DeadArgElimConfig::default());
        assert_eq!(dead_arg.removed_args, 2);
        assert_sig(&parsed.module, "helper", 1, 1);

        let helper = dump_func(&parsed.module, "helper");
        assert!(
            helper.contains("add 3.i256 4.i256"),
            "callee should compute with bound constants:\n{helper}"
        );
        assert_verified(&parsed.module);
    }
}
