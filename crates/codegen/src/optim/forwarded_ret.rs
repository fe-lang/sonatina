use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use sonatina_ir::{
    Function, Type, Value,
    inst::{control_flow, downcast},
    module::{FuncRef, Module},
};

use super::{
    dead_func::collect_object_roots,
    signature_rewrite::{
        SignatureRewritePlan, propagate_signature_rewrite_types, retain_function_returns,
        retain_higher_order_safe_plans, rewrite_declared_signatures,
    },
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ForwardedRetElimConfig {
    pub private_only: bool,
    pub require_higher_order_safe: bool,
}

impl Default for ForwardedRetElimConfig {
    fn default() -> Self {
        Self {
            private_only: true,
            require_higher_order_safe: true,
        }
    }
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct ForwardedRetElimStats {
    pub rewritten_funcs: usize,
    pub removed_rets: usize,
    pub rewritten_calls: usize,
    pub replaced_call_results: usize,
    pub blocked_higher_order_funcs: usize,
    pub rounds: usize,
}

#[derive(Clone)]
struct FuncPlan {
    forwarded_args: Vec<Option<usize>>,
    keep_rets: Vec<bool>,
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
        self.forwarded_args == other.forwarded_args && self.new_arg_tys == other.new_arg_tys
    }
}

/// Removes private function result lanes that return one unchanged argument on
/// every exit. Each direct caller uses its original call argument in place of
/// the redundant result, so the call and all of its effects remain intact.
///
/// The rewrite runs to a fixed point. Simplifying a leaf can expose an unchanged
/// argument through a wrapper without relying on name-based specialization.
/// Explicit section roots and object entry/include directives retain every return lane.
pub fn run_forwarded_ret_elim(
    module: &Module,
    roots: &[FuncRef],
    config: ForwardedRetElimConfig,
) -> ForwardedRetElimStats {
    let mut stats = ForwardedRetElimStats::default();
    let roots: FxHashSet<_> = collect_object_roots(module)
        .into_iter()
        .chain(roots.iter().copied())
        .collect();
    let mut blocked = FxHashSet::default();

    loop {
        for func_ref in module.funcs() {
            module.func_store.modify(func_ref, Function::rebuild_users);
        }

        let mut plans = collect_plans(module, config);
        plans.retain(|func, _| !roots.contains(func));
        if config.require_higher_order_safe {
            let before: Vec<_> = plans.keys().copied().collect();
            retain_higher_order_safe_plans(module, &mut plans);
            blocked.extend(before.into_iter().filter(|func| !plans.contains_key(func)));
        }
        if plans.is_empty() {
            break;
        }

        stats.rounds += 1;
        stats.rewritten_funcs += plans.len();
        stats.removed_rets += plans
            .values()
            .map(|plan| plan.keep_rets.iter().filter(|keep| !**keep).count())
            .sum::<usize>();

        let old_sigs = rewrite_declared_signatures(module, &plans);
        for (&func_ref, plan) in &plans {
            module.func_store.modify(func_ref, |function| {
                retain_function_returns(function, &plan.keep_rets);
            });
        }

        for func_ref in module.funcs() {
            let (calls, results) = module
                .func_store
                .modify(func_ref, |function| rewrite_calls(function, &plans));
            stats.rewritten_calls += calls;
            stats.replaced_call_results += results;
        }

        propagate_signature_rewrite_types(module, &old_sigs);
    }

    stats.blocked_higher_order_funcs = blocked.len();
    stats
}

#[derive(Clone, Copy)]
enum ForwardState {
    Unseen,
    Arg(usize),
    NotForwarded,
}

fn collect_plans(module: &Module, config: ForwardedRetElimConfig) -> FxHashMap<FuncRef, FuncPlan> {
    let mut plans = FxHashMap::default();

    for func_ref in module.funcs() {
        let linkage = module.ctx.func_linkage(func_ref);
        let Some(signature) = module.ctx.get_sig(func_ref) else {
            continue;
        };
        if !linkage.has_definition()
            || (config.private_only && !linkage.is_private())
            || signature.ret_tys().is_empty()
        {
            continue;
        }

        let mut states = vec![ForwardState::Unseen; signature.ret_tys().len()];
        let mut saw_return = false;
        let mut malformed = false;
        module.func_store.view(func_ref, |function| {
            for block in function.layout.iter_block() {
                for inst in function.layout.iter_inst(block) {
                    let Some(ret) = downcast::<&control_flow::Return>(
                        function.inst_set(),
                        function.dfg.inst(inst),
                    ) else {
                        continue;
                    };
                    saw_return = true;
                    if ret.args().len() != states.len() {
                        malformed = true;
                        continue;
                    }
                    for (state, &value) in states.iter_mut().zip(ret.args().iter()) {
                        let arg = match function.dfg.value(value) {
                            Value::Arg { idx, .. } => Some(*idx),
                            _ => None,
                        };
                        *state = match (*state, arg) {
                            (ForwardState::Unseen, Some(idx)) => ForwardState::Arg(idx),
                            (ForwardState::Arg(left), Some(right)) if left == right => {
                                ForwardState::Arg(left)
                            }
                            _ => ForwardState::NotForwarded,
                        };
                    }
                }
            }
        });

        if !saw_return || malformed {
            continue;
        }
        let forwarded_args = states
            .into_iter()
            .map(|state| match state {
                ForwardState::Arg(idx) if idx < signature.args().len() => Some(idx),
                ForwardState::Unseen | ForwardState::Arg(_) | ForwardState::NotForwarded => None,
            })
            .collect::<Vec<_>>();
        if forwarded_args.iter().all(Option::is_none) {
            continue;
        }
        let keep_rets = forwarded_args
            .iter()
            .map(Option::is_none)
            .collect::<Vec<_>>();
        let new_ret_tys = signature
            .ret_tys()
            .iter()
            .zip(keep_rets.iter())
            .filter_map(|(&ty, &keep)| keep.then_some(ty))
            .collect();
        plans.insert(
            func_ref,
            FuncPlan {
                forwarded_args,
                keep_rets,
                new_arg_tys: SmallVec::from_slice(signature.args()),
                new_ret_tys,
            },
        );
    }

    plans
}

fn rewrite_calls(function: &mut Function, plans: &FxHashMap<FuncRef, FuncPlan>) -> (usize, usize) {
    let mut rewritten_calls = 0;
    let mut replaced_results = 0;
    let blocks = function.layout.iter_block().collect::<Vec<_>>();
    for block in blocks {
        let insts = function.layout.iter_inst(block).collect::<Vec<_>>();
        for inst in insts {
            let Some(call) = function.dfg.cast_call(inst).cloned() else {
                continue;
            };
            let Some(plan) = plans.get(call.callee()) else {
                continue;
            };
            let call_args = call.args().iter().copied().collect::<Vec<_>>();
            let call_results = function.dfg.inst_results(inst).to_vec();
            assert_eq!(
                call_results.len(),
                plan.forwarded_args.len(),
                "call result arity must match the rewritten function signature"
            );
            for (&result, forwarded_arg) in call_results.iter().zip(&plan.forwarded_args) {
                let Some(arg_idx) = forwarded_arg else {
                    continue;
                };
                let replacement = call_args[*arg_idx];
                function.dfg.change_to_alias(result, replacement);
                replaced_results += 1;
            }
            function.dfg.retain_inst_results(inst, &plan.keep_rets);
            rewritten_calls += 1;
        }
    }
    (rewritten_calls, replaced_results)
}

#[cfg(test)]
mod tests {
    use sonatina_ir::{
        Module,
        ir_writer::{FuncWriter, ModuleWriter},
    };
    use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

    use super::{ForwardedRetElimConfig, run_forwarded_ret_elim};

    fn parse_module(input: &str) -> sonatina_parser::ParsedModule {
        sonatina_parser::parse_module(input).unwrap_or_else(|errs| panic!("parse failed: {errs:?}"))
    }

    fn find_func(module: &Module, name: &str) -> sonatina_ir::module::FuncRef {
        module
            .funcs()
            .into_iter()
            .find(|&func_ref| module.ctx.func_sig(func_ref, |sig| sig.name() == name))
            .unwrap_or_else(|| panic!("missing function {name}"))
    }

    fn dump_function(module: &Module, name: &str) -> String {
        let func_ref = find_func(module, name);
        module.func_store.view(func_ref, |function| {
            FuncWriter::new(func_ref, function).dump_string()
        })
    }

    fn assert_verified(module: &Module) {
        let verifier = VerifierConfig::for_level(VerificationLevel::Fast);
        let report = verify_module(module, &verifier);
        assert!(!report.has_errors(), "verification failed: {report:?}");
    }

    #[test]
    fn replaces_unchanged_result_with_call_argument() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func private %advance(v0.i32, v1.i32) -> (i32, i32) {
    block0:
        v2.i32 = add v1 1.i32;
        return (v0, v2);
}

func public %entry(v0.i32, v1.i32) -> i32 {
    block0:
        (v2.i32, v3.i32) = call %advance v0 v1;
        v4.i32 = add v2 v3;
        return v4;
}
"#,
        );

        let stats = run_forwarded_ret_elim(&parsed.module, &[], ForwardedRetElimConfig::default());

        assert_eq!(stats.removed_rets, 1);
        assert_eq!(stats.replaced_call_results, 1);
        assert!(dump_function(&parsed.module, "advance").contains("return v2;"));
        let entry = dump_function(&parsed.module, "entry");
        assert!(entry.contains("v3.i32 = call %advance v0 v1;"));
        assert!(entry.contains("add v0 v3"));
        assert_verified(&parsed.module);
    }

    #[test]
    fn keeps_lane_when_any_exit_returns_something_else() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func private %choose(v0.i32, v1.i1) -> i32 {
    block0:
        br v1 block1 block2;
    block1:
        return v0;
    block2:
        v2.i32 = add v0 1.i32;
        return v2;
}

func public %entry(v0.i32, v1.i1) -> i32 {
    block0:
        v2.i32 = call %choose v0 v1;
        return v2;
}
"#,
        );

        let stats = run_forwarded_ret_elim(&parsed.module, &[], ForwardedRetElimConfig::default());

        assert_eq!(stats.removed_rets, 0);
        assert!(
            ModuleWriter::new(&parsed.module)
                .dump_string()
                .contains("-> i32")
        );
        assert_verified(&parsed.module);
    }

    #[test]
    fn reaches_fixed_point_through_wrapper() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func private %leaf(v0.i32) -> i32 {
    block0:
        return v0;
}

func private %wrapper(v0.i32) -> i32 {
    block0:
        v1.i32 = call %leaf v0;
        return v1;
}

func public %entry(v0.i32) -> i32 {
    block0:
        v1.i32 = call %wrapper v0;
        return v1;
}
"#,
        );

        let stats = run_forwarded_ret_elim(&parsed.module, &[], ForwardedRetElimConfig::default());

        assert_eq!(stats.rounds, 2);
        assert_eq!(stats.removed_rets, 2);
        assert!(dump_function(&parsed.module, "leaf").contains("return;"));
        assert!(dump_function(&parsed.module, "wrapper").contains("call %leaf v0;"));
        assert!(dump_function(&parsed.module, "entry").contains("call %wrapper v0;"));
        assert!(dump_function(&parsed.module, "entry").contains("return v0;"));
        assert_verified(&parsed.module);
    }
}
