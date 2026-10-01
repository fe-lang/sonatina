use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use sonatina_ir::{
    Function, Type,
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
pub struct DeadRetElimConfig {
    pub private_only: bool,
    pub require_higher_order_safe: bool,
}

impl Default for DeadRetElimConfig {
    fn default() -> Self {
        Self {
            private_only: true,
            require_higher_order_safe: true,
        }
    }
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct DeadRetElimStats {
    pub rewritten_funcs: usize,
    pub removed_rets: usize,
    pub rewritten_calls: usize,
    pub removed_call_results: usize,
    pub blocked_higher_order_funcs: usize,
    pub rounds: usize,
}

#[derive(Clone)]
struct FuncPlan {
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
        self.keep_rets == other.keep_rets && self.new_arg_tys == other.new_arg_tys
    }
}

/// Removes private function result lanes that are unused at every direct call site.
///
/// The rewrite runs to a fixed point so removing a dead wrapper result can expose
/// the corresponding result of a deeper callee. Calls themselves remain in place,
/// preserving effects even when all of their result lanes disappear.
/// Explicit section roots and object entry/include directives retain every return lane.
pub fn run_dead_ret_elim(
    module: &Module,
    roots: &[FuncRef],
    config: DeadRetElimConfig,
) -> DeadRetElimStats {
    let mut stats = DeadRetElimStats::default();
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
            stats.removed_call_results += results;
        }

        propagate_signature_rewrite_types(module, &old_sigs);
    }

    stats.blocked_higher_order_funcs = blocked.len();
    stats
}

fn collect_plans(module: &Module, config: DeadRetElimConfig) -> FxHashMap<FuncRef, FuncPlan> {
    let mut live_rets = FxHashMap::<FuncRef, Vec<bool>>::default();
    for func_ref in module.funcs() {
        let linkage = module.ctx.func_linkage(func_ref);
        let Some(signature) = module.ctx.get_sig(func_ref) else {
            continue;
        };
        if linkage.has_definition()
            && (!config.private_only || linkage.is_private())
            && !signature.ret_tys().is_empty()
        {
            live_rets.insert(func_ref, vec![false; signature.ret_tys().len()]);
        }
    }

    for caller in module.funcs() {
        module.func_store.view(caller, |function| {
            for block in function.layout.iter_block() {
                for inst in function.layout.iter_inst(block) {
                    let Some(call) = function.dfg.cast_call(inst) else {
                        continue;
                    };
                    let Some(mask) = live_rets.get_mut(call.callee()) else {
                        continue;
                    };
                    let results = function.dfg.inst_results(inst);
                    if results.len() != mask.len() {
                        mask.fill(true);
                        continue;
                    }
                    for (&result, live) in results.iter().zip(mask.iter_mut()) {
                        *live |= function.dfg.users_num(result) != 0;
                    }
                }
            }
        });
    }

    let mut plans = FxHashMap::default();
    for (func_ref, keep_rets) in live_rets {
        if keep_rets.iter().all(|keep| *keep) {
            continue;
        }
        let signature = module
            .ctx
            .get_sig(func_ref)
            .expect("candidate function should retain its signature");
        let new_ret_tys = signature
            .ret_tys()
            .iter()
            .zip(keep_rets.iter())
            .filter_map(|(&ty, &keep)| keep.then_some(ty))
            .collect();
        plans.insert(
            func_ref,
            FuncPlan {
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
    let mut removed_results = 0;
    let blocks = function.layout.iter_block().collect::<Vec<_>>();
    for block in blocks {
        let insts = function.layout.iter_inst(block).collect::<Vec<_>>();
        for inst in insts {
            let Some(callee) = function.dfg.call_info(inst).map(|call| call.callee()) else {
                continue;
            };
            let Some(plan) = plans.get(&callee) else {
                continue;
            };
            removed_results += plan.keep_rets.iter().filter(|keep| !**keep).count();
            function.dfg.retain_inst_results(inst, &plan.keep_rets);
            rewritten_calls += 1;
        }
    }
    (rewritten_calls, removed_results)
}

#[cfg(test)]
mod tests {
    use sonatina_ir::{
        Module,
        ir_writer::{FuncWriter, ModuleWriter},
    };
    use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

    use super::{DeadRetElimConfig, run_dead_ret_elim};

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
    fn removes_one_unused_result_lane() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func private %pair(v0.i32) -> (i32, i32) {
    block0:
        v1.i32 = add v0 1.i32;
        v2.i32 = add v0 2.i32;
        return (v1, v2);
}

func public %entry(v0.i32) -> i32 {
    block0:
        (v1.i32, v2.i32) = call %pair v0;
        return v2;
}
"#,
        );

        let stats = run_dead_ret_elim(&parsed.module, &[], DeadRetElimConfig::default());

        assert_eq!(stats.removed_rets, 1);
        assert_eq!(stats.removed_call_results, 1);
        assert!(dump_function(&parsed.module, "pair").contains("return v2;"));
        assert!(dump_function(&parsed.module, "entry").contains("v2.i32 = call %pair v0;"));
        assert_verified(&parsed.module);
    }

    #[test]
    fn preserves_lanes_used_across_distinct_call_sites() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func private %pair(v0.i32) -> (i32, i32) {
    block0:
        v1.i32 = add v0 1.i32;
        v2.i32 = add v0 2.i32;
        return (v1, v2);
}

func public %entry(v0.i32) -> i32 {
    block0:
        (v1.i32, v2.i32) = call %pair v0;
        (v3.i32, v4.i32) = call %pair v1;
        v5.i32 = add v2 v3;
        return v5;
}
"#,
        );

        let stats = run_dead_ret_elim(&parsed.module, &[], DeadRetElimConfig::default());

        assert_eq!(stats.removed_rets, 0);
        assert!(
            ModuleWriter::new(&parsed.module)
                .dump_string()
                .contains("-> (i32, i32)")
        );
        assert_verified(&parsed.module);
    }

    #[test]
    fn reaches_through_dead_wrapper_lanes() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func private %leaf(v0.i32) -> (i32, i32) {
    block0:
        v1.i32 = add v0 1.i32;
        v2.i32 = add v0 2.i32;
        return (v1, v2);
}

func private %wrapper(v0.i32) -> (i32, i32) {
    block0:
        (v1.i32, v2.i32) = call %leaf v0;
        return (v1, v2);
}

func public %entry(v0.i32) -> i32 {
    block0:
        (v1.i32, v2.i32) = call %wrapper v0;
        return v2;
}
"#,
        );

        let stats = run_dead_ret_elim(&parsed.module, &[], DeadRetElimConfig::default());

        assert_eq!(stats.rounds, 2);
        assert_eq!(stats.removed_rets, 2);
        assert!(dump_function(&parsed.module, "leaf").contains("return v2;"));
        assert!(dump_function(&parsed.module, "wrapper").contains("return v2;"));
        assert_verified(&parsed.module);
    }
}
