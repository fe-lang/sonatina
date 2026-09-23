//! Closed-call proofs from baseline effects, never from promoted callees.

use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    Function, InstId, Module, Type, ValueId,
    inst::{control_flow, data, downcast},
    module::FuncRef,
    visitor::Visitor,
};

use crate::{
    module_analysis::{CallGraph, SccBuilder},
    optim::dead_func::collect_object_roots,
};

use super::{
    ModuleObjectFacts, ObjectMemoryAnalysis,
    object_access::{ObjectAccess, ObjectAccessFacts},
    object_tracking::ObjectSlice,
    shape::{self, AggregateLayoutCache, AggregateSlice},
};

/// A separate proof that the actual region is allocated, initialized, and has
/// no enum guard at every call. This is not implied by unchanged contents.
struct EntryReadValidity;

struct ArgMemoryInvariantCertificate {
    index: usize,
    argument: ValueId,
    argument_ty: Type,
    slice: AggregateSlice,
    total_leaves: usize,
    entry_validity: Option<EntryReadValidity>,
}

pub(crate) struct FunctionArgInvariance {
    function: FuncRef,
    certificates: Vec<ArgMemoryInvariantCertificate>,
}

impl FunctionArgInvariance {
    pub(crate) fn is_for_function(&self, function: FuncRef) -> bool {
        self.function == function
    }
    fn certificate(
        &self,
        func: &Function,
        slice: ObjectSlice,
    ) -> Option<&ArgMemoryInvariantCertificate> {
        self.certificates.iter().find(|proof| {
            func.arg_values.get(proof.index) == Some(&proof.argument)
                && proof.total_leaves == slice.total_leaves
                && proof.argument == slice.root
                && func.dfg.value_ty(proof.argument) == proof.argument_ty
                && proof.slice
                    == AggregateSlice {
                        ty: slice.ty,
                        first_leaf: slice.first_leaf,
                        leaf_count: slice.leaf_count,
                    }
        })
    }

    pub(crate) fn proves_unchanged(&self, func: &Function, slice: ObjectSlice) -> bool {
        self.certificate(func, slice).is_some()
    }

    pub(crate) fn permits_entry_read(&self, func: &Function, slice: ObjectSlice) -> bool {
        self.certificate(func, slice)
            .is_some_and(|proof| proof.entry_validity.is_some())
    }
}

struct Candidate {
    proof: ArgMemoryInvariantCertificate,
    invariant: bool,
    entry_valid: bool,
    called: bool,
}

#[derive(Default)]
struct NonCallUses(FxHashSet<FuncRef>);

impl Visitor for NonCallUses {
    fn visit_func_ref(&mut self, function: FuncRef) {
        self.0.insert(function);
    }
}

/// Owned only by one scalarization batch. All inference precedes mutation and
/// uses baseline facts. Scalarization preserves calls, signatures, and escaping
/// object identities, and adds no writes to borrowed inputs. Consequently its
/// batch preserves these proofs even when callers and callees are rewritten in
/// parallel. No other pass may reuse this map.
pub(crate) fn compute_arg_invariance(
    module: &Module,
    facts: &ModuleObjectFacts,
) -> FxHashMap<FuncRef, FunctionArgInvariance> {
    if facts.local_args().is_empty() {
        return FxHashMap::default();
    }
    let sccs = SccBuilder::new().compute_scc(&CallGraph::build_graph(module));
    let mut blocked = NonCallUses(collect_object_roots(module).into_iter().collect());
    let mut calls = FxHashMap::<FuncRef, Vec<(InstId, FuncRef)>>::default();
    for caller in module.funcs() {
        module.func_store.view(caller, |func| {
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    if let Some(call) =
                        downcast::<&control_flow::Call>(func.inst_set(), func.dfg.inst(inst))
                    {
                        calls
                            .entry(caller)
                            .or_default()
                            .push((inst, *call.callee()));
                    } else {
                        // Includes get_function_ptr and all function symbols,
                        // even unused/address-only and unreachable occurrences.
                        func.dfg.inst(inst).accept(&mut blocked);
                    }
                }
            }
        });
    }
    let mut candidates = FxHashMap::<FuncRef, Vec<Candidate>>::default();
    let mut layouts = AggregateLayoutCache::default();
    for (&callee, args) in facts.local_args() {
        if blocked.0.contains(&callee)
            || !module.ctx.func_linkage(callee).is_private()
            || sccs.scc_of(callee).is_cycle
        {
            continue;
        }
        module.func_store.view(callee, |func| {
            let accesses = ObjectAccessFacts::new(func, Some(facts.effects()));
            let mut seen = FxHashSet::default();
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    let Some(load) =
                        downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst))
                    else {
                        continue;
                    };
                    let access = accesses.access(*load.object(), None);
                    let [ObjectAccess::Exact(projection)] = access.as_slice() else {
                        continue;
                    };
                    let argument = projection.root_value.value();
                    let Some(index) = func.arg_values.iter().position(|&arg| arg == argument)
                    else {
                        continue;
                    };
                    if !args.contains_key(&index) || !seen.insert((index, projection.slice)) {
                        continue;
                    }
                    let root = accesses.access(argument, None);
                    let [ObjectAccess::Exact(root)] = root.as_slice() else {
                        continue;
                    };
                    if root.slice.leaf_count > 4
                        || !shape::is_leaf_reifiable_ty(func.ctx(), root.slice.ty)
                    {
                        continue;
                    }
                    candidates.entry(callee).or_default().push(Candidate {
                        proof: ArgMemoryInvariantCertificate {
                            index,
                            argument,
                            argument_ty: func.dfg.value_ty(argument),
                            slice: projection.slice,
                            total_leaves: root.slice.leaf_count,
                            entry_validity: None,
                        },
                        invariant: true,
                        entry_valid: true,
                        called: false,
                    });
                }
            }
        });
    }
    for (caller, sites) in calls {
        if !sites
            .iter()
            .any(|(_, callee)| candidates.contains_key(callee))
        {
            continue;
        }
        module.func_store.view(caller, |func| {
            // One access/memory context per caller, shared by all its sites and
            // candidate slices. Neither analysis consumes certificates.
            let accesses = ObjectAccessFacts::new(func, Some(facts.effects()));
            let mut memory = None;
            for (inst, callee) in sites {
                let Some(candidates) = candidates.get_mut(&callee) else {
                    continue;
                };
                let call =
                    downcast::<&control_flow::Call>(func.inst_set(), func.dfg.inst(inst)).unwrap();
                let effects = accesses.effects(func, inst, Some(facts.effects()));
                for candidate in candidates
                    .iter_mut()
                    .filter(|candidate| candidate.invariant)
                {
                    candidate.called = true;
                    let Some(&actual) = call.args().get(candidate.proof.index) else {
                        candidate.invariant = false;
                        continue;
                    };
                    let actual_root = accesses.access(actual, None);
                    if !matches!(actual_root.as_slice(), [ObjectAccess::Exact(projection)] if projection.slice.leaf_count == candidate.proof.total_leaves) {
                        candidate.invariant = false;
                        continue;
                    }
                    let actual_access = accesses.access(actual, Some(candidate.proof.slice));
                    let [ObjectAccess::Exact(projection)] = actual_access.as_slice() else {
                        candidate.invariant = false;
                        continue;
                    };
                    let slice = accesses.projection_slice(*projection);
                    // Repeating allocation sites and guarded views need stronger
                    // instance/ancestor proofs than this initial analysis.
                    if func.dfg.value_ty(actual) != candidate.proof.argument_ty
                        || !accesses.single_instance(projection.root_value)
                        || !accesses
                            .ancestor_guards(func, slice, &mut layouts)
                            .is_some_and(|guards| guards.is_empty())
                        || effects
                            .writes
                            .iter()
                            .chain(&effects.unreadable)
                            .any(|&write| accesses.may_overlap(write, slice))
                    {
                        candidate.invariant = false;
                        continue;
                    }
                    let allocation = func.dfg.value_inst(slice.root).is_some_and(|definition| {
                        downcast::<&data::ObjAlloc>(func.inst_set(), func.dfg.inst(definition))
                            .is_some()
                    });
                    candidate.entry_valid = candidate.entry_valid && allocation && memory.get_or_insert_with(|| {
                        let mut memory = ObjectMemoryAnalysis::default();
                        memory.compute(func, facts.local_args().get(&caller), Some(facts.effects()));
                        memory
                    }).slice_initialized_before_inst(func, inst, slice);
                }
            }
        });
    }
    candidates
        .into_iter()
        .filter_map(|(func, candidates)| {
            let certificates: Vec<_> = candidates
                .into_iter()
                .filter_map(|mut candidate| {
                    if !candidate.called || !candidate.invariant {
                        return None;
                    }
                    candidate.proof.entry_validity =
                        candidate.entry_valid.then_some(EntryReadValidity);
                    Some(candidate.proof)
                })
                .collect();
            (!certificates.is_empty()).then_some((
                func,
                FunctionArgInvariance {
                    function: func,
                    certificates,
                },
            ))
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::optim::{Pass, Pipeline, Step};
    use sonatina_ir::ir_writer::FuncWriter;
    use sonatina_parser::parse_module;
    use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

    fn first_argument_read(func: &Function, accesses: &ObjectAccessFacts) -> (usize, ObjectSlice) {
        func.layout
            .iter_block()
            .flat_map(|block| func.layout.iter_inst(block))
            .enumerate()
            .find_map(|(order, inst)| {
                let load = downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst))?;
                match accesses.access(*load.object(), None).as_slice() {
                    [ObjectAccess::Exact(projection)]
                        if projection.root_value.value() == func.arg_values[0] =>
                    {
                        Some((order, accesses.projection_slice(*projection)))
                    }
                    _ => None,
                }
            })
            .unwrap()
    }

    fn check(source: &str, invariant: bool, entry_valid: bool, promoted: bool) {
        let mut module = parse_module(source).unwrap().module;
        let config = VerifierConfig::for_level(VerificationLevel::Full);
        let report = verify_module(&module, &config);
        assert!(report.is_ok(), "{report}");
        let callee = module
            .funcs()
            .into_iter()
            .find(|&func| module.ctx.func_sig(func, |sig| sig.name() == "f"))
            .unwrap();
        let facts = ModuleObjectFacts::compute(&module);
        let proofs = compute_arg_invariance(&module, &facts);
        module.func_store.view(callee, |func| {
            let accesses = ObjectAccessFacts::new(func, Some(facts.effects()));
            let (_, slice) = first_argument_read(func, &accesses);
            assert_eq!(
                proofs
                    .get(&callee)
                    .is_some_and(|proof| proof.proves_unchanged(func, slice)),
                invariant,
                "{source}"
            );
            assert_eq!(
                proofs
                    .get(&callee)
                    .is_some_and(|proof| proof.permits_entry_read(func, slice)),
                entry_valid,
                "{source}"
            );
        });
        let mut pipeline = Pipeline::new();
        pipeline.add_step(Step::FuncPasses(vec![Pass::AggregateScalarize]));
        pipeline.run(&mut module);
        let report = verify_module(&module, &config);
        assert!(report.is_ok(), "{report}");
        module.func_store.view(callee, |func| {
            let text = FuncWriter::new(callee, func).dump_string();
            let accesses = ObjectAccessFacts::new(func, None);
            let (read, _) = first_argument_read(func, &accesses);
            let write = func
                .layout
                .iter_block()
                .flat_map(|block| func.layout.iter_inst(block))
                .position(|inst| {
                    downcast::<&data::ObjStore>(func.inst_set(), func.dfg.inst(inst)).is_some()
                })
                .unwrap();
            assert_eq!(read < write, promoted, "{text}");
        });
    }

    #[test]
    fn disjoint_callers_promote_but_one_aliasing_site_rejects() {
        for mixed in [false, true] {
            let second = if mixed { "v0" } else { "v1" };
            check(
                &format!(
                    r#"
target = "evm-ethereum-osaka"
func inline(never) private %f(v0.objref<i256>, v1.objref<i256>) -> i256 {{
block0:
    obj.store v1 22.i256;
    v2.i256 = obj.load v0;
    return v2;
}}
func public %caller() -> i256 {{
block0:
    v0.objref<i256> = obj.alloc i256;
    v1.objref<i256> = obj.alloc i256;
    obj.store v0 11.i256;
    obj.store v1 33.i256;
    v2.i256 = call %f v0 v1;
    v3.i256 = call %f v0 {second};
    v4.i256 = add v2 v3;
    return v4;
}}
"#
                ),
                !mixed,
                !mixed,
                !mixed,
            );
        }
    }

    #[test]
    fn changing_call_actuals_discards_the_previous_certificate_batch() {
        let mut module = parse_module(
            r#"
target = "evm-ethereum-osaka"
func inline(never) private %f(v0.objref<i256>, v1.objref<i256>) -> i256 {
block0:
    obj.store v1 22.i256;
    v2.i256 = obj.load v0;
    return v2;
}
func public %caller() -> i256 {
block0:
    v0.objref<i256> = obj.alloc i256;
    v1.objref<i256> = obj.alloc i256;
    obj.store v0 11.i256;
    obj.store v1 33.i256;
    v2.i256 = call %f v0 v1;
    return v2;
}
"#,
        )
        .unwrap()
        .module;
        let config = VerifierConfig::for_level(VerificationLevel::Full);
        assert!(verify_module(&module, &config).is_ok());
        let lookup = |name| {
            module
                .funcs()
                .into_iter()
                .find(|&func| module.ctx.func_sig(func, |sig| sig.name() == name))
                .unwrap()
        };
        let callee = lookup("f");
        let caller = lookup("caller");
        let old_facts = ModuleObjectFacts::compute(&module);
        let old_proofs = compute_arg_invariance(&module, &old_facts);
        assert!(old_proofs.contains_key(&callee));
        module.func_store.modify(caller, |func| {
            let inst = func
                .layout
                .iter_inst(func.layout.entry_block().unwrap())
                .find(|&inst| {
                    downcast::<&control_flow::Call>(func.inst_set(), func.dfg.inst(inst)).is_some()
                })
                .unwrap();
            let call =
                downcast::<&control_flow::Call>(func.inst_set(), func.dfg.inst(inst)).unwrap();
            let mut args = call.args().clone();
            args[1] = args[0];
            let call = control_flow::Call::new_unchecked(func.inst_set(), callee, args);
            func.dfg.replace_inst(inst, Box::new(call));
            func.rebuild_users();
        });
        assert!(verify_module(&module, &config).is_ok());
        let current_facts = ModuleObjectFacts::compute(&module);
        let current_proofs = compute_arg_invariance(&module, &current_facts);
        assert!(!current_proofs.contains_key(&callee));
        // There is no override for old_proofs. The pipeline infers its own batch
        // from current call operands before entering any modification closure.
        let mut pipeline = Pipeline::new();
        pipeline.add_step(Step::FuncPasses(vec![Pass::AggregateScalarize]));
        pipeline.run(&mut module);
        assert!(verify_module(&module, &config).is_ok());
        module.func_store.view(callee, |func| {
            let text = FuncWriter::new(callee, func).dump_string();
            assert!(
                text.find("obj.store").unwrap() < text.find("obj.load").unwrap(),
                "{text}"
            );
        });
    }

    #[test]
    fn only_demanded_fields_need_invocation_invariance() {
        check(
            r#"
target = "evm-ethereum-osaka"
type @pair = { i256, i256 };
func inline(never) private %f(v0.objref<@pair>, v1.objref<i256>) -> i256 {
block0:
    obj.store v1 22.i256;
    v2.objref<i256> = obj.proj v0 0.i8;
    v3.i256 = obj.load v2;
    return v3;
}
func public %caller() -> i256 {
block0:
    v0.objref<@pair> = obj.alloc @pair;
    v1.objref<i256> = obj.proj v0 0.i8;
    v2.objref<i256> = obj.proj v0 1.i8;
    obj.store v1 11.i256;
    obj.store v2 33.i256;
    v3.i256 = call %f v0 v2;
    return v3;
}
"#,
            true,
            true,
            true,
        );
    }

    #[test]
    fn sibling_actuals_retain_separation_and_readonly_formals_may_alias() {
        for readonly_alias in [false, true] {
            let source = if readonly_alias {
                r#"
target = "evm-ethereum-osaka"
func inline(never) private %f(v0.objref<i256>, v1.objref<i256>, v2.objref<i256>) -> i256 {
block0:
    obj.store v2 22.i256;
    v3.i256 = obj.load v0;
    v4.i256 = obj.load v1;
    v5.i256 = add v3 v4;
    return v5;
}
func public %caller() -> i256 {
block0:
    v0.objref<i256> = obj.alloc i256;
    v1.objref<i256> = obj.alloc i256;
    obj.store v0 11.i256;
    obj.store v1 33.i256;
    v2.i256 = call %f v0 v0 v1;
    return v2;
}
"#
            } else {
                r#"
target = "evm-ethereum-osaka"
type @pair = { i256, i256 };
func inline(never) private %f(v0.objref<i256>, v1.objref<i256>) -> i256 {
block0:
    obj.store v1 22.i256;
    v2.i256 = obj.load v0;
    return v2;
}
func public %caller() -> i256 {
block0:
    v0.objref<@pair> = obj.alloc @pair;
    v1.objref<i256> = obj.proj v0 0.i8;
    v2.objref<i256> = obj.proj v0 1.i8;
    obj.store v1 11.i256;
    obj.store v2 33.i256;
    v3.i256 = call %f v1 v2;
    return v3;
}
"#
            };
            check(source, true, true, true);
        }
    }

    #[test]
    fn incoming_actuals_need_separate_entry_validity() {
        for unknown_writer in [false, true] {
            let (args, allocate) = if unknown_writer {
                ("v0.objref<i256>, v1.objref<i256>", "")
            } else {
                ("v0.objref<i256>", "v1.objref<i256> = obj.alloc i256;")
            };
            check(
                &format!(
                    r#"
target = "evm-ethereum-osaka"
func inline(never) private %f(v0.objref<i256>, v1.objref<i256>) -> i256 {{
block0:
    obj.store v1 22.i256;
    v2.i256 = obj.load v0;
    return v2;
}}
func private %caller({args}) -> i256 {{
block0:
    {allocate}
    v2.i256 = call %f v0 v1;
    return v2;
}}
"#
                ),
                !unknown_writer,
                false,
                false,
            );
        }
    }

    #[test]
    fn published_and_recovered_actuals_cannot_hide_writers() {
        check(
            r#"
target = "evm-ethereum-osaka"
declare external %opaque();
func inline(never) private %f(v0.objref<i256>, v1.objref<i256>) -> i256 {
block0:
    obj.store v1 22.i256;
    call %opaque;
    v2.i256 = obj.load v0;
    return v2;
}
func public %caller() -> i256 {
block0:
    v0.objref<i256> = obj.alloc i256;
    v1.objref<i256> = obj.alloc i256;
    obj.store v0 11.i256;
    v2.*i256 = obj.materialize.heap v0;
    v3.i256 = ptr_to_int v2 i256;
    mstore 0.i256 v3 i256;
    v4.i256 = call %f v0 v1;
    return v4;
}
"#,
            false,
            false,
            false,
        );
        check(
            r#"
target = "evm-ethereum-osaka"
type @holder = { objref<i256> };
func inline(never) private %f(v0.objref<i256>, v1.objref<@holder>) -> i256 {
block0:
    v2.objref<objref<i256>> = obj.proj v1 0.i8;
    v3.objref<i256> = obj.load v2;
    obj.store v3 22.i256;
    v4.i256 = obj.load v0;
    return v4;
}
func public %caller() -> i256 {
block0:
    v0.objref<i256> = obj.alloc i256;
    v1.objref<@holder> = obj.alloc @holder;
    v2.objref<objref<i256>> = obj.proj v1 0.i8;
    obj.store v0 11.i256;
    obj.store v2 v0;
    v3.i256 = call %f v0 v1;
    return v3;
}
"#,
            false,
            false,
            false,
        );
    }

    #[test]
    fn incomplete_and_repeating_actuals_are_rejected() {
        let callee = r#"
target = "evm-ethereum-osaka"
func inline(never) private %f(v0.objref<i256>, v1.objref<i256>) -> i256 {
block0:
    obj.store v1 22.i256;
    v2.i256 = obj.load v0;
    return v2;
}
"#;
        for caller in [
            r#"
func public %caller(v0.i1) -> i256 {
block0:
    v1.objref<i256> = obj.alloc i256;
    v2.objref<i256> = obj.alloc i256;
    obj.store v1 11.i256;
    obj.store v2 33.i256;
    br v0 block1 block2;
block1:
    jump block3;
block2:
    jump block3;
block3:
    v3.objref<i256> = phi (v1 block1) (v2 block2);
    v4.i256 = call %f v3 v2;
    return v4;
}
"#,
            r#"
func public %caller(v0.i1) -> i256 {
block0:
    jump block1;
block1:
    v1.objref<i256> = obj.alloc i256;
    v2.objref<i256> = obj.alloc i256;
    obj.store v1 11.i256;
    v3.i256 = call %f v1 v2;
    br v0 block1 block2;
block2:
    return v3;
}
"#,
        ] {
            check(&format!("{callee}{caller}"), false, false, false);
        }
    }

    #[test]
    fn invariance_does_not_supply_entry_validity_for_uninitialized_storage() {
        check(
            r#"
target = "evm-ethereum-osaka"
func inline(never) private %f(v0.objref<i256>, v1.objref<i256>) -> i256 {
block0:
    obj.store v1 22.i256;
    v2.i256 = obj.load v0;
    return v2;
}
func public %caller() -> i256 {
block0:
    v0.objref<i256> = obj.alloc i256;
    v1.objref<i256> = obj.alloc i256;
    v2.i256 = call %f v0 v1;
    return v2;
}
"#,
            true,
            false,
            false,
        );
    }

    #[test]
    fn address_taken_zero_caller_and_recursive_functions_are_rejected() {
        for (extra, recursive, with_call, objects) in [
            ("v3.i256 = sym_addr %f;", false, true, ""),
            ("", false, false, ""),
            ("", true, true, ""),
            (
                "",
                false,
                true,
                "object @Test { section runtime { entry %caller; include %f; } }",
            ),
        ] {
            let recursive_call = if recursive {
                "v3.i256 = call %f v0 v1;"
            } else {
                ""
            };
            let call = if with_call {
                "v2.i256 = call %f v0 v1;"
            } else {
                ""
            };
            check(
                &format!(
                    r#"
target = "evm-ethereum-osaka"
func inline(never) private %f(v0.objref<i256>, v1.objref<i256>) -> i256 {{
block0:
    obj.store v1 22.i256;
    {recursive_call}
    v2.i256 = obj.load v0;
    return v2;
}}
func public %caller() {{
block0:
    v0.objref<i256> = obj.alloc i256;
    v1.objref<i256> = obj.alloc i256;
    obj.store v0 11.i256;
    {call}
    {extra}
    return;
}}
{objects}
"#
                ),
                false,
                false,
                false,
            );
        }
    }
}
