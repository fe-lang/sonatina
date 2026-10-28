//! Tail calls: a call whose results its function returns at once becomes a
//! Cranelift `return_call` when the callee cannot reach the caller's frame,
//! which the call then replaces.
//!
//! Cranelift tail-calls only between functions of its `tail` calling
//! convention, which keeps the platform's callee-saved registers. The
//! functions on either side of a tail call use it; the rest keep the
//! platform convention, as external code calls public functions.

use std::collections::{HashMap, HashSet};

use sonatina_ir::{
    BlockId, Function, Module, Type, Value, ValueId,
    inst::{InstId, control_flow, data},
    module::FuncRef,
    types::CompoundType,
};
use sonatina_triple::TargetTriple;

/// The tail calls of a module.
#[derive(Default)]
pub(super) struct TailCalls {
    sites: HashMap<FuncRef, HashSet<InstId>>,
    functions: HashSet<FuncRef>,
    switches: HashMap<(FuncRef, InstId), TailSwitch>,
}

/// A `br_table` each of whose destinations, the default included, begins
/// with a tail call taking the same arguments. It becomes one indirect tail
/// call through a table of the callees, as an interpreter's dispatch wants.
pub(super) struct TailSwitch {
    /// Each key with its destination's callee.
    pub(super) keys: Vec<(u64, FuncRef)>,
    pub(super) default: FuncRef,
    /// One of the calls, whose arguments every callee takes.
    pub(super) call: InstId,
}

impl TailCalls {
    pub(super) fn new(module: &Module) -> Self {
        let mut tail_calls = Self::default();
        // SP1 guests keep plain calls: their objects link statically into a
        // zkVM program, where neither tail calls nor function tables are
        // tested.
        if module.ctx.triple == TargetTriple::SP1 {
            return tail_calls;
        }
        for func_ref in module.funcs() {
            if !module.ctx.func_linkage(func_ref).is_private() {
                continue;
            }
            let sites: Vec<_> = module.func_store.view(func_ref, |function| {
                if frame_storage_escapes(function) {
                    return Vec::new();
                }
                function
                    .layout
                    .iter_block()
                    .filter_map(|block| tail_call(module, func_ref, function, block))
                    .collect()
            });
            for (call, callee) in sites {
                tail_calls.sites.entry(func_ref).or_default().insert(call);
                tail_calls.functions.extend([func_ref, callee]);
            }
            let Some(sites) = tail_calls.sites.get(&func_ref) else {
                continue;
            };
            let switches: Vec<_> = module.func_store.view(func_ref, |function| {
                function
                    .layout
                    .iter_block()
                    .filter_map(|block| {
                        let inst = function.layout.last_inst_of(block)?;
                        Some((inst, tail_switch(function, sites, inst)?))
                    })
                    .collect()
            });
            for (inst, switch) in switches {
                tail_calls.switches.insert((func_ref, inst), switch);
            }
        }
        tail_calls
    }

    pub(super) fn tail_switch(&self, func: FuncRef, br_table: InstId) -> Option<&TailSwitch> {
        self.switches.get(&(func, br_table))
    }

    /// Whether `func` takes part in a tail call, and so uses the `tail`
    /// calling convention.
    pub(super) fn uses_tail_convention(&self, func: FuncRef) -> bool {
        self.functions.contains(&func)
    }

    pub(super) fn is_tail_call(&self, func: FuncRef, call: InstId) -> bool {
        self.sites
            .get(&func)
            .is_some_and(|sites| sites.contains(&call))
    }
}

/// The call ending `block` and its callee, if it is a tail call: the block
/// returns the call's results right after it, and the callee is a private
/// function returning the same types. No argument refers to the caller's
/// frame, and an indirect result passes the caller's own result buffer on.
fn tail_call(
    module: &Module,
    func_ref: FuncRef,
    function: &Function,
    block: BlockId,
) -> Option<(InstId, FuncRef)> {
    let last = function.layout.last_inst_of(block)?;
    let call_inst = function.layout.prev_inst_of(last)?;
    let call = function.dfg.downcast::<&control_flow::Call>(call_inst)?;
    let callee = *call.callee();
    let ctx = &module.ctx;
    let same_returns = ctx.func_sig(func_ref, |caller| {
        ctx.func_sig(callee, |callee| caller.ret_tys() == callee.ret_tys())
    });
    let args_outside_frame = call
        .args()
        .iter()
        .all(|&arg| outside_frame(module, function, arg));
    (ctx.func_linkage(callee).is_private()
        && returns_at_once(function, block, last, function.dfg.inst_results(call_inst))
        && same_returns
        && args_outside_frame)
        .then_some((call_inst, callee))
}

/// The tail switch `inst` ends its block with, if it is one.
fn tail_switch(function: &Function, sites: &HashSet<InstId>, inst: InstId) -> Option<TailSwitch> {
    let table = function.dfg.downcast::<&control_flow::BrTable>(inst)?;
    // The call a destination begins with, if it is a tail call; a phi
    // would come first.
    let dest_call = |dest: BlockId| {
        let call_inst = function
            .layout
            .first_inst_of(dest)
            .filter(|call_inst| sites.contains(call_inst))?;
        let call = function.dfg.downcast::<&control_flow::Call>(call_inst)?;
        Some((call_inst, *call.callee(), call.args().as_slice()))
    };
    let (call, default, args) = dest_call((*table.default())?)?;
    let keys = table
        .table()
        .iter()
        .map(|&(key, dest)| {
            let (_, callee, dest_args) = dest_call(dest)?;
            let key = function
                .dfg
                .value_imm(key)?
                .zext(Type::I256)
                .as_i256()
                .to_u256();
            (dest_args == args && key.0[1..] == [0; 3]).then_some((key.0[0], callee))
        })
        .collect::<Option<_>>()?;
    Some(TailSwitch {
        keys,
        default,
        call,
    })
}

/// Whether `last`, which ends `block`, returns `results` right away: a
/// `return` of them, or a jump to a block of phis that returns the phis
/// taking them from `block`, as a `match` whose arms make calls joins.
fn returns_at_once(function: &Function, block: BlockId, last: InstId, results: &[ValueId]) -> bool {
    if let Some(ret) = function.dfg.downcast::<&control_flow::Return>(last) {
        return ret.args().as_slice() == results;
    }
    let Some(jump) = function.dfg.downcast::<&control_flow::Jump>(last) else {
        return false;
    };
    let dest = *jump.dest();
    let Some(ret) = function
        .layout
        .iter_inst(dest)
        .find(|&inst| !function.dfg.is_phi(inst))
        .and_then(|inst| function.dfg.downcast::<&control_flow::Return>(inst))
    else {
        return false;
    };
    ret.args().as_slice().len() == results.len()
        && ret
            .args()
            .as_slice()
            .iter()
            .zip(results)
            .all(|(&returned, &result)| {
                function.dfg.value_inst(returned).is_some_and(|inst| {
                    function.layout.inst_block(inst) == dest
                        && function.dfg.cast_phi(inst).is_some_and(|phi| {
                            phi.args()
                                .iter()
                                .any(|&(value, from)| from == block && value == result)
                        })
                })
            })
}

/// Whether `arg` neither lives in the caller's frame nor refers to it. i256
/// and aggregate arguments pass as the address of caller storage, and a
/// constref is outside the frame only when it reaches a global or one of
/// the caller's own arguments through projections: a constref call result
/// is a copy in the frame.
fn outside_frame(module: &Module, function: &Function, arg: ValueId) -> bool {
    let ty = function.dfg.value_ty(arg);
    match ty.resolve_compound(&module.ctx) {
        _ if ty == Type::I256 => false,
        Some(CompoundType::Array { .. } | CompoundType::Struct(_) | CompoundType::Enum(_)) => false,
        Some(CompoundType::ConstRef(_)) => constref_outside_frame(function, arg),
        _ => true,
    }
}

fn constref_outside_frame(function: &Function, value: ValueId) -> bool {
    let Value::Inst { inst, .. } = *function.dfg.value(value) else {
        return matches!(function.dfg.value(value), Value::Arg { .. });
    };
    if let Some(proj) = function.dfg.downcast::<&data::ConstProj>(inst) {
        return constref_outside_frame(function, proj.values()[0]);
    }
    if let Some(index) = function.dfg.downcast::<&data::ConstIndex>(inst) {
        return constref_outside_frame(function, *index.object());
    }
    function.dfg.downcast::<&data::ConstRef>(inst).is_some()
}

/// Whether a callee could reach storage in this function's frame: an
/// `obj.alloc` whose reference, or a projection of it, is used other than as
/// the address of an object load or store, or any `alloca` or
/// `obj.materialize.stack`, whose addresses are raw pointers.
fn frame_storage_escapes(function: &Function) -> bool {
    let mut references: Vec<ValueId> = Vec::new();
    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            if function.dfg.downcast::<&data::Alloca>(inst).is_some()
                || function
                    .dfg
                    .downcast::<&data::ObjMaterializeStack>(inst)
                    .is_some()
            {
                return true;
            }
            if function.dfg.downcast::<&data::ObjAlloc>(inst).is_some() {
                references.extend(function.dfg.inst_results(inst));
            }
        }
    }
    while let Some(reference) = references.pop() {
        for &user in function.dfg.users(reference) {
            if !function.layout.is_inst_inserted(user) {
                continue;
            }
            if let Some(load) = function.dfg.downcast::<&data::ObjLoad>(user)
                && *load.object() == reference
            {
                continue;
            }
            if let Some(store) = function.dfg.downcast::<&data::ObjStore>(user)
                && *store.object() == reference
                && *store.value() != reference
            {
                continue;
            }
            if let Some(proj) = function.dfg.downcast::<&data::ObjProj>(user)
                && proj.values().first() == Some(&reference)
                && !proj.values()[1..].contains(&reference)
            {
                references.extend(function.dfg.inst_results(user));
                continue;
            }
            if let Some(index) = function.dfg.downcast::<&data::ObjIndex>(user)
                && *index.object() == reference
                && *index.index() != reference
            {
                references.extend(function.dfg.inst_results(user));
                continue;
            }
            return true;
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use sonatina_ir::Module;

    use super::TailCalls;
    use sonatina_ir::module::FuncRef;
    use sonatina_parser::parse_module;

    fn parse_test_module(source: &str) -> Module {
        parse_module(source).expect("parse should succeed").module
    }

    fn lookup_func(module: &Module, name: &str) -> FuncRef {
        module
            .funcs()
            .into_iter()
            .find(|&func| module.ctx.func_sig(func, |sig| sig.name() == name))
            .expect("function should exist")
    }

    fn tail_calls(source: &str) -> (Module, TailCalls) {
        let module = parse_test_module(&format!("target = \"x86_64-unknown-native\"\n{source}"));
        let tail_calls = TailCalls::new(&module);
        (module, tail_calls)
    }

    /// The names of the functions using the `tail` convention.
    fn tail_functions(source: &str) -> Vec<String> {
        let (module, tail_calls) = tail_calls(source);
        let mut names: Vec<_> = module
            .funcs()
            .into_iter()
            .filter(|&func| tail_calls.uses_tail_convention(func))
            .map(|func| module.ctx.func_sig(func, |sig| sig.name().to_string()))
            .collect();
        names.sort();
        names
    }

    #[test]
    fn returned_call_results_are_tail_calls() {
        let names = tail_functions(
            r#"
func private %f(v0.i64) -> i64 {
    block0:
        v1.i64 = call %g v0;
        return v1;
}

func private %g(v0.i64) -> i64 {
    block0:
        return v0;
}

func public %entry(v0.i64) -> i64 {
    block0:
        v1.i64 = call %f v0;
        return v1;
}
"#,
        );
        // A public caller keeps the platform convention and calls normally.
        assert_eq!(names, ["f", "g"]);
    }

    #[test]
    fn calls_joining_a_returning_block_are_tail_calls() {
        let (module, tail_calls) = tail_calls(
            r#"
func private %dispatch(v0.i64, v1.i64) -> i64 {
    block0:
        br_table v0 block3 (0.i64 block1) (1.i64 block2);
    block1:
        v2.i64 = call %inc v1;
        jump block4;
    block2:
        v3.i64 = call %dec v1;
        v5.i64 = add v3 1.i64;
        jump block4;
    block3:
        jump block4;
    block4:
        v4.i64 = phi (v2 block1) (v5 block2) (v1 block3);
        return v4;
}

func private %inc(v0.i64) -> i64 {
    block0:
        v1.i64 = add v0 1.i64;
        return v1;
}

func private %dec(v0.i64) -> i64 {
    block0:
        v1.i64 = sub v0 1.i64;
        return v1;
}
"#,
        );
        let dispatch = lookup_func(&module, "dispatch");
        let calls: Vec<_> = module.func_store.view(dispatch, |function| {
            function
                .layout
                .iter_block()
                .flat_map(|block| function.layout.iter_inst(block))
                .filter(|&inst| tail_calls.is_tail_call(dispatch, inst))
                .map(|inst| function.layout.inst_block(inst))
                .collect()
        });
        // `dec`'s result is used before the join.
        assert_eq!(calls.len(), 1);
        assert!(tail_calls.uses_tail_convention(lookup_func(&module, "inc")));
        assert!(!tail_calls.uses_tail_convention(lookup_func(&module, "dec")));
    }

    #[test]
    fn used_results_and_frame_arguments_are_not_tail_calls() {
        let names = tail_functions(
            r#"
func private %adds(v0.i64) -> i64 {
    block0:
        v1.i64 = call %g v0;
        v2.i64 = add v1 1.i64;
        return v2;
}

func private %wide(v0.i256) -> i256 {
    block0:
        v1.i256 = call %h v0;
        return v1;
}

func private %narrows(v0.i64) -> i32 {
    block0:
        v1.i64 = call %g v0;
        v2.i32 = trunc v1 i32;
        return v2;
}

func private %g(v0.i64) -> i64 {
    block0:
        return v0;
}

func private %h(v0.i256) -> i256 {
    block0:
        return v0;
}
"#,
        );
        assert!(names.is_empty(), "{names:?}");
    }

    #[test]
    fn constrefs_from_arguments_pass_on() {
        let (module, tail_calls) = tail_calls(
            r#"
type @pair = { i64, i64 };

declare external %make(i64) -> constref<@pair>;

func private %passes_argument(v0.constref<@pair>, v1.i64) -> i64 {
    block0:
        v2.i64 = call %first v0 v1;
        return v2;
}

func private %passes_result(v0.i64) -> i64 {
    block0:
        v1.constref<@pair> = call %make v0;
        v2.i64 = call %first v1 v0;
        return v2;
}

func private %first(v0.constref<@pair>, v1.i64) -> i64 {
    block0:
        v2.constref<i64> = const.proj v0 0.i256;
        v3.i64 = const.load v2;
        return v3;
}
"#,
        );
        assert!(tail_calls.uses_tail_convention(lookup_func(&module, "passes_argument")));
        assert!(!tail_calls.uses_tail_convention(lookup_func(&module, "passes_result")));
    }

    #[test]
    fn switches_of_like_tail_calls_are_tail_switches() {
        let source = |second_args: &str, default: &str| {
            format!(
                r#"
func private %switch(v0.i64, v1.i64) -> i64 {{
    block0:
        br_table v0 {default} (0.i64 block1) (2.i64 block2);
    block1:
        v2.i64 = call %f v0 v1;
        return v2;
    block2:
        v3.i64 = call %g {second_args};
        return v3;
    block3:
        v4.i64 = call %f v0 v1;
        return v4;
    block4:
        return 0.i64;
}}

func private %f(v0.i64, v1.i64) -> i64 {{
    block0:
        return v1;
}}

func private %g(v0.i64, v1.i64) -> i64 {{
    block0:
        return v0;
}}
"#
            )
        };
        let switch_of = |source: String| {
            let (module, tail_calls) = tail_calls(&source);
            let switch = lookup_func(&module, "switch");
            let br_table = module.func_store.view(switch, |function| {
                let entry = function.layout.entry_block().unwrap();
                function.layout.last_inst_of(entry).unwrap()
            });
            tail_calls
                .tail_switch(switch, br_table)
                .map(|switch| switch.keys.iter().map(|&(key, _)| key).collect::<Vec<_>>())
        };
        assert_eq!(switch_of(source("v0 v1", "block3")), Some(vec![0, 2]));
        // Different arguments, or a default that is no tail call.
        assert_eq!(switch_of(source("v1 v0", "block3")), None);
        assert_eq!(switch_of(source("v0 v1", "block4")), None);
    }

    #[test]
    fn escaped_allocations_keep_calls() {
        let (module, tail_calls) = tail_calls(
            r#"
func private %passes_reference() -> i64 {
    block0:
        v0.objref<i64> = obj.alloc i64;
        obj.store v0 42.i64;
        v1.i64 = call %read v0;
        return v1;
}

func private %local_only(v0.i64) -> i64 {
    block0:
        v1.objref<[i64; 2]> = obj.alloc [i64; 2];
        v2.objref<i64> = obj.index v1 1.i8;
        obj.store v2 v0;
        v3.i64 = obj.load v2;
        v4.i64 = call %g v3;
        return v4;
}

func private %read(v0.objref<i64>) -> i64 {
    block0:
        v1.i64 = obj.load v0;
        return v1;
}

func private %g(v0.i64) -> i64 {
    block0:
        return v0;
}
"#,
        );
        let passes_reference = lookup_func(&module, "passes_reference");
        let local_only = lookup_func(&module, "local_only");
        assert!(!tail_calls.uses_tail_convention(passes_reference));
        assert!(tail_calls.uses_tail_convention(local_only));
    }
}
