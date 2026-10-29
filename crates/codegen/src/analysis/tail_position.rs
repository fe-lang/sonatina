//! Calls in tail position: a call whose results its function returns right
//! away, which a backend may make a tail call.

use std::collections::{HashMap, HashSet};

use sonatina_ir::{
    BlockId, Function, Module, Type, Value, ValueId,
    inst::{InstId, control_flow, data},
    module::FuncRef,
    types::CompoundType,
};
use sonatina_triple::TargetTriple;

use crate::{analysis::known_bits::KnownBitsQuery, module_analysis::analyze_module};

/// The functions that make tail calls: the private functions in a recursive
/// cycle. Only recursion needs a call to replace its caller's frame. Every
/// caller of a tail-convention function keeps its own registers across the
/// call, so elsewhere a tail call would cost more than the return it saves.
pub fn tail_callers(module: &Module) -> Vec<FuncRef> {
    // SP1 guests keep plain calls: their objects link statically into a
    // zkVM program, where neither tail calls nor function tables are tested.
    if module.ctx.triple == TargetTriple::SP1 {
        return Vec::new();
    }
    recursive_functions(module)
}

/// The private functions that a function in a recursive cycle calls in
/// tail position. A tail call passes their arguments in place, so removing
/// one they ignore saves nothing and can keep calls in a dispatch table
/// from sharing a signature.
pub(crate) fn recursive_tail_callees(module: &Module) -> Vec<FuncRef> {
    let mut callees = Vec::new();
    for func_ref in recursive_functions(module) {
        module.func_store.view(func_ref, |function| {
            for block in function.layout.iter_block() {
                if let Some(last) = function.layout.last_inst_of(block)
                    && let Some(call_inst) = function.layout.prev_inst_of(last)
                    && let Some(call) = function.dfg.downcast::<&control_flow::Call>(call_inst)
                    && module.ctx.func_linkage(*call.callee()).is_private()
                    && returns_at_once(function, block, last, function.dfg.inst_results(call_inst))
                {
                    callees.push(*call.callee());
                }
            }
        });
    }
    callees.sort_unstable();
    callees.dedup();
    callees
}

/// The private functions in a recursive cycle.
fn recursive_functions(module: &Module) -> Vec<FuncRef> {
    let sccs = analyze_module(module).scc;
    module
        .funcs()
        .into_iter()
        .filter(|&func_ref| {
            module.ctx.func_linkage(func_ref).is_private()
                && sccs.scc_info(sccs.scc_ref(func_ref)).is_cycle
        })
        .collect()
}

/// The tail calls of `function`, one of the [`tail_callers`], with their
/// callees: none when a callee could reach storage in its frame.
pub fn tail_calls(func_ref: FuncRef, function: &Function) -> Vec<(InstId, FuncRef)> {
    if frame_storage_escapes(function) {
        return Vec::new();
    }
    function
        .layout
        .iter_block()
        .filter_map(|block| tail_call(func_ref, function, block))
        .collect()
}

/// A `br_table` each of whose destinations, the default included, begins
/// with a tail call taking the same arguments. It becomes one indirect tail
/// call through a table of the callees, as an interpreter's dispatch wants.
pub struct TailSwitch {
    /// Each key with its destination's callee.
    pub keys: Vec<(u64, FuncRef)>,
    pub default: FuncRef,
    /// One of the calls, whose arguments every callee takes.
    pub call: InstId,
    /// The bits of the table's index: the fewest, up to a 1024-entry table,
    /// that hold every key and every value the scrutinee's known bits allow,
    /// so the table needs no bounds check.
    pub bits: u16,
}

/// The tail switches of `function`, by their `br_table`s. `sites` are its
/// [`tail_calls`].
pub fn tail_switches(function: &Function, sites: &HashSet<InstId>) -> HashMap<InstId, TailSwitch> {
    let mut known_bits = None;
    function
        .layout
        .iter_block()
        .filter_map(|block| {
            let inst = function.layout.last_inst_of(block)?;
            Some((inst, tail_switch(function, sites, inst, &mut known_bits)?))
        })
        .collect()
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

/// The call ending `block` and its callee, if it is a tail call: the block
/// returns the call's results right after it, and the callee is a private
/// function returning the same types. No argument refers to the caller's
/// frame, and an indirect result passes the caller's own result buffer on.
fn tail_call(func_ref: FuncRef, function: &Function, block: BlockId) -> Option<(InstId, FuncRef)> {
    let last = function.layout.last_inst_of(block)?;
    let call_inst = function.layout.prev_inst_of(last)?;
    let call = function.dfg.downcast::<&control_flow::Call>(call_inst)?;
    let callee = *call.callee();
    let ctx = function.ctx();
    let same_returns = ctx.func_sig(func_ref, |caller| {
        ctx.func_sig(callee, |callee| caller.ret_tys() == callee.ret_tys())
    });
    let args_outside_frame = call.args().iter().all(|&arg| outside_frame(function, arg));
    (ctx.func_linkage(callee).is_private()
        && returns_at_once(function, block, last, function.dfg.inst_results(call_inst))
        && same_returns
        && args_outside_frame)
        .then_some((call_inst, callee))
}

/// The tail switch `inst` ends its block with, if it is one.
fn tail_switch(
    function: &Function,
    sites: &HashSet<InstId>,
    inst: InstId,
    known_bits: &mut Option<KnownBitsQuery>,
) -> Option<TailSwitch> {
    let table = function.dfg.downcast::<&control_flow::BrTable>(inst)?;
    let scrutinee = *table.scrutinee();
    if !matches!(
        function.dfg.value_ty(scrutinee),
        Type::I8 | Type::I16 | Type::I32 | Type::I64
    ) {
        return None;
    }
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
    let keys: Vec<_> = table
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
    let max_key = keys.iter().map(|&(key, _)| key).max().unwrap_or(0);
    let key_bits = (u64::BITS - max_key.leading_zeros()) as u16;
    let known_bits = known_bits.get_or_insert_with(|| KnownBitsQuery::new(function));
    let bits =
        (key_bits..=10).find(|&bits| known_bits.fits_in_low_bits(function, scrutinee, bits))?;
    Some(TailSwitch {
        keys,
        default,
        call,
        bits,
    })
}

/// Whether `arg` neither lives in the caller's frame nor refers to it. i256
/// and aggregate arguments pass as the address of caller storage, and a
/// constref is outside the frame only when it reaches a global or one of
/// the caller's own arguments through projections: a constref call result
/// is a copy in the frame.
fn outside_frame(function: &Function, arg: ValueId) -> bool {
    let ty = function.dfg.value_ty(arg);
    match ty.resolve_compound(function.ctx()) {
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
