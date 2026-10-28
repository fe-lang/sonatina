//! Calls in tail position: a call whose results its function returns right
//! away, which a backend may make a tail call.

use sonatina_ir::{
    BlockId, Function, Module, ValueId,
    inst::{InstId, control_flow},
    module::FuncRef,
};

use crate::module_analysis::analyze_module;

/// The private functions that a function in a recursive cycle calls in
/// tail position. A tail call passes their arguments in place, so removing
/// one they ignore saves nothing and can keep calls in a dispatch table
/// from sharing a signature.
pub(crate) fn recursive_tail_callees(module: &Module) -> Vec<FuncRef> {
    let sccs = analyze_module(module).scc;
    let mut callees = Vec::new();
    for func_ref in module.funcs() {
        if !module.ctx.func_linkage(func_ref).is_private()
            || !sccs.scc_info(sccs.scc_ref(func_ref)).is_cycle
        {
            continue;
        }
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

/// Whether `last`, which ends `block`, returns `results` right away: a
/// `return` of them, or a jump to a block of phis that returns the phis
/// taking them from `block`, as a `match` whose arms make calls joins.
pub(crate) fn returns_at_once(
    function: &Function,
    block: BlockId,
    last: InstId,
    results: &[ValueId],
) -> bool {
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
