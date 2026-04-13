use sonatina_ir::{Function, InstId};

/// Returns true for a defined direct call whose current module effect summary
/// says it always returns and does not mutate state.
///
/// Read-only calls are intentionally included: they can be erased when their
/// results are dead, and they are safe to keep inside straight-line trivial
/// inline splices. Unknown callees stay conservative until function behavior
/// analysis populates `ctx.func_effects`.
pub(crate) fn is_nonmutating_returning_call(func: &Function, inst_id: InstId) -> bool {
    let Some(call) = func.dfg.call_info(inst_id) else {
        return false;
    };

    func.ctx().func_linkage(call.callee()).has_definition()
        && func
            .ctx()
            .func_effects(call.callee())
            .can_elide_if_unused_call()
}
