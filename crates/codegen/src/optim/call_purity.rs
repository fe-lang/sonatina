use sonatina_ir::{Function, InstId};

pub(crate) fn is_proven_pure_call(func: &Function, inst_id: InstId) -> bool {
    let Some(call) = func.dfg.call_info(inst_id) else {
        return false;
    };

    func.ctx()
        .func_effects(call.callee())
        .can_elide_if_unused_call()
}

pub(crate) fn is_removable_pure_call(func: &Function, inst_id: InstId) -> bool {
    let Some(call) = func.dfg.call_info(inst_id) else {
        return false;
    };

    func.ctx().func_linkage(call.callee()).has_definition() && is_proven_pure_call(func, inst_id)
}
