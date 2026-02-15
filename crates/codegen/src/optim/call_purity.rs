use sonatina_ir::{Function, InstId, module::FuncAttrs};

pub(crate) fn is_proven_pure_call(func: &Function, inst_id: InstId) -> bool {
    let Some(call) = func.dfg.call_info(inst_id) else {
        return false;
    };

    let attrs = func.ctx().func_attrs(call.callee());
    let impure_attrs = FuncAttrs::NORETURN | FuncAttrs::MEM_WRITE;
    attrs.contains(FuncAttrs::WILLRETURN) && !attrs.intersects(impure_attrs)
}

pub(crate) fn is_removable_pure_call(func: &Function, inst_id: InstId) -> bool {
    let Some(call) = func.dfg.call_info(inst_id) else {
        return false;
    };

    func.ctx().func_linkage(call.callee()).has_definition() && is_proven_pure_call(func, inst_id)
}
