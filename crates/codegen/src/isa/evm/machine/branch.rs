use sonatina_ir::{
    Function, InstId, Type, ValueId,
    inst::{
        InstClassKind, UnaryInstKind,
        control_flow::{Br, BranchKind},
    },
};

pub(crate) fn canonicalize_machine_branch_conditions(func: &mut Function) -> bool {
    let blocks: Vec<_> = func.layout.iter_block().collect();
    let mut changed = false;

    for block in blocks {
        let Some(term) = func.layout.last_inst_of(block) else {
            continue;
        };
        let Some((arg, is_zero_inst, nz_dest, z_dest)) = is_zero_branch_rewrite(func, term) else {
            continue;
        };

        func.dfg.replace_inst(
            term,
            Box::new(Br::new_unchecked(func.inst_set(), arg, z_dest, nz_dest)),
        );
        remove_dead_single_result_inst(func, is_zero_inst);
        changed = true;
    }

    changed
}

fn is_zero_branch_rewrite(
    func: &Function,
    term: InstId,
) -> Option<(ValueId, InstId, sonatina_ir::BlockId, sonatina_ir::BlockId)> {
    let BranchKind::Br(br) = func.dfg.branch_info(term)?.branch_kind() else {
        return None;
    };
    let cond = *br.cond();
    let cond_inst = func.dfg.value_inst(cond)?;
    if !matches!(
        func.dfg.inst(cond_inst).kind(),
        InstClassKind::Unary(UnaryInstKind::IsZero)
    ) {
        return None;
    }

    let arg = func.dfg.inst(cond_inst).collect_values()[0];
    matches!(func.dfg.value_ty(arg), Type::I1 | Type::I256).then_some((
        arg,
        cond_inst,
        *br.nz_dest(),
        *br.z_dest(),
    ))
}

fn remove_dead_single_result_inst(func: &mut Function, inst: InstId) {
    if !func.layout.is_inst_inserted(inst) || !func.dfg.can_drop_if_unused(inst) {
        return;
    }

    let Some(result) = func.dfg.inst_result(inst) else {
        return;
    };
    if func.dfg.users_num(result) != 0 {
        return;
    }

    func.layout.remove_inst(inst);
    func.erase_inst(inst);
}
