use sonatina_ir::{
    BlockId, Function, Immediate, InstId, Type, Value, ValueId,
    inst::{BinaryInstKind, InstClassKind, UnaryInstKind, cmp, control_flow::Br, downcast},
};

#[derive(Default)]
pub struct BranchCanonicalize;

impl BranchCanonicalize {
    pub fn new() -> Self {
        Self
    }

    pub fn run(&mut self, func: &mut Function) -> bool {
        let blocks: Vec<_> = func.layout.iter_block().collect();
        let mut changed = false;

        for block in blocks {
            let Some(term) = func.layout.last_inst_of(block) else {
                continue;
            };
            let Some(br) = downcast::<&Br>(func.inst_set(), func.dfg.inst(term)) else {
                continue;
            };
            let cond = *br.cond();
            let nz_dest = *br.nz_dest();
            let z_dest = *br.z_dest();

            let Some(plan) = self.rewrite_plan(func, term, cond, nz_dest, z_dest) else {
                continue;
            };

            func.dfg.replace_inst(
                term,
                Box::new(Br::new_unchecked(
                    func.inst_set(),
                    plan.cond,
                    plan.nz_dest,
                    plan.z_dest,
                )),
            );

            for inst in plan.dead_insts {
                remove_dead_single_result_inst(func, inst);
            }

            if let Some(cmp_inst) = plan.dead_cmp_inst {
                remove_dead_single_result_inst(func, cmp_inst);
            }

            changed = true;
        }

        changed
    }

    fn rewrite_plan(
        &self,
        func: &mut Function,
        term: InstId,
        mut cond: ValueId,
        old_nz_dest: BlockId,
        old_z_dest: BlockId,
    ) -> Option<Plan> {
        let original_cond = cond;
        let cond_ty = func.dfg.value_ty(cond);
        let mut swap = false;
        let mut dead_insts = Vec::new();

        while let Some(inst) = func.dfg.value_inst(cond) {
            let InstClassKind::Unary(kind @ (UnaryInstKind::IsZero | UnaryInstKind::Not)) =
                func.dfg.inst(inst).kind()
            else {
                break;
            };

            let arg = func.dfg.inst(inst).collect_values()[0];
            let arg_ty = func.dfg.value_ty(arg);
            if arg_ty != Type::I1
                && !(cond_ty == Type::I256 && kind == UnaryInstKind::IsZero && arg_ty.is_integral())
            {
                break;
            }

            dead_insts.push(inst);
            cond = arg;
            swap = !swap;
        }

        let mut dead_cmp_inst = None;
        if let Some((cmp_inst, kind, lhs, rhs)) = compare_value(func, cond) {
            if let Some(zero_compare) =
                zero_compare_branch_rewrite(func, term, kind, lhs, rhs, cond_ty)
            {
                cond = zero_compare.cond;
                swap ^= zero_compare.swap;
                dead_cmp_inst = Some(cmp_inst);
            } else if compare_cost(invert_compare(kind)) < compare_cost(kind) {
                cond = insert_compare_before(func, term, invert_compare(kind), lhs, rhs, cond_ty);
                swap = !swap;
                dead_cmp_inst = Some(cmp_inst);
            }
        }

        let (nz_dest, z_dest) = if swap {
            (old_z_dest, old_nz_dest)
        } else {
            (old_nz_dest, old_z_dest)
        };

        if cond == original_cond && nz_dest == old_nz_dest && z_dest == old_z_dest {
            return None;
        }

        Some(Plan {
            cond,
            nz_dest,
            z_dest,
            dead_insts,
            dead_cmp_inst,
        })
    }
}

struct Plan {
    cond: ValueId,
    nz_dest: BlockId,
    z_dest: BlockId,
    dead_insts: Vec<InstId>,
    dead_cmp_inst: Option<InstId>,
}

struct ZeroComparePlan {
    cond: ValueId,
    swap: bool,
}

fn compare_value(
    func: &Function,
    value: ValueId,
) -> Option<(InstId, BinaryInstKind, ValueId, ValueId)> {
    let inst = func.dfg.value_inst(value)?;
    let InstClassKind::Binary(kind) = func.dfg.inst(inst).kind() else {
        return None;
    };
    if !is_compare(kind) {
        return None;
    }

    let args = func.dfg.inst(inst).collect_values();
    Some((inst, kind, args[0], args[1]))
}

fn is_compare(kind: BinaryInstKind) -> bool {
    matches!(
        kind,
        BinaryInstKind::Lt
            | BinaryInstKind::Gt
            | BinaryInstKind::Slt
            | BinaryInstKind::Sgt
            | BinaryInstKind::Le
            | BinaryInstKind::Ge
            | BinaryInstKind::Sle
            | BinaryInstKind::Sge
            | BinaryInstKind::Eq
            | BinaryInstKind::Ne
    )
}

fn invert_compare(kind: BinaryInstKind) -> BinaryInstKind {
    match kind {
        BinaryInstKind::Lt => BinaryInstKind::Ge,
        BinaryInstKind::Gt => BinaryInstKind::Le,
        BinaryInstKind::Slt => BinaryInstKind::Sge,
        BinaryInstKind::Sgt => BinaryInstKind::Sle,
        BinaryInstKind::Le => BinaryInstKind::Gt,
        BinaryInstKind::Ge => BinaryInstKind::Lt,
        BinaryInstKind::Sle => BinaryInstKind::Sgt,
        BinaryInstKind::Sge => BinaryInstKind::Slt,
        BinaryInstKind::Eq => BinaryInstKind::Ne,
        BinaryInstKind::Ne => BinaryInstKind::Eq,
        _ => unreachable!("non-compare kind"),
    }
}

fn compare_cost(kind: BinaryInstKind) -> u8 {
    match kind {
        BinaryInstKind::Lt
        | BinaryInstKind::Gt
        | BinaryInstKind::Slt
        | BinaryInstKind::Sgt
        | BinaryInstKind::Eq => 0,
        BinaryInstKind::Le
        | BinaryInstKind::Ge
        | BinaryInstKind::Sle
        | BinaryInstKind::Sge
        | BinaryInstKind::Ne => 1,
        _ => unreachable!("non-compare kind"),
    }
}

fn zero_compare_branch_rewrite(
    func: &mut Function,
    term: InstId,
    kind: BinaryInstKind,
    lhs: ValueId,
    rhs: ValueId,
    result_ty: Type,
) -> Option<ZeroComparePlan> {
    if matches!(kind, BinaryInstKind::Eq | BinaryInstKind::Ne)
        && func.dfg.value_ty(lhs) == Type::I1
        && let Some(bit) = i1_literal(func, rhs)
    {
        return Some(ZeroComparePlan {
            cond: lhs,
            swap: matches!(
                (kind, bit),
                (BinaryInstKind::Eq, false) | (BinaryInstKind::Ne, true)
            ),
        });
    }
    if matches!(kind, BinaryInstKind::Eq | BinaryInstKind::Ne)
        && func.dfg.value_ty(rhs) == Type::I1
        && let Some(bit) = i1_literal(func, lhs)
    {
        return Some(ZeroComparePlan {
            cond: rhs,
            swap: matches!(
                (kind, bit),
                (BinaryInstKind::Eq, false) | (BinaryInstKind::Ne, true)
            ),
        });
    }

    let (arg, swap) = match kind {
        BinaryInstKind::Eq if is_integral_zero_compare(func, lhs, rhs) => (lhs, false),
        BinaryInstKind::Eq if is_integral_zero_compare(func, rhs, lhs) => (rhs, false),
        BinaryInstKind::Ne if is_integral_zero_compare(func, lhs, rhs) => (lhs, true),
        BinaryInstKind::Ne if is_integral_zero_compare(func, rhs, lhs) => (rhs, true),
        BinaryInstKind::Gt if is_integral_zero_compare(func, lhs, rhs) => (lhs, true),
        BinaryInstKind::Lt if is_integral_zero_compare(func, rhs, lhs) => (rhs, true),
        BinaryInstKind::Le if is_integral_zero_compare(func, lhs, rhs) => (lhs, false),
        BinaryInstKind::Ge if is_integral_zero_compare(func, rhs, lhs) => (rhs, false),
        _ => return None,
    };

    Some(ZeroComparePlan {
        cond: insert_is_zero_before(func, term, arg, result_ty)?,
        swap,
    })
}

fn is_integral_zero_compare(func: &Function, value: ValueId, zero: ValueId) -> bool {
    func.dfg.value_ty(value).is_integral()
        && func.dfg.value_imm(zero).is_some_and(Immediate::is_zero)
}

fn i1_literal(func: &Function, value: ValueId) -> Option<bool> {
    match func.dfg.value_imm(value)? {
        Immediate::I1(bit) => Some(bit),
        _ => None,
    }
}

fn insert_compare_before(
    func: &mut Function,
    before: InstId,
    kind: BinaryInstKind,
    lhs: ValueId,
    rhs: ValueId,
    result_ty: Type,
) -> ValueId {
    let is = func.inst_set();
    let inst = match kind {
        BinaryInstKind::Lt => func.dfg.make_inst(cmp::Lt::new_unchecked(is, lhs, rhs)),
        BinaryInstKind::Gt => func.dfg.make_inst(cmp::Gt::new_unchecked(is, lhs, rhs)),
        BinaryInstKind::Slt => func.dfg.make_inst(cmp::Slt::new_unchecked(is, lhs, rhs)),
        BinaryInstKind::Sgt => func.dfg.make_inst(cmp::Sgt::new_unchecked(is, lhs, rhs)),
        BinaryInstKind::Le => func.dfg.make_inst(cmp::Le::new_unchecked(is, lhs, rhs)),
        BinaryInstKind::Ge => func.dfg.make_inst(cmp::Ge::new_unchecked(is, lhs, rhs)),
        BinaryInstKind::Sle => func.dfg.make_inst(cmp::Sle::new_unchecked(is, lhs, rhs)),
        BinaryInstKind::Sge => func.dfg.make_inst(cmp::Sge::new_unchecked(is, lhs, rhs)),
        BinaryInstKind::Eq => func.dfg.make_inst(cmp::Eq::new_unchecked(is, lhs, rhs)),
        BinaryInstKind::Ne => func.dfg.make_inst(cmp::Ne::new_unchecked(is, lhs, rhs)),
        _ => unreachable!("non-compare kind"),
    };
    let value = func.dfg.make_value(Value::Inst {
        inst,
        result_idx: 0,
        ty: result_ty,
    });
    func.dfg.attach_result(inst, value);
    func.layout.insert_inst_before(inst, before);
    value
}

fn insert_is_zero_before(
    func: &mut Function,
    before: InstId,
    arg: ValueId,
    result_ty: Type,
) -> Option<ValueId> {
    let inst = func
        .dfg
        .make_inst(cmp::IsZero::new(func.inst_set().has_is_zero()?, arg));
    let value = func.dfg.make_value(Value::Inst {
        inst,
        result_idx: 0,
        ty: result_ty,
    });
    func.dfg.attach_result(inst, value);
    func.layout.insert_inst_before(inst, before);
    Some(value)
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
