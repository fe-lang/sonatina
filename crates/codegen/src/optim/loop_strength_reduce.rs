use rustc_hash::FxHashMap;
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, I256, InstDowncast, InstId, Type, Value, ValueId,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{
        Inst,
        arith::{Add, Mul, Sub},
        cast::{Bitcast, IntToPtr, PtrToInt},
        data::{Gep, Mload, Mstore},
        evm::EvmMstore8,
    },
};

use crate::{
    analysis::induction::{
        BasicInductionVar, LoopId, detect_basic_ivs_for_loop, match_affine_addr_details,
    },
    cfg_edit::{CfgEditor, CleanupMode},
    domtree::DomTree,
    loop_analysis::{Loop, LoopTree},
};

#[derive(Debug)]
pub struct LoopStrengthReduce {
    rewrites: Vec<LoopRewritePlan>,
}

#[derive(Debug, Default, Clone)]
struct LoopRewritePlan {
    plans: SmallVec<[AddrRecurrencePlan; 8]>,
}

#[derive(Debug, Clone)]
struct AddrRecurrencePlan {
    loop_id: LoopId,
    header: BlockId,
    latch: BlockId,
    preheader: BlockId,
    biv: BasicInductionVar,
    base: ValueId,
    const_bytes: i64,
    coeff_bytes: i64,
    step_bytes: i64,
    users: SmallVec<[InstId; 8]>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct FamilyKey {
    biv: ValueId,
    base: ValueId,
    const_bytes: i64,
    coeff_bytes: i64,
    step_bytes: i64,
}

#[derive(Debug, Default)]
struct MaterializeCache {
    invariant_values: FxHashMap<ValueId, ValueId>,
    addr_i256_values: FxHashMap<ValueId, ValueId>,
}

impl LoopStrengthReduce {
    pub fn new() -> Self {
        Self {
            rewrites: Vec::new(),
        }
    }

    pub fn run(
        &mut self,
        func: &mut Function,
        cfg: &mut ControlFlowGraph,
        domtree: &mut DomTree,
        lpt: &mut LoopTree,
    ) -> bool {
        self.rewrites.clear();
        cfg.compute(func);
        domtree.compute(cfg);
        lpt.compute(cfg, domtree);

        let mut changed = false;
        loop {
            let mut changed_this_round = false;
            let loops: Vec<_> = lpt.loops().collect();
            for loop_id in loops {
                if !func.layout.is_block_inserted(lpt.loop_header(loop_id)) {
                    continue;
                }
                match self.try_rewrite_loop(func, cfg, domtree, lpt, loop_id) {
                    LoopRewriteResult::NoChange => {}
                    LoopRewriteResult::Restart => {
                        changed = true;
                        changed_this_round = true;
                        cfg.compute(func);
                        domtree.compute(cfg);
                        lpt.compute(cfg, domtree);
                        break;
                    }
                    LoopRewriteResult::Changed(plan) => {
                        changed = true;
                        changed_this_round = true;
                        self.rewrites.push(*plan);
                        cfg.compute(func);
                        domtree.compute(cfg);
                        lpt.compute(cfg, domtree);
                        break;
                    }
                }
            }

            if !changed_this_round {
                break;
            }
        }

        changed
    }

    fn try_rewrite_loop(
        &mut self,
        func: &mut Function,
        cfg: &mut ControlFlowGraph,
        domtree: &DomTree,
        lpt: &mut LoopTree,
        loop_id: Loop,
    ) -> LoopRewriteResult {
        if !has_unique_loop_preheader(cfg, lpt, loop_id)
            && loop_has_memory_users(func, lpt, loop_id)
            && ensure_preheader(func, cfg, lpt, loop_id).is_some()
        {
            return LoopRewriteResult::Restart;
        }

        let bivs = detect_basic_ivs_for_loop(func, loop_id, cfg, lpt);
        if bivs.is_empty() {
            return LoopRewriteResult::NoChange;
        }

        let plan = self.plan_loop(func, lpt, loop_id, &bivs);
        if plan.plans.is_empty() {
            return LoopRewriteResult::NoChange;
        }

        let actual_preheader = match ensure_preheader(func, cfg, lpt, loop_id) {
            Some(preheader) => preheader,
            None => return LoopRewriteResult::NoChange,
        };
        if actual_preheader != plan.plans[0].preheader {
            return LoopRewriteResult::Restart;
        }

        let changed = self.apply_rewrite_plan(func, domtree, lpt, &plan);
        if changed {
            LoopRewriteResult::Changed(Box::new(plan))
        } else {
            LoopRewriteResult::NoChange
        }
    }

    fn plan_loop(
        &self,
        func: &Function,
        lpt: &LoopTree,
        loop_id: LoopId,
        bivs: &[BasicInductionVar],
    ) -> LoopRewritePlan {
        let mut groups = FxHashMap::<FamilyKey, usize>::default();
        let mut plans = SmallVec::<[AddrRecurrencePlan; 8]>::new();
        for block in func.layout.iter_block() {
            if !lpt.is_in_loop(block, loop_id) {
                continue;
            }
            for inst in func.layout.iter_inst(block) {
                let Some(addr) = memory_addr_operand(func, inst) else {
                    continue;
                };
                for biv in bivs {
                    if func.dfg.value_ty(biv.phi) != Type::I256
                        || func.dfg.value_ty(biv.init) != Type::I256
                    {
                        continue;
                    }
                    let Some(matched) = match_affine_addr_details(func, lpt, addr, biv) else {
                        continue;
                    };
                    if !matched.profitable || matched.coeff_bytes == 0 {
                        continue;
                    }
                    let Some(step) = biv.step.signed_step_i64() else {
                        continue;
                    };
                    let Some(step_bytes) = matched.coeff_bytes.checked_mul(step) else {
                        continue;
                    };
                    if step_bytes == 0 {
                        continue;
                    }
                    let Some(base) = matched.base else {
                        continue;
                    };

                    let key = FamilyKey {
                        biv: biv.phi,
                        base,
                        const_bytes: matched.const_bytes,
                        coeff_bytes: matched.coeff_bytes,
                        step_bytes,
                    };
                    if let Some(&idx) = groups.get(&key) {
                        plans[idx].users.push(inst);
                    } else {
                        let idx = plans.len();
                        plans.push(AddrRecurrencePlan {
                            loop_id,
                            header: biv.header,
                            latch: biv.latch,
                            preheader: biv.preheader,
                            biv: biv.clone(),
                            base,
                            const_bytes: matched.const_bytes,
                            coeff_bytes: matched.coeff_bytes,
                            step_bytes,
                            users: smallvec![inst],
                        });
                        groups.insert(key, idx);
                    }
                    break;
                }
            }
        }

        LoopRewritePlan { plans }
    }

    fn apply_rewrite_plan(
        &self,
        func: &mut Function,
        domtree: &DomTree,
        lpt: &LoopTree,
        plan: &LoopRewritePlan,
    ) -> bool {
        let mut changed = false;
        let mut cache = MaterializeCache::default();
        for addr_plan in &plan.plans {
            let Some(base_preheader) = materialize_invariant_in_preheader(
                func,
                addr_plan.preheader,
                addr_plan.base,
                addr_plan.loop_id,
                domtree,
                lpt,
                &mut cache,
            ) else {
                continue;
            };
            let Some(base_i256) =
                materialize_addr_base_i256(func, addr_plan.preheader, base_preheader, &mut cache)
            else {
                continue;
            };
            let Some(init_addr) = emit_init_addr(func, addr_plan, base_i256) else {
                continue;
            };
            let Some(addr_phi) =
                insert_addr_phi(func, addr_plan.header, addr_plan.preheader, init_addr)
            else {
                continue;
            };
            let Some(addr_next) =
                emit_addr_step(func, addr_plan.latch, addr_phi, addr_plan.step_bytes)
            else {
                continue;
            };
            let Some(phi_inst) = func.dfg.value_inst(addr_phi) else {
                continue;
            };
            func.dfg
                .append_phi_arg(phi_inst, addr_next, addr_plan.latch);

            for &user in &addr_plan.users {
                rewrite_mem_addr(func, user, addr_phi);
            }
            changed = true;
        }

        changed
    }
}

impl Default for LoopStrengthReduce {
    fn default() -> Self {
        Self::new()
    }
}

enum LoopRewriteResult {
    NoChange,
    Restart,
    Changed(Box<LoopRewritePlan>),
}

fn ensure_preheader(
    func: &mut Function,
    cfg: &mut ControlFlowGraph,
    lpt: &mut LoopTree,
    loop_id: Loop,
) -> Option<BlockId> {
    let header = lpt.loop_header(loop_id);
    let outside_preds: Vec<_> = cfg
        .preds_of(header)
        .copied()
        .filter(|pred| !lpt.is_in_loop(*pred, loop_id))
        .collect();
    let mut editor = CfgEditor::new(func, CleanupMode::Strict);
    let preheader = editor.create_or_reuse_loop_preheader(header, &outside_preds)?;
    *cfg = editor.cfg().clone();

    if !outside_preds.contains(&preheader)
        && let Some(parent_loop) = lpt.parent_loop(loop_id)
    {
        lpt.map_block(preheader, parent_loop);
    }

    Some(preheader)
}

fn has_unique_loop_preheader(cfg: &ControlFlowGraph, lpt: &LoopTree, loop_id: Loop) -> bool {
    let header = lpt.loop_header(loop_id);
    let mut outside_preds = cfg
        .preds_of(header)
        .copied()
        .filter(|pred| !lpt.is_in_loop(*pred, loop_id));
    outside_preds.next().is_some() && outside_preds.next().is_none()
}

fn materialize_invariant_in_preheader(
    func: &mut Function,
    preheader: BlockId,
    value: ValueId,
    loop_id: LoopId,
    domtree: &DomTree,
    lpt: &LoopTree,
    cache: &mut MaterializeCache,
) -> Option<ValueId> {
    if let Some(&materialized) = cache.invariant_values.get(&value) {
        return Some(materialized);
    }

    let materialized = match func.dfg.value(value) {
        Value::Immediate { .. } | Value::Arg { .. } | Value::Global { .. } => value,
        Value::Undef { .. } => return None,
        Value::Inst { inst, .. } => {
            let inst = *inst;
            let block = func.layout.inst_block(inst);
            if block == preheader
                || domtree.dominates(block, preheader) && !lpt.is_in_loop(block, loop_id)
            {
                value
            } else {
                let is = func.inst_set();
                if let Some(cast) =
                    <&Bitcast as InstDowncast>::downcast(is, func.dfg.inst(inst)).cloned()
                {
                    let from = materialize_invariant_in_preheader(
                        func,
                        preheader,
                        *cast.from(),
                        loop_id,
                        domtree,
                        lpt,
                        cache,
                    )?;
                    insert_with_result_before_terminator(
                        func,
                        preheader,
                        Bitcast::new_unchecked(func.inst_set(), from, *cast.ty()),
                        *cast.ty(),
                    )
                } else if let Some(cast) =
                    <&IntToPtr as InstDowncast>::downcast(is, func.dfg.inst(inst)).cloned()
                {
                    let from = materialize_invariant_in_preheader(
                        func,
                        preheader,
                        *cast.from(),
                        loop_id,
                        domtree,
                        lpt,
                        cache,
                    )?;
                    insert_with_result_before_terminator(
                        func,
                        preheader,
                        IntToPtr::new_unchecked(func.inst_set(), from, *cast.ty()),
                        *cast.ty(),
                    )
                } else if let Some(cast) =
                    <&PtrToInt as InstDowncast>::downcast(is, func.dfg.inst(inst)).cloned()
                {
                    let from = materialize_invariant_in_preheader(
                        func,
                        preheader,
                        *cast.from(),
                        loop_id,
                        domtree,
                        lpt,
                        cache,
                    )?;
                    insert_with_result_before_terminator(
                        func,
                        preheader,
                        PtrToInt::new_unchecked(func.inst_set(), from, *cast.ty()),
                        *cast.ty(),
                    )
                } else if let Some(add) =
                    <&Add as InstDowncast>::downcast(is, func.dfg.inst(inst)).cloned()
                {
                    if value_i64(func, *add.lhs()).is_none()
                        && value_i64(func, *add.rhs()).is_none()
                    {
                        return None;
                    }
                    let lhs = materialize_invariant_in_preheader(
                        func,
                        preheader,
                        *add.lhs(),
                        loop_id,
                        domtree,
                        lpt,
                        cache,
                    )?;
                    let rhs = materialize_invariant_in_preheader(
                        func,
                        preheader,
                        *add.rhs(),
                        loop_id,
                        domtree,
                        lpt,
                        cache,
                    )?;
                    insert_with_result_before_terminator(
                        func,
                        preheader,
                        Add::new_unchecked(func.inst_set(), lhs, rhs),
                        func.dfg.value_ty(value),
                    )
                } else if let Some(sub) =
                    <&Sub as InstDowncast>::downcast(is, func.dfg.inst(inst)).cloned()
                {
                    if value_i64(func, *sub.lhs()).is_none()
                        && value_i64(func, *sub.rhs()).is_none()
                    {
                        return None;
                    }
                    let lhs = materialize_invariant_in_preheader(
                        func,
                        preheader,
                        *sub.lhs(),
                        loop_id,
                        domtree,
                        lpt,
                        cache,
                    )?;
                    let rhs = materialize_invariant_in_preheader(
                        func,
                        preheader,
                        *sub.rhs(),
                        loop_id,
                        domtree,
                        lpt,
                        cache,
                    )?;
                    insert_with_result_before_terminator(
                        func,
                        preheader,
                        Sub::new_unchecked(func.inst_set(), lhs, rhs),
                        func.dfg.value_ty(value),
                    )
                } else if let Some(gep) =
                    <&Gep as InstDowncast>::downcast(is, func.dfg.inst(inst)).cloned()
                {
                    let (&base, indices) = gep.values().split_first()?;
                    const_gep_offset(func, base, indices)?;
                    let base = materialize_invariant_in_preheader(
                        func, preheader, base, loop_id, domtree, lpt, cache,
                    )?;
                    let mut values = SmallVec::<[ValueId; 8]>::with_capacity(gep.values().len());
                    values.push(base);
                    values.extend(indices.iter().copied());
                    insert_with_result_before_terminator(
                        func,
                        preheader,
                        Gep::new_unchecked(func.inst_set(), values),
                        func.dfg.value_ty(value),
                    )
                } else {
                    return None;
                }
            }
        }
    };

    cache.invariant_values.insert(value, materialized);
    Some(materialized)
}

fn materialize_addr_base_i256(
    func: &mut Function,
    preheader: BlockId,
    value: ValueId,
    cache: &mut MaterializeCache,
) -> Option<ValueId> {
    if let Some(&materialized) = cache.addr_i256_values.get(&value) {
        return Some(materialized);
    }

    let ty = func.dfg.value_ty(value);
    if ty == Type::I256 {
        return Some(value);
    }
    if !ty.is_pointer(func.ctx()) {
        return None;
    }

    let converted = insert_with_result_before_terminator(
        func,
        preheader,
        PtrToInt::new_unchecked(func.inst_set(), value, Type::I256),
        Type::I256,
    );
    cache.addr_i256_values.insert(value, converted);
    Some(converted)
}

fn emit_init_addr(
    func: &mut Function,
    plan: &AddrRecurrencePlan,
    base_i256: ValueId,
) -> Option<ValueId> {
    let mut addr = base_i256;
    let mut const_bytes = plan.const_bytes;
    if plan.coeff_bytes != 0 {
        if let Some(init_imm) = value_i64(func, plan.biv.init) {
            const_bytes = const_bytes.checked_add(plan.coeff_bytes.checked_mul(init_imm)?)?;
        } else {
            let scaled_init = if plan.coeff_bytes == 1 || plan.coeff_bytes == -1 {
                plan.biv.init
            } else {
                let coeff = make_i256_imm(func, plan.coeff_bytes.unsigned_abs());
                insert_with_result_before_terminator(
                    func,
                    plan.preheader,
                    Mul::new_unchecked(func.inst_set(), plan.biv.init, coeff),
                    Type::I256,
                )
            };
            addr = if plan.coeff_bytes >= 0 {
                insert_with_result_before_terminator(
                    func,
                    plan.preheader,
                    Add::new_unchecked(func.inst_set(), addr, scaled_init),
                    Type::I256,
                )
            } else {
                insert_with_result_before_terminator(
                    func,
                    plan.preheader,
                    Sub::new_unchecked(func.inst_set(), addr, scaled_init),
                    Type::I256,
                )
            };
        }
    }

    if const_bytes == 0 {
        return Some(addr);
    }

    let delta = make_i256_imm(func, const_bytes.unsigned_abs());
    Some(if const_bytes >= 0 {
        insert_with_result_before_terminator(
            func,
            plan.preheader,
            Add::new_unchecked(func.inst_set(), addr, delta),
            Type::I256,
        )
    } else {
        insert_with_result_before_terminator(
            func,
            plan.preheader,
            Sub::new_unchecked(func.inst_set(), addr, delta),
            Type::I256,
        )
    })
}

fn emit_addr_step(
    func: &mut Function,
    latch: BlockId,
    addr_phi: ValueId,
    step_bytes: i64,
) -> Option<ValueId> {
    let delta = make_i256_imm(func, step_bytes.unsigned_abs());
    Some(if step_bytes >= 0 {
        insert_with_result_before_terminator(
            func,
            latch,
            Add::new_unchecked(func.inst_set(), addr_phi, delta),
            Type::I256,
        )
    } else {
        insert_with_result_before_terminator(
            func,
            latch,
            Sub::new_unchecked(func.inst_set(), addr_phi, delta),
            Type::I256,
        )
    })
}

fn insert_addr_phi(
    func: &mut Function,
    header: BlockId,
    preheader: BlockId,
    init_addr: ValueId,
) -> Option<ValueId> {
    let mut last_phi = None;
    for inst in func.layout.iter_inst(header) {
        if func.dfg.is_phi(inst) {
            last_phi = Some(inst);
        } else {
            break;
        }
    }

    let loc = last_phi.map_or(CursorLocation::BlockTop(header), CursorLocation::At);
    let mut cursor = InstInserter::at_location(loc);
    let phi_inst = cursor.insert_inst_data(func, func.dfg.make_phi(vec![(init_addr, preheader)]));
    let phi_value = cursor.make_result(func, phi_inst, Type::I256);
    cursor.attach_result(func, phi_inst, phi_value);
    Some(phi_value)
}

fn insert_with_result_before_terminator<I: Inst>(
    func: &mut Function,
    block: BlockId,
    inst_data: I,
    ty: Type,
) -> ValueId {
    let mut cursor = InstInserter::at_location(before_terminator_loc(func, block));
    let inst = cursor.insert_inst_data(func, inst_data);
    let value = cursor.make_result(func, inst, ty);
    cursor.attach_result(func, inst, value);
    value
}

fn before_terminator_loc(func: &Function, block: BlockId) -> CursorLocation {
    let term = func
        .layout
        .last_inst_of(block)
        .unwrap_or_else(|| panic!("block {block:?} missing terminator"));
    func.layout
        .prev_inst_of(term)
        .map_or(CursorLocation::BlockTop(block), CursorLocation::At)
}

fn rewrite_mem_addr(func: &mut Function, inst: InstId, new_addr: ValueId) {
    let is = func.inst_set();
    if let Some(mload) = <&Mload as InstDowncast>::downcast(is, func.dfg.inst(inst)).cloned() {
        func.dfg.replace_inst_preserving_results(
            inst,
            Box::new(Mload::new_unchecked(is, new_addr, *mload.ty())),
        );
        return;
    }
    if let Some(mstore) = <&Mstore as InstDowncast>::downcast(is, func.dfg.inst(inst)).cloned() {
        func.dfg.replace_inst_preserving_results(
            inst,
            Box::new(Mstore::new_unchecked(
                is,
                new_addr,
                *mstore.value(),
                *mstore.ty(),
            )),
        );
        return;
    }
    if let Some(mstore8) = <&EvmMstore8 as InstDowncast>::downcast(is, func.dfg.inst(inst)).cloned()
    {
        func.dfg.replace_inst_preserving_results(
            inst,
            Box::new(EvmMstore8::new_unchecked(is, new_addr, *mstore8.val())),
        );
    }
}

fn memory_addr_operand(func: &Function, inst: InstId) -> Option<ValueId> {
    let is = func.inst_set();
    if let Some(mload) = <&Mload as InstDowncast>::downcast(is, func.dfg.inst(inst)) {
        return Some(*mload.addr());
    }
    if let Some(mstore) = <&Mstore as InstDowncast>::downcast(is, func.dfg.inst(inst)) {
        return Some(*mstore.addr());
    }
    if let Some(mstore8) = <&EvmMstore8 as InstDowncast>::downcast(is, func.dfg.inst(inst)) {
        return Some(*mstore8.addr());
    }
    None
}

fn loop_has_memory_users(func: &Function, lpt: &LoopTree, loop_id: Loop) -> bool {
    func.layout.iter_block().any(|block| {
        lpt.is_in_loop(block, loop_id)
            && func
                .layout
                .iter_inst(block)
                .any(|inst| memory_addr_operand(func, inst).is_some())
    })
}

fn const_gep_offset(func: &Function, base: ValueId, indices: &[ValueId]) -> Option<i64> {
    let mut current_ty = func.dfg.value_ty(base);
    if !current_ty.is_pointer(func.ctx()) {
        return None;
    }

    let mut total = 0i64;
    for &idx_value in indices {
        let idx = value_i64(func, idx_value)?;
        match current_ty.resolve_compound(func.ctx())? {
            sonatina_ir::types::CompoundType::Ptr(elem_ty) => {
                let elem_size = i64::try_from(func.ctx().size_of_unchecked(elem_ty)).ok()?;
                total = total.checked_add(elem_size.checked_mul(idx)?)?;
                current_ty = elem_ty;
            }
            sonatina_ir::types::CompoundType::Array { elem, .. } => {
                let elem_size = i64::try_from(func.ctx().size_of_unchecked(elem)).ok()?;
                total = total.checked_add(elem_size.checked_mul(idx)?)?;
                current_ty = elem;
            }
            sonatina_ir::types::CompoundType::Struct(s) => {
                let idx = usize::try_from(idx).ok()?;
                let (field_offset, field_ty) =
                    crate::optim::aggregate::shape::struct_field_offset_bytes(
                        &s.fields,
                        s.packed,
                        idx,
                        func.ctx(),
                    )?;
                total = total.checked_add(i64::from(field_offset))?;
                current_ty = field_ty;
            }
            sonatina_ir::types::CompoundType::Enum(_)
            | sonatina_ir::types::CompoundType::ObjRef(_)
            | sonatina_ir::types::CompoundType::Func { .. } => return None,
        }
    }

    Some(total)
}

fn value_i64(func: &Function, value: ValueId) -> Option<i64> {
    let imm = func.dfg.value_imm(value)?;
    let value = imm.as_i256();
    if value < I256::from(i64::MIN) || value > I256::from(i64::MAX) {
        return None;
    }
    Some(value.trunc_to_i64())
}

fn make_i256_imm(func: &mut Function, value: u64) -> ValueId {
    func.dfg.make_imm_value(sonatina_ir::Immediate::from_i256(
        I256::from(value),
        Type::I256,
    ))
}

#[cfg(test)]
mod tests {
    use sonatina_ir::{ir_writer::FuncWriter, module::FuncRef};
    use sonatina_parser::parse_module;
    use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_function};

    use crate::optim::{
        branch_canonicalize::BranchCanonicalize, cfg_cleanup::CfgCleanup,
        checked_arith_elim::CheckedArithElim, load_store::LoadStoreSolver, sccp::SccpSolver,
    };

    use super::*;

    #[test]
    fn rewrites_forward_gep_loop_and_verifies() {
        let src = r#"
target = "evm-ethereum-osaka"

func public %forward(v0.*i256) -> i256 {
    block0:
        jump block1;

    block1:
        v1.i256 = phi (0.i256 block0) (v5 block2);
        v2.i256 = phi (0.i256 block0) (v6 block2);
        v3.i1 = lt v1 4.i256;
        br v3 block2 block3;

    block2:
        v4.*i256 = gep v0 v1;
        v7.i256 = mload v4 i256;
        v6.i256 = add v2 v7;
        v5.i256 = add v1 1.i256;
        jump block1;

    block3:
        return v2;
}
"#;

        let parsed = parse_module(src).expect("parse");
        let func_ref = parsed.module.funcs()[0];
        let dump = parsed
            .module
            .func_store
            .modify(func_ref, |func| run_lsr_pipeline(func_ref, func));

        assert!(dump.contains("mload"));
        assert!(dump.contains("32.i256"));
        assert!(dump.contains("phi ("));
        assert!(!dump.contains(" = gep v0 v1"));
    }

    #[test]
    fn rewrites_reverse_gep_loop_and_verifies() {
        let src = r#"
target = "evm-ethereum-osaka"

func public %reverse(v0.*[i256; 8]) -> i256 {
    block0:
        jump block1;

    block1:
        v1.i256 = phi (0.i256 block0) (v6 block2);
        v2.i256 = phi (0.i256 block0) (v7 block2);
        v3.i1 = lt v1 4.i256;
        br v3 block2 block3;

    block2:
        v4.i256 = sub 7.i256 v1;
        v5.*i256 = gep v0 0.i256 v4;
        v8.i256 = mload v5 i256;
        v7.i256 = add v2 v8;
        v6.i256 = add v1 1.i256;
        jump block1;

    block3:
        return v2;
}
"#;

        let parsed = parse_module(src).expect("parse");
        let func_ref = parsed.module.funcs()[0];
        let dump = parsed
            .module
            .func_store
            .modify(func_ref, |func| run_lsr_pipeline(func_ref, func));

        assert!(dump.contains("32.i256"));
        assert!(dump.contains(" = sub "));
        assert!(!dump.contains(" = gep v0 0.i256 v4"));
    }

    #[test]
    fn shares_one_addr_phi_for_load_store_family() {
        let src = r#"
target = "evm-ethereum-osaka"

func public %bump(v0.*i256) -> i256 {
    block0:
        jump block1;

    block1:
        v1.i256 = phi (0.i256 block0) (v6 block2);
        v2.i256 = phi (0.i256 block0) (v10 block2);
        v3.i1 = lt v1 4.i256;
        br v3 block2 block3;

    block2:
        v4.*i256 = gep v0 v1;
        v5.i256 = mload v4 i256;
        v7.i256 = add v5 1.i256;
        mstore v4 v7 i256;
        v10.i256 = add v2 v7;
        v6.i256 = add v1 1.i256;
        jump block1;

    block3:
        return v2;
}
"#;

        let parsed = parse_module(src).expect("parse");
        let func_ref = parsed.module.funcs()[0];
        let dump = parsed
            .module
            .func_store
            .modify(func_ref, |func| run_lsr_pipeline(func_ref, func));

        assert_eq!(dump.matches(" = phi ").count(), 3);
        assert!(dump.contains("mload"));
        assert!(dump.contains("mstore"));
    }

    #[test]
    fn rewrites_after_preheader_split() {
        let src = r#"
target = "evm-ethereum-osaka"

func public %branching(v0.i1, v1.*i256) -> i256 {
    block0:
        br v0 block1 block2;

    block1:
        jump block3;

    block2:
        jump block3;

    block3:
        v2.i256 = phi (0.i256 block1) (1.i256 block2) (v6 block4);
        v3.i256 = phi (0.i256 block1) (0.i256 block2) (v7 block4);
        v4.i1 = lt v2 4.i256;
        br v4 block4 block5;

    block4:
        v5.*i256 = gep v1 v2;
        v8.i256 = mload v5 i256;
        v7.i256 = add v3 v8;
        v6.i256 = add v2 1.i256;
        jump block3;

    block5:
        return v3;
}
"#;

        let parsed = parse_module(src).expect("parse");
        let func_ref = parsed.module.funcs()[0];
        let dump = parsed
            .module
            .func_store
            .modify(func_ref, |func| run_lsr_pipeline(func_ref, func));

        assert!(dump.contains("mload"));
        assert!(!dump.contains(" = gep v1 v2"));
    }

    #[test]
    fn rewrites_multiple_families_with_shared_base_chain() {
        let src = r#"
target = "evm-ethereum-osaka"

func public %two_streams(v0.*i256) -> i256 {
    block0:
        v1.*i256 = gep v0 2.i256;
        jump block1;

    block1:
        v2.i256 = phi (0.i256 block0) (v9 block2);
        v3.i256 = phi (0.i256 block0) (v8 block2);
        v4.i1 = lt v2 4.i256;
        br v4 block2 block3;

    block2:
        v5.*i256 = gep v0 v2;
        v6.i256 = mload v5 i256;
        v7.*i256 = gep v1 v2;
        v10.i256 = mload v7 i256;
        v11.i256 = add v6 v10;
        v8.i256 = add v3 v11;
        v9.i256 = add v2 1.i256;
        jump block1;

    block3:
        return v3;
}
"#;

        let parsed = parse_module(src).expect("parse");
        let func_ref = parsed.module.funcs()[0];
        let dump = parsed
            .module
            .func_store
            .modify(func_ref, |func| run_lsr_pipeline(func_ref, func));

        assert_eq!(dump.matches("mload").count(), 2);
        assert!(!dump.contains(" = gep v0 v2"));
        assert!(!dump.contains(" = gep v1 v2"));
    }

    fn run_lsr_pipeline(func_ref: FuncRef, func: &mut Function) -> String {
        CfgCleanup::new(CleanupMode::Strict).run(func);
        BranchCanonicalize::new().run(func);

        let mut cfg = ControlFlowGraph::default();
        cfg.compute(func);
        LoadStoreSolver::new().run(func, &mut cfg);

        cfg.compute(func);
        let mut domtree = DomTree::default();
        domtree.compute(&cfg);
        let mut lpt = LoopTree::default();
        lpt.compute(&cfg, &domtree);
        CheckedArithElim::new().run(func, &cfg, &lpt);

        cfg.compute(func);
        SccpSolver::new().run(func, &mut cfg);

        cfg.compute(func);
        domtree.compute(&cfg);
        lpt.compute(&cfg, &domtree);
        LoopStrengthReduce::new().run(func, &mut cfg, &mut domtree, &mut lpt);

        cfg.compute(func);
        SccpSolver::new().run(func, &mut cfg);
        CfgCleanup::new(CleanupMode::Strict).run(func);

        let verify_cfg = VerifierConfig::for_level(VerificationLevel::Fast);
        let report = verify_function(func.ctx(), func_ref, func, &verify_cfg);
        assert!(!report.has_errors(), "{report}");

        FuncWriter::new(func_ref, func).dump_string()
    }
}
