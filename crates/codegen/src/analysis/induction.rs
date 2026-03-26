use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, I256, Immediate, InstDowncast, InstId, Type, Value,
    ValueId,
    inst::{
        arith::{Add, Mul, Sub},
        cast::{Bitcast, IntToPtr, PtrToInt},
        control_flow::Phi,
        data::Gep,
    },
    types::CompoundType,
};

use crate::{
    loop_analysis::{Loop, LoopTree},
    optim::aggregate::shape,
};

pub type LoopId = Loop;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BasicInductionVar {
    pub loop_id: LoopId,
    pub header: BlockId,
    pub preheader: BlockId,
    pub latch: BlockId,
    pub phi: ValueId,
    pub init: ValueId,
    pub step_inst: InstId,
    pub step_value: ValueId,
    pub step: StepKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StepKind {
    AddConst(Immediate),
    SubConst(Immediate),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct AffineIv {
    pub loop_id: LoopId,
    pub phi: ValueId,
}

impl From<&BasicInductionVar> for AffineIv {
    fn from(biv: &BasicInductionVar) -> Self {
        Self {
            loop_id: biv.loop_id,
            phi: biv.phi,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct BasicInductionVarProbe {
    pub iv: AffineIv,
    pub step: StepKind,
}

impl From<&BasicInductionVarProbe> for AffineIv {
    fn from(probe: &BasicInductionVarProbe) -> Self {
        probe.iv
    }
}

impl StepKind {
    pub fn signed_step_i64(self) -> Option<i64> {
        match self {
            Self::AddConst(imm) => imm_i64(imm),
            Self::SubConst(imm) => imm_i64(imm)?.checked_neg(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AffineAddrExpr {
    pub iv: ValueId,
    pub base: ValueId,
    pub const_bytes: i64,
    pub coeff_bytes: i64,
    pub addr_ty: Type,
}

#[derive(Debug, Default)]
pub struct InductionAnalysis {
    bivs_by_loop: FxHashMap<u32, SmallVec<[BasicInductionVar; 4]>>,
}

impl InductionAnalysis {
    pub fn compute(func: &Function, cfg: &ControlFlowGraph, lpt: &LoopTree) -> Self {
        let mut bivs_by_loop = FxHashMap::default();
        for loop_id in lpt.loops() {
            let bivs = detect_basic_ivs_for_loop(func, loop_id, cfg, lpt);
            if !bivs.is_empty() {
                bivs_by_loop.insert(loop_id.as_u32(), bivs);
            }
        }
        Self { bivs_by_loop }
    }

    pub fn basic_ivs_in_loop(&self, loop_id: LoopId) -> &[BasicInductionVar] {
        self.bivs_by_loop
            .get(&loop_id.as_u32())
            .map(SmallVec::as_slice)
            .unwrap_or(&[])
    }
}

pub fn detect_basic_ivs_for_loop(
    func: &Function,
    loop_id: LoopId,
    cfg: &ControlFlowGraph,
    lpt: &LoopTree,
) -> SmallVec<[BasicInductionVar; 4]> {
    let header = lpt.loop_header(loop_id);
    let Some(preheader) = unique_outside_pred(cfg, lpt, loop_id, header) else {
        return smallvec![];
    };
    let Some(latch) = unique_latch(cfg, lpt, loop_id, header) else {
        return smallvec![];
    };

    let mut bivs = SmallVec::new();
    for inst in func.layout.iter_inst(header) {
        let Some(phi) = func.dfg.cast_phi(inst) else {
            break;
        };
        let Some(phi_value) = func.dfg.inst_result(inst) else {
            continue;
        };
        if !func.dfg.value_ty(phi_value).is_integral() {
            continue;
        }

        let Some((init, backedge)) = phi_init_and_backedge(phi, preheader, latch) else {
            continue;
        };
        let Some((step_inst, step_value, step)) =
            detect_basic_iv_step(func, latch, phi_value, backedge)
        else {
            continue;
        };

        bivs.push(BasicInductionVar {
            loop_id,
            header,
            preheader,
            latch,
            phi: phi_value,
            init,
            step_inst,
            step_value,
            step,
        });
    }

    bivs
}

pub fn match_affine_addr(
    func: &Function,
    lpt: &LoopTree,
    value: ValueId,
    biv: &BasicInductionVar,
) -> Option<AffineAddrExpr> {
    let matched = match_affine_addr_details(func, lpt, value, biv.into())?;
    let base = matched.base?;
    Some(AffineAddrExpr {
        iv: biv.phi,
        base,
        const_bytes: matched.const_bytes,
        coeff_bytes: matched.coeff_bytes,
        addr_ty: Type::I256,
    })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct MatchedAffineAddr {
    pub base: Option<ValueId>,
    pub const_bytes: i64,
    pub coeff_bytes: i64,
    pub profitable: bool,
}

pub(crate) fn match_affine_addr_details(
    func: &Function,
    lpt: &LoopTree,
    value: ValueId,
    biv: AffineIv,
) -> Option<MatchedAffineAddr> {
    let mut visiting = FxHashSet::default();
    let matched = match_addr_term(func, lpt, biv, value, &mut visiting)?;
    (matched.base.is_some() || matched.const_bytes != 0 || matched.coeff_bytes != 0)
        .then_some(matched)
}

fn match_addr_term(
    func: &Function,
    lpt: &LoopTree,
    biv: AffineIv,
    value: ValueId,
    visiting: &mut FxHashSet<ValueId>,
) -> Option<MatchedAffineAddr> {
    if !visiting.insert(value) {
        return None;
    }

    let matched = if value == biv.phi {
        Some(MatchedAffineAddr {
            base: None,
            const_bytes: 0,
            coeff_bytes: 1,
            profitable: false,
        })
    } else if let Some(imm) = func.dfg.value_imm(value) {
        Some(MatchedAffineAddr {
            base: None,
            const_bytes: imm_i64(imm)?,
            coeff_bytes: 0,
            profitable: false,
        })
    } else if is_loop_invariant_value(func, lpt, biv, value, &mut FxHashSet::default()) {
        Some(MatchedAffineAddr {
            base: Some(value),
            const_bytes: 0,
            coeff_bytes: 0,
            profitable: false,
        })
    } else {
        let inst = func.dfg.value_inst(value)?;
        let inst_data = func.dfg.inst(inst);
        let is = func.inst_set();

        if let Some(cast) = <&Bitcast as InstDowncast>::downcast(is, inst_data) {
            match_addr_term(func, lpt, biv, *cast.from(), visiting)
        } else if let Some(cast) = <&IntToPtr as InstDowncast>::downcast(is, inst_data) {
            match_addr_term(func, lpt, biv, *cast.from(), visiting)
        } else if let Some(cast) = <&PtrToInt as InstDowncast>::downcast(is, inst_data) {
            match_addr_term(func, lpt, biv, *cast.from(), visiting)
        } else if let Some(add) = <&Add as InstDowncast>::downcast(is, inst_data) {
            combine_add(
                match_addr_term(func, lpt, biv, *add.lhs(), visiting)?,
                match_addr_term(func, lpt, biv, *add.rhs(), visiting)?,
            )
        } else if let Some(sub) = <&Sub as InstDowncast>::downcast(is, inst_data) {
            combine_sub(
                match_addr_term(func, lpt, biv, *sub.lhs(), visiting)?,
                match_addr_term(func, lpt, biv, *sub.rhs(), visiting)?,
            )
        } else if let Some(mul) = <&Mul as InstDowncast>::downcast(is, inst_data) {
            if let Some(scale) = value_i64(func, *mul.lhs()) {
                let (const_term, coeff_term) = match_index_expr(func, *mul.rhs(), biv)?;
                Some(MatchedAffineAddr {
                    base: None,
                    const_bytes: scale.checked_mul(const_term)?,
                    coeff_bytes: scale.checked_mul(coeff_term)?,
                    profitable: coeff_term != 0,
                })
            } else if let Some(scale) = value_i64(func, *mul.rhs()) {
                let (const_term, coeff_term) = match_index_expr(func, *mul.lhs(), biv)?;
                Some(MatchedAffineAddr {
                    base: None,
                    const_bytes: scale.checked_mul(const_term)?,
                    coeff_bytes: scale.checked_mul(coeff_term)?,
                    profitable: coeff_term != 0,
                })
            } else {
                None
            }
        } else if let Some(gep) = <&Gep as InstDowncast>::downcast(is, inst_data) {
            match_gep(func, biv, gep)
        } else {
            None
        }
    };

    visiting.remove(&value);
    matched
}

fn match_gep(func: &Function, biv: AffineIv, gep: &Gep) -> Option<MatchedAffineAddr> {
    let (&base, indices) = gep.values().split_first()?;
    let mut current_ty = func.dfg.value_ty(base);
    if !current_ty.is_pointer(func.ctx()) {
        return None;
    }

    let mut const_bytes = 0i64;
    let mut coeff_bytes = 0i64;
    for &idx_value in indices {
        match current_ty.resolve_compound(func.ctx())? {
            CompoundType::Ptr(elem_ty) => {
                let elem_size = i64::try_from(func.ctx().size_of_unchecked(elem_ty)).ok()?;
                let (idx_const, idx_coeff) = match_index_expr(func, idx_value, biv)?;
                const_bytes = const_bytes.checked_add(elem_size.checked_mul(idx_const)?)?;
                coeff_bytes = coeff_bytes.checked_add(elem_size.checked_mul(idx_coeff)?)?;
                current_ty = elem_ty;
            }
            CompoundType::Array { elem, .. } => {
                let elem_size = i64::try_from(func.ctx().size_of_unchecked(elem)).ok()?;
                let (idx_const, idx_coeff) = match_index_expr(func, idx_value, biv)?;
                const_bytes = const_bytes.checked_add(elem_size.checked_mul(idx_const)?)?;
                coeff_bytes = coeff_bytes.checked_add(elem_size.checked_mul(idx_coeff)?)?;
                current_ty = elem;
            }
            CompoundType::Struct(s) => {
                let (idx_const, idx_coeff) = match_index_expr(func, idx_value, biv)?;
                if idx_coeff != 0 {
                    return None;
                }
                let idx = usize::try_from(idx_const).ok()?;
                let (field_offset, field_ty) =
                    shape::struct_field_offset_bytes(&s.fields, s.packed, idx, func.ctx())?;
                const_bytes = const_bytes.checked_add(i64::from(field_offset))?;
                current_ty = field_ty;
            }
            CompoundType::Enum(_)
            | CompoundType::ObjRef(_)
            | CompoundType::ConstRef(_)
            | CompoundType::Func { .. } => {
                return None;
            }
        }
    }

    Some(MatchedAffineAddr {
        base: Some(base),
        const_bytes,
        coeff_bytes,
        profitable: coeff_bytes != 0,
    })
}

fn match_index_expr(func: &Function, value: ValueId, biv: AffineIv) -> Option<(i64, i64)> {
    match_index_expr_rec(func, value, biv, &mut FxHashSet::default())
}

fn match_index_expr_rec(
    func: &Function,
    value: ValueId,
    biv: AffineIv,
    visiting: &mut FxHashSet<ValueId>,
) -> Option<(i64, i64)> {
    if !visiting.insert(value) {
        return None;
    }

    let matched = if value == biv.phi {
        Some((0, 1))
    } else if let Some(imm) = func.dfg.value_imm(value) {
        Some((imm_i64(imm)?, 0))
    } else {
        let inst = func.dfg.value_inst(value)?;
        let inst_data = func.dfg.inst(inst);
        let is = func.inst_set();

        if let Some(cast) = <&Bitcast as InstDowncast>::downcast(is, inst_data) {
            match_index_expr_rec(func, *cast.from(), biv, visiting)
        } else if let Some(cast) = <&IntToPtr as InstDowncast>::downcast(is, inst_data) {
            match_index_expr_rec(func, *cast.from(), biv, visiting)
        } else if let Some(cast) = <&PtrToInt as InstDowncast>::downcast(is, inst_data) {
            match_index_expr_rec(func, *cast.from(), biv, visiting)
        } else if let Some(add) = <&Add as InstDowncast>::downcast(is, inst_data) {
            let (lhs_const, lhs_coeff) = match_index_expr_rec(func, *add.lhs(), biv, visiting)?;
            let (rhs_const, rhs_coeff) = match_index_expr_rec(func, *add.rhs(), biv, visiting)?;
            Some((
                lhs_const.checked_add(rhs_const)?,
                lhs_coeff.checked_add(rhs_coeff)?,
            ))
        } else if let Some(sub) = <&Sub as InstDowncast>::downcast(is, inst_data) {
            let (lhs_const, lhs_coeff) = match_index_expr_rec(func, *sub.lhs(), biv, visiting)?;
            let (rhs_const, rhs_coeff) = match_index_expr_rec(func, *sub.rhs(), biv, visiting)?;
            Some((
                lhs_const.checked_sub(rhs_const)?,
                lhs_coeff.checked_sub(rhs_coeff)?,
            ))
        } else {
            None
        }
    };

    visiting.remove(&value);
    matched
}

fn combine_add(lhs: MatchedAffineAddr, rhs: MatchedAffineAddr) -> Option<MatchedAffineAddr> {
    let base = match (lhs.base, rhs.base) {
        (Some(base), None) | (None, Some(base)) => Some(base),
        (None, None) => None,
        (Some(_), Some(_)) => return None,
    };
    Some(MatchedAffineAddr {
        base,
        const_bytes: lhs.const_bytes.checked_add(rhs.const_bytes)?,
        coeff_bytes: lhs.coeff_bytes.checked_add(rhs.coeff_bytes)?,
        profitable: lhs.profitable || rhs.profitable,
    })
}

fn combine_sub(lhs: MatchedAffineAddr, rhs: MatchedAffineAddr) -> Option<MatchedAffineAddr> {
    if rhs.base.is_some() {
        return None;
    }
    Some(MatchedAffineAddr {
        base: lhs.base,
        const_bytes: lhs.const_bytes.checked_sub(rhs.const_bytes)?,
        coeff_bytes: lhs.coeff_bytes.checked_sub(rhs.coeff_bytes)?,
        profitable: lhs.profitable || rhs.profitable,
    })
}

fn phi_init_and_backedge(
    phi: &Phi,
    preheader: BlockId,
    latch: BlockId,
) -> Option<(ValueId, ValueId)> {
    if phi.args().len() != 2 {
        return None;
    }

    let mut init = None;
    let mut backedge = None;
    for &(value, block) in phi.args() {
        if block == preheader {
            init = Some(value);
        } else if block == latch {
            backedge = Some(value);
        } else {
            return None;
        }
    }

    Some((init?, backedge?))
}

fn detect_basic_iv_step(
    func: &Function,
    latch: BlockId,
    phi: ValueId,
    backedge: ValueId,
) -> Option<(InstId, ValueId, StepKind)> {
    let step_inst = func.dfg.value_inst(backedge)?;
    if !func.layout.is_inst_inserted(step_inst) || func.layout.inst_block(step_inst) != latch {
        return None;
    }

    let inst = func.dfg.inst(step_inst);
    let is = func.inst_set();
    if let Some(add) = <&Add as InstDowncast>::downcast(is, inst) {
        if *add.lhs() == phi {
            let step = nonzero_step_imm(func, *add.rhs())?;
            return Some((step_inst, backedge, StepKind::AddConst(step)));
        }
        if *add.rhs() == phi {
            let step = nonzero_step_imm(func, *add.lhs())?;
            return Some((step_inst, backedge, StepKind::AddConst(step)));
        }
        return None;
    }

    let sub = <&Sub as InstDowncast>::downcast(is, inst)?;
    if *sub.lhs() != phi {
        return None;
    }
    let step = nonzero_step_imm(func, *sub.rhs())?;
    Some((step_inst, backedge, StepKind::SubConst(step)))
}

fn nonzero_step_imm(func: &Function, value: ValueId) -> Option<Immediate> {
    let imm = func.dfg.value_imm(value)?;
    (!imm.is_zero()).then_some(imm)
}

fn unique_outside_pred(
    cfg: &ControlFlowGraph,
    lpt: &LoopTree,
    loop_id: LoopId,
    header: BlockId,
) -> Option<BlockId> {
    let mut outside_preds = cfg
        .preds_of(header)
        .copied()
        .filter(|pred| !lpt.is_in_loop(*pred, loop_id));
    let preheader = outside_preds.next()?;
    outside_preds.next().is_none().then_some(preheader)
}

fn unique_latch(
    cfg: &ControlFlowGraph,
    lpt: &LoopTree,
    loop_id: LoopId,
    header: BlockId,
) -> Option<BlockId> {
    let mut latches = cfg
        .preds_of(header)
        .copied()
        .filter(|pred| lpt.is_in_loop(*pred, loop_id));
    let latch = latches.next()?;
    latches.next().is_none().then_some(latch)
}

pub(crate) fn detect_basic_iv_probes_for_loop(
    func: &Function,
    loop_id: LoopId,
    cfg: &ControlFlowGraph,
    lpt: &LoopTree,
) -> SmallVec<[BasicInductionVarProbe; 4]> {
    let header = lpt.loop_header(loop_id);
    let Some(latch) = unique_latch(cfg, lpt, loop_id, header) else {
        return smallvec![];
    };

    let mut probes = SmallVec::new();
    for inst in func.layout.iter_inst(header) {
        let Some(phi) = func.dfg.cast_phi(inst) else {
            break;
        };
        let Some(phi_value) = func.dfg.inst_result(inst) else {
            continue;
        };
        if !func.dfg.value_ty(phi_value).is_integral() {
            continue;
        }

        let Some(backedge) = phi_backedge_with_outside_preds(phi, latch, loop_id, lpt) else {
            continue;
        };
        let Some((_, _, step)) = detect_basic_iv_step(func, latch, phi_value, backedge) else {
            continue;
        };

        probes.push(BasicInductionVarProbe {
            iv: AffineIv {
                loop_id,
                phi: phi_value,
            },
            step,
        });
    }

    probes
}

fn phi_backedge_with_outside_preds(
    phi: &Phi,
    latch: BlockId,
    loop_id: LoopId,
    lpt: &LoopTree,
) -> Option<ValueId> {
    let mut backedge = None;
    let mut has_outside_pred = false;
    for &(value, block) in phi.args() {
        if block == latch {
            if backedge.replace(value).is_some() {
                return None;
            }
        } else if lpt.is_in_loop(block, loop_id) {
            return None;
        } else {
            has_outside_pred = true;
        }
    }

    if has_outside_pred { backedge } else { None }
}

fn is_loop_invariant_value(
    func: &Function,
    lpt: &LoopTree,
    biv: AffineIv,
    value: ValueId,
    visiting: &mut FxHashSet<ValueId>,
) -> bool {
    if !visiting.insert(value) {
        return false;
    }

    let invariant = match func.dfg.value(value) {
        Value::Immediate { .. } | Value::Arg { .. } | Value::Global { .. } => true,
        Value::Undef { .. } => false,
        Value::Inst { inst, .. } => {
            let block = func.layout.inst_block(*inst);
            if !lpt.is_in_loop(block, biv.loop_id) {
                true
            } else {
                let inst = func.dfg.inst(*inst);
                let is = func.inst_set();
                if <&Phi as InstDowncast>::downcast(is, inst).is_some() {
                    false
                } else if let Some(cast) = <&Bitcast as InstDowncast>::downcast(is, inst) {
                    is_loop_invariant_value(func, lpt, biv, *cast.from(), visiting)
                } else if let Some(cast) = <&IntToPtr as InstDowncast>::downcast(is, inst) {
                    is_loop_invariant_value(func, lpt, biv, *cast.from(), visiting)
                } else if let Some(cast) = <&PtrToInt as InstDowncast>::downcast(is, inst) {
                    is_loop_invariant_value(func, lpt, biv, *cast.from(), visiting)
                } else if let Some(add) = <&Add as InstDowncast>::downcast(is, inst) {
                    let lhs_const = value_i64(func, *add.lhs()).is_some();
                    let rhs_const = value_i64(func, *add.rhs()).is_some();
                    (lhs_const || rhs_const)
                        && is_loop_invariant_value(func, lpt, biv, *add.lhs(), visiting)
                        && is_loop_invariant_value(func, lpt, biv, *add.rhs(), visiting)
                } else if let Some(sub) = <&Sub as InstDowncast>::downcast(is, inst) {
                    let lhs_const = value_i64(func, *sub.lhs()).is_some();
                    let rhs_const = value_i64(func, *sub.rhs()).is_some();
                    (lhs_const || rhs_const)
                        && is_loop_invariant_value(func, lpt, biv, *sub.lhs(), visiting)
                        && is_loop_invariant_value(func, lpt, biv, *sub.rhs(), visiting)
                } else if let Some(gep) = <&Gep as InstDowncast>::downcast(is, inst) {
                    let Some((&base, indices)) = gep.values().split_first() else {
                        return false;
                    };
                    const_gep_offset(func, base, indices).is_some()
                        && is_loop_invariant_value(func, lpt, biv, base, visiting)
                } else {
                    false
                }
            }
        }
    };

    visiting.remove(&value);
    invariant
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
            CompoundType::Ptr(elem_ty) => {
                let elem_size = i64::try_from(func.ctx().size_of_unchecked(elem_ty)).ok()?;
                total = total.checked_add(elem_size.checked_mul(idx)?)?;
                current_ty = elem_ty;
            }
            CompoundType::Array { elem, .. } => {
                let elem_size = i64::try_from(func.ctx().size_of_unchecked(elem)).ok()?;
                total = total.checked_add(elem_size.checked_mul(idx)?)?;
                current_ty = elem;
            }
            CompoundType::Struct(s) => {
                let idx = usize::try_from(idx).ok()?;
                let (field_offset, field_ty) =
                    shape::struct_field_offset_bytes(&s.fields, s.packed, idx, func.ctx())?;
                total = total.checked_add(i64::from(field_offset))?;
                current_ty = field_ty;
            }
            CompoundType::Enum(_)
            | CompoundType::ObjRef(_)
            | CompoundType::ConstRef(_)
            | CompoundType::Func { .. } => {
                return None;
            }
        }
    }

    Some(total)
}

fn value_i64(func: &Function, value: ValueId) -> Option<i64> {
    imm_i64(func.dfg.value_imm(value)?)
}

fn imm_i64(imm: Immediate) -> Option<i64> {
    let value = imm.as_i256();
    if value < I256::from(i64::MIN) || value > I256::from(i64::MAX) {
        return None;
    }
    Some(value.trunc_to_i64())
}

#[cfg(test)]
mod tests {
    use smallvec::smallvec;
    use sonatina_ir::{
        ControlFlowGraph, Function, I256, Type,
        builder::test_util::*,
        inst::{
            arith::{Add, Sub},
            control_flow::{Br, Jump, Phi, Return},
            data::{Gep, Mload},
        },
        prelude::*,
    };

    use crate::domtree::DomTree;

    use super::{InductionAnalysis, detect_basic_ivs_for_loop, match_affine_addr};

    #[test]
    fn detects_incrementing_basic_iv() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::I256);
        let is = evm.inst_set();

        let preheader = builder.append_block();
        let header = builder.append_block();
        let latch = builder.append_block();
        let exit = builder.append_block();

        builder.switch_to_block(preheader);
        builder.insert_inst_no_result_with(|| Jump::new(is, header));

        builder.switch_to_block(header);
        let iv = builder.insert_inst_with(|| Phi::new(is, vec![]), Type::I256);
        let cond = builder.make_imm_value(true);
        builder.insert_inst_no_result_with(|| Br::new(is, cond, latch, exit));

        builder.switch_to_block(latch);
        let zero = builder.make_imm_value(I256::from(0u8));
        let one = builder.make_imm_value(I256::from(1u8));
        let next = builder.insert_inst_with(|| Add::new(is, iv, one), Type::I256);
        builder.insert_inst_no_result_with(|| Jump::new(is, header));
        builder.append_phi_arg(iv, zero, preheader);
        builder.append_phi_arg(iv, next, latch);

        builder.switch_to_block(exit);
        builder.insert_inst_no_result_with(|| Return::new_single(is, iv));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        module.func_store.view(func_ref, |func| {
            let mut cfg = ControlFlowGraph::default();
            cfg.compute(func);
            let mut domtree = DomTree::default();
            domtree.compute(&cfg);
            let mut lpt = crate::loop_analysis::LoopTree::default();
            lpt.compute(&cfg, &domtree);
            let loop_id = lpt.loops().next().expect("loop");
            let bivs = detect_basic_ivs_for_loop(func, loop_id, &cfg, &lpt);
            assert_eq!(bivs.len(), 1);
            assert_eq!(bivs[0].phi, iv);
            assert_eq!(bivs[0].init, zero);
        });
    }

    #[test]
    fn detects_decrementing_basic_iv() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::I256);
        let is = evm.inst_set();

        let preheader = builder.append_block();
        let header = builder.append_block();
        let latch = builder.append_block();
        let exit = builder.append_block();

        builder.switch_to_block(preheader);
        builder.insert_inst_no_result_with(|| Jump::new(is, header));

        builder.switch_to_block(header);
        let iv = builder.insert_inst_with(|| Phi::new(is, vec![]), Type::I256);
        let cond = builder.make_imm_value(true);
        builder.insert_inst_no_result_with(|| Br::new(is, cond, latch, exit));

        builder.switch_to_block(latch);
        let init = builder.make_imm_value(I256::from(7u8));
        let one = builder.make_imm_value(I256::from(1u8));
        let next = builder.insert_inst_with(|| Sub::new(is, iv, one), Type::I256);
        builder.insert_inst_no_result_with(|| Jump::new(is, header));
        builder.append_phi_arg(iv, init, preheader);
        builder.append_phi_arg(iv, next, latch);

        builder.switch_to_block(exit);
        builder.insert_inst_no_result_with(|| Return::new_single(is, iv));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        module.func_store.view(func_ref, |func| {
            let analysis = build_induction_analysis(func);
            let loop_id = analysis.2.loops().next().expect("loop");
            let bivs = analysis.3.basic_ivs_in_loop(loop_id);
            assert_eq!(bivs.len(), 1);
            assert!(matches!(bivs[0].step, super::StepKind::SubConst(_)));
        });
    }

    #[test]
    fn rejects_nonconstant_basic_iv_step() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I256], Type::I256);
        let is = evm.inst_set();

        let preheader = builder.append_block();
        let header = builder.append_block();
        let latch = builder.append_block();
        let exit = builder.append_block();
        let arg = builder.args()[0];

        builder.switch_to_block(preheader);
        builder.insert_inst_no_result_with(|| Jump::new(is, header));

        builder.switch_to_block(header);
        let iv = builder.insert_inst_with(|| Phi::new(is, vec![]), Type::I256);
        let cond = builder.make_imm_value(true);
        builder.insert_inst_no_result_with(|| Br::new(is, cond, latch, exit));

        builder.switch_to_block(latch);
        let zero = builder.make_imm_value(I256::from(0u8));
        let next = builder.insert_inst_with(|| Add::new(is, iv, arg), Type::I256);
        builder.insert_inst_no_result_with(|| Jump::new(is, header));
        builder.append_phi_arg(iv, zero, preheader);
        builder.append_phi_arg(iv, next, latch);

        builder.switch_to_block(exit);
        builder.insert_inst_no_result_with(|| Return::new_single(is, iv));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        module.func_store.view(func_ref, |func| {
            let analysis = build_induction_analysis(func);
            let loop_id = analysis.2.loops().next().expect("loop");
            assert!(analysis.3.basic_ivs_in_loop(loop_id).is_empty());
        });
    }

    #[test]
    fn rejects_two_backedge_phi() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::I256);
        let is = evm.inst_set();

        let preheader = builder.append_block();
        let header = builder.append_block();
        let latch0 = builder.append_block();
        let latch1 = builder.append_block();
        let exit = builder.append_block();

        builder.switch_to_block(preheader);
        builder.insert_inst_no_result_with(|| Jump::new(is, header));

        builder.switch_to_block(header);
        let iv = builder.insert_inst_with(|| Phi::new(is, vec![]), Type::I256);
        let cond = builder.make_imm_value(true);
        builder.insert_inst_no_result_with(|| Br::new(is, cond, latch0, exit));

        builder.switch_to_block(latch0);
        let zero = builder.make_imm_value(I256::from(0u8));
        let one = builder.make_imm_value(I256::from(1u8));
        let next0 = builder.insert_inst_with(|| Add::new(is, iv, one), Type::I256);
        builder.insert_inst_no_result_with(|| Br::new(is, cond, header, latch1));

        builder.switch_to_block(latch1);
        let next1 = builder.insert_inst_with(|| Add::new(is, iv, one), Type::I256);
        builder.insert_inst_no_result_with(|| Jump::new(is, header));
        builder.append_phi_arg(iv, zero, preheader);
        builder.append_phi_arg(iv, next0, latch0);
        builder.append_phi_arg(iv, next1, latch1);

        builder.switch_to_block(exit);
        builder.insert_inst_no_result_with(|| Return::new_single(is, iv));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        module.func_store.view(func_ref, |func| {
            let analysis = build_induction_analysis(func);
            let loop_id = analysis.2.loops().next().expect("loop");
            assert!(analysis.3.basic_ivs_in_loop(loop_id).is_empty());
        });
    }

    #[test]
    fn matches_forward_gep_affine_address() {
        let mb = test_module_builder();
        let arr_ty = mb.declare_array_type(Type::I256, 8);
        let ptr_ty = mb.ptr_type(arr_ty);
        let elem_ptr_ty = mb.ptr_type(Type::I256);
        let (evm, mut builder) = test_func_builder(&mb, &[ptr_ty], Type::I256);
        let is = evm.inst_set();

        let preheader = builder.append_block();
        let header = builder.append_block();
        let body = builder.append_block();
        let exit = builder.append_block();
        let base = builder.args()[0];

        builder.switch_to_block(preheader);
        builder.insert_inst_no_result_with(|| Jump::new(is, header));

        builder.switch_to_block(header);
        let iv = builder.insert_inst_with(|| Phi::new(is, vec![]), Type::I256);
        let cond = builder.make_imm_value(true);
        builder.insert_inst_no_result_with(|| Br::new(is, cond, body, exit));

        builder.switch_to_block(body);
        let zero = builder.make_imm_value(I256::from(0u8));
        let gep = builder.insert_inst_with(|| Gep::new(is, smallvec![base, zero, iv]), elem_ptr_ty);
        let _load = builder.insert_inst_with(|| Mload::new(is, gep, Type::I256), Type::I256);
        let one = builder.make_imm_value(I256::from(1u8));
        let next = builder.insert_inst_with(|| Add::new(is, iv, one), Type::I256);
        builder.insert_inst_no_result_with(|| Jump::new(is, header));
        let init = builder.make_imm_value(I256::from(0u8));
        builder.append_phi_arg(iv, init, preheader);
        builder.append_phi_arg(iv, next, body);

        builder.switch_to_block(exit);
        builder.insert_inst_no_result_with(|| Return::new_single(is, iv));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        module.func_store.view(func_ref, |func| {
            let (cfg, domtree, lpt, induction) = build_induction_analysis(func);
            let loop_id = lpt.loops().next().expect("loop");
            let biv = &induction.basic_ivs_in_loop(loop_id)[0];
            let matched = match_affine_addr(func, &lpt, gep, biv).expect("affine gep");
            assert_eq!(matched.base, base);
            assert_eq!(matched.const_bytes, 0);
            assert_eq!(matched.coeff_bytes, 32);
            let _ = (cfg, domtree);
        });
    }

    #[test]
    fn matches_offset_gep_affine_address() {
        let mb = test_module_builder();
        let arr_ty = mb.declare_array_type(Type::I256, 8);
        let ptr_ty = mb.ptr_type(arr_ty);
        let elem_ptr_ty = mb.ptr_type(Type::I256);
        let (evm, mut builder) = test_func_builder(&mb, &[ptr_ty], Type::I256);
        let is = evm.inst_set();

        let preheader = builder.append_block();
        let header = builder.append_block();
        let body = builder.append_block();
        let exit = builder.append_block();
        let base = builder.args()[0];

        builder.switch_to_block(preheader);
        builder.insert_inst_no_result_with(|| Jump::new(is, header));

        builder.switch_to_block(header);
        let iv = builder.insert_inst_with(|| Phi::new(is, vec![]), Type::I256);
        let cond = builder.make_imm_value(true);
        builder.insert_inst_no_result_with(|| Br::new(is, cond, body, exit));

        builder.switch_to_block(body);
        let zero = builder.make_imm_value(I256::from(0u8));
        let two = builder.make_imm_value(I256::from(2u8));
        let idx = builder.insert_inst_with(|| Add::new(is, iv, two), Type::I256);
        let gep =
            builder.insert_inst_with(|| Gep::new(is, smallvec![base, zero, idx]), elem_ptr_ty);
        let _load = builder.insert_inst_with(|| Mload::new(is, gep, Type::I256), Type::I256);
        let one = builder.make_imm_value(I256::from(1u8));
        let next = builder.insert_inst_with(|| Add::new(is, iv, one), Type::I256);
        builder.insert_inst_no_result_with(|| Jump::new(is, header));
        let init = builder.make_imm_value(I256::from(0u8));
        builder.append_phi_arg(iv, init, preheader);
        builder.append_phi_arg(iv, next, body);

        builder.switch_to_block(exit);
        builder.insert_inst_no_result_with(|| Return::new_single(is, iv));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        module.func_store.view(func_ref, |func| {
            let (_, _, lpt, induction) = build_induction_analysis(func);
            let loop_id = lpt.loops().next().expect("loop");
            let biv = &induction.basic_ivs_in_loop(loop_id)[0];
            let matched = match_affine_addr(func, &lpt, gep, biv).expect("affine gep");
            assert_eq!(matched.base, base);
            assert_eq!(matched.const_bytes, 64);
            assert_eq!(matched.coeff_bytes, 32);
        });
    }

    #[test]
    fn matches_reverse_gep_affine_address() {
        let mb = test_module_builder();
        let arr_ty = mb.declare_array_type(Type::I256, 8);
        let ptr_ty = mb.ptr_type(arr_ty);
        let elem_ptr_ty = mb.ptr_type(Type::I256);
        let (evm, mut builder) = test_func_builder(&mb, &[ptr_ty], Type::I256);
        let is = evm.inst_set();

        let preheader = builder.append_block();
        let header = builder.append_block();
        let body = builder.append_block();
        let exit = builder.append_block();
        let base = builder.args()[0];

        builder.switch_to_block(preheader);
        builder.insert_inst_no_result_with(|| Jump::new(is, header));

        builder.switch_to_block(header);
        let iv = builder.insert_inst_with(|| Phi::new(is, vec![]), Type::I256);
        let cond = builder.make_imm_value(true);
        builder.insert_inst_no_result_with(|| Br::new(is, cond, body, exit));

        builder.switch_to_block(body);
        let zero = builder.make_imm_value(I256::from(0u8));
        let seven = builder.make_imm_value(I256::from(7u8));
        let idx = builder.insert_inst_with(|| Sub::new(is, seven, iv), Type::I256);
        let gep =
            builder.insert_inst_with(|| Gep::new(is, smallvec![base, zero, idx]), elem_ptr_ty);
        let _load = builder.insert_inst_with(|| Mload::new(is, gep, Type::I256), Type::I256);
        let one = builder.make_imm_value(I256::from(1u8));
        let next = builder.insert_inst_with(|| Add::new(is, iv, one), Type::I256);
        builder.insert_inst_no_result_with(|| Jump::new(is, header));
        let init = builder.make_imm_value(I256::from(0u8));
        builder.append_phi_arg(iv, init, preheader);
        builder.append_phi_arg(iv, next, body);

        builder.switch_to_block(exit);
        builder.insert_inst_no_result_with(|| Return::new_single(is, iv));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        module.func_store.view(func_ref, |func| {
            let (_, _, lpt, induction) = build_induction_analysis(func);
            let loop_id = lpt.loops().next().expect("loop");
            let biv = &induction.basic_ivs_in_loop(loop_id)[0];
            let matched = match_affine_addr(func, &lpt, gep, biv).expect("affine gep");
            assert_eq!(matched.base, base);
            assert_eq!(matched.const_bytes, 224);
            assert_eq!(matched.coeff_bytes, -32);
        });
    }

    #[test]
    fn rejects_two_dynamic_terms_in_affine_address() {
        let mb = test_module_builder();
        let arr_ty = mb.declare_array_type(Type::I256, 8);
        let ptr_ty = mb.ptr_type(arr_ty);
        let elem_ptr_ty = mb.ptr_type(Type::I256);
        let (evm, mut builder) = test_func_builder(&mb, &[ptr_ty], Type::I256);
        let is = evm.inst_set();

        let preheader = builder.append_block();
        let header = builder.append_block();
        let body = builder.append_block();
        let exit = builder.append_block();
        let base = builder.args()[0];

        builder.switch_to_block(preheader);
        builder.insert_inst_no_result_with(|| Jump::new(is, header));

        builder.switch_to_block(header);
        let iv = builder.insert_inst_with(|| Phi::new(is, vec![]), Type::I256);
        let other = builder.insert_inst_with(|| Phi::new(is, vec![]), Type::I256);
        let cond = builder.make_imm_value(true);
        builder.insert_inst_no_result_with(|| Br::new(is, cond, body, exit));

        builder.switch_to_block(body);
        let zero = builder.make_imm_value(I256::from(0u8));
        let idx = builder.insert_inst_with(|| Add::new(is, iv, other), Type::I256);
        let gep =
            builder.insert_inst_with(|| Gep::new(is, smallvec![base, zero, idx]), elem_ptr_ty);
        let _load = builder.insert_inst_with(|| Mload::new(is, gep, Type::I256), Type::I256);
        let one = builder.make_imm_value(I256::from(1u8));
        let two = builder.make_imm_value(I256::from(2u8));
        let iv_next = builder.insert_inst_with(|| Add::new(is, iv, one), Type::I256);
        let other_next = builder.insert_inst_with(|| Add::new(is, other, two), Type::I256);
        builder.insert_inst_no_result_with(|| Jump::new(is, header));
        let init = builder.make_imm_value(I256::from(0u8));
        builder.append_phi_arg(iv, init, preheader);
        builder.append_phi_arg(iv, iv_next, body);
        builder.append_phi_arg(other, init, preheader);
        builder.append_phi_arg(other, other_next, body);

        builder.switch_to_block(exit);
        builder.insert_inst_no_result_with(|| Return::new_single(is, iv));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        module.func_store.view(func_ref, |func| {
            let (_, _, lpt, induction) = build_induction_analysis(func);
            let loop_id = lpt.loops().next().expect("loop");
            let biv = induction
                .basic_ivs_in_loop(loop_id)
                .iter()
                .find(|biv| biv.phi == iv)
                .expect("primary iv");
            assert!(match_affine_addr(func, &lpt, gep, biv).is_none());
        });
    }

    fn build_induction_analysis(
        func: &Function,
    ) -> (
        ControlFlowGraph,
        DomTree,
        crate::loop_analysis::LoopTree,
        InductionAnalysis,
    ) {
        let mut cfg = ControlFlowGraph::default();
        cfg.compute(func);
        let mut domtree = DomTree::default();
        domtree.compute(&cfg);
        let mut lpt = crate::loop_analysis::LoopTree::default();
        lpt.compute(&cfg, &domtree);
        let induction = InductionAnalysis::compute(func, &cfg, &lpt);
        (cfg, domtree, lpt, induction)
    }
}
