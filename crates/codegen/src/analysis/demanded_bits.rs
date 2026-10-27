use std::collections::VecDeque;

use cranelift_entity::SecondaryMap;
use sonatina_ir::{
    Function, U256, Value, ValueId,
    inst::{BinaryInstKind, CastInstKind, InstClassKind, UnaryInstKind},
};

use super::known_bits::{bswap_bits, low_mask, supports_known_bits, type_bits, type_mask};

pub struct DemandedBitsQuery<'a> {
    func: &'a Function,
    demanded: SecondaryMap<ValueId, U256>,
}

impl<'a> DemandedBitsQuery<'a> {
    pub fn new(func: &'a Function) -> Self {
        let mut query = Self {
            func,
            demanded: SecondaryMap::default(),
        };
        query.solve();
        query
    }

    pub fn for_value(&self, value: ValueId) -> U256 {
        let ty = self.func.dfg.value_ty(value);
        if !supports_known_bits(ty) {
            return U256::zero();
        }

        self.demanded[value] & type_mask(ty)
    }

    pub fn all_uses_within_mask(&self, value: ValueId, mask: U256) -> bool {
        self.for_value(value) & !mask == U256::zero()
    }

    fn solve(&mut self) {
        let mut queued = SecondaryMap::<ValueId, bool>::default();
        let mut worklist = VecDeque::new();

        for block in self.func.layout.iter_block() {
            for inst in self.func.layout.iter_inst(block) {
                self.seed_external_uses(inst, &mut worklist, &mut queued);
            }
        }

        while let Some(value) = worklist.pop_front() {
            queued[value] = false;
            self.propagate_from_value(value, &mut worklist, &mut queued);
        }
    }

    fn seed_external_uses(
        &mut self,
        inst: sonatina_ir::InstId,
        worklist: &mut VecDeque<ValueId>,
        queued: &mut SecondaryMap<ValueId, bool>,
    ) {
        let inst_data = self.func.dfg.inst(inst);
        let is_external_use = self.func.dfg.branch_info(inst).is_some()
            || inst_data.kind() == InstClassKind::Opaque
            || !self.func.dfg.can_drop_if_unused(inst);
        if !is_external_use {
            return;
        }

        for value in inst_data.collect_values() {
            self.add_demand(value, type_mask_or_zero(self.func, value), worklist, queued);
        }
    }

    fn propagate_from_value(
        &mut self,
        value: ValueId,
        worklist: &mut VecDeque<ValueId>,
        queued: &mut SecondaryMap<ValueId, bool>,
    ) {
        let Value::Inst {
            inst, result_idx, ..
        } = self.func.dfg.value(value)
        else {
            return;
        };
        if *result_idx != 0 {
            return;
        }

        let demand = self.for_value(value);
        if demand == U256::zero() {
            return;
        }

        if let Some(phi) = self.func.dfg.cast_phi(*inst) {
            for (incoming, _) in phi.args() {
                self.add_demand(*incoming, demand, worklist, queued);
            }
            return;
        }

        let inst_data = self.func.dfg.inst(*inst);
        let args = inst_data.collect_values();
        match inst_data.kind() {
            InstClassKind::Unary(kind) => {
                self.propagate_unary(kind, &args, demand, worklist, queued)
            }
            InstClassKind::Binary(kind) => {
                self.propagate_binary(kind, &args, demand, worklist, queued)
            }
            InstClassKind::Cast(kind) => self.propagate_cast(kind, &args, demand, worklist, queued),
            InstClassKind::Phi => unreachable!("phis handled above"),
            InstClassKind::Opaque => {
                for arg in args {
                    self.add_demand(arg, type_mask_or_zero(self.func, arg), worklist, queued);
                }
            }
        }
    }

    fn propagate_unary(
        &mut self,
        kind: UnaryInstKind,
        args: &[ValueId],
        demand: U256,
        worklist: &mut VecDeque<ValueId>,
        queued: &mut SecondaryMap<ValueId, bool>,
    ) {
        let [arg] = args else {
            return;
        };

        match kind {
            UnaryInstKind::Not => self.add_demand(*arg, demand, worklist, queued),
            UnaryInstKind::Bswap => {
                let demand = bswap_bits(self.func.dfg.value_ty(*arg), demand);
                self.add_demand(*arg, demand, worklist, queued);
            }
            UnaryInstKind::IsZero
            | UnaryInstKind::Neg
            | UnaryInstKind::Snego
            | UnaryInstKind::EvmClz => {
                self.add_demand(*arg, type_mask_or_zero(self.func, *arg), worklist, queued);
            }
        }
    }

    fn propagate_binary(
        &mut self,
        kind: BinaryInstKind,
        args: &[ValueId],
        demand: U256,
        worklist: &mut VecDeque<ValueId>,
        queued: &mut SecondaryMap<ValueId, bool>,
    ) {
        let [lhs, rhs] = args else {
            return;
        };

        match kind {
            BinaryInstKind::And | BinaryInstKind::Or | BinaryInstKind::Xor => {
                self.add_demand(*lhs, demand, worklist, queued);
                self.add_demand(*rhs, demand, worklist, queued);
            }
            BinaryInstKind::Shl => {
                self.add_demand(*lhs, type_mask_or_zero(self.func, *lhs), worklist, queued);
                if let Some(shift) = constant_shift(self.func, *lhs) {
                    let rhs_bits = type_bits(self.func.dfg.value_ty(*rhs));
                    if shift < U256::from(rhs_bits) {
                        self.add_demand(*rhs, demand >> shift.as_usize(), worklist, queued);
                    }
                } else {
                    self.add_demand(*rhs, type_mask_or_zero(self.func, *rhs), worklist, queued);
                }
            }
            BinaryInstKind::Shr => {
                self.add_demand(*lhs, type_mask_or_zero(self.func, *lhs), worklist, queued);
                if let Some(shift) = constant_shift(self.func, *lhs) {
                    let rhs_bits = type_bits(self.func.dfg.value_ty(*rhs));
                    if shift < U256::from(rhs_bits) {
                        self.add_demand(*rhs, demand << shift.as_usize(), worklist, queued);
                    }
                } else {
                    self.add_demand(*rhs, type_mask_or_zero(self.func, *rhs), worklist, queued);
                }
            }
            BinaryInstKind::Sar => {
                self.add_demand(*lhs, type_mask_or_zero(self.func, *lhs), worklist, queued);
                if let Some(shift) = constant_shift(self.func, *lhs) {
                    let rhs_ty = self.func.dfg.value_ty(*rhs);
                    let rhs_mask = type_mask_or_zero(self.func, *rhs);
                    let rhs_bits = type_bits(rhs_ty);
                    // Wider shifts only depend on the sign bit. Clamp before narrowing.
                    let shift = shift.min(U256::from(rhs_bits)).as_usize();
                    let shifted = (demand << shift) & rhs_mask;
                    self.add_demand(*rhs, shifted, worklist, queued);
                    let fill_mask = rhs_mask & !low_mask(rhs_bits - shift as u16);
                    if demand & fill_mask != U256::zero() {
                        self.add_demand(
                            *rhs,
                            U256::one() << usize::from(rhs_bits - 1),
                            worklist,
                            queued,
                        );
                    }
                } else {
                    self.add_demand(*rhs, type_mask_or_zero(self.func, *rhs), worklist, queued);
                }
            }
            BinaryInstKind::EvmSignExtend => {
                if let Some(byte) = constant_shift(self.func, *lhs) {
                    self.propagate_evm_signextend(*rhs, byte, demand, worklist, queued);
                } else {
                    self.add_demand(*lhs, type_mask_or_zero(self.func, *lhs), worklist, queued);
                    self.add_demand(*rhs, type_mask_or_zero(self.func, *rhs), worklist, queued);
                }
            }
            BinaryInstKind::Eq
            | BinaryInstKind::Ne
            | BinaryInstKind::Lt
            | BinaryInstKind::Gt
            | BinaryInstKind::Slt
            | BinaryInstKind::Sgt
            | BinaryInstKind::Le
            | BinaryInstKind::Ge
            | BinaryInstKind::Sle
            | BinaryInstKind::Sge => {
                self.add_demand(*lhs, type_mask_or_zero(self.func, *lhs), worklist, queued);
                self.add_demand(*rhs, type_mask_or_zero(self.func, *rhs), worklist, queued);
            }
            _ => {
                self.add_demand(*lhs, type_mask_or_zero(self.func, *lhs), worklist, queued);
                self.add_demand(*rhs, type_mask_or_zero(self.func, *rhs), worklist, queued);
            }
        }
    }

    fn propagate_evm_signextend(
        &mut self,
        value: ValueId,
        byte: U256,
        demand: U256,
        worklist: &mut VecDeque<ValueId>,
        queued: &mut SecondaryMap<ValueId, bool>,
    ) {
        let value_ty = self.func.dfg.value_ty(value);
        let value_bits = type_bits(value_ty);
        let value_mask = type_mask_or_zero(self.func, value);
        if byte >= U256::from(32u8) {
            self.add_demand(value, demand & value_mask, worklist, queued);
            return;
        }

        let sign_width = ((byte.as_usize() + 1) * 8) as u16;
        if sign_width >= value_bits {
            self.add_demand(value, demand & value_mask, worklist, queued);
            return;
        }

        let low_mask = low_mask(sign_width);
        let high_demand = demand & value_mask & !low_mask;
        let mut value_demand = demand & low_mask;
        if high_demand != U256::zero() {
            value_demand |= U256::one() << usize::from(sign_width - 1);
        }
        self.add_demand(value, value_demand, worklist, queued);
    }

    fn propagate_cast(
        &mut self,
        kind: CastInstKind,
        args: &[ValueId],
        demand: U256,
        worklist: &mut VecDeque<ValueId>,
        queued: &mut SecondaryMap<ValueId, bool>,
    ) {
        let [arg] = args else {
            return;
        };
        let src_ty = self.func.dfg.value_ty(*arg);
        let src_mask = type_mask_or_zero(self.func, *arg);
        match kind {
            CastInstKind::Zext | CastInstKind::Trunc => {
                self.add_demand(*arg, demand & src_mask, worklist, queued);
            }
            CastInstKind::Sext => {
                self.add_demand(*arg, demand & src_mask, worklist, queued);
                if demand & !src_mask != U256::zero() && supports_known_bits(src_ty) {
                    self.add_demand(
                        *arg,
                        U256::one() << usize::from(type_bits(src_ty) - 1),
                        worklist,
                        queued,
                    );
                }
            }
            CastInstKind::Bitcast | CastInstKind::IntToPtr | CastInstKind::PtrToInt => {
                self.add_demand(*arg, src_mask, worklist, queued);
            }
        }
    }

    fn add_demand(
        &mut self,
        value: ValueId,
        demand: U256,
        worklist: &mut VecDeque<ValueId>,
        queued: &mut SecondaryMap<ValueId, bool>,
    ) {
        let ty = self.func.dfg.value_ty(value);
        if !supports_known_bits(ty) {
            return;
        }

        let demand = demand & type_mask(ty);
        if demand == U256::zero() {
            return;
        }

        let old = self.demanded[value];
        let new = old | demand;
        if new == old {
            return;
        }

        self.demanded[value] = new;
        if queued[value] {
            return;
        }

        queued[value] = true;
        worklist.push_back(value);
    }
}

fn constant_shift(func: &Function, value: ValueId) -> Option<U256> {
    Some(func.dfg.value_imm(value)?.as_i256().to_u256())
}

fn type_mask_or_zero(func: &Function, value: ValueId) -> U256 {
    let ty = func.dfg.value_ty(value);
    if supports_known_bits(ty) {
        type_mask(ty)
    } else {
        U256::zero()
    }
}

#[cfg(test)]
mod tests {
    use sonatina_ir::{
        Function, I256, Type,
        builder::test_util::*,
        inst::{
            arith::{Sar, Shl, Shr},
            cast::{Trunc, Zext},
            control_flow::Return,
            evm::EvmSignExtend,
        },
        isa::Isa,
    };

    use super::*;

    #[test]
    fn trunc_of_shr_only_demands_low_result_bits() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I256], Type::I32);
        let is = evm.inst_set();
        let block = builder.append_block();
        builder.switch_to_block(block);
        let arg = builder.args()[0];
        let shift = builder.make_imm_value(sonatina_ir::Immediate::from_i256(
            I256::from(224u16),
            Type::I256,
        ));
        let shr = builder.insert_inst_with(|| Shr::new(is, shift, arg), Type::I256);
        let trunc = builder.insert_inst_with(|| Trunc::new(is, shr, Type::I32), Type::I32);
        builder.insert_inst_no_result_with(|| Return::new_single(is, trunc));
        builder.seal_all();
        builder.finish();

        let func = only_func(&mb);
        let query = DemandedBitsQuery::new(&func);
        assert_eq!(query.for_value(shr), low_mask(32));
        assert_eq!(query.for_value(arg), low_mask(256) & !low_mask(224));
    }

    #[test]
    fn oversized_logical_shifts_demand_no_input_bits() {
        for ty in [Type::I1, Type::I8, Type::I32, Type::I256] {
            for shift in oversized_shifts(ty) {
                for kind in [BinaryInstKind::Shl, BinaryInstKind::Shr] {
                    assert_eq!(
                        shift_input_demand(kind, ty, shift, false),
                        U256::zero(),
                        "{kind:?} {shift} {ty:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn oversized_sar_demands_only_the_sign_bit() {
        for ty in [Type::I1, Type::I8, Type::I32, Type::I256] {
            let sign_bit = U256::one() << usize::from(type_bits(ty) - 1);
            for shift in oversized_shifts(ty) {
                for low_bit_only in [false, true] {
                    assert_eq!(
                        shift_input_demand(BinaryInstKind::Sar, ty, shift, low_bit_only),
                        sign_bit,
                        "sar {shift} {ty:?}, low_bit_only={low_bit_only}"
                    );
                }
            }
        }
    }

    #[test]
    fn in_range_shift_demands_preserve_boundary_bits() {
        for ty in [Type::I1, Type::I8, Type::I32, Type::I256] {
            for kind in [
                BinaryInstKind::Shl,
                BinaryInstKind::Shr,
                BinaryInstKind::Sar,
            ] {
                assert_eq!(
                    shift_input_demand(kind, ty, U256::zero(), false),
                    type_mask(ty),
                    "{kind:?} 0 {ty:?}"
                );
                let shift = type_bits(ty) - 1;
                let expected = if kind == BinaryInstKind::Shl {
                    U256::one()
                } else {
                    U256::one() << usize::from(shift)
                };
                assert_eq!(
                    shift_input_demand(kind, ty, U256::from(shift), false),
                    expected,
                    "{kind:?} {shift} {ty:?}"
                );
            }
        }
    }

    fn oversized_shifts(ty: Type) -> impl Iterator<Item = U256> {
        [
            U256::from(type_bits(ty)),
            U256::from(type_bits(ty) + 1),
            U256::one() << 16,
            U256::one() << 32,
            U256::one() << 64,
            U256::one() << 128,
            U256::MAX,
        ]
        .into_iter()
        .filter(move |shift| *shift <= type_mask(ty))
    }

    fn shift_input_demand(kind: BinaryInstKind, ty: Type, shift: U256, low_bit_only: bool) -> U256 {
        let mb = test_module_builder();
        let result_ty = if low_bit_only { Type::I1 } else { ty };
        let (evm, mut builder) = test_func_builder(&mb, &[ty], result_ty);
        let is = evm.inst_set();
        let block = builder.append_block();
        builder.switch_to_block(block);
        let arg = builder.args()[0];
        let shift = builder.make_imm_value(sonatina_ir::Immediate::from_i256(shift.into(), ty));
        let result = match kind {
            BinaryInstKind::Shl => builder.insert_inst_with(|| Shl::new(is, shift, arg), ty),
            BinaryInstKind::Shr => builder.insert_inst_with(|| Shr::new(is, shift, arg), ty),
            BinaryInstKind::Sar => builder.insert_inst_with(|| Sar::new(is, shift, arg), ty),
            _ => unreachable!(),
        };
        let result = if result_ty != ty {
            builder.insert_inst_with(|| Trunc::new(is, result, result_ty), result_ty)
        } else {
            result
        };
        builder.insert_inst_no_result_with(|| Return::new_single(is, result));
        builder.seal_all();
        builder.finish();

        DemandedBitsQuery::new(&only_func(&mb)).for_value(arg)
    }

    #[test]
    fn trunc_of_zext_only_demands_source_width() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I8], Type::I8);
        let is = evm.inst_set();
        let block = builder.append_block();
        builder.switch_to_block(block);
        let arg = builder.args()[0];
        let zext = builder.insert_inst_with(|| Zext::new(is, arg, Type::I16), Type::I16);
        let trunc = builder.insert_inst_with(|| Trunc::new(is, zext, Type::I8), Type::I8);
        builder.insert_inst_no_result_with(|| Return::new_single(is, trunc));
        builder.seal_all();
        builder.finish();

        let func = only_func(&mb);
        let query = DemandedBitsQuery::new(&func);
        assert_eq!(query.for_value(zext), low_mask(8));
        assert_eq!(query.for_value(arg), low_mask(8));
    }

    #[test]
    fn trunc_of_evm_signextend_demands_sign_bit_for_fill_bits() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I256], Type::I16);
        let is = evm.inst_set();
        let block = builder.append_block();
        builder.switch_to_block(block);
        let arg = builder.args()[0];
        let byte = builder.make_imm_value(sonatina_ir::Immediate::zero(Type::I256));
        let extended = builder.insert_inst_with(|| EvmSignExtend::new(is, byte, arg), Type::I256);
        let trunc = builder.insert_inst_with(|| Trunc::new(is, extended, Type::I16), Type::I16);
        builder.insert_inst_no_result_with(|| Return::new_single(is, trunc));
        builder.seal_all();
        builder.finish();

        let func = only_func(&mb);
        let query = DemandedBitsQuery::new(&func);
        assert_eq!(query.for_value(extended), low_mask(16));
        assert_eq!(query.for_value(arg), low_mask(8));
    }

    fn only_func(mb: &sonatina_ir::builder::ModuleBuilder) -> Function {
        let func_ref = mb.func_store.funcs()[0];
        mb.func_store.view(func_ref, |func| func.clone())
    }
}
