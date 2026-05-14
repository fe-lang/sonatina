use rustc_hash::FxHashMap;
use sonatina_ir::{
    Function, I256, Immediate, InstId, Type, U256, ValueId,
    inst::{arith, cmp, evm},
};

use super::{
    add_i256, and_i256, imm_i256, imm_i256_from_immediate, imm_i256_u256, imm_i256_usize,
    insert_before_one, mul_i256, shl_i256, shr_i256, sub_i256, trunc_i256_to, umod_i256,
    zext_to_i256, zext_to_ty,
};

type SparseExceptions = Vec<(usize, Immediate)>;

pub(super) fn can_emit_dynamic_values_lookup(
    result_ty: Type,
    values: &[Immediate],
    allow_periodic: bool,
) -> bool {
    can_emit_packed_bool_lookup(values)
        || can_emit_packed_byte_lookup(values)
        || affine_sequence(values).is_some()
        || can_emit_power_of_two_lookup(result_ty, values)
        || can_emit_packed_subword_lookup(result_ty, values)
        || allow_periodic
            && periodic_len(values).is_some_and(|period| {
                can_emit_dynamic_values_lookup(result_ty, &values[..period], false)
            })
        || can_emit_sparse_lookup(result_ty, values)
}

fn can_emit_packed_bool_lookup(values: &[Immediate]) -> bool {
    values.len() <= 256 && values.iter().all(|imm| matches!(imm, Immediate::I1(_)))
}

fn can_emit_packed_byte_lookup(values: &[Immediate]) -> bool {
    values.len() <= 32 && values.iter().all(|imm| imm.ty() == Type::I8)
}

fn can_emit_power_of_two_lookup(result_ty: Type, values: &[Immediate]) -> bool {
    result_ty == Type::I256 && power_of_two_exponents(values).is_some()
}

fn can_emit_packed_subword_lookup(result_ty: Type, values: &[Immediate]) -> bool {
    let Some(width) = packed_subword_width(result_ty) else {
        return false;
    };
    !values.is_empty()
        && values.len() <= 256 / width
        && values
            .iter()
            .all(|&imm| unsigned_immediate_bits(imm, width).is_some())
}

fn can_emit_sparse_lookup(result_ty: Type, values: &[Immediate]) -> bool {
    if result_ty == Type::I1 {
        return false;
    }
    sparse_exceptions(values).is_some_and(|(_, default_count, exceptions)| {
        exceptions.len() <= 4 && (default_count != 1 || values.len() <= 4)
    })
}

pub(super) fn emit_dynamic_values_lookup(
    func: &mut Function,
    before: InstId,
    index: ValueId,
    result_ty: Type,
    values: &[Immediate],
    allow_periodic: bool,
) -> Option<ValueId> {
    emit_packed_bool_lookup(func, before, index, values)
        .or_else(|| emit_packed_byte_lookup(func, before, index, values))
        .or_else(|| emit_affine_lookup(func, before, index, result_ty, values))
        .or_else(|| emit_power_of_two_lookup(func, before, index, result_ty, values))
        .or_else(|| emit_packed_subword_lookup(func, before, index, result_ty, values))
        .or_else(|| {
            allow_periodic
                .then(|| emit_periodic_lookup(func, before, index, result_ty, values))
                .flatten()
        })
        .or_else(|| emit_sparse_lookup(func, before, index, result_ty, values))
}

fn emit_packed_bool_lookup(
    func: &mut Function,
    before: InstId,
    index: ValueId,
    values: &[Immediate],
) -> Option<ValueId> {
    if values.len() > 256 || !values.iter().all(|imm| matches!(imm, Immediate::I1(_))) {
        return None;
    }

    let mut bits = U256::zero();
    for (idx, imm) in values.iter().enumerate() {
        if matches!(imm, Immediate::I1(true)) {
            bits |= U256::one() << idx;
        }
    }

    let index = zext_to_i256(func, before, index);
    let bitset = imm_i256_u256(func, bits);
    let shifted = shr_i256(func, before, bitset, index);
    let one = imm_i256(func, 1);
    let masked = and_i256(func, before, shifted, one);
    let zero = imm_i256(func, 0);
    Some(insert_before_one(
        func,
        before,
        cmp::Ne::new_unchecked(func.inst_set(), masked, zero),
        Type::I1,
    ))
}

fn emit_packed_byte_lookup(
    func: &mut Function,
    before: InstId,
    index: ValueId,
    values: &[Immediate],
) -> Option<ValueId> {
    if values.len() > 32 || !values.iter().all(|imm| imm.ty() == Type::I8) {
        return None;
    }

    let mut packed = U256::zero();
    for &imm in values {
        packed = (packed << 8) | unsigned_immediate(imm)?;
    }

    let index = zext_to_i256(func, before, index);
    let pos = match 32u32.checked_sub(u32::try_from(values.len()).ok()?)? {
        0 => index,
        offset => {
            let offset = imm_i256(func, offset);
            add_i256(func, before, index, offset)
        }
    };
    let table = imm_i256_u256(func, packed);
    let byte = insert_before_one(
        func,
        before,
        evm::EvmByte::new_unchecked(func.inst_set(), pos, table),
        Type::I256,
    );
    Some(trunc_i256_to(func, before, byte, Type::I8))
}

fn emit_affine_lookup(
    func: &mut Function,
    before: InstId,
    index: ValueId,
    result_ty: Type,
    values: &[Immediate],
) -> Option<ValueId> {
    let (base, stride) = affine_sequence(values)?;
    let mut value = zext_to_i256(func, before, index);
    if !stride.is_one() {
        let stride = imm_i256_from_immediate(func, stride);
        value = mul_i256(func, before, value, stride);
    }
    if !base.is_zero() {
        let base = imm_i256_from_immediate(func, base);
        value = add_i256(func, before, base, value);
    }
    Some(trunc_i256_to(func, before, value, result_ty))
}

fn affine_sequence(values: &[Immediate]) -> Option<(Immediate, Immediate)> {
    if values.len() < 2 || values[0].ty() == Type::I1 {
        return None;
    }

    let base = values[0];
    let stride = values[1] - base;
    if stride.is_zero() {
        return None;
    }

    values
        .iter()
        .copied()
        .enumerate()
        .all(|(idx, value)| {
            let idx = Immediate::from_i256(I256::from_usize(idx), base.ty());
            value == base + stride * idx
        })
        .then_some((base, stride))
}

fn emit_power_of_two_lookup(
    func: &mut Function,
    before: InstId,
    index: ValueId,
    result_ty: Type,
    values: &[Immediate],
) -> Option<ValueId> {
    if result_ty != Type::I256 {
        return None;
    }

    let (base_exp, stride) = power_of_two_exponents(values)?;
    let mut shift = zext_to_i256(func, before, index);
    if stride != 1 {
        let stride = imm_i256(func, stride);
        shift = mul_i256(func, before, shift, stride);
    }
    if base_exp != 0 {
        let base_exp = imm_i256(func, base_exp);
        shift = add_i256(func, before, base_exp, shift);
    }
    let one = imm_i256(func, 1);
    Some(shl_i256(func, before, one, shift))
}

fn power_of_two_exponents(values: &[Immediate]) -> Option<(u32, u32)> {
    let mut exponents = values.iter().copied().map(power_of_two_exponent);
    let base = exponents.next()??;
    let next = exponents.next()??;
    let stride = next.checked_sub(base)?;
    if stride == 0 {
        return None;
    }
    exponents
        .enumerate()
        .all(|(idx, exp)| {
            let idx = u32::try_from(idx + 2).ok();
            idx.and_then(|idx| base.checked_add(stride.checked_mul(idx)?)) == exp
        })
        .then_some((base, stride))
}

fn power_of_two_exponent(value: Immediate) -> Option<u32> {
    let value = value.zext(Type::I256).as_i256().to_u256();
    if value.is_zero() || value & (value - U256::one()) != U256::zero() {
        return None;
    }
    (0..256u32).find(|&bit| value == U256::one() << bit as usize)
}

fn emit_packed_subword_lookup(
    func: &mut Function,
    before: InstId,
    index: ValueId,
    result_ty: Type,
    values: &[Immediate],
) -> Option<ValueId> {
    let width = packed_subword_width(result_ty)?;
    if values.is_empty() || values.len() > 256 / width {
        return None;
    }

    let mut packed = U256::zero();
    for &imm in values {
        packed = (packed << width) | unsigned_immediate_bits(imm, width)?;
    }

    let mut shift = zext_to_i256(func, before, index);
    if width != 1 {
        let width = imm_i256(func, u32::try_from(width).ok()?);
        shift = mul_i256(func, before, shift, width);
    }
    let base_shift = imm_i256(func, u32::try_from((values.len() - 1) * width).ok()?);
    let shift = sub_i256(func, before, base_shift, shift);
    let table = imm_i256_u256(func, packed);
    let shifted = shr_i256(func, before, table, shift);
    Some(trunc_i256_to(func, before, shifted, result_ty))
}

fn packed_subword_width(ty: Type) -> Option<usize> {
    match ty {
        Type::I16 => Some(16),
        Type::I32 => Some(32),
        Type::I64 => Some(64),
        _ => None,
    }
}

fn emit_periodic_lookup(
    func: &mut Function,
    before: InstId,
    index: ValueId,
    result_ty: Type,
    values: &[Immediate],
) -> Option<ValueId> {
    let period = periodic_len(values)?;
    let index = zext_to_i256(func, before, index);
    let index = if period.is_power_of_two() {
        let mask = imm_i256_usize(func, period - 1)?;
        and_i256(func, before, index, mask)
    } else {
        let modulus = imm_i256_usize(func, period)?;
        umod_i256(func, before, index, modulus)
    };
    emit_dynamic_values_lookup(func, before, index, result_ty, &values[..period], false)
}

fn periodic_len(values: &[Immediate]) -> Option<usize> {
    (2..values.len())
        .filter(|period| values.len().is_multiple_of(*period))
        .find(|&period| {
            values
                .iter()
                .enumerate()
                .all(|(idx, value)| *value == values[idx % period])
        })
}

fn emit_sparse_lookup(
    func: &mut Function,
    before: InstId,
    index: ValueId,
    result_ty: Type,
    values: &[Immediate],
) -> Option<ValueId> {
    if result_ty == Type::I1 {
        return None;
    }

    let (default, default_count, exceptions) = sparse_exceptions(values)?;
    if exceptions.len() > 4 || default_count == 1 && values.len() > 4 {
        return None;
    }

    let index = zext_to_i256(func, before, index);
    let mut value = (!default.is_zero()).then(|| func.dfg.make_imm_value(default));
    for (exception_idx, exception) in exceptions {
        let exception_idx = imm_i256_usize(func, exception_idx)?;
        let is_exception = insert_before_one(
            func,
            before,
            cmp::Eq::new_unchecked(func.inst_set(), index, exception_idx),
            Type::I1,
        );
        let selector = zext_to_ty(func, before, is_exception, result_ty);
        let delta = func.dfg.make_imm_value(exception - default);
        let selected_delta = insert_before_one(
            func,
            before,
            arith::Mul::new_unchecked(func.inst_set(), selector, delta),
            result_ty,
        );
        value = Some(if let Some(value) = value {
            insert_before_one(
                func,
                before,
                arith::Add::new_unchecked(func.inst_set(), value, selected_delta),
                result_ty,
            )
        } else {
            selected_delta
        });
    }
    Some(value.unwrap_or_else(|| func.dfg.make_imm_value(default)))
}

fn sparse_exceptions(values: &[Immediate]) -> Option<(Immediate, usize, SparseExceptions)> {
    let mut counts = FxHashMap::default();
    let mut order = Vec::new();
    for &value in values {
        if !counts.contains_key(&value) {
            order.push(value);
        }
        *counts.entry(value).or_insert(0usize) += 1;
    }

    let mut candidates = order.into_iter();
    let mut default = candidates.next()?;
    let mut default_count = counts[&default];
    for candidate in candidates {
        let count = counts[&candidate];
        if count > default_count {
            default = candidate;
            default_count = count;
        }
    }

    let exceptions = values
        .iter()
        .copied()
        .enumerate()
        .filter(|(_, value)| *value != default)
        .collect();
    Some((default, default_count, exceptions))
}

fn unsigned_immediate(imm: Immediate) -> Option<U256> {
    unsigned_immediate_bits(imm, 8)
}

fn unsigned_immediate_bits(imm: Immediate, bits: usize) -> Option<U256> {
    let value = imm.zext(Type::I256).as_i256().to_u256();
    let max = (U256::one() << bits) - U256::one();
    (value <= max).then_some(value)
}
