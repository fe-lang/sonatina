use std::{cmp::Ordering, collections::HashMap};

use cranelift_codegen::ir::{
    self as clif, InstBuilder, MemFlagsData, StackSlotData, StackSlotKind, condcodes::IntCC,
};
use cranelift_frontend::FunctionBuilder;
use sonatina_ir::{Function, Immediate, Type, Value, ValueId, module::ModuleCtx};

use super::{
    DivRemKind,
    memory::{stack_slot_data, storage_chunks},
    scalar_constant, sonatina_scalar_type_to_clif_or_err,
};

const I256_LIMBS: usize = 4;
const I256_PRODUCT_LIMBS: usize = I256_LIMBS * 2;
const I256_BITS: i64 = 256;
const I256_LIMB_BITS: i64 = 64;
const I256_ALIGN_SHIFT: u8 = 4;

pub(super) fn create_i256_slot(builder: &mut FunctionBuilder) -> clif::Value {
    let slot = builder.create_sized_stack_slot(StackSlotData::new(
        StackSlotKind::ExplicitSlot,
        32,
        I256_ALIGN_SHIFT,
    ));
    builder.ins().stack_addr(clif::types::I64, slot, 0)
}

pub(super) fn create_stack_slot_for_type(
    ty: Type,
    ctx: &ModuleCtx,
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    let slot = builder.create_sized_stack_slot(stack_slot_data(ty, ctx)?);
    Ok(builder.ins().stack_addr(clif::types::I64, slot, 0))
}

pub(super) fn load_i256_limb(
    addr: clif::Value,
    limb: usize,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    builder.ins().load(
        clif::types::I64,
        MemFlagsData::new(),
        addr,
        (limb * 8) as i32,
    )
}

pub(super) fn store_i256_limb(
    addr: clif::Value,
    limb: usize,
    value: clif::Value,
    builder: &mut FunctionBuilder,
) {
    builder
        .ins()
        .store(MemFlagsData::new(), value, addr, (limb * 8) as i32);
}

pub(super) fn copy_bytes(
    src: clif::Value,
    dst: clif::Value,
    size: u32,
    builder: &mut FunctionBuilder,
) {
    for (offset, ty) in storage_chunks(size) {
        let value = builder.ins().load(ty, MemFlagsData::new(), src, offset);
        builder.ins().store(MemFlagsData::new(), value, dst, offset);
    }
}

pub(super) fn materialize_scalar_as_i256(
    value: clif::Value,
    source_ty: Type,
    signed: bool,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    // Extend to two scalar words before materializing the four-word value.
    // Reducing directly to I64 would discard the upper half of an I128 input.
    let wide = if source_ty == Type::I1 {
        bool_to_int_value(value, clif::types::I128, signed, builder)
    } else {
        resize_int_value(value, clif::types::I128, signed, builder)
    };
    let (low, high) = builder.ins().isplit(wide);
    let fill = if signed {
        builder.ins().sshr_imm_s(high, 63)
    } else {
        builder.ins().iconst(clif::types::I64, 0)
    };
    store_i256_limbs([low, high, fill, fill], builder)
}

pub(super) fn load_i256_limbs(
    value: clif::Value,
    builder: &mut FunctionBuilder,
) -> [clif::Value; I256_LIMBS] {
    [
        load_i256_limb(value, 0, builder),
        load_i256_limb(value, 1, builder),
        load_i256_limb(value, 2, builder),
        load_i256_limb(value, 3, builder),
    ]
}

pub(super) fn store_i256_limbs(
    limbs: [clif::Value; I256_LIMBS],
    builder: &mut FunctionBuilder,
) -> clif::Value {
    let result = create_i256_slot(builder);
    for (limb_idx, limb) in limbs.into_iter().enumerate() {
        store_i256_limb(result, limb_idx, limb, builder);
    }
    result
}

pub(super) fn zero_i256_limbs(builder: &mut FunctionBuilder) -> [clif::Value; I256_LIMBS] {
    let zero = builder.ins().iconst(clif::types::I64, 0);
    [zero; I256_LIMBS]
}

pub(super) fn unsigned_max_i256_limbs(builder: &mut FunctionBuilder) -> [clif::Value; I256_LIMBS] {
    let all_ones = builder.ins().iconst(clif::types::I64, -1);
    [all_ones; I256_LIMBS]
}

pub(super) fn signed_min_i256_limbs(builder: &mut FunctionBuilder) -> [clif::Value; I256_LIMBS] {
    let zero = builder.ins().iconst(clif::types::I64, 0);
    let high = builder.ins().iconst(clif::types::I64, i64::MIN);
    [zero, zero, zero, high]
}

pub(super) fn signed_max_i256_limbs(builder: &mut FunctionBuilder) -> [clif::Value; I256_LIMBS] {
    let all_ones = builder.ins().iconst(clif::types::I64, -1);
    let high = builder.ins().iconst(clif::types::I64, i64::MAX);
    [all_ones, all_ones, all_ones, high]
}

pub(super) fn select_i256_limbs(
    condition: clif::Value,
    if_true: [clif::Value; I256_LIMBS],
    if_false: [clif::Value; I256_LIMBS],
    builder: &mut FunctionBuilder,
) -> [clif::Value; I256_LIMBS] {
    std::array::from_fn(|limb| {
        builder
            .ins()
            .select(condition, if_true[limb], if_false[limb])
    })
}

pub(super) fn bool_xor(
    lhs: clif::Value,
    rhs: clif::Value,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    let not_rhs = bool_not(rhs, builder);
    builder.ins().select(lhs, not_rhs, rhs)
}

pub(super) fn bool_eq(
    lhs: clif::Value,
    rhs: clif::Value,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    let different = bool_xor(lhs, rhs, builder);
    bool_not(different, builder)
}

pub(super) fn i256_sign_bit(
    limbs: [clif::Value; I256_LIMBS],
    builder: &mut FunctionBuilder,
) -> clif::Value {
    let zero = builder.ins().iconst(clif::types::I64, 0);
    builder
        .ins()
        .icmp(IntCC::SignedLessThan, limbs[I256_LIMBS - 1], zero)
}

pub(super) fn add_i256_limbs(
    lhs: [clif::Value; I256_LIMBS],
    rhs: [clif::Value; I256_LIMBS],
    builder: &mut FunctionBuilder,
) -> ([clif::Value; I256_LIMBS], clif::Value) {
    let zero = builder.ins().iconst(clif::types::I64, 0);
    let one = builder.ins().iconst(clif::types::I64, 1);
    let mut carry = zero;
    let mut result = [zero; I256_LIMBS];

    for limb in 0..I256_LIMBS {
        let (sum, carry_from_sum) = builder.ins().uadd_overflow(lhs[limb], rhs[limb]);
        let (sum, carry_from_carry) = builder.ins().uadd_overflow(sum, carry);
        result[limb] = sum;
        let carry_from_sum = builder.ins().select(carry_from_sum, one, zero);
        let carry_from_carry = builder.ins().select(carry_from_carry, one, zero);
        carry = builder.ins().bor(carry_from_sum, carry_from_carry);
    }

    let overflow = builder.ins().icmp(IntCC::NotEqual, carry, zero);
    (result, overflow)
}

pub(super) fn sub_i256_limbs(
    lhs: [clif::Value; I256_LIMBS],
    rhs: [clif::Value; I256_LIMBS],
    builder: &mut FunctionBuilder,
) -> ([clif::Value; I256_LIMBS], clif::Value) {
    let zero = builder.ins().iconst(clif::types::I64, 0);
    let one = builder.ins().iconst(clif::types::I64, 1);
    let mut borrow = zero;
    let mut result = [zero; I256_LIMBS];

    for limb in 0..I256_LIMBS {
        let (diff, borrow_from_diff) = builder.ins().usub_overflow(lhs[limb], rhs[limb]);
        let (diff, borrow_from_borrow) = builder.ins().usub_overflow(diff, borrow);
        result[limb] = diff;
        let borrow_from_diff = builder.ins().select(borrow_from_diff, one, zero);
        let borrow_from_borrow = builder.ins().select(borrow_from_borrow, one, zero);
        borrow = builder.ins().bor(borrow_from_diff, borrow_from_borrow);
    }

    let overflow = builder.ins().icmp(IntCC::NotEqual, borrow, zero);
    (result, overflow)
}

pub(super) fn neg_i256_limbs(
    value: [clif::Value; I256_LIMBS],
    builder: &mut FunctionBuilder,
) -> [clif::Value; I256_LIMBS] {
    sub_i256_limbs(zero_i256_limbs(builder), value, builder).0
}

pub(super) fn abs_i256_limbs(
    value: [clif::Value; I256_LIMBS],
    builder: &mut FunctionBuilder,
) -> [clif::Value; I256_LIMBS] {
    let negative = i256_sign_bit(value, builder);
    let negated = neg_i256_limbs(value, builder);
    select_i256_limbs(negative, negated, value, builder)
}

pub(super) fn add_to_wide_limbs(
    limbs: &mut [clif::Value],
    start: usize,
    value: clif::Value,
    builder: &mut FunctionBuilder,
) {
    let zero = builder.ins().iconst(clif::types::I64, 0);
    let one = builder.ins().iconst(clif::types::I64, 1);
    let (sum, carry) = builder.ins().uadd_overflow(limbs[start], value);
    limbs[start] = sum;
    let mut carry = builder.ins().select(carry, one, zero);

    for limb in &mut limbs[start + 1..] {
        let (sum, next_carry) = builder.ins().uadd_overflow(*limb, carry);
        *limb = sum;
        carry = builder.ins().select(next_carry, one, zero);
    }
}

pub(super) fn mul_i256_limbs_full(
    lhs: [clif::Value; I256_LIMBS],
    rhs: [clif::Value; I256_LIMBS],
    builder: &mut FunctionBuilder,
) -> [clif::Value; I256_PRODUCT_LIMBS] {
    mul_limbs_full(&lhs, &rhs, builder)
}

pub(super) fn mul_limbs_full<const N: usize>(
    lhs: &[clif::Value],
    rhs: &[clif::Value],
    builder: &mut FunctionBuilder,
) -> [clif::Value; N] {
    assert_eq!(N, lhs.len() + rhs.len());
    let zero = builder.ins().iconst(clif::types::I64, 0);
    let mut result = [zero; N];

    for (lhs_idx, &lhs_limb) in lhs.iter().enumerate() {
        for (rhs_idx, &rhs_limb) in rhs.iter().enumerate() {
            let result_idx = lhs_idx + rhs_idx;
            let product_low = builder.ins().imul(lhs_limb, rhs_limb);
            let product_high = builder.ins().umulhi(lhs_limb, rhs_limb);
            add_to_wide_limbs(&mut result, result_idx, product_low, builder);
            add_to_wide_limbs(&mut result, result_idx + 1, product_high, builder);
        }
    }

    result
}

pub(super) fn low_i256_limbs(
    limbs: [clif::Value; I256_PRODUCT_LIMBS],
) -> [clif::Value; I256_LIMBS] {
    [limbs[0], limbs[1], limbs[2], limbs[3]]
}

pub(super) fn wide_i256_high_nonzero(
    limbs: [clif::Value; I256_PRODUCT_LIMBS],
    builder: &mut FunctionBuilder,
) -> clif::Value {
    let zero = builder.ins().iconst(clif::types::I64, 0);
    let mut result = bool_const(false, builder);
    for limb in limbs.into_iter().skip(I256_LIMBS) {
        let nonzero = builder.ins().icmp(IntCC::NotEqual, limb, zero);
        result = bool_or(result, nonzero, builder);
    }
    result
}

pub(super) fn emit_i256_add(
    function: &Function,
    lhs: ValueId,
    rhs: ValueId,
    value_map: &HashMap<ValueId, clif::Value>,
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    let lhs = resolve_value(function, lhs, value_map, builder)?;
    let rhs = resolve_value(function, rhs, value_map, builder)?;
    let result = add_i256_limbs(
        load_i256_limbs(lhs, builder),
        load_i256_limbs(rhs, builder),
        builder,
    )
    .0;
    Ok(store_i256_limbs(result, builder))
}

pub(super) fn emit_i256_sub(
    function: &Function,
    lhs: ValueId,
    rhs: ValueId,
    value_map: &HashMap<ValueId, clif::Value>,
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    let lhs = resolve_value(function, lhs, value_map, builder)?;
    let rhs = resolve_value(function, rhs, value_map, builder)?;
    let result = sub_i256_limbs(
        load_i256_limbs(lhs, builder),
        load_i256_limbs(rhs, builder),
        builder,
    )
    .0;
    Ok(store_i256_limbs(result, builder))
}

pub(super) fn emit_i256_mul(
    function: &Function,
    lhs: ValueId,
    rhs: ValueId,
    value_map: &HashMap<ValueId, clif::Value>,
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    let lhs = resolve_value(function, lhs, value_map, builder)?;
    let rhs = resolve_value(function, rhs, value_map, builder)?;
    let result = low_i256_limbs(mul_i256_limbs_full(
        load_i256_limbs(lhs, builder),
        load_i256_limbs(rhs, builder),
        builder,
    ));
    Ok(store_i256_limbs(result, builder))
}

pub(super) fn emit_i256_neg(
    function: &Function,
    value: ValueId,
    value_map: &HashMap<ValueId, clif::Value>,
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    let value = resolve_value(function, value, value_map, builder)?;
    Ok(store_i256_limbs(
        neg_i256_limbs(load_i256_limbs(value, builder), builder),
        builder,
    ))
}

pub(super) fn i256_limb_bit(
    limbs: [clif::Value; I256_LIMBS],
    bit: usize,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    let limb = limbs[bit / I256_LIMB_BITS as usize];
    let shifted = builder
        .ins()
        .ushr_imm_s(limb, (bit % I256_LIMB_BITS as usize) as i64);
    let one = builder.ins().iconst(clif::types::I64, 1);
    let bit = builder.ins().band(shifted, one);
    let zero = builder.ins().iconst(clif::types::I64, 0);
    builder.ins().icmp(IntCC::NotEqual, bit, zero)
}

pub(super) fn i256_shl_one_with_bit(
    limbs: [clif::Value; I256_LIMBS],
    bit: clif::Value,
    builder: &mut FunctionBuilder,
) -> [clif::Value; I256_LIMBS] {
    let zero = builder.ins().iconst(clif::types::I64, 0);
    let one = builder.ins().iconst(clif::types::I64, 1);
    let mut carry = builder.ins().select(bit, one, zero);
    std::array::from_fn(|limb_idx| {
        let shifted = builder.ins().ishl_imm_s(limbs[limb_idx], 1);
        let result = builder.ins().bor(shifted, carry);
        carry = builder
            .ins()
            .ushr_imm_s(limbs[limb_idx], I256_LIMB_BITS - 1);
        result
    })
}

pub(super) fn i256_set_bit_if(
    mut limbs: [clif::Value; I256_LIMBS],
    bit: usize,
    condition: clif::Value,
    builder: &mut FunctionBuilder,
) -> [clif::Value; I256_LIMBS] {
    let limb_idx = bit / I256_LIMB_BITS as usize;
    let mask = 1u64 << (bit % I256_LIMB_BITS as usize);
    let mask = builder.ins().iconst(clif::types::I64, mask as i64);
    let with_bit = builder.ins().bor(limbs[limb_idx], mask);
    limbs[limb_idx] = builder.ins().select(condition, with_bit, limbs[limb_idx]);
    limbs
}

pub(super) fn unsigned_div_rem_i256_limbs(
    numerator: [clif::Value; I256_LIMBS],
    denominator: [clif::Value; I256_LIMBS],
    bits: usize,
    builder: &mut FunctionBuilder,
) -> ([clif::Value; I256_LIMBS], [clif::Value; I256_LIMBS]) {
    let mut quotient = zero_i256_limbs(builder);
    let mut remainder = zero_i256_limbs(builder);

    for bit in (0..bits).rev() {
        let next_bit = i256_limb_bit(numerator, bit, builder);
        remainder = i256_shl_one_with_bit(remainder, next_bit, builder);
        let remainder_lt_denominator = emit_i256_unsigned_lt_limbs(remainder, denominator, builder);
        let should_subtract = bool_not(remainder_lt_denominator, builder);
        let subtracted = sub_i256_limbs(remainder, denominator, builder).0;
        remainder = select_i256_limbs(should_subtract, subtracted, remainder, builder);
        quotient = i256_set_bit_if(quotient, bit, should_subtract, builder);
    }

    (quotient, remainder)
}

pub(super) fn emit_i256_div_rem(
    function: &Function,
    lhs: ValueId,
    rhs: ValueId,
    kind: DivRemKind,
    value_map: &HashMap<ValueId, clif::Value>,
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    let lhs = load_i256_limbs(resolve_value(function, lhs, value_map, builder)?, builder);
    let rhs = load_i256_limbs(resolve_value(function, rhs, value_map, builder)?, builder);
    let result = match kind {
        DivRemKind::Udiv | DivRemKind::Umod => {
            let (quotient, remainder) =
                unsigned_div_rem_i256_limbs(lhs, rhs, I256_BITS as usize, builder);
            match kind {
                DivRemKind::Udiv => quotient,
                DivRemKind::Umod => remainder,
                DivRemKind::Sdiv | DivRemKind::Smod => unreachable!(),
            }
        }
        DivRemKind::Sdiv | DivRemKind::Smod => {
            let lhs_negative = i256_sign_bit(lhs, builder);
            let rhs_negative = i256_sign_bit(rhs, builder);
            let lhs_abs = abs_i256_limbs(lhs, builder);
            let rhs_abs = abs_i256_limbs(rhs, builder);
            let (quotient, remainder) =
                unsigned_div_rem_i256_limbs(lhs_abs, rhs_abs, I256_BITS as usize, builder);
            let quotient_negative = bool_xor(lhs_negative, rhs_negative, builder);
            let quotient = select_i256_limbs(
                quotient_negative,
                neg_i256_limbs(quotient, builder),
                quotient,
                builder,
            );
            let remainder = select_i256_limbs(
                lhs_negative,
                neg_i256_limbs(remainder, builder),
                remainder,
                builder,
            );
            match kind {
                DivRemKind::Sdiv => quotient,
                DivRemKind::Smod => remainder,
                DivRemKind::Udiv | DivRemKind::Umod => unreachable!(),
            }
        }
    };
    Ok(store_i256_limbs(result, builder))
}

pub(super) fn emit_i256_uaddo(
    function: &Function,
    lhs: ValueId,
    rhs: ValueId,
    value_map: &HashMap<ValueId, clif::Value>,
    builder: &mut FunctionBuilder,
) -> Result<(clif::Value, clif::Value), String> {
    let lhs = load_i256_limbs(resolve_value(function, lhs, value_map, builder)?, builder);
    let rhs = load_i256_limbs(resolve_value(function, rhs, value_map, builder)?, builder);
    let (result, overflow) = add_i256_limbs(lhs, rhs, builder);
    Ok((store_i256_limbs(result, builder), overflow))
}

pub(super) fn emit_i256_saddo(
    function: &Function,
    lhs: ValueId,
    rhs: ValueId,
    value_map: &HashMap<ValueId, clif::Value>,
    builder: &mut FunctionBuilder,
) -> Result<(clif::Value, clif::Value), String> {
    let lhs = load_i256_limbs(resolve_value(function, lhs, value_map, builder)?, builder);
    let rhs = load_i256_limbs(resolve_value(function, rhs, value_map, builder)?, builder);
    let (result, _) = add_i256_limbs(lhs, rhs, builder);
    let lhs_negative = i256_sign_bit(lhs, builder);
    let rhs_negative = i256_sign_bit(rhs, builder);
    let result_negative = i256_sign_bit(result, builder);
    let same_sign = bool_eq(lhs_negative, rhs_negative, builder);
    let sign_changed = bool_xor(result_negative, lhs_negative, builder);
    let overflow = bool_and(same_sign, sign_changed, builder);
    Ok((store_i256_limbs(result, builder), overflow))
}

pub(super) fn emit_i256_usubo(
    function: &Function,
    lhs: ValueId,
    rhs: ValueId,
    value_map: &HashMap<ValueId, clif::Value>,
    builder: &mut FunctionBuilder,
) -> Result<(clif::Value, clif::Value), String> {
    let lhs = load_i256_limbs(resolve_value(function, lhs, value_map, builder)?, builder);
    let rhs = load_i256_limbs(resolve_value(function, rhs, value_map, builder)?, builder);
    let (result, overflow) = sub_i256_limbs(lhs, rhs, builder);
    Ok((store_i256_limbs(result, builder), overflow))
}

pub(super) fn emit_i256_ssubo(
    function: &Function,
    lhs: ValueId,
    rhs: ValueId,
    value_map: &HashMap<ValueId, clif::Value>,
    builder: &mut FunctionBuilder,
) -> Result<(clif::Value, clif::Value), String> {
    let lhs = load_i256_limbs(resolve_value(function, lhs, value_map, builder)?, builder);
    let rhs = load_i256_limbs(resolve_value(function, rhs, value_map, builder)?, builder);
    let (result, _) = sub_i256_limbs(lhs, rhs, builder);
    let lhs_negative = i256_sign_bit(lhs, builder);
    let rhs_negative = i256_sign_bit(rhs, builder);
    let result_negative = i256_sign_bit(result, builder);
    let different_sign = bool_xor(lhs_negative, rhs_negative, builder);
    let sign_changed = bool_xor(result_negative, lhs_negative, builder);
    let overflow = bool_and(different_sign, sign_changed, builder);
    Ok((store_i256_limbs(result, builder), overflow))
}

pub(super) fn emit_i256_umulo(
    function: &Function,
    lhs: ValueId,
    rhs: ValueId,
    value_map: &HashMap<ValueId, clif::Value>,
    builder: &mut FunctionBuilder,
) -> Result<(clif::Value, clif::Value), String> {
    let lhs = load_i256_limbs(resolve_value(function, lhs, value_map, builder)?, builder);
    let rhs = load_i256_limbs(resolve_value(function, rhs, value_map, builder)?, builder);
    let product = mul_i256_limbs_full(lhs, rhs, builder);
    let overflow = wide_i256_high_nonzero(product, builder);
    Ok((store_i256_limbs(low_i256_limbs(product), builder), overflow))
}

pub(super) fn emit_i256_smulo(
    function: &Function,
    lhs: ValueId,
    rhs: ValueId,
    value_map: &HashMap<ValueId, clif::Value>,
    builder: &mut FunctionBuilder,
) -> Result<(clif::Value, clif::Value), String> {
    let lhs = load_i256_limbs(resolve_value(function, lhs, value_map, builder)?, builder);
    let rhs = load_i256_limbs(resolve_value(function, rhs, value_map, builder)?, builder);
    let raw = low_i256_limbs(mul_i256_limbs_full(lhs, rhs, builder));
    let lhs_negative = i256_sign_bit(lhs, builder);
    let rhs_negative = i256_sign_bit(rhs, builder);
    let product_negative = bool_xor(lhs_negative, rhs_negative, builder);
    let abs_product = mul_i256_limbs_full(
        abs_i256_limbs(lhs, builder),
        abs_i256_limbs(rhs, builder),
        builder,
    );
    let high_nonzero = wide_i256_high_nonzero(abs_product, builder);
    let low_abs_product = low_i256_limbs(abs_product);
    let positive_limit = signed_max_i256_limbs(builder);
    let negative_limit = signed_min_i256_limbs(builder);
    let limit = select_i256_limbs(product_negative, negative_limit, positive_limit, builder);
    let over_limit = emit_i256_unsigned_lt_limbs(limit, low_abs_product, builder);
    let overflow = bool_or(high_nonzero, over_limit, builder);
    Ok((store_i256_limbs(raw, builder), overflow))
}

pub(super) fn emit_i256_snego(
    function: &Function,
    value: ValueId,
    value_map: &HashMap<ValueId, clif::Value>,
    builder: &mut FunctionBuilder,
) -> Result<(clif::Value, clif::Value), String> {
    let value = load_i256_limbs(resolve_value(function, value, value_map, builder)?, builder);
    let result = neg_i256_limbs(value, builder);
    let overflow = emit_i256_eq_limbs(value, signed_min_i256_limbs(builder), builder);
    Ok((store_i256_limbs(result, builder), overflow))
}

pub(super) enum I256SaturatingOp {
    Uadd,
    Sadd,
    Usub,
    Ssub,
    Umul,
    Smul,
}

pub(super) fn emit_i256_saturating_binary(
    function: &Function,
    lhs: ValueId,
    rhs: ValueId,
    op: I256SaturatingOp,
    value_map: &HashMap<ValueId, clif::Value>,
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    let lhs_value = load_i256_limbs(resolve_value(function, lhs, value_map, builder)?, builder);
    let rhs_value = load_i256_limbs(resolve_value(function, rhs, value_map, builder)?, builder);
    let (raw, overflow, saturated) = match op {
        I256SaturatingOp::Uadd => {
            let (raw, overflow) = add_i256_limbs(lhs_value, rhs_value, builder);
            (raw, overflow, unsigned_max_i256_limbs(builder))
        }
        I256SaturatingOp::Sadd => {
            let (raw, _) = add_i256_limbs(lhs_value, rhs_value, builder);
            let lhs_negative = i256_sign_bit(lhs_value, builder);
            let rhs_negative = i256_sign_bit(rhs_value, builder);
            let result_negative = i256_sign_bit(raw, builder);
            let same_sign = bool_eq(lhs_negative, rhs_negative, builder);
            let sign_changed = bool_xor(result_negative, lhs_negative, builder);
            let overflow = bool_and(same_sign, sign_changed, builder);
            let saturated = select_i256_limbs(
                lhs_negative,
                signed_min_i256_limbs(builder),
                signed_max_i256_limbs(builder),
                builder,
            );
            (raw, overflow, saturated)
        }
        I256SaturatingOp::Usub => {
            let (raw, overflow) = sub_i256_limbs(lhs_value, rhs_value, builder);
            (raw, overflow, zero_i256_limbs(builder))
        }
        I256SaturatingOp::Ssub => {
            let (raw, _) = sub_i256_limbs(lhs_value, rhs_value, builder);
            let lhs_negative = i256_sign_bit(lhs_value, builder);
            let rhs_negative = i256_sign_bit(rhs_value, builder);
            let result_negative = i256_sign_bit(raw, builder);
            let different_sign = bool_xor(lhs_negative, rhs_negative, builder);
            let sign_changed = bool_xor(result_negative, lhs_negative, builder);
            let overflow = bool_and(different_sign, sign_changed, builder);
            let saturated = select_i256_limbs(
                lhs_negative,
                signed_min_i256_limbs(builder),
                signed_max_i256_limbs(builder),
                builder,
            );
            (raw, overflow, saturated)
        }
        I256SaturatingOp::Umul => {
            let product = mul_i256_limbs_full(lhs_value, rhs_value, builder);
            (
                low_i256_limbs(product),
                wide_i256_high_nonzero(product, builder),
                unsigned_max_i256_limbs(builder),
            )
        }
        I256SaturatingOp::Smul => {
            let raw = low_i256_limbs(mul_i256_limbs_full(lhs_value, rhs_value, builder));
            let lhs_negative = i256_sign_bit(lhs_value, builder);
            let rhs_negative = i256_sign_bit(rhs_value, builder);
            let product_negative = bool_xor(lhs_negative, rhs_negative, builder);
            let abs_product = mul_i256_limbs_full(
                abs_i256_limbs(lhs_value, builder),
                abs_i256_limbs(rhs_value, builder),
                builder,
            );
            let high_nonzero = wide_i256_high_nonzero(abs_product, builder);
            let low_abs_product = low_i256_limbs(abs_product);
            let limit = select_i256_limbs(
                product_negative,
                signed_min_i256_limbs(builder),
                signed_max_i256_limbs(builder),
                builder,
            );
            let over_limit = emit_i256_unsigned_lt_limbs(limit, low_abs_product, builder);
            let overflow = bool_or(high_nonzero, over_limit, builder);
            let saturated = select_i256_limbs(
                product_negative,
                signed_min_i256_limbs(builder),
                signed_max_i256_limbs(builder),
                builder,
            );
            (raw, overflow, saturated)
        }
    };
    Ok(store_i256_limbs(
        select_i256_limbs(overflow, saturated, raw, builder),
        builder,
    ))
}

pub(super) enum I256BitwiseOp {
    And,
    Or,
    Xor,
}

pub(super) fn emit_i256_bitwise(
    function: &Function,
    lhs: ValueId,
    rhs: ValueId,
    op: I256BitwiseOp,
    value_map: &HashMap<ValueId, clif::Value>,
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    let lhs = resolve_value(function, lhs, value_map, builder)?;
    let rhs = resolve_value(function, rhs, value_map, builder)?;
    let result = create_i256_slot(builder);

    for limb in 0..I256_LIMBS {
        let lhs_limb = load_i256_limb(lhs, limb, builder);
        let rhs_limb = load_i256_limb(rhs, limb, builder);
        let value = match op {
            I256BitwiseOp::And => builder.ins().band(lhs_limb, rhs_limb),
            I256BitwiseOp::Or => builder.ins().bor(lhs_limb, rhs_limb),
            I256BitwiseOp::Xor => builder.ins().bxor(lhs_limb, rhs_limb),
        };
        store_i256_limb(result, limb, value, builder);
    }

    Ok(result)
}

pub(super) fn emit_i256_not(
    function: &Function,
    value: ValueId,
    value_map: &HashMap<ValueId, clif::Value>,
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    let value = resolve_value(function, value, value_map, builder)?;
    let result = create_i256_slot(builder);

    for limb in 0..I256_LIMBS {
        let limb_value = load_i256_limb(value, limb, builder);
        store_i256_limb(result, limb, builder.ins().bnot(limb_value), builder);
    }

    Ok(result)
}

pub(super) enum I256ShiftKind {
    Shl,
    Shr,
    Sar,
}

struct I256ShiftParts {
    limbs: [clif::Value; I256_LIMBS],
    limb_shift: clif::Value,
    bit_shift: clif::Value,
    inverse_shift: clif::Value,
    bit_shift_is_zero: clif::Value,
}

pub(super) fn emit_i256_shift(
    function: &Function,
    value: ValueId,
    bits: ValueId,
    kind: I256ShiftKind,
    value_map: &HashMap<ValueId, clif::Value>,
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    let value_addr = resolve_value(function, value, value_map, builder)?;
    let limbs = [
        load_i256_limb(value_addr, 0, builder),
        load_i256_limb(value_addr, 1, builder),
        load_i256_limb(value_addr, 2, builder),
        load_i256_limb(value_addr, 3, builder),
    ];
    let (shift, too_large) = resolve_i256_shift_amount(function, bits, value_map, builder)?;
    let result = create_i256_slot(builder);
    let zero = builder.ins().iconst(clif::types::I64, 0);
    let limb_mask = builder.ins().iconst(clif::types::I64, I256_LIMB_BITS - 1);
    let limb_shift = builder.ins().ushr_imm_s(shift, 6);
    let bit_shift = builder.ins().band(shift, limb_mask);
    let bit_shift_is_zero = builder.ins().icmp(IntCC::Equal, bit_shift, zero);
    let limb_bits = builder.ins().iconst(clif::types::I64, I256_LIMB_BITS);
    let inverse_shift = builder.ins().isub(limb_bits, bit_shift);
    let parts = I256ShiftParts {
        limbs,
        limb_shift,
        bit_shift,
        inverse_shift,
        bit_shift_is_zero,
    };
    let high_limb_is_negative =
        builder
            .ins()
            .icmp(IntCC::SignedLessThan, limbs[I256_LIMBS - 1], zero);
    let all_ones = builder.ins().iconst(clif::types::I64, -1);
    let sign_fill = builder.ins().select(high_limb_is_negative, all_ones, zero);
    let overshift_fill = match kind {
        I256ShiftKind::Sar => sign_fill,
        I256ShiftKind::Shl | I256ShiftKind::Shr => zero,
    };

    for result_limb_idx in 0..I256_LIMBS {
        let shifted = match kind {
            I256ShiftKind::Shl => emit_i256_shl_limb(result_limb_idx, &parts, builder),
            I256ShiftKind::Shr => {
                emit_i256_right_shift_limb(result_limb_idx, &parts, zero, builder)
            }
            I256ShiftKind::Sar => {
                emit_i256_right_shift_limb(result_limb_idx, &parts, sign_fill, builder)
            }
        };
        let shifted = builder.ins().select(too_large, overshift_fill, shifted);
        store_i256_limb(result, result_limb_idx, shifted, builder);
    }

    Ok(result)
}

pub(super) fn resolve_i256_shift_amount(
    function: &Function,
    bits: ValueId,
    value_map: &HashMap<ValueId, clif::Value>,
    builder: &mut FunctionBuilder,
) -> Result<(clif::Value, clif::Value), String> {
    let zero = builder.ins().iconst(clif::types::I64, 0);
    let max_shift = builder.ins().iconst(clif::types::I64, I256_BITS);
    let bits_ty = function.dfg.value_ty(bits);

    if bits_ty == Type::I256 {
        let bits_addr = resolve_value(function, bits, value_map, builder)?;
        let shift = load_i256_limb(bits_addr, 0, builder);
        let mut upper_nonzero = bool_const(false, builder);
        for limb in 1..I256_LIMBS {
            let limb_value = load_i256_limb(bits_addr, limb, builder);
            let limb_nonzero = builder.ins().icmp(IntCC::NotEqual, limb_value, zero);
            upper_nonzero = bool_or(upper_nonzero, limb_nonzero, builder);
        }
        let shift_too_large =
            builder
                .ins()
                .icmp(IntCC::UnsignedGreaterThanOrEqual, shift, max_shift);
        return Ok((shift, bool_or(upper_nonzero, shift_too_large, builder)));
    }

    let raw = resolve_value(function, bits, value_map, builder)?;
    let raw_ty = builder.func.dfg.value_type(raw);
    let shift = resize_int_value(raw, clif::types::I64, false, builder);
    let shift_too_large = builder
        .ins()
        .icmp(IntCC::UnsignedGreaterThanOrEqual, shift, max_shift);
    if raw_ty.bits() <= I256_LIMB_BITS as u32 {
        return Ok((shift, shift_too_large));
    }

    let high_bits = builder.ins().ushr_imm_s(raw, I256_LIMB_BITS);
    let zero_raw = scalar_constant(raw_ty, 0, builder);
    let high_bits_nonzero = builder.ins().icmp(IntCC::NotEqual, high_bits, zero_raw);
    Ok((shift, bool_or(high_bits_nonzero, shift_too_large, builder)))
}

fn emit_i256_shl_limb(
    result_limb_idx: usize,
    parts: &I256ShiftParts,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    let zero = builder.ins().iconst(clif::types::I64, 0);
    let mut result = zero;

    for shifted_limb_count in 0..=result_limb_idx {
        let low_idx = result_limb_idx - shifted_limb_count;
        let low = builder.ins().ishl(parts.limbs[low_idx], parts.bit_shift);
        let high = if low_idx > 0 {
            let high = builder
                .ins()
                .ushr(parts.limbs[low_idx - 1], parts.inverse_shift);
            builder.ins().select(parts.bit_shift_is_zero, zero, high)
        } else {
            zero
        };
        let combined = builder.ins().bor(low, high);
        let count = builder
            .ins()
            .iconst(clif::types::I64, shifted_limb_count as i64);
        let matches_count = builder.ins().icmp(IntCC::Equal, parts.limb_shift, count);
        result = builder.ins().select(matches_count, combined, result);
    }

    result
}

fn emit_i256_right_shift_limb(
    result_limb_idx: usize,
    parts: &I256ShiftParts,
    fill: clif::Value,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    let mut result = fill;

    for shifted_limb_count in 0..I256_LIMBS {
        let low_idx = result_limb_idx + shifted_limb_count;
        let low_source = parts.limbs.get(low_idx).copied().unwrap_or(fill);
        let high_source = parts.limbs.get(low_idx + 1).copied().unwrap_or(fill);
        let low = builder.ins().ushr(low_source, parts.bit_shift);
        let high = builder.ins().ishl(high_source, parts.inverse_shift);
        let zero = builder.ins().iconst(clif::types::I64, 0);
        let high = builder.ins().select(parts.bit_shift_is_zero, zero, high);
        let combined = builder.ins().bor(low, high);
        let count = builder
            .ins()
            .iconst(clif::types::I64, shifted_limb_count as i64);
        let matches_count = builder.ins().icmp(IntCC::Equal, parts.limb_shift, count);
        result = builder.ins().select(matches_count, combined, result);
    }

    result
}

pub(super) fn bool_const(value: bool, builder: &mut FunctionBuilder) -> clif::Value {
    let zero = builder.ins().iconst(clif::types::I8, 0);
    let rhs = builder.ins().iconst(clif::types::I8, (!value) as i64);
    builder.ins().icmp(IntCC::Equal, zero, rhs)
}

pub(super) fn bool_not(value: clif::Value, builder: &mut FunctionBuilder) -> clif::Value {
    let yes = bool_const(true, builder);
    let no = bool_const(false, builder);
    builder.ins().select(value, no, yes)
}

pub(super) fn bool_and(
    lhs: clif::Value,
    rhs: clif::Value,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    let no = bool_const(false, builder);
    builder.ins().select(lhs, rhs, no)
}

pub(super) fn bool_or(
    lhs: clif::Value,
    rhs: clif::Value,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    let yes = bool_const(true, builder);
    builder.ins().select(lhs, yes, rhs)
}

pub(super) fn emit_i256_eq_limbs(
    lhs: [clif::Value; I256_LIMBS],
    rhs: [clif::Value; I256_LIMBS],
    builder: &mut FunctionBuilder,
) -> clif::Value {
    let mut result = bool_const(true, builder);
    for limb in 0..I256_LIMBS {
        let limbs_equal = builder.ins().icmp(IntCC::Equal, lhs[limb], rhs[limb]);
        result = bool_and(result, limbs_equal, builder);
    }
    result
}

pub(super) fn emit_i256_eq(
    lhs: clif::Value,
    rhs: clif::Value,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    emit_i256_eq_limbs(
        load_i256_limbs(lhs, builder),
        load_i256_limbs(rhs, builder),
        builder,
    )
}

pub(super) fn emit_i256_unsigned_lt_limbs(
    lhs: [clif::Value; I256_LIMBS],
    rhs: [clif::Value; I256_LIMBS],
    builder: &mut FunctionBuilder,
) -> clif::Value {
    let mut result = bool_const(false, builder);
    let mut equal_prefix = bool_const(true, builder);
    for limb in (0..I256_LIMBS).rev() {
        let limb_lt = builder
            .ins()
            .icmp(IntCC::UnsignedLessThan, lhs[limb], rhs[limb]);
        let limb_eq = builder.ins().icmp(IntCC::Equal, lhs[limb], rhs[limb]);
        result = builder.ins().select(equal_prefix, limb_lt, result);
        equal_prefix = bool_and(equal_prefix, limb_eq, builder);
    }
    result
}

pub(super) fn emit_i256_unsigned_lt(
    lhs: clif::Value,
    rhs: clif::Value,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    emit_i256_unsigned_lt_limbs(
        load_i256_limbs(lhs, builder),
        load_i256_limbs(rhs, builder),
        builder,
    )
}

pub(super) fn emit_i256_signed_lt(
    lhs: clif::Value,
    rhs: clif::Value,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    let lhs_high = load_i256_limb(lhs, 3, builder);
    let rhs_high = load_i256_limb(rhs, 3, builder);
    let high_lt = builder
        .ins()
        .icmp(IntCC::SignedLessThan, lhs_high, rhs_high);
    let high_eq = builder.ins().icmp(IntCC::Equal, lhs_high, rhs_high);
    let lower_lt = emit_i256_unsigned_lt(lhs, rhs, builder);
    let equal_high_lower_lt = bool_and(high_eq, lower_lt, builder);
    bool_or(high_lt, equal_high_lower_lt, builder)
}

pub(super) fn emit_i256_icmp(
    cc: IntCC,
    lhs: clif::Value,
    rhs: clif::Value,
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    let result = match cc {
        IntCC::Equal => emit_i256_eq(lhs, rhs, builder),
        IntCC::NotEqual => {
            let equal = emit_i256_eq(lhs, rhs, builder);
            bool_not(equal, builder)
        }
        IntCC::UnsignedLessThan => emit_i256_unsigned_lt(lhs, rhs, builder),
        IntCC::UnsignedGreaterThan => emit_i256_unsigned_lt(rhs, lhs, builder),
        IntCC::UnsignedLessThanOrEqual => {
            let greater = emit_i256_unsigned_lt(rhs, lhs, builder);
            bool_not(greater, builder)
        }
        IntCC::UnsignedGreaterThanOrEqual => {
            let less = emit_i256_unsigned_lt(lhs, rhs, builder);
            bool_not(less, builder)
        }
        IntCC::SignedLessThan => emit_i256_signed_lt(lhs, rhs, builder),
        IntCC::SignedGreaterThan => emit_i256_signed_lt(rhs, lhs, builder),
        IntCC::SignedLessThanOrEqual => {
            let greater = emit_i256_signed_lt(rhs, lhs, builder);
            bool_not(greater, builder)
        }
        IntCC::SignedGreaterThanOrEqual => {
            let less = emit_i256_signed_lt(lhs, rhs, builder);
            bool_not(less, builder)
        }
    };
    Ok(result)
}

pub(super) fn emit_i256_is_zero(value: clif::Value, builder: &mut FunctionBuilder) -> clif::Value {
    let zero = builder.ins().iconst(clif::types::I64, 0);
    let mut result = bool_const(true, builder);
    for limb in 0..4 {
        let limb = load_i256_limb(value, limb, builder);
        let limb_is_zero = builder.ins().icmp(IntCC::Equal, limb, zero);
        result = bool_and(result, limb_is_zero, builder);
    }
    result
}

pub(super) fn resize_int_value(
    value: clif::Value,
    to_ty: clif::Type,
    signed: bool,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    let from_ty = builder.func.dfg.value_type(value);
    match from_ty.bits().cmp(&to_ty.bits()) {
        Ordering::Equal => value,
        Ordering::Less if signed => builder.ins().sextend(to_ty, value),
        Ordering::Less => builder.ins().uextend(to_ty, value),
        Ordering::Greater => builder.ins().ireduce(to_ty, value),
    }
}

pub(super) fn bool_to_int_value(
    value: clif::Value,
    to_ty: clif::Type,
    signed: bool,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    let zero = scalar_constant(to_ty, 0, builder);
    let set = scalar_constant(to_ty, if signed { -1 } else { 1 }, builder);
    builder.ins().select(value, set, zero)
}

pub(super) fn translate_bitcast(
    value: clif::Value,
    to_ty: clif::Type,
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    let from_ty = builder.func.dfg.value_type(value);
    if from_ty == to_ty {
        Ok(value)
    } else if from_ty.bits() == to_ty.bits() {
        Ok(builder.ins().bitcast(to_ty, MemFlagsData::new(), value))
    } else {
        Err(format!(
            "cannot bitcast Cranelift value from {from_ty} to {to_ty}"
        ))
    }
}

pub(super) fn insert_clif_results(
    function: &Function,
    inst_id: sonatina_ir::inst::InstId,
    values: impl IntoIterator<Item = clif::Value>,
    value_map: &mut HashMap<ValueId, clif::Value>,
) {
    for (ir_result, clif_result) in function.dfg.inst_results(inst_id).iter().zip(values) {
        value_map.insert(*ir_result, clif_result);
    }
}

pub(super) fn resolve_value(
    function: &Function,
    value_id: ValueId,
    value_map: &HashMap<ValueId, clif::Value>,
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    if let Some(&clif_val) = value_map.get(&value_id) {
        return Ok(clif_val);
    }
    // Check if there's a Variable for this (phi values in loops)
    // Variables are looked up via the FunctionBuilder's SSA system

    let value = function.dfg.value(value_id);
    match value {
        Value::Immediate { imm, ty } => match imm {
            Immediate::I128(value) => Ok(scalar_constant(clif::types::I128, *value, builder)),
            Immediate::I256(value) => Ok(emit_i256_immediate(value, builder)),
            _ => {
                let clif_ty = sonatina_scalar_type_to_clif_or_err(*ty)?;
                let i64_val = imm_to_i64(imm)?;
                let val = builder.ins().iconst(clif_ty, i64_val);
                Ok(val)
            }
        },
        _ => Err(format!("unresolved value v{}", value_id.0)),
    }
}

pub(super) fn imm_to_i64(imm: &Immediate) -> Result<i64, String> {
    match imm {
        Immediate::I1(b) => Ok(*b as i64),
        Immediate::I8(v) => Ok(*v as i64),
        Immediate::I16(v) => Ok(*v as i64),
        Immediate::I32(v) => Ok(*v as i64),
        Immediate::I64(v) => Ok(*v),
        _ => Err(format!("unsupported immediate type for cranelift: {imm:?}")),
    }
}

pub(super) fn emit_i256_immediate(
    imm: &sonatina_ir::I256,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    let slot = builder.create_sized_stack_slot(StackSlotData::new(
        StackSlotKind::ExplicitSlot,
        32,
        I256_ALIGN_SHIFT,
    ));
    let addr = builder.ins().stack_addr(clif::types::I64, slot, 0);

    let u256 = imm.to_u256();
    let bytes = u256.to_little_endian();
    for i in 0..4 {
        let limb = u64::from_le_bytes(bytes[i * 8..(i + 1) * 8].try_into().unwrap());
        let val = builder.ins().iconst(clif::types::I64, limb as i64);
        builder
            .ins()
            .store(MemFlagsData::new(), val, addr, (i * 8) as i32);
    }

    addr
}
