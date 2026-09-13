use cranelift_codegen::ir::{self as clif, InstBuilder, TrapCode, condcodes::IntCC};
use cranelift_frontend::FunctionBuilder;
use sonatina_ir::Type;

use super::{mul_limbs_full, unsigned_div_rem_i256_limbs};

pub(super) fn scalar_constant(
    ty: clif::Type,
    value: i128,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    if ty == clif::types::I128 {
        let low = builder.ins().iconst(clif::types::I64, value as i64);
        let high = builder.ins().iconst(clif::types::I64, (value >> 64) as i64);
        builder.ins().iconcat(low, high)
    } else {
        builder.ins().iconst(ty, value as i64)
    }
}

pub(super) enum ScalarShift {
    Shl,
    Shr,
    Sar,
}

pub(super) enum DivRemKind {
    Udiv,
    Sdiv,
    Umod,
    Smod,
}

pub(super) fn unsigned_max_value(ty: clif::Type, builder: &mut FunctionBuilder) -> clif::Value {
    scalar_constant(ty, -1, builder)
}

pub(super) fn signed_min_value(ty: clif::Type, builder: &mut FunctionBuilder) -> clif::Value {
    scalar_constant(ty, i128::MIN >> (128 - ty.bits()), builder)
}

pub(super) fn signed_max_value(ty: clif::Type, builder: &mut FunctionBuilder) -> clif::Value {
    scalar_constant(ty, i128::MAX >> (128 - ty.bits()), builder)
}

pub(super) fn emit_scalar_shift(
    value: clif::Value,
    count: clif::Value,
    ty: Type,
    kind: ScalarShift,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    let clif_ty = builder.func.dfg.value_type(value);
    let width = if ty == Type::I1 { 1 } else { clif_ty.bits() };
    // Cranelift masks shift counts; Sonatina saturates oversized shifts.
    // Compare at the original count width before any instruction narrows it.
    let limit = scalar_constant(
        builder.func.dfg.value_type(count),
        i128::from(width),
        builder,
    );
    let oversized = builder
        .ins()
        .icmp(IntCC::UnsignedGreaterThanOrEqual, count, limit);
    let count = if builder.func.dfg.value_type(count) == clif::types::I128 {
        builder.ins().ireduce(clif::types::I64, count)
    } else {
        count
    };
    let zero = scalar_constant(clif_ty, 0, builder);
    let (shifted, fill) = match kind {
        ScalarShift::Shl => (builder.ins().ishl(value, count), zero),
        ScalarShift::Shr => (builder.ins().ushr(value, count), zero),
        ScalarShift::Sar if ty == Type::I1 => (value, value),
        ScalarShift::Sar => (
            builder.ins().sshr(value, count),
            builder.ins().sshr_imm_s(value, i64::from(width - 1)),
        ),
    };
    builder.ins().select(oversized, fill, shifted)
}

pub(super) fn emit_scalar_div_rem(
    lhs: clif::Value,
    rhs: clif::Value,
    kind: DivRemKind,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    let ty = builder.func.dfg.value_type(lhs);
    if ty != clif::types::I128 {
        return match kind {
            DivRemKind::Udiv => builder.ins().udiv(lhs, rhs),
            DivRemKind::Umod => builder.ins().urem(lhs, rhs),
            DivRemKind::Smod => builder.ins().srem(lhs, rhs),
            DivRemKind::Sdiv => {
                let min = signed_min_value(ty, builder);
                let lhs_min = builder.ins().icmp(IntCC::Equal, lhs, min);
                let minus_one = scalar_constant(ty, -1, builder);
                let rhs_minus_one = builder.ins().icmp(IntCC::Equal, rhs, minus_one);
                let overflow = builder.ins().band(lhs_min, rhs_minus_one);
                let one = scalar_constant(ty, 1, builder);
                // Dividing the minimum by one gives the wrapping overflow
                // result without executing Cranelift's trapping min / -1.
                let divisor = builder.ins().select(overflow, one, rhs);
                builder.ins().sdiv(lhs, divisor)
            }
        };
    }

    // Upstream Cranelift does not lower I128 division or remainder. Use the
    // shared unsigned limb divider, restoring signs only for signed operations.
    let zero = scalar_constant(ty, 0, builder);
    let rhs_zero = builder.ins().icmp(IntCC::Equal, rhs, zero);
    builder
        .ins()
        .trapnz(rhs_zero, TrapCode::INTEGER_DIVISION_BY_ZERO);
    let signed = matches!(kind, DivRemKind::Sdiv | DivRemKind::Smod);
    let remainder = matches!(kind, DivRemKind::Umod | DivRemKind::Smod);
    let (numerator, denominator, negative) = if signed {
        let lhs_negative = builder.ins().icmp(IntCC::SignedLessThan, lhs, zero);
        let rhs_negative = builder.ins().icmp(IntCC::SignedLessThan, rhs, zero);
        // Signed remainder takes the dividend's sign, not the quotient's.
        let negative = if remainder {
            lhs_negative
        } else {
            builder.ins().bxor(lhs_negative, rhs_negative)
        };
        let lhs_negated = builder.ins().ineg(lhs);
        let rhs_negated = builder.ins().ineg(rhs);
        let lhs_abs = builder.ins().select(lhs_negative, lhs_negated, lhs);
        let rhs_abs = builder.ins().select(rhs_negative, rhs_negated, rhs);
        (lhs_abs, rhs_abs, negative)
    } else {
        (lhs, rhs, builder.ins().iconst(clif::types::I8, 0))
    };
    let (lhs_low, lhs_high) = builder.ins().isplit(numerator);
    let (rhs_low, rhs_high) = builder.ins().isplit(denominator);
    let zero_limb = builder.ins().iconst(clif::types::I64, 0);
    let (quotient, modulus) = unsigned_div_rem_i256_limbs(
        [lhs_low, lhs_high, zero_limb, zero_limb],
        [rhs_low, rhs_high, zero_limb, zero_limb],
        128,
        builder,
    );
    let limbs = if remainder { modulus } else { quotient };
    let result = builder.ins().iconcat(limbs[0], limbs[1]);
    if signed {
        let negated = builder.ins().ineg(result);
        builder.ins().select(negative, negated, result)
    } else {
        result
    }
}

pub(super) fn emit_scalar_mul_overflow(
    lhs: clif::Value,
    rhs: clif::Value,
    signed: bool,
    builder: &mut FunctionBuilder,
) -> (clif::Value, clif::Value) {
    if builder.func.dfg.value_type(lhs) != clif::types::I128 {
        return if signed {
            builder.ins().smul_overflow(lhs, rhs)
        } else {
            builder.ins().umul_overflow(lhs, rhs)
        };
    }

    // Cranelift has no i128 multiply-with-overflow instruction lowering.
    // Multiply magnitudes at full width, then restore the sign if necessary.
    let zero = scalar_constant(clif::types::I128, 0, builder);
    let negative = if signed {
        let signs = builder.ins().bxor(lhs, rhs);
        builder.ins().icmp(IntCC::SignedLessThan, signs, zero)
    } else {
        builder.ins().iconst(clif::types::I8, 0)
    };
    let magnitude = |value, builder: &mut FunctionBuilder| {
        if signed {
            let neg = builder.ins().ineg(value);
            let is_negative = builder.ins().icmp(IntCC::SignedLessThan, value, zero);
            builder.ins().select(is_negative, neg, value)
        } else {
            value
        }
    };
    let lhs = magnitude(lhs, builder);
    let rhs = magnitude(rhs, builder);
    let (lhs_low, lhs_high) = builder.ins().isplit(lhs);
    let (rhs_low, rhs_high) = builder.ins().isplit(rhs);
    let [low, high, upper_low, upper_high] =
        mul_limbs_full(&[lhs_low, lhs_high], &[rhs_low, rhs_high], builder);
    let raw = builder.ins().iconcat(low, high);
    let upper = builder.ins().bor(upper_low, upper_high);
    let mut overflow = builder.ins().icmp_imm_s(IntCC::NotEqual, upper, 0);
    let result = if signed {
        let min = signed_min_value(clif::types::I128, builder);
        let max = signed_max_value(clif::types::I128, builder);
        let limit = builder.ins().select(negative, min, max);
        let over_limit = builder.ins().icmp(IntCC::UnsignedGreaterThan, raw, limit);
        overflow = builder.ins().bor(overflow, over_limit);
        let negated = builder.ins().ineg(raw);
        builder.ins().select(negative, negated, raw)
    } else {
        raw
    };
    (result, overflow)
}
