use std::collections::HashMap;

use cranelift_codegen::ir::{self as clif, InstBuilder, InstructionData, Opcode, condcodes::IntCC};
use cranelift_frontend::FunctionBuilder;
use sonatina_ir::{Immediate, Type, U256};

use super::{ShiftKind, mul_limbs, resize_int_value, shift_by_constant};

/// Sonatina's one-bit values use an I8 register, but only bit zero is data.
pub(super) fn normalize_scalar(
    value: clif::Value,
    ty: Type,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    if ty == Type::I1 {
        builder.ins().band_imm_s(value, 1)
    } else {
        value
    }
}

/// The two compares whose `bor` a one-bit `value` is, looking through the
/// masks `normalize_scalar` adds. Each is 0 or 1, so `value` is set exactly
/// when either is.
pub(super) fn compare_disjunction(
    value: clif::Value,
    dfg: &clif::DataFlowGraph,
) -> Option<[clif::Value; 2]> {
    let definition = |value| dfg.value_def(value).inst().map(|inst| &dfg.insts[inst]);
    let binary = |value, opcode| match *definition(value)? {
        InstructionData::Binary {
            opcode: found,
            args,
        } if found == opcode => Some(args),
        _ => None,
    };
    let unmasked = |value| match binary(value, Opcode::Band) {
        Some([bits, mask])
            if matches!(
                definition(mask),
                Some(InstructionData::UnaryImm { opcode: Opcode::Iconst, imm }) if imm.bits() == 1
            ) =>
        {
            bits
        }
        _ => value,
    };
    let compare = |value| {
        let value = unmasked(value);
        (definition(value)?.opcode() == Opcode::Icmp).then_some(value)
    };
    let [lhs, rhs] = binary(unmasked(value), Opcode::Bor)?;
    Some([compare(lhs)?, compare(rhs)?])
}

/// Makes each repeated `isplit` of a value in a block take the first one's
/// words. The low and the high word of a product are extracted apart, and
/// Cranelift neither merges the splits nor folds a load into an instruction
/// whose result two instructions use: a 64-bit product split twice read its
/// operand into a register instead of from memory.
pub(super) fn merge_repeated_isplits(func: &mut clif::Function) {
    for block in func.layout.blocks().collect::<Vec<_>>() {
        let mut first = HashMap::<clif::Value, clif::Inst>::new();
        let mut inst = func.layout.first_inst(block);
        while let Some(current) = inst {
            inst = func.layout.next_inst(current);
            let InstructionData::Unary {
                opcode: Opcode::Isplit,
                arg,
            } = func.dfg.insts[current]
            else {
                continue;
            };
            let arg = func.dfg.resolve_aliases(arg);
            let Some(&kept) = first.get(&arg) else {
                first.insert(arg, current);
                continue;
            };
            let kept = func.dfg.inst_results(kept).to_vec();
            let repeated = func.dfg.inst_results(current).to_vec();
            func.dfg.detach_inst_results(current);
            for (value, original) in repeated.into_iter().zip(kept) {
                func.dfg.change_to_alias(value, original);
            }
            func.layout.remove_inst(current);
        }
    }
}

/// The low `to_ty` bits of an i128 value, from its low word: the `iconcat`
/// operand that built it, if one did. An `ireduce` would let Cranelift narrow
/// an i128 product or sum to a separate 64-bit one, duplicating the
/// arithmetic whose high word is usually needed too.
pub(super) fn truncate_i128(
    value: clif::Value,
    to_ty: clif::Type,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    let dfg = &builder.func.dfg;
    let concat_low = match dfg.value_def(value).inst().map(|inst| dfg.insts[inst]) {
        Some(InstructionData::Binary {
            opcode: Opcode::Iconcat,
            args: [low, _],
        }) => Some(low),
        _ => None,
    };
    let low = concat_low.unwrap_or_else(|| builder.ins().isplit(value).0);
    resize_int_value(low, to_ty, false, builder)
}

pub(super) fn signed_scalar(
    value: clif::Value,
    ty: Type,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    if ty == Type::I1 {
        builder.ins().ineg(value)
    } else {
        value
    }
}

pub(super) enum ScalarArithmetic {
    Add,
    Sub,
    Mul,
}

pub(super) fn emit_scalar_overflow(
    lhs: clif::Value,
    rhs: clif::Value,
    ty: Type,
    op: ScalarArithmetic,
    signed: bool,
    builder: &mut FunctionBuilder,
) -> (clif::Value, clif::Value) {
    if ty == Type::I1 {
        let (lhs, rhs) = if signed {
            (
                signed_scalar(lhs, ty, builder),
                signed_scalar(rhs, ty, builder),
            )
        } else {
            (lhs, rhs)
        };
        let raw = match op {
            ScalarArithmetic::Add => builder.ins().iadd(lhs, rhs),
            ScalarArithmetic::Sub => builder.ins().isub(lhs, rhs),
            ScalarArithmetic::Mul => builder.ins().imul(lhs, rhs),
        };
        // Shift the signed range [-1, 0] to [0, 1]. Every out-of-range
        // result, including negative results, then compares unsigned > 1.
        let range_value = if signed {
            builder.ins().iadd_imm_s(raw, 1)
        } else {
            raw
        };
        let overflow = builder
            .ins()
            .icmp_imm_s(IntCC::UnsignedGreaterThan, range_value, 1);
        return (raw, overflow);
    }
    match (op, signed) {
        (ScalarArithmetic::Add, false) => builder.ins().uadd_overflow(lhs, rhs),
        (ScalarArithmetic::Add, true) => builder.ins().sadd_overflow(lhs, rhs),
        (ScalarArithmetic::Sub, false) => builder.ins().usub_overflow(lhs, rhs),
        (ScalarArithmetic::Sub, true) => builder.ins().ssub_overflow(lhs, rhs),
        (ScalarArithmetic::Mul, signed) => emit_scalar_mul_overflow(lhs, rhs, signed, builder),
    }
}

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
    constant_count: Option<Immediate>,
    ty: Type,
    kind: ShiftKind,
    count_in_range: bool,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    let clif_ty = builder.func.dfg.value_type(value);
    // Cranelift shifts an i128 by a count in a register even when the count
    // is constant, so shift its two words here instead.
    if clif_ty == clif::types::I128
        && let Some(count) = constant_count
    {
        let count = count.zext(Type::I256).as_i256().to_u256();
        let (low, high) = builder.ins().isplit(value);
        let fill = match kind {
            ShiftKind::Sar => builder.ins().sshr_imm_s(high, 63),
            ShiftKind::Shl | ShiftKind::Shr => builder.ins().iconst(clif::types::I64, 0),
        };
        let [low, high] = if count < U256::from(128) {
            shift_by_constant([low, high], count.low_u32(), kind, fill, builder)
        } else {
            [fill; 2]
        };
        return builder.ins().iconcat(low, high);
    }
    let width = if ty == Type::I1 { 1 } else { clif_ty.bits() };
    // Cranelift masks shift counts; Sonatina saturates oversized shifts, so
    // a count that may reach the width needs a fallback. Compare at the
    // original count width before any instruction narrows it.
    let oversized = (!count_in_range).then(|| {
        let limit = scalar_constant(
            builder.func.dfg.value_type(count),
            i128::from(width),
            builder,
        );
        builder
            .ins()
            .icmp(IntCC::UnsignedGreaterThanOrEqual, count, limit)
    });
    let count = if builder.func.dfg.value_type(count) == clif::types::I128 {
        builder.ins().ireduce(clif::types::I64, count)
    } else {
        count
    };
    let shifted = match kind {
        ShiftKind::Shl => builder.ins().ishl(value, count),
        ShiftKind::Shr => builder.ins().ushr(value, count),
        ShiftKind::Sar if ty == Type::I1 => value,
        ShiftKind::Sar => builder.ins().sshr(value, count),
    };
    let Some(oversized) = oversized else {
        return shifted;
    };
    let fill = match kind {
        ShiftKind::Shl | ShiftKind::Shr => scalar_constant(clif_ty, 0, builder),
        ShiftKind::Sar if ty == Type::I1 => value,
        ShiftKind::Sar => builder.ins().sshr_imm_s(value, i64::from(width - 1)),
    };
    builder.ins().select(oversized, fill, shifted)
}

pub(super) fn emit_scalar_div_rem(
    lhs: clif::Value,
    rhs: clif::Value,
    source_ty: Type,
    kind: DivRemKind,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    let (lhs, rhs) = if matches!(kind, DivRemKind::Sdiv | DivRemKind::Smod) {
        (
            signed_scalar(lhs, source_ty, builder),
            signed_scalar(rhs, source_ty, builder),
        )
    } else {
        (lhs, rhs)
    };
    match kind {
        DivRemKind::Udiv => builder.ins().udiv(lhs, rhs),
        DivRemKind::Umod => builder.ins().urem(lhs, rhs),
        DivRemKind::Smod => builder.ins().srem(lhs, rhs),
        DivRemKind::Sdiv => {
            let ty = builder.func.dfg.value_type(lhs);
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
    }
}

/// The low and high limbs of the i128 `value`; a zero extension of a word
/// has a constant zero high limb, which `mul_limbs` skips.
fn i128_limbs(value: clif::Value, builder: &mut FunctionBuilder) -> (clif::Value, clif::Value) {
    let dfg = &builder.func.dfg;
    if let Some(inst) = dfg.value_def(value).inst()
        && let InstructionData::Unary {
            opcode: Opcode::Uextend,
            arg,
        } = dfg.insts[inst]
        && dfg.value_type(arg).bits() <= 64
    {
        let low = if dfg.value_type(arg) == clif::types::I64 {
            arg
        } else {
            builder.ins().uextend(clif::types::I64, arg)
        };
        return (low, builder.ins().iconst(clif::types::I64, 0));
    }
    builder.ins().isplit(value)
}

/// `value`, an i128 whose high 64 bits are zero, as the zero extension of its
/// low limb, so that products take it as one limb.
pub(super) fn narrow_i128(value: clif::Value, builder: &mut FunctionBuilder) -> clif::Value {
    let low = builder.ins().ireduce(clif::types::I64, value);
    builder.ins().uextend(clif::types::I128, low)
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
    let (lhs_low, lhs_high) = i128_limbs(lhs, builder);
    let (rhs_low, rhs_high) = i128_limbs(rhs, builder);
    let [low, high, upper_low, upper_high] =
        mul_limbs::<4>(&[lhs_low, lhs_high], &[rhs_low, rhs_high], builder);
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

#[cfg(test)]
mod tests {
    use cranelift_codegen::{
        cursor::{Cursor, FuncCursor},
        ir::{AbiParam, InstBuilder, InstructionData, Opcode, Signature, UserFuncName, types},
        isa::CallConv,
    };

    use super::{clif, merge_repeated_isplits};

    #[test]
    fn repeated_isplits_take_the_first_words() {
        let mut signature = Signature::new(CallConv::SystemV);
        signature.params.push(AbiParam::new(types::I128));
        signature.returns.extend([AbiParam::new(types::I64); 2]);
        let mut func = clif::Function::with_name_signature(UserFuncName::default(), signature);
        let block = func.dfg.make_block();
        let value = func.dfg.append_block_param(block, types::I128);
        func.layout.append_block(block);
        let mut cursor = FuncCursor::new(&mut func).at_bottom(block);
        // A product's low word, then its high word, each split apart.
        let (low, _) = cursor.ins().isplit(value);
        let (_, high) = cursor.ins().isplit(value);
        cursor.ins().return_(&[low, high]);

        merge_repeated_isplits(&mut func);

        let splits: Vec<_> = func
            .layout
            .block_insts(block)
            .filter(|&inst| func.dfg.insts[inst].opcode() == Opcode::Isplit)
            .collect();
        assert_eq!(splits.len(), 1, "{}", func.display());
        let words = func.dfg.inst_results(splits[0]).to_vec();
        let ret = func.layout.last_inst(block).unwrap();
        let InstructionData::MultiAry { args, .. } = func.dfg.insts[ret] else {
            panic!("{}", func.display());
        };
        let returned: Vec<_> = args
            .as_slice(&func.dfg.value_lists)
            .iter()
            .map(|&value| func.dfg.resolve_aliases(value))
            .collect();
        assert_eq!(returned, words, "{}", func.display());
    }
}
