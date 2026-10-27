//! i256 values as four i64 limbs, least significant first. Limbs live in
//! Cranelift SSA values; only memory and call boundaries store them.

use std::{cmp::Ordering, collections::HashMap};

use cranelift_codegen::ir::{
    self as clif, InstBuilder, MemFlagsData, StackSlotData, StackSlotKind,
    condcodes::IntCC,
    types::{I64, I128},
};
use cranelift_frontend::FunctionBuilder;
use sonatina_ir::{
    Function, Type, U256, ValueId,
    inst::{InstId, inst_set::InstSetExt, native::inst_set::NativeInstKind},
    isa::native::inst_set as native_inst_set,
};

use super::{ValueMap, resolve_i256, scalar_constant};

pub(super) const LIMBS: usize = 4;
pub(super) type Limbs = [clif::Value; LIMBS];

const LIMB_BITS: u32 = 64;
const I256_ALIGN_SHIFT: u8 = 4;

/// Memory that carries i256 values across calls. An argument is stored
/// right before its call and a result loaded right after it, so a function
/// needs one slot per argument position and one for results.
#[derive(Default)]
pub(super) struct I256Storage {
    /// The caller's storage for each i256 argument, unchanged for the call.
    incoming: HashMap<ValueId, clif::Value>,
    outgoing: Vec<clif::StackSlot>,
    result: Option<clif::StackSlot>,
}

impl I256Storage {
    /// Records the caller's storage of argument `value` and loads its limbs.
    pub fn incoming(
        &mut self,
        value: ValueId,
        address: clif::Value,
        builder: &mut FunctionBuilder,
    ) -> Limbs {
        self.incoming.insert(value, address);
        load_limbs(address, 0, MemFlagsData::new().with_notrap(), builder)
    }

    /// The address of storage holding `value` for the `index`th i256
    /// argument of a call.
    pub fn outgoing(
        &mut self,
        function: &Function,
        value: ValueId,
        index: usize,
        value_map: &ValueMap,
        builder: &mut FunctionBuilder,
    ) -> Result<clif::Value, String> {
        if let Some(&address) = self.incoming.get(&value) {
            return Ok(address);
        }
        let limbs = resolve_i256(function, value, value_map, builder)?;
        while self.outgoing.len() <= index {
            let slot = i256_slot(builder);
            self.outgoing.push(slot);
        }
        let address = builder.ins().stack_addr(I64, self.outgoing[index], 0);
        store_limbs(limbs, address, 0, MemFlagsData::trusted(), builder);
        Ok(address)
    }

    /// The address of the return buffer for an i256 call result.
    pub fn result(&mut self, builder: &mut FunctionBuilder) -> clif::Value {
        let slot = *self.result.get_or_insert_with(|| i256_slot(builder));
        builder.ins().stack_addr(I64, slot, 0)
    }
}

fn i256_slot(builder: &mut FunctionBuilder) -> clif::StackSlot {
    builder.create_sized_stack_slot(StackSlotData::new(
        StackSlotKind::ExplicitSlot,
        32,
        I256_ALIGN_SHIFT,
    ))
}

pub(super) fn constant_limbs(value: U256, builder: &mut FunctionBuilder) -> Limbs {
    value.0.map(|limb| builder.ins().iconst(I64, limb as i64))
}

pub(super) fn load_limbs(
    address: clif::Value,
    offset: i32,
    flags: MemFlagsData,
    builder: &mut FunctionBuilder,
) -> Limbs {
    std::array::from_fn(|limb| {
        builder
            .ins()
            .load(I64, flags, address, offset + 8 * limb as i32)
    })
}

pub(super) fn store_limbs(
    limbs: Limbs,
    address: clif::Value,
    offset: i32,
    flags: MemFlagsData,
    builder: &mut FunctionBuilder,
) {
    for (limb, value) in limbs.into_iter().enumerate() {
        builder
            .ins()
            .store(flags, value, address, offset + 8 * limb as i32);
    }
}

/// Extends a scalar of Sonatina type `source_ty` to i256.
pub(super) fn extend_to_limbs(
    value: clif::Value,
    source_ty: Type,
    signed: bool,
    builder: &mut FunctionBuilder,
) -> Limbs {
    let fill = |high, builder: &mut FunctionBuilder| {
        if signed {
            builder.ins().sshr_imm_s(high, 63)
        } else {
            builder.ins().iconst(I64, 0)
        }
    };
    if builder.func.dfg.value_type(value) == I128 {
        let (low, high) = builder.ins().isplit(value);
        let fill = fill(high, builder);
        return [low, high, fill, fill];
    }
    let low = if source_ty == Type::I1 {
        bool_to_int_value(value, I64, signed, builder)
    } else {
        resize_int_value(value, I64, signed, builder)
    };
    let fill = fill(low, builder);
    [low, fill, fill, fill]
}

/// The low `to_ty` bits of an i256 value.
pub(super) fn truncate_limbs(
    limbs: Limbs,
    to_ty: clif::Type,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    match to_ty.bits() {
        128 => builder.ins().iconcat(limbs[0], limbs[1]),
        64 => limbs[0],
        _ => builder.ins().ireduce(to_ty, limbs[0]),
    }
}

/// The low and high 128-bit halves of an i256 value.
fn halves(limbs: Limbs, builder: &mut FunctionBuilder) -> (clif::Value, clif::Value) {
    (
        builder.ins().iconcat(limbs[0], limbs[1]),
        builder.ins().iconcat(limbs[2], limbs[3]),
    )
}

fn from_halves(low: clif::Value, high: clif::Value, builder: &mut FunctionBuilder) -> Limbs {
    let (limb0, limb1) = builder.ins().isplit(low);
    let (limb2, limb3) = builder.ins().isplit(high);
    [limb0, limb1, limb2, limb3]
}

fn carry_to_i128(carry: clif::Value, builder: &mut FunctionBuilder) -> clif::Value {
    let carry = builder.ins().uextend(I64, carry);
    builder.ins().uextend(I128, carry)
}

// Cranelift has no carry-in additions for i64, so a 256-bit addition is two
// i128 additions (add/adc pairs) and an addition of the low half's carry.

fn add(lhs: Limbs, rhs: Limbs, builder: &mut FunctionBuilder) -> Limbs {
    let (lhs_low, lhs_high) = halves(lhs, builder);
    let (rhs_low, rhs_high) = halves(rhs, builder);
    let (low, carry) = builder.ins().uadd_overflow(lhs_low, rhs_low);
    let high = builder.ins().iadd(lhs_high, rhs_high);
    let carry = carry_to_i128(carry, builder);
    let high = builder.ins().iadd(high, carry);
    from_halves(low, high, builder)
}

/// The sum and its carry out.
pub(super) fn add_carry(
    lhs: Limbs,
    rhs: Limbs,
    builder: &mut FunctionBuilder,
) -> (Limbs, clif::Value) {
    let (lhs_low, lhs_high) = halves(lhs, builder);
    let (rhs_low, rhs_high) = halves(rhs, builder);
    let (low, carry) = builder.ins().uadd_overflow(lhs_low, rhs_low);
    let (high, high_carry) = builder.ins().uadd_overflow(lhs_high, rhs_high);
    let carry = carry_to_i128(carry, builder);
    let (high, carry) = builder.ins().uadd_overflow(high, carry);
    let carry = builder.ins().bor(high_carry, carry);
    (from_halves(low, high, builder), carry)
}

pub(super) fn sub(lhs: Limbs, rhs: Limbs, builder: &mut FunctionBuilder) -> Limbs {
    let (lhs_low, lhs_high) = halves(lhs, builder);
    let (rhs_low, rhs_high) = halves(rhs, builder);
    let (low, borrow) = builder.ins().usub_overflow(lhs_low, rhs_low);
    let high = builder.ins().isub(lhs_high, rhs_high);
    let borrow = carry_to_i128(borrow, builder);
    let high = builder.ins().isub(high, borrow);
    from_halves(low, high, builder)
}

/// The difference and its borrow out.
pub(super) fn sub_borrow(
    lhs: Limbs,
    rhs: Limbs,
    builder: &mut FunctionBuilder,
) -> (Limbs, clif::Value) {
    let (lhs_low, lhs_high) = halves(lhs, builder);
    let (rhs_low, rhs_high) = halves(rhs, builder);
    let (low, borrow) = builder.ins().usub_overflow(lhs_low, rhs_low);
    let (high, high_borrow) = builder.ins().usub_overflow(lhs_high, rhs_high);
    let borrow = carry_to_i128(borrow, builder);
    let (high, borrow) = builder.ins().usub_overflow(high, borrow);
    let borrow = builder.ins().bor(high_borrow, borrow);
    (from_halves(low, high, builder), borrow)
}

pub(super) fn neg(value: Limbs, builder: &mut FunctionBuilder) -> Limbs {
    sub(constant_limbs(U256::zero(), builder), value, builder)
}

pub(super) fn sign(value: Limbs, builder: &mut FunctionBuilder) -> clif::Value {
    builder.ins().icmp_imm_s(IntCC::SignedLessThan, value[3], 0)
}

pub(super) fn abs(value: Limbs, builder: &mut FunctionBuilder) -> Limbs {
    let negative = sign(value, builder);
    let negated = neg(value, builder);
    select(negative, negated, value, builder)
}

pub(super) fn select(
    condition: clif::Value,
    if_true: Limbs,
    if_false: Limbs,
    builder: &mut FunctionBuilder,
) -> Limbs {
    std::array::from_fn(|limb| {
        builder
            .ins()
            .select(condition, if_true[limb], if_false[limb])
    })
}

fn any_nonzero(limbs: &[clif::Value], builder: &mut FunctionBuilder) -> clif::Value {
    let combined = limbs
        .iter()
        .copied()
        .reduce(|lhs, rhs| builder.ins().bor(lhs, rhs))
        .expect("at least one limb");
    builder.ins().icmp_imm_s(IntCC::NotEqual, combined, 0)
}

pub(super) fn is_zero(value: Limbs, builder: &mut FunctionBuilder) -> clif::Value {
    let nonzero = any_nonzero(&value, builder);
    bool_not(nonzero, builder)
}

pub(super) fn eq(lhs: Limbs, rhs: Limbs, builder: &mut FunctionBuilder) -> clif::Value {
    let diff: Limbs = std::array::from_fn(|limb| builder.ins().bxor(lhs[limb], rhs[limb]));
    is_zero(diff, builder)
}

/// Compares the high halves with `high_cc` and, when they are equal, the
/// low halves unsigned.
fn lexicographic_lt(
    high_cc: IntCC,
    lhs: Limbs,
    rhs: Limbs,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    let (lhs_low, lhs_high) = halves(lhs, builder);
    let (rhs_low, rhs_high) = halves(rhs, builder);
    let high_lt = builder.ins().icmp(high_cc, lhs_high, rhs_high);
    let high_eq = builder.ins().icmp(IntCC::Equal, lhs_high, rhs_high);
    let low_lt = builder
        .ins()
        .icmp(IntCC::UnsignedLessThan, lhs_low, rhs_low);
    let low_decides = builder.ins().band(high_eq, low_lt);
    builder.ins().bor(high_lt, low_decides)
}

pub(super) fn ult(lhs: Limbs, rhs: Limbs, builder: &mut FunctionBuilder) -> clif::Value {
    lexicographic_lt(IntCC::UnsignedLessThan, lhs, rhs, builder)
}

fn icmp(cc: IntCC, lhs: Limbs, rhs: Limbs, builder: &mut FunctionBuilder) -> clif::Value {
    let (high_cc, lhs, rhs, negate) = match cc {
        IntCC::Equal => return eq(lhs, rhs, builder),
        IntCC::NotEqual => {
            let equal = eq(lhs, rhs, builder);
            return bool_not(equal, builder);
        }
        IntCC::UnsignedLessThan => (IntCC::UnsignedLessThan, lhs, rhs, false),
        IntCC::UnsignedGreaterThan => (IntCC::UnsignedLessThan, rhs, lhs, false),
        IntCC::UnsignedLessThanOrEqual => (IntCC::UnsignedLessThan, rhs, lhs, true),
        IntCC::UnsignedGreaterThanOrEqual => (IntCC::UnsignedLessThan, lhs, rhs, true),
        IntCC::SignedLessThan => (IntCC::SignedLessThan, lhs, rhs, false),
        IntCC::SignedGreaterThan => (IntCC::SignedLessThan, rhs, lhs, false),
        IntCC::SignedLessThanOrEqual => (IntCC::SignedLessThan, rhs, lhs, true),
        IntCC::SignedGreaterThanOrEqual => (IntCC::SignedLessThan, lhs, rhs, true),
    };
    let less = lexicographic_lt(high_cc, lhs, rhs, builder);
    if negate {
        bool_not(less, builder)
    } else {
        less
    }
}

/// The low `N` limbs of the product of two little-endian limb sequences.
pub(super) fn mul_limbs<const N: usize>(
    lhs: &[clif::Value],
    rhs: &[clif::Value],
    builder: &mut FunctionBuilder,
) -> [clif::Value; N] {
    // Schoolbook rows. Each partial sum `lhs[i] * rhs[j] + result + carry`
    // fits in 128 bits; when the product is truncated, the top limb needs
    // only the low halves of its partial products.
    let truncated = N < lhs.len() + rhs.len();
    let mut result: [Option<clif::Value>; N] = [None; N];
    for (i, &lhs_limb) in lhs.iter().enumerate() {
        let mut carry = None;
        for (j, &rhs_limb) in rhs.iter().enumerate().take(N.saturating_sub(i)) {
            let k = i + j;
            if truncated && k == N - 1 {
                let product = builder.ins().imul(lhs_limb, rhs_limb);
                let sum = [result[k], carry]
                    .into_iter()
                    .flatten()
                    .fold(product, |sum, addend| builder.ins().iadd(sum, addend));
                result[k] = Some(sum);
                carry = None;
            } else {
                let lhs_wide = builder.ins().uextend(I128, lhs_limb);
                let rhs_wide = builder.ins().uextend(I128, rhs_limb);
                let product = builder.ins().imul(lhs_wide, rhs_wide);
                let sum = [result[k], carry]
                    .into_iter()
                    .flatten()
                    .fold(product, |sum, addend| {
                        let addend = builder.ins().uextend(I128, addend);
                        builder.ins().iadd(sum, addend)
                    });
                let (low, high) = builder.ins().isplit(sum);
                result[k] = Some(low);
                carry = Some(high);
            }
        }
        if let Some(carry) = carry {
            result[i + rhs.len()] = Some(carry);
        }
    }
    result.map(|limb| limb.unwrap_or_else(|| builder.ins().iconst(I64, 0)))
}

fn low_limbs(product: [clif::Value; 2 * LIMBS]) -> Limbs {
    std::array::from_fn(|limb| product[limb])
}

fn signed_min_limbs(builder: &mut FunctionBuilder) -> Limbs {
    constant_limbs(U256::one() << 255, builder)
}

fn signed_max_limbs(builder: &mut FunctionBuilder) -> Limbs {
    constant_limbs(U256::MAX >> 1, builder)
}

/// The wrapping signed product and whether it overflowed.
fn smul_overflow(lhs: Limbs, rhs: Limbs, builder: &mut FunctionBuilder) -> (Limbs, clif::Value) {
    // The wrapping product is the magnitudes' product with the sign applied.
    let lhs_negative = sign(lhs, builder);
    let rhs_negative = sign(rhs, builder);
    let negative = builder.ins().bxor(lhs_negative, rhs_negative);
    let lhs_abs = abs(lhs, builder);
    let rhs_abs = abs(rhs, builder);
    let product = mul_limbs::<{ 2 * LIMBS }>(&lhs_abs, &rhs_abs, builder);
    let high_nonzero = any_nonzero(&product[LIMBS..], builder);
    let magnitude = low_limbs(product);
    let negative_limit = signed_min_limbs(builder);
    let positive_limit = signed_max_limbs(builder);
    let limit = select(negative, negative_limit, positive_limit, builder);
    let over_limit = ult(limit, magnitude, builder);
    let overflow = builder.ins().bor(high_nonzero, over_limit);
    let negated = neg(magnitude, builder);
    (select(negative, negated, magnitude, builder), overflow)
}

/// The signed overflow of `result = lhs + rhs`: both operands have the
/// same sign, which differs from the result's.
fn sadd_overflow(
    lhs: Limbs,
    rhs: Limbs,
    result: Limbs,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    let lhs_changed = builder.ins().bxor(lhs[3], result[3]);
    let rhs_changed = builder.ins().bxor(rhs[3], result[3]);
    let both = builder.ins().band(lhs_changed, rhs_changed);
    builder.ins().icmp_imm_s(IntCC::SignedLessThan, both, 0)
}

/// The signed overflow of `result = lhs - rhs`: the operands' signs differ
/// and the result's differs from `lhs`'s.
fn ssub_overflow(
    lhs: Limbs,
    rhs: Limbs,
    result: Limbs,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    let operands_differ = builder.ins().bxor(lhs[3], rhs[3]);
    let result_changed = builder.ins().bxor(lhs[3], result[3]);
    let both = builder.ins().band(operands_differ, result_changed);
    builder.ins().icmp_imm_s(IntCC::SignedLessThan, both, 0)
}

/// The saturation bound of a signed overflow: MIN when `negative`, else MAX.
fn signed_bound(negative: clif::Value, builder: &mut FunctionBuilder) -> Limbs {
    let min = signed_min_limbs(builder);
    let max = signed_max_limbs(builder);
    select(negative, min, max, builder)
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum ShiftKind {
    Shl,
    Shr,
    Sar,
}

/// A shift amount: a constant (`None` when at least 256), or a variable
/// amount with its truncation to 64 bits and whether it is at least 256.
enum ShiftAmount {
    Constant(Option<u32>),
    Variable(clif::Value, clif::Value),
}

fn shift_amount(
    function: &Function,
    bits: ValueId,
    value_map: &ValueMap,
    builder: &mut FunctionBuilder,
) -> Result<ShiftAmount, String> {
    if let Some(imm) = function.dfg.value_imm(bits) {
        let amount = imm.zext(Type::I256).as_i256().to_u256();
        return Ok(ShiftAmount::Constant(
            (amount < U256::from(256)).then(|| amount.low_u32()),
        ));
    }
    // The verifier gives a shift amount the type of the shifted value.
    let limbs = resolve_i256(function, bits, value_map, builder)?;
    let high_nonzero = any_nonzero(&limbs[1..], builder);
    let too_large = builder
        .ins()
        .icmp_imm_s(IntCC::UnsignedGreaterThanOrEqual, limbs[0], 256);
    let too_large = builder.ins().bor(too_large, high_nonzero);
    Ok(ShiftAmount::Variable(limbs[0], too_large))
}

fn shift(
    value: Limbs,
    amount: ShiftAmount,
    kind: ShiftKind,
    builder: &mut FunctionBuilder,
) -> Limbs {
    let zero = builder.ins().iconst(I64, 0);
    let fill = match kind {
        ShiftKind::Sar => builder.ins().sshr_imm_s(value[3], 63),
        ShiftKind::Shl | ShiftKind::Shr => zero,
    };
    match amount {
        ShiftAmount::Constant(None) => [fill; LIMBS],
        ShiftAmount::Constant(Some(amount)) => {
            shift_by_constant(value, amount, kind, fill, builder)
        }
        ShiftAmount::Variable(amount, too_large) => {
            let shifted = shift_by_variable(value, amount, kind, fill, builder);
            std::array::from_fn(|limb| builder.ins().select(too_large, fill, shifted[limb]))
        }
    }
}

/// Shifts by `amount < 256` known at translation time: limb moves and
/// constant funnel shifts.
fn shift_by_constant(
    value: Limbs,
    amount: u32,
    kind: ShiftKind,
    fill: clif::Value,
    builder: &mut FunctionBuilder,
) -> Limbs {
    let limb_shift = (amount / LIMB_BITS) as usize;
    let bits = i64::from(amount % LIMB_BITS);
    std::array::from_fn(|limb| match kind {
        ShiftKind::Shl => {
            let Some(source) = limb.checked_sub(limb_shift) else {
                return fill;
            };
            if bits == 0 {
                return value[source];
            }
            let high = builder.ins().ishl_imm_s(value[source], bits);
            match source.checked_sub(1) {
                Some(below) => {
                    let low = builder
                        .ins()
                        .ushr_imm_s(value[below], i64::from(LIMB_BITS) - bits);
                    builder.ins().bor(high, low)
                }
                None => high,
            }
        }
        ShiftKind::Shr | ShiftKind::Sar => {
            let source = limb + limb_shift;
            if source >= LIMBS {
                return fill;
            }
            if bits == 0 {
                return value[source];
            }
            if source == LIMBS - 1 {
                return match kind {
                    ShiftKind::Sar => builder.ins().sshr_imm_s(value[source], bits),
                    _ => builder.ins().ushr_imm_s(value[source], bits),
                };
            }
            let low = builder.ins().ushr_imm_s(value[source], bits);
            let high = builder
                .ins()
                .ishl_imm_s(value[source + 1], i64::from(LIMB_BITS) - bits);
            builder.ins().bor(low, high)
        }
    })
}

/// Shifts by a variable amount below 256 (callers handle larger amounts):
/// a funnel shift of every limb by `amount % 64`, then limb moves by one
/// and two places selected from the amount's bits 6 and 7.
pub(super) fn shift_by_variable(
    value: Limbs,
    amount: clif::Value,
    kind: ShiftKind,
    fill: clif::Value,
    builder: &mut FunctionBuilder,
) -> Limbs {
    let bits = builder.ins().band_imm_s(amount, 63);
    // `x >> (64 - bits)` as `(x >> 1) >> (63 - bits)`, which is zero for
    // `bits == 0`, and likewise for left shifts.
    let inverse = builder.ins().bxor_imm_s(bits, 63);
    let funnel: Limbs = std::array::from_fn(|limb| match kind {
        ShiftKind::Shl => {
            let high = builder.ins().ishl(value[limb], bits);
            if limb == 0 {
                return high;
            }
            let low = builder.ins().ushr_imm_s(value[limb - 1], 1);
            let low = builder.ins().ushr(low, inverse);
            builder.ins().bor(high, low)
        }
        ShiftKind::Shr | ShiftKind::Sar => {
            if limb == LIMBS - 1 {
                return match kind {
                    ShiftKind::Sar => builder.ins().sshr(value[limb], bits),
                    _ => builder.ins().ushr(value[limb], bits),
                };
            }
            let low = builder.ins().ushr(value[limb], bits);
            let high = builder.ins().ishl_imm_s(value[limb + 1], 1);
            let high = builder.ins().ishl(high, inverse);
            builder.ins().bor(low, high)
        }
    });
    let limb_shift = builder.ins().ushr_imm_s(amount, 6);
    [1, 2].into_iter().fold(funnel, |limbs, places| {
        let moves = builder.ins().band_imm_s(limb_shift, places as i64);
        std::array::from_fn(|limb| {
            let moved = match kind {
                ShiftKind::Shl => limb
                    .checked_sub(places)
                    .map_or(fill, |source| limbs[source]),
                ShiftKind::Shr | ShiftKind::Sar => {
                    limbs.get(limb + places).copied().unwrap_or(fill)
                }
            };
            builder.ins().select(moves, moved, limbs[limb])
        })
    })
}

/// Translates `inst` if it is an integer operation on i256 operands other
/// than division and modular arithmetic.
pub(super) fn translate_i256_op(
    function: &Function,
    inst: InstId,
    value_map: &mut ValueMap,
    builder: &mut FunctionBuilder,
) -> Result<bool, String> {
    enum Output {
        Limbs(Limbs),
        Flag(clif::Value),
        Overflowing(Limbs, clif::Value),
    }
    let dfg = &function.dfg;
    let wide = |value: &ValueId| dfg.value_ty(*value) == Type::I256;
    let binary =
        |lhs: &ValueId, rhs: &ValueId, value_map: &ValueMap, builder: &mut FunctionBuilder| {
            Ok::<_, String>((
                resolve_i256(function, *lhs, value_map, builder)?,
                resolve_i256(function, *rhs, value_map, builder)?,
            ))
        };
    let compare = |cc: IntCC,
                   lhs: &ValueId,
                   rhs: &ValueId,
                   value_map: &ValueMap,
                   builder: &mut FunctionBuilder| {
        if !wide(lhs) || !wide(rhs) {
            return Err(format!(
                "cannot compare mismatched i256 and scalar values: {:?}, {:?}",
                dfg.value_ty(*lhs),
                dfg.value_ty(*rhs)
            ));
        }
        let (lhs, rhs) = binary(lhs, rhs, value_map, builder)?;
        Ok(Output::Flag(icmp(cc, lhs, rhs, builder)))
    };
    let shift_op = |value: &ValueId,
                    bits: &ValueId,
                    kind: ShiftKind,
                    value_map: &ValueMap,
                    builder: &mut FunctionBuilder| {
        let value = resolve_i256(function, *value, value_map, builder)?;
        let amount = shift_amount(function, *bits, value_map, builder)?;
        Ok::<_, String>(Output::Limbs(shift(value, amount, kind, builder)))
    };
    let bitwise = |lhs: &ValueId,
                   rhs: &ValueId,
                   op: fn(&mut FunctionBuilder, clif::Value, clif::Value) -> clif::Value,
                   value_map: &ValueMap,
                   builder: &mut FunctionBuilder| {
        let (lhs, rhs) = binary(lhs, rhs, value_map, builder)?;
        Ok::<_, String>(Output::Limbs(std::array::from_fn(|limb| {
            op(builder, lhs[limb], rhs[limb])
        })))
    };

    let output = match native_inst_set().resolve_inst(dfg.inst(inst)) {
        NativeInstKind::Add(op) if wide(op.lhs()) => {
            let (lhs, rhs) = binary(op.lhs(), op.rhs(), value_map, builder)?;
            Output::Limbs(add(lhs, rhs, builder))
        }
        NativeInstKind::Sub(op) if wide(op.lhs()) => {
            let (lhs, rhs) = binary(op.lhs(), op.rhs(), value_map, builder)?;
            Output::Limbs(sub(lhs, rhs, builder))
        }
        NativeInstKind::Mul(op) if wide(op.lhs()) => {
            let (lhs, rhs) = binary(op.lhs(), op.rhs(), value_map, builder)?;
            Output::Limbs(mul_limbs::<LIMBS>(&lhs, &rhs, builder))
        }
        NativeInstKind::Neg(op) if wide(op.arg()) => {
            let value = resolve_i256(function, *op.arg(), value_map, builder)?;
            Output::Limbs(neg(value, builder))
        }
        NativeInstKind::Shl(op) if wide(op.value()) => {
            shift_op(op.value(), op.bits(), ShiftKind::Shl, value_map, builder)?
        }
        NativeInstKind::Shr(op) if wide(op.value()) => {
            shift_op(op.value(), op.bits(), ShiftKind::Shr, value_map, builder)?
        }
        NativeInstKind::Sar(op) if wide(op.value()) => {
            shift_op(op.value(), op.bits(), ShiftKind::Sar, value_map, builder)?
        }
        NativeInstKind::And(op) if wide(op.lhs()) => bitwise(
            op.lhs(),
            op.rhs(),
            |builder, lhs, rhs| builder.ins().band(lhs, rhs),
            value_map,
            builder,
        )?,
        NativeInstKind::Or(op) if wide(op.lhs()) => bitwise(
            op.lhs(),
            op.rhs(),
            |builder, lhs, rhs| builder.ins().bor(lhs, rhs),
            value_map,
            builder,
        )?,
        NativeInstKind::Xor(op) if wide(op.lhs()) => bitwise(
            op.lhs(),
            op.rhs(),
            |builder, lhs, rhs| builder.ins().bxor(lhs, rhs),
            value_map,
            builder,
        )?,
        NativeInstKind::Not(op) if wide(op.arg()) => {
            let value = resolve_i256(function, *op.arg(), value_map, builder)?;
            Output::Limbs(value.map(|limb| builder.ins().bnot(limb)))
        }
        // Reversing all 32 bytes reverses the limb order and the bytes
        // within each limb.
        NativeInstKind::Bswap(op) if wide(op.arg()) => {
            let value = resolve_i256(function, *op.arg(), value_map, builder)?;
            Output::Limbs(std::array::from_fn(|limb| {
                builder.ins().bswap(value[LIMBS - 1 - limb])
            }))
        }
        NativeInstKind::Lt(op) if wide(op.lhs()) || wide(op.rhs()) => compare(
            IntCC::UnsignedLessThan,
            op.lhs(),
            op.rhs(),
            value_map,
            builder,
        )?,
        NativeInstKind::Gt(op) if wide(op.lhs()) || wide(op.rhs()) => compare(
            IntCC::UnsignedGreaterThan,
            op.lhs(),
            op.rhs(),
            value_map,
            builder,
        )?,
        NativeInstKind::Le(op) if wide(op.lhs()) || wide(op.rhs()) => compare(
            IntCC::UnsignedLessThanOrEqual,
            op.lhs(),
            op.rhs(),
            value_map,
            builder,
        )?,
        NativeInstKind::Ge(op) if wide(op.lhs()) || wide(op.rhs()) => compare(
            IntCC::UnsignedGreaterThanOrEqual,
            op.lhs(),
            op.rhs(),
            value_map,
            builder,
        )?,
        NativeInstKind::Slt(op) if wide(op.lhs()) || wide(op.rhs()) => compare(
            IntCC::SignedLessThan,
            op.lhs(),
            op.rhs(),
            value_map,
            builder,
        )?,
        NativeInstKind::Sgt(op) if wide(op.lhs()) || wide(op.rhs()) => compare(
            IntCC::SignedGreaterThan,
            op.lhs(),
            op.rhs(),
            value_map,
            builder,
        )?,
        NativeInstKind::Sle(op) if wide(op.lhs()) || wide(op.rhs()) => compare(
            IntCC::SignedLessThanOrEqual,
            op.lhs(),
            op.rhs(),
            value_map,
            builder,
        )?,
        NativeInstKind::Sge(op) if wide(op.lhs()) || wide(op.rhs()) => compare(
            IntCC::SignedGreaterThanOrEqual,
            op.lhs(),
            op.rhs(),
            value_map,
            builder,
        )?,
        NativeInstKind::Eq(op) if wide(op.lhs()) || wide(op.rhs()) => {
            compare(IntCC::Equal, op.lhs(), op.rhs(), value_map, builder)?
        }
        NativeInstKind::Ne(op) if wide(op.lhs()) || wide(op.rhs()) => {
            compare(IntCC::NotEqual, op.lhs(), op.rhs(), value_map, builder)?
        }
        NativeInstKind::IsZero(op) if wide(op.lhs()) => {
            let value = resolve_i256(function, *op.lhs(), value_map, builder)?;
            Output::Flag(is_zero(value, builder))
        }
        NativeInstKind::Uaddo(op) if wide(op.lhs()) => {
            let (lhs, rhs) = binary(op.lhs(), op.rhs(), value_map, builder)?;
            let (sum, carry) = add_carry(lhs, rhs, builder);
            Output::Overflowing(sum, carry)
        }
        NativeInstKind::Saddo(op) if wide(op.lhs()) => {
            let (lhs, rhs) = binary(op.lhs(), op.rhs(), value_map, builder)?;
            let sum = add(lhs, rhs, builder);
            Output::Overflowing(sum, sadd_overflow(lhs, rhs, sum, builder))
        }
        NativeInstKind::Usubo(op) if wide(op.lhs()) => {
            let (lhs, rhs) = binary(op.lhs(), op.rhs(), value_map, builder)?;
            let (difference, borrow) = sub_borrow(lhs, rhs, builder);
            Output::Overflowing(difference, borrow)
        }
        NativeInstKind::Ssubo(op) if wide(op.lhs()) => {
            let (lhs, rhs) = binary(op.lhs(), op.rhs(), value_map, builder)?;
            let difference = sub(lhs, rhs, builder);
            Output::Overflowing(difference, ssub_overflow(lhs, rhs, difference, builder))
        }
        NativeInstKind::Umulo(op) if wide(op.lhs()) => {
            let (lhs, rhs) = binary(op.lhs(), op.rhs(), value_map, builder)?;
            let product = mul_limbs::<{ 2 * LIMBS }>(&lhs, &rhs, builder);
            let overflow = any_nonzero(&product[LIMBS..], builder);
            Output::Overflowing(low_limbs(product), overflow)
        }
        NativeInstKind::Smulo(op) if wide(op.lhs()) => {
            let (lhs, rhs) = binary(op.lhs(), op.rhs(), value_map, builder)?;
            let (product, overflow) = smul_overflow(lhs, rhs, builder);
            Output::Overflowing(product, overflow)
        }
        NativeInstKind::Snego(op) if wide(op.arg()) => {
            let value = resolve_i256(function, *op.arg(), value_map, builder)?;
            let min = signed_min_limbs(builder);
            let overflow = eq(value, min, builder);
            Output::Overflowing(neg(value, builder), overflow)
        }
        NativeInstKind::Uaddsat(op) if wide(op.lhs()) => {
            let (lhs, rhs) = binary(op.lhs(), op.rhs(), value_map, builder)?;
            let (sum, carry) = add_carry(lhs, rhs, builder);
            let max = constant_limbs(U256::MAX, builder);
            Output::Limbs(select(carry, max, sum, builder))
        }
        NativeInstKind::Saddsat(op) if wide(op.lhs()) => {
            let (lhs, rhs) = binary(op.lhs(), op.rhs(), value_map, builder)?;
            let sum = add(lhs, rhs, builder);
            let overflow = sadd_overflow(lhs, rhs, sum, builder);
            let lhs_negative = sign(lhs, builder);
            let bound = signed_bound(lhs_negative, builder);
            Output::Limbs(select(overflow, bound, sum, builder))
        }
        NativeInstKind::Usubsat(op) if wide(op.lhs()) => {
            let (lhs, rhs) = binary(op.lhs(), op.rhs(), value_map, builder)?;
            let (difference, borrow) = sub_borrow(lhs, rhs, builder);
            let zero = constant_limbs(U256::zero(), builder);
            Output::Limbs(select(borrow, zero, difference, builder))
        }
        NativeInstKind::Ssubsat(op) if wide(op.lhs()) => {
            let (lhs, rhs) = binary(op.lhs(), op.rhs(), value_map, builder)?;
            let difference = sub(lhs, rhs, builder);
            let overflow = ssub_overflow(lhs, rhs, difference, builder);
            let lhs_negative = sign(lhs, builder);
            let bound = signed_bound(lhs_negative, builder);
            Output::Limbs(select(overflow, bound, difference, builder))
        }
        NativeInstKind::Umulsat(op) if wide(op.lhs()) => {
            let (lhs, rhs) = binary(op.lhs(), op.rhs(), value_map, builder)?;
            let product = mul_limbs::<{ 2 * LIMBS }>(&lhs, &rhs, builder);
            let overflow = any_nonzero(&product[LIMBS..], builder);
            let max = constant_limbs(U256::MAX, builder);
            Output::Limbs(select(overflow, max, low_limbs(product), builder))
        }
        NativeInstKind::Smulsat(op) if wide(op.lhs()) => {
            let (lhs, rhs) = binary(op.lhs(), op.rhs(), value_map, builder)?;
            let (product, overflow) = smul_overflow(lhs, rhs, builder);
            let lhs_negative = sign(lhs, builder);
            let rhs_negative = sign(rhs, builder);
            let negative = builder.ins().bxor(lhs_negative, rhs_negative);
            let bound = signed_bound(negative, builder);
            Output::Limbs(select(overflow, bound, product, builder))
        }
        _ => return Ok(false),
    };
    let results = dfg.inst_results(inst);
    match output {
        Output::Limbs(limbs) => value_map.insert_limbs(results[0], limbs),
        Output::Flag(flag) => value_map.insert(results[0], flag),
        Output::Overflowing(limbs, overflow) => {
            value_map.insert_limbs(results[0], limbs);
            value_map.insert(results[1], overflow);
        }
    }
    Ok(true)
}

/// Booleans are canonical i8 zero or one.
fn bool_not(value: clif::Value, builder: &mut FunctionBuilder) -> clif::Value {
    builder.ins().bxor_imm_s(value, 1)
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
