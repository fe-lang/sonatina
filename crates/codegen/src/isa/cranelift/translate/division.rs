//! Wide unsigned division. Each division site handles a zero divisor, a
//! smaller numerator and single-limb operands inline, and calls the
//! module's divider for everything else: Knuth's algorithm D on 64-bit
//! limbs, with quotient digits from a 128/64-bit division by reciprocal
//! (Möller and Granlund, "Improved division by invariant integers").

use cranelift_codegen::ir::{
    self as clif, AbiParam, InstBuilder, MemFlagsData, StackSlotData, StackSlotKind,
    condcodes::IntCC,
    instructions::BlockArg,
    types::{I64, I128},
};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{FuncId, Module as ClifModule};

use super::{
    DivRemKind, LIMBS, Limbs, abs, add_carry, is_zero, load_limbs, mul_limbs, neg, select, sign,
    store_limbs, sub_borrow, ult,
};

/// The divider takes one pointer to a buffer of an eight-limb numerator
/// and a four-limb divisor, which it overwrites with the quotient and the
/// remainder. The divisor must be nonzero.
const NUMERATOR_LIMBS: usize = 2 * LIMBS;
const DIVISOR_OFFSET: i32 = 8 * NUMERATOR_LIMBS as i32;
const BUFFER_BYTES: u32 = 8 * (NUMERATOR_LIMBS + LIMBS) as u32;

/// The module's out-of-line divider, declared on first use and defined
/// after the functions that call it, with the current function's
/// reference to it.
#[derive(Default)]
pub(super) struct Divider {
    id: Option<FuncId>,
    call: Option<DividerCall>,
}

/// The divider as called from one function: its reference and the stack
/// buffer for its operands and results.
#[derive(Clone, Copy)]
pub(super) struct DividerCall {
    func: clif::FuncRef,
    buffer: clif::StackSlot,
}

impl Divider {
    /// Forgets the previous function's reference to the divider.
    pub fn start_function(&mut self) {
        self.call = None;
    }

    /// The divider call for the function being built.
    pub fn call(
        &mut self,
        clif_module: &mut impl ClifModule,
        builder: &mut FunctionBuilder,
    ) -> Result<DividerCall, String> {
        if let Some(call) = self.call {
            return Ok(call);
        }
        let id = match self.id {
            Some(id) => id,
            None => {
                let signature = signature(clif_module);
                let id = clif_module
                    .declare_anonymous_function(&signature)
                    .map_err(|error| format!("failed to declare the divider: {error}"))?;
                *self.id.insert(id)
            }
        };
        let call = DividerCall {
            func: clif_module.declare_func_in_func(id, builder.func),
            buffer: builder.create_sized_stack_slot(StackSlotData::new(
                StackSlotKind::ExplicitSlot,
                BUFFER_BYTES,
                4,
            )),
        };
        self.call = Some(call);
        Ok(call)
    }

    /// Defines the divider if any function calls it.
    pub fn define(self, clif_module: &mut impl ClifModule) -> Result<(), String> {
        let Some(id) = self.id else {
            return Ok(());
        };
        let mut ctx = clif_module.make_context();
        ctx.func.signature = signature(clif_module);
        let mut builder_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_ctx);
        build_divider(&mut builder);
        builder.seal_all_blocks();
        builder.finalize(clif_module.target_config());
        if std::env::var("DUMP_CLIF").is_ok() {
            eprintln!(
                "[cranelift] CLIF IR for the divider:\n{}",
                ctx.func.display()
            );
        }
        clif_module
            .define_function(id, &mut ctx)
            .map_err(|error| format!("cranelift define_function failed for the divider: {error}"))
    }
}

fn signature(clif_module: &impl ClifModule) -> clif::Signature {
    let mut signature = clif_module.make_signature();
    signature
        .params
        .push(AbiParam::new(clif_module.target_config().pointer_type()));
    signature
}

/// The quotient and remainder of unsigned `numerator / divisor`. Division
/// by zero is undefined in the IR; here it gives an all-ones quotient and
/// the numerator as remainder.
pub(super) fn udivrem(
    numerator: Limbs,
    divisor: Limbs,
    call: DividerCall,
    builder: &mut FunctionBuilder,
) -> (Limbs, Limbs) {
    let exit = builder.create_block();
    let results: [clif::Value; 2 * LIMBS] =
        std::array::from_fn(|_| builder.append_block_param(exit, I64));
    let zero = builder.ins().iconst(I64, 0);
    let all_ones = builder.ins().iconst(I64, -1);
    let [n0, n1, n2, n3] = numerator;
    let exit_with = |quotient: Limbs, remainder: Limbs| -> Vec<BlockArg> {
        quotient
            .into_iter()
            .chain(remainder)
            .map(BlockArg::Value)
            .collect()
    };

    let nonzero = builder.create_block();
    let divisor_zero = is_zero(divisor, builder);
    builder.ins().brif(
        divisor_zero,
        exit,
        &exit_with([all_ones; LIMBS], numerator),
        nonzero,
        &[],
    );
    builder.switch_to_block(nonzero);
    let not_smaller = builder.create_block();
    let smaller = ult(numerator, divisor, builder);
    builder.ins().brif(
        smaller,
        exit,
        &exit_with([zero; LIMBS], numerator),
        not_smaller,
        &[],
    );
    builder.switch_to_block(not_smaller);
    let scalar = builder.create_block();
    let wide = builder.create_block();
    let high = [n1, n2, n3, divisor[1], divisor[2], divisor[3]]
        .into_iter()
        .reduce(|high, limb| builder.ins().bor(high, limb))
        .unwrap();
    builder.ins().brif(high, wide, &[], scalar, &[]);

    builder.switch_to_block(scalar);
    let quotient = builder.ins().udiv(n0, divisor[0]);
    let product = builder.ins().imul(quotient, divisor[0]);
    let remainder = builder.ins().isub(n0, product);
    builder.ins().jump(
        exit,
        &exit_with([quotient, zero, zero, zero], [remainder, zero, zero, zero]),
    );

    builder.switch_to_block(wide);
    let buffer = call_divider(&numerator, divisor, call, builder);
    let quotient = load_limbs(buffer, 0, MemFlagsData::trusted(), builder);
    let remainder = load_limbs(buffer, DIVISOR_OFFSET, MemFlagsData::trusted(), builder);
    builder.ins().jump(exit, &exit_with(quotient, remainder));

    builder.switch_to_block(exit);
    let [q0, q1, q2, q3, r0, r1, r2, r3] = results;
    ([q0, q1, q2, q3], [r0, r1, r2, r3])
}

/// Divides i256 operands. Signed division divides magnitudes: the quotient
/// is negative when the operands' signs differ and the remainder takes the
/// dividend's sign, so `MIN / -1` wraps to `MIN`.
pub(super) fn div_rem(
    kind: DivRemKind,
    lhs: Limbs,
    rhs: Limbs,
    call: DividerCall,
    builder: &mut FunctionBuilder,
) -> Limbs {
    match kind {
        DivRemKind::Udiv => udivrem(lhs, rhs, call, builder).0,
        DivRemKind::Umod => udivrem(lhs, rhs, call, builder).1,
        DivRemKind::Sdiv | DivRemKind::Smod => {
            let lhs_negative = sign(lhs, builder);
            let rhs_negative = sign(rhs, builder);
            let lhs_abs = abs(lhs, builder);
            let rhs_abs = abs(rhs, builder);
            let (quotient, remainder) = udivrem(lhs_abs, rhs_abs, call, builder);
            let (magnitude, negative) = match kind {
                DivRemKind::Sdiv => (quotient, builder.ins().bxor(lhs_negative, rhs_negative)),
                _ => (remainder, lhs_negative),
            };
            let negated = neg(magnitude, builder);
            select(negative, negated, magnitude, builder)
        }
    }
}

/// Divides up to eight numerator limbs by a nonzero divisor and returns
/// the address of the quotient, followed by the remainder at
/// `DIVISOR_OFFSET`.
fn call_divider(
    numerator: &[clif::Value],
    divisor: Limbs,
    call: DividerCall,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    let flags = MemFlagsData::trusted();
    let buffer = builder.ins().stack_addr(I64, call.buffer, 0);
    let zero = builder.ins().iconst(I64, 0);
    for (limb, &value) in numerator
        .iter()
        .chain(std::iter::repeat_n(
            &zero,
            NUMERATOR_LIMBS - numerator.len(),
        ))
        .enumerate()
    {
        builder.ins().store(flags, value, buffer, 8 * limb as i32);
    }
    store_limbs(divisor, buffer, DIVISOR_OFFSET, flags, builder);
    builder.ins().call(call.func, &[buffer]);
    buffer
}

fn remainder(
    numerator: &[clif::Value],
    modulus: Limbs,
    call: DividerCall,
    builder: &mut FunctionBuilder,
) -> Limbs {
    let buffer = call_divider(numerator, modulus, call, builder);
    load_limbs(buffer, DIVISOR_OFFSET, MemFlagsData::trusted(), builder)
}

/// Branches to a block that returns zero for a zero modulus and switches
/// to one for a nonzero modulus. Returns the exit block's limbs.
fn zero_modulus_exit(modulus: Limbs, builder: &mut FunctionBuilder) -> (clif::Block, Limbs) {
    let exit = builder.create_block();
    let results = std::array::from_fn(|_| builder.append_block_param(exit, I64));
    let nonzero = builder.create_block();
    let modulus_zero = is_zero(modulus, builder);
    let zero = builder.ins().iconst(I64, 0);
    builder.ins().brif(
        modulus_zero,
        exit,
        &[BlockArg::Value(zero); LIMBS],
        nonzero,
        &[],
    );
    builder.switch_to_block(nonzero);
    (exit, results)
}

/// `(lhs + rhs) % modulus` at full precision; a zero modulus gives zero.
pub(super) fn addmod(
    lhs: Limbs,
    rhs: Limbs,
    modulus: Limbs,
    call: DividerCall,
    builder: &mut FunctionBuilder,
) -> Limbs {
    let (exit, results) = zero_modulus_exit(modulus, builder);
    let (sum, carry) = add_carry(lhs, rhs, builder);
    // With both operands reduced, the sum is below twice the modulus.
    let lhs_reduced = ult(lhs, modulus, builder);
    let rhs_reduced = ult(rhs, modulus, builder);
    let reduced = builder.ins().band(lhs_reduced, rhs_reduced);
    let subtract = builder.create_block();
    let divide = builder.create_block();
    builder.ins().brif(reduced, subtract, &[], divide, &[]);

    builder.switch_to_block(subtract);
    let (difference, borrow) = sub_borrow(sum, modulus, builder);
    let below = builder.ins().bxor_imm_s(carry, 1);
    let below = builder.ins().band(below, borrow);
    let result = select(below, sum, difference, builder);
    builder.ins().jump(exit, &result.map(BlockArg::Value));

    builder.switch_to_block(divide);
    let carry = builder.ins().uextend(I64, carry);
    let [s0, s1, s2, s3] = sum;
    let result = remainder(&[s0, s1, s2, s3, carry], modulus, call, builder);
    builder.ins().jump(exit, &result.map(BlockArg::Value));

    builder.switch_to_block(exit);
    results
}

/// `(lhs * rhs) % modulus` at full precision; a zero modulus gives zero.
pub(super) fn mulmod(
    lhs: Limbs,
    rhs: Limbs,
    modulus: Limbs,
    call: DividerCall,
    builder: &mut FunctionBuilder,
) -> Limbs {
    let (exit, results) = zero_modulus_exit(modulus, builder);
    let product = mul_limbs::<NUMERATOR_LIMBS>(&lhs, &rhs, builder);
    let result = remainder(&product, modulus, call, builder);
    builder.ins().jump(exit, &result.map(BlockArg::Value));
    builder.switch_to_block(exit);
    results
}

/// Divides i128 operands, trapping on a zero divisor like Cranelift's
/// narrower divisions.
pub(super) fn div_rem_i128(
    kind: DivRemKind,
    lhs: clif::Value,
    rhs: clif::Value,
    call: DividerCall,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    let rhs_zero = builder.ins().icmp_imm_s(IntCC::Equal, rhs, 0);
    builder
        .ins()
        .trapnz(rhs_zero, clif::TrapCode::INTEGER_DIVISION_BY_ZERO);
    let remainder = matches!(kind, DivRemKind::Umod | DivRemKind::Smod);
    let (numerator, denominator, negative) = if matches!(kind, DivRemKind::Sdiv | DivRemKind::Smod)
    {
        let lhs_negative = builder.ins().icmp_imm_s(IntCC::SignedLessThan, lhs, 0);
        let rhs_negative = builder.ins().icmp_imm_s(IntCC::SignedLessThan, rhs, 0);
        // The remainder takes the dividend's sign, the quotient the
        // product of both signs.
        let negative = if remainder {
            lhs_negative
        } else {
            builder.ins().bxor(lhs_negative, rhs_negative)
        };
        let lhs_negated = builder.ins().ineg(lhs);
        let rhs_negated = builder.ins().ineg(rhs);
        (
            builder.ins().select(lhs_negative, lhs_negated, lhs),
            builder.ins().select(rhs_negative, rhs_negated, rhs),
            Some(negative),
        )
    } else {
        (lhs, rhs, None)
    };
    let zero = builder.ins().iconst(I64, 0);
    let (lhs_low, lhs_high) = builder.ins().isplit(numerator);
    let (rhs_low, rhs_high) = builder.ins().isplit(denominator);
    let (quotient, modulus) = udivrem(
        [lhs_low, lhs_high, zero, zero],
        [rhs_low, rhs_high, zero, zero],
        call,
        builder,
    );
    let limbs = if remainder { modulus } else { quotient };
    let result = builder.ins().iconcat(limbs[0], limbs[1]);
    match negative {
        Some(negative) => {
            let negated = builder.ins().ineg(result);
            builder.ins().select(negative, negated, result)
        }
        None => result,
    }
}

/// The base-2^64 quotient digit and remainder of `(high, low) / divisor`
/// for a normalized divisor and `high < divisor`, given the divisor's
/// reciprocal (Möller and Granlund, algorithm 4).
fn div2by1(
    high: clif::Value,
    low: clif::Value,
    divisor: clif::Value,
    reciprocal: clif::Value,
    builder: &mut FunctionBuilder,
) -> (clif::Value, clif::Value) {
    let reciprocal_wide = builder.ins().uextend(I128, reciprocal);
    let high_wide = builder.ins().uextend(I128, high);
    let product = builder.ins().imul(reciprocal_wide, high_wide);
    let numerator = builder.ins().iconcat(low, high);
    let estimate = builder.ins().iadd(product, numerator);
    let (fraction, quotient) = builder.ins().isplit(estimate);
    let quotient = builder.ins().iadd_imm_s(quotient, 1);
    let product = builder.ins().imul(quotient, divisor);
    let remainder = builder.ins().isub(low, product);
    let over = builder
        .ins()
        .icmp(IntCC::UnsignedGreaterThan, remainder, fraction);
    let decremented = builder.ins().iadd_imm_s(quotient, -1);
    let quotient = builder.ins().select(over, decremented, quotient);
    let restored = builder.ins().iadd(remainder, divisor);
    let remainder = builder.ins().select(over, restored, remainder);
    let excess = builder
        .ins()
        .icmp(IntCC::UnsignedGreaterThanOrEqual, remainder, divisor);
    let incremented = builder.ins().iadd_imm_s(quotient, 1);
    let quotient = builder.ins().select(excess, incremented, quotient);
    let reduced = builder.ins().isub(remainder, divisor);
    let remainder = builder.ins().select(excess, reduced, remainder);
    (quotient, remainder)
}

/// `floor((2^128 - 1) / divisor) - 2^64` for a normalized divisor: the
/// quotient of `(!divisor, 2^64 - 1) / divisor`, by two base-2^32 digits
/// from 64-bit divisions (Hacker's Delight, `divlu`).
fn reciprocal(divisor: clif::Value, builder: &mut FunctionBuilder) -> clif::Value {
    let divisor_high = builder.ins().ushr_imm_s(divisor, 32);
    let divisor_low = builder.ins().band_imm_s(divisor, 0xffff_ffff);
    // The numerator's low word is all ones, so both of its 32-bit digits
    // are `0xffff_ffff`.
    let ones = builder.ins().iconst(I64, 0xffff_ffff);
    // Knuth's estimate of the digit of `(high * 2^32 + next) / divisor`
    // exceeds it by at most two; each correction step fixes one.
    let digit = |high, builder: &mut FunctionBuilder| {
        let quotient = builder.ins().udiv(high, divisor_high);
        let product = builder.ins().imul(quotient, divisor_high);
        let remainder = builder.ins().isub(high, product);
        let correct = |quotient, remainder, builder: &mut FunctionBuilder| {
            let too_wide =
                builder
                    .ins()
                    .icmp_imm_s(IntCC::UnsignedGreaterThanOrEqual, quotient, 1 << 32);
            let estimate = builder.ins().imul(quotient, divisor_low);
            let shifted = builder.ins().ishl_imm_s(remainder, 32);
            let bound = builder.ins().bor(shifted, ones);
            let too_large = builder
                .ins()
                .icmp(IntCC::UnsignedGreaterThan, estimate, bound);
            let wrong = builder.ins().bor(too_wide, too_large);
            // A remainder of at least 2^32 proves the digit right.
            let checked = builder
                .ins()
                .icmp_imm_s(IntCC::UnsignedLessThan, remainder, 1 << 32);
            let decrement = builder.ins().band(wrong, checked);
            let decremented = builder.ins().iadd_imm_s(quotient, -1);
            let increased = builder.ins().iadd(remainder, divisor_high);
            (
                builder.ins().select(decrement, decremented, quotient),
                builder.ins().select(decrement, increased, remainder),
            )
        };
        let (quotient, remainder) = correct(quotient, remainder, builder);
        correct(quotient, remainder, builder).0
    };
    let high = builder.ins().bnot(divisor);
    let first = digit(high, builder);
    let shifted = builder.ins().ishl_imm_s(high, 32);
    let partial = builder.ins().bor(shifted, ones);
    let product = builder.ins().imul(first, divisor);
    let partial = builder.ins().isub(partial, product);
    let second = digit(partial, builder);
    let first = builder.ins().ishl_imm_s(first, 32);
    builder.ins().bor(first, second)
}

/// The address of limb `index` of the limb array at `base`.
fn limb_address(
    base: clif::Value,
    index: clif::Value,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    let offset = builder.ins().ishl_imm_s(index, 3);
    builder.ins().iadd(base, offset)
}

/// The divider's operands after normalization by `shift`, the left shift
/// that sets the divisor's top bit.
struct Normalized {
    buffer: clif::Value,
    /// The numerator's nine normalized limbs in memory.
    numerator: clif::Value,
    /// The number of significant numerator limbs.
    numerator_limbs: clif::Value,
    divisor: Limbs,
    reciprocal: clif::Value,
    shift: clif::Value,
    inverse: clif::Value,
}

/// Emits the divider's body (see `Divider`).
fn build_divider(builder: &mut FunctionBuilder) {
    let flags = MemFlagsData::trusted();
    let entry = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.switch_to_block(entry);
    let buffer = builder.block_params(entry)[0];
    let numerator: [clif::Value; NUMERATOR_LIMBS] =
        std::array::from_fn(|limb| builder.ins().load(I64, flags, buffer, 8 * limb as i32));
    let divisor = load_limbs(buffer, DIVISOR_OFFSET, flags, builder);

    // `n` divisor and `m` numerator limbs are significant. Each select
    // chain ends at the highest nonzero limb.
    let count = |limbs: &[clif::Value], first: i64, builder: &mut FunctionBuilder| {
        let initial = builder.ins().iconst(I64, first);
        limbs
            .iter()
            .enumerate()
            .skip(first as usize)
            .fold(initial, |count, (index, &limb)| {
                let nonzero = builder.ins().icmp_imm_s(IntCC::NotEqual, limb, 0);
                let index = builder.ins().iconst(I64, index as i64 + 1);
                builder.ins().select(nonzero, index, count)
            })
    };
    let n = count(&divisor, 1, builder);
    let m = count(&numerator, 0, builder);
    let zero = builder.ins().iconst(I64, 0);
    // Quotient digits above the computed ones are zero.
    store_limbs([zero; LIMBS], buffer, 0, flags, builder);
    store_limbs([zero; LIMBS], buffer, 8 * LIMBS as i32, flags, builder);
    // A numerator smaller than the divisor is the remainder.
    let smaller = builder.create_block();
    let divide = builder.create_block();
    let below = builder.ins().icmp(IntCC::UnsignedLessThan, m, n);
    builder.ins().brif(below, smaller, &[], divide, &[]);
    builder.switch_to_block(smaller);
    store_limbs(
        std::array::from_fn(|limb| numerator[limb]),
        buffer,
        DIVISOR_OFFSET,
        flags,
        builder,
    );
    builder.ins().return_(&[]);

    builder.switch_to_block(divide);
    let top = divisor[1..].iter().fold(divisor[0], |top, &limb| {
        let nonzero = builder.ins().icmp_imm_s(IntCC::NotEqual, limb, 0);
        builder.ins().select(nonzero, limb, top)
    });
    let shift = builder.ins().clz(top);
    let inverse = builder.ins().bxor_imm_s(shift, 63);
    // `(high << shift) | (low >> (64 - shift))`, also for a zero shift.
    let funnel = |high, low, builder: &mut FunctionBuilder| {
        let high = builder.ins().ishl(high, shift);
        let low = builder.ins().ushr_imm_s(low, 1);
        let low = builder.ins().ushr(low, inverse);
        builder.ins().bor(high, low)
    };
    let normalized_divisor: Limbs = std::array::from_fn(|limb| match limb {
        0 => builder.ins().ishl(divisor[0], shift),
        _ => funnel(divisor[limb], divisor[limb - 1], builder),
    });
    let normalized_numerator: [clif::Value; NUMERATOR_LIMBS + 1] =
        std::array::from_fn(|limb| match limb {
            0 => builder.ins().ishl(numerator[0], shift),
            _ => {
                let high = numerator.get(limb).copied().unwrap_or(zero);
                funnel(high, numerator[limb - 1], builder)
            }
        });
    let slot = builder.create_sized_stack_slot(StackSlotData::new(
        StackSlotKind::ExplicitSlot,
        8 * (NUMERATOR_LIMBS as u32 + 1),
        3,
    ));
    let normalized = builder.ins().stack_addr(I64, slot, 0);
    for (limb, &value) in normalized_numerator.iter().enumerate() {
        builder
            .ins()
            .store(flags, value, normalized, 8 * limb as i32);
    }
    // The normalized divisor's top limb, whose reciprocal every digit uses.
    let top = normalized_divisor.iter().zip(&divisor).skip(1).fold(
        normalized_divisor[0],
        |top, (&normalized, &limb)| {
            let nonzero = builder.ins().icmp_imm_s(IntCC::NotEqual, limb, 0);
            builder.ins().select(nonzero, normalized, top)
        },
    );
    let operands = Normalized {
        buffer,
        numerator: normalized,
        numerator_limbs: m,
        divisor: normalized_divisor,
        reciprocal: reciprocal(top, builder),
        shift,
        inverse,
    };
    // One digit loop per divisor length.
    for limbs in 1..LIMBS {
        let this = builder.create_block();
        let other = builder.create_block();
        let matches = builder.ins().icmp_imm_s(IntCC::Equal, n, limbs as i64);
        builder.ins().brif(matches, this, &[], other, &[]);
        builder.switch_to_block(this);
        emit_digit_loop(limbs, &operands, builder);
        builder.switch_to_block(other);
    }
    emit_digit_loop(LIMBS, &operands, builder);
}

/// Emits Knuth's algorithm D for a divisor of exactly `n` limbs: quotient
/// digits `j` from `m - n` down to zero, each from the window of the
/// numerator limb `j` below the `n`-limb partial remainder.
fn emit_digit_loop(n: usize, operands: &Normalized, builder: &mut FunctionBuilder) {
    let flags = MemFlagsData::trusted();
    let divisor = &operands.divisor[..n];
    let divisor_top = divisor[n - 1];
    let head = builder.create_block();
    let done = builder.create_block();
    let j = builder.append_block_param(head, I64);
    let remainder: Vec<_> = (0..n)
        .map(|_| builder.append_block_param(head, I64))
        .collect();
    let final_remainder: Vec<_> = (0..n)
        .map(|_| builder.append_block_param(done, I64))
        .collect();
    // The first partial remainder is the numerator's top `n` limbs, up to
    // the normalization's overflow limb.
    let first = builder
        .ins()
        .iadd_imm_s(operands.numerator_limbs, -(n as i64));
    let address = limb_address(operands.numerator, first, builder);
    let initial: Vec<_> = (1..=n)
        .map(|limb| BlockArg::Value(builder.ins().load(I64, flags, address, 8 * limb as i32)))
        .collect();
    builder.ins().jump(
        head,
        &[BlockArg::Value(first)]
            .into_iter()
            .chain(initial)
            .collect::<Vec<_>>(),
    );

    builder.switch_to_block(head);
    let address = limb_address(operands.numerator, j, builder);
    let low = builder.ins().load(I64, flags, address, 0);
    let window: Vec<_> = std::iter::once(low)
        .chain(remainder.iter().copied())
        .collect();
    let join = builder.create_block();
    let digit_param = builder.append_block_param(join, I64);
    let next_remainder: Vec<_> = (0..n)
        .map(|_| builder.append_block_param(join, I64))
        .collect();
    if n == 1 {
        let (digit, remainder) = div2by1(
            window[1],
            window[0],
            divisor_top,
            operands.reciprocal,
            builder,
        );
        builder
            .ins()
            .jump(join, &[digit, remainder].map(BlockArg::Value));
    } else {
        let (u2, u1, u0) = (window[n], window[n - 1], window[n - 2]);
        let zero = builder.ins().iconst(I64, 0);
        // The remainder's top limb never exceeds the divisor's; when they
        // are equal the estimate is the largest digit.
        let equal = builder
            .ins()
            .icmp(IntCC::UnsignedGreaterThanOrEqual, u2, divisor_top);
        let high = builder.ins().select(equal, zero, u2);
        let (estimate, estimate_remainder) =
            div2by1(high, u1, divisor_top, operands.reciprocal, builder);
        let (sum, sum_overflow) = builder.ins().uadd_overflow(u1, divisor_top);
        let all_ones = builder.ins().iconst(I64, -1);
        let digit = builder.ins().select(equal, all_ones, estimate);
        let rhat = builder.ins().select(equal, sum, estimate_remainder);
        let rhat_wide = builder.ins().band(equal, sum_overflow);
        // The estimate exceeds the digit by at most two. Knuth's test
        // against the second divisor limb lowers it while it is provably
        // too large (only while the partial remainder fits a limb): the
        // first step leaves at most one excess, which adding back the
        // divisor fixes, and the second makes that rare.
        let divisor_second = builder.ins().uextend(I128, divisor[n - 2]);
        let correct = |digit, rhat, rhat_wide, builder: &mut FunctionBuilder| {
            let digit_wide = builder.ins().uextend(I128, digit);
            let product = builder.ins().imul(digit_wide, divisor_second);
            let bound = builder.ins().iconcat(u0, rhat);
            let too_large = builder
                .ins()
                .icmp(IntCC::UnsignedGreaterThan, product, bound);
            let narrow = builder.ins().bxor_imm_s(rhat_wide, 1);
            let decrement = builder.ins().band(too_large, narrow);
            let decremented = builder.ins().iadd_imm_s(digit, -1);
            let (increased, overflow) = builder.ins().uadd_overflow(rhat, divisor_top);
            let overflow = builder.ins().band(decrement, overflow);
            (
                builder.ins().select(decrement, decremented, digit),
                builder.ins().select(decrement, increased, rhat),
                builder.ins().bor(rhat_wide, overflow),
            )
        };
        let (digit, rhat, rhat_wide) = correct(digit, rhat, rhat_wide, builder);
        let (digit, _, _) = correct(digit, rhat, rhat_wide, builder);

        // Subtract `digit * divisor` from the window.
        let digit_wide = builder.ins().uextend(I128, digit);
        let mut carry = zero;
        let mut borrow = zero;
        let mut difference = Vec::with_capacity(n);
        for (&limb, &divisor_limb) in window.iter().zip(divisor) {
            let divisor_limb = builder.ins().uextend(I128, divisor_limb);
            let product = builder.ins().imul(digit_wide, divisor_limb);
            let carry_wide = builder.ins().uextend(I128, carry);
            let product = builder.ins().iadd(product, carry_wide);
            let (product_low, product_high) = builder.ins().isplit(product);
            let (limb, borrow_low) = builder.ins().usub_overflow(limb, product_low);
            let (limb, borrow_in) = builder.ins().usub_overflow(limb, borrow);
            difference.push(limb);
            let borrow_out = builder.ins().bor(borrow_low, borrow_in);
            borrow = builder.ins().uextend(I64, borrow_out);
            carry = product_high;
        }
        let (top, borrow_low) = builder.ins().usub_overflow(u2, carry);
        let (_, borrow_in) = builder.ins().usub_overflow(top, borrow);
        let negative = builder.ins().bor(borrow_low, borrow_in);
        let add_back = builder.create_block();
        builder.ins().brif(
            negative,
            add_back,
            &[],
            join,
            &std::iter::once(digit)
                .chain(difference.iter().copied())
                .map(BlockArg::Value)
                .collect::<Vec<_>>(),
        );

        // The digit was one too large: add the divisor back. The carry
        // out clears the window's top limb.
        builder.switch_to_block(add_back);
        let mut carry = zero;
        let mut sum = Vec::with_capacity(n);
        for (&limb, &divisor_limb) in difference.iter().zip(divisor) {
            let (limb, carry_low) = builder.ins().uadd_overflow(limb, divisor_limb);
            let (limb, carry_in) = builder.ins().uadd_overflow(limb, carry);
            sum.push(limb);
            let carry_out = builder.ins().bor(carry_low, carry_in);
            carry = builder.ins().uextend(I64, carry_out);
        }
        let decremented = builder.ins().iadd_imm_s(digit, -1);
        builder.ins().jump(
            join,
            &std::iter::once(decremented)
                .chain(sum)
                .map(BlockArg::Value)
                .collect::<Vec<_>>(),
        );
    }

    builder.switch_to_block(join);
    let address = limb_address(operands.buffer, j, builder);
    builder.ins().store(flags, digit_param, address, 0);
    let previous = builder.ins().iadd_imm_s(j, -1);
    let next_args: Vec<_> = next_remainder
        .iter()
        .copied()
        .map(BlockArg::Value)
        .collect();
    builder.ins().brif(
        j,
        head,
        &std::iter::once(BlockArg::Value(previous))
            .chain(next_args.iter().copied())
            .collect::<Vec<_>>(),
        done,
        &next_args,
    );

    // Undo the normalization of the remainder.
    builder.switch_to_block(done);
    let zero = builder.ins().iconst(I64, 0);
    let remainder: Limbs = std::array::from_fn(|limb| {
        let Some(&low) = final_remainder.get(limb) else {
            return zero;
        };
        let low = builder.ins().ushr(low, operands.shift);
        let Some(&high) = final_remainder.get(limb + 1) else {
            return low;
        };
        let high = builder.ins().ishl_imm_s(high, 1);
        let high = builder.ins().ishl(high, operands.inverse);
        builder.ins().bor(low, high)
    });
    store_limbs(remainder, operands.buffer, DIVISOR_OFFSET, flags, builder);
    builder.ins().return_(&[]);
}
