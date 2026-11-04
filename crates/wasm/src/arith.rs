//! Lowering of Sonatina's integer operations to WebAssembly operators.
//!
//! # Representation
//!
//! `i1`, `i8`, `i16` and `i32` values use WebAssembly's `i32`, and `i64`
//! values use `i64`. A narrow integer is always kept in canonical form: the
//! value is zero-extended and the bits above its width are zero. Every
//! lowering below assumes canonical operands and returns a canonical result.
//! Signed operations sign-extend their operands first and re-canonicalize the
//! result.

use waffle::{FunctionBody, Operator, Type as WType};

use sonatina_ir::Type;

/// The integer types the backend lowers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Int {
    I1,
    I8,
    I16,
    I32,
    I64,
}

impl Int {
    pub(super) fn from_type(ty: Type) -> Option<Self> {
        match ty {
            Type::I1 => Some(Self::I1),
            Type::I8 => Some(Self::I8),
            Type::I16 => Some(Self::I16),
            Type::I32 => Some(Self::I32),
            Type::I64 => Some(Self::I64),
            _ => None,
        }
    }

    pub(super) fn bits(self) -> u32 {
        match self {
            Self::I1 => 1,
            Self::I8 => 8,
            Self::I16 => 16,
            Self::I32 => 32,
            Self::I64 => 64,
        }
    }

    pub(super) fn is_wide(self) -> bool {
        self == Self::I64
    }

    pub(super) fn carrier(self) -> WType {
        if self.is_wide() {
            WType::I64
        } else {
            WType::I32
        }
    }

    fn is_narrow(self) -> bool {
        self.bits() < 32
    }

    /// All bits of the type set, as an unsigned value.
    fn all_ones(self) -> u64 {
        if self.bits() == 64 {
            u64::MAX
        } else {
            (1u64 << self.bits()) - 1
        }
    }

    /// The minimum signed value, as a canonical unsigned value.
    fn signed_min(self) -> u64 {
        1u64 << (self.bits() - 1)
    }

    /// The maximum signed value, as a canonical unsigned value.
    fn signed_max(self) -> u64 {
        self.signed_min() - 1
    }
}

#[derive(Clone, Copy, Debug)]
pub(super) enum Arith {
    Add,
    Sub,
    Mul,
}

#[derive(Clone, Copy, Debug)]
pub(super) enum Shift {
    Shl,
    Shr,
    Sar,
}

#[derive(Clone, Copy, Debug)]
pub(super) enum DivRem {
    Udiv,
    Sdiv,
    Umod,
    Smod,
}

#[derive(Clone, Copy, Debug)]
pub(super) enum Cmp {
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,
}

/// Appends operators to one WAFFLE block.
pub(super) struct Emit<'a> {
    pub(super) body: &'a mut FunctionBody,
    pub(super) block: waffle::Block,
}

type V = waffle::Value;

impl Emit<'_> {
    pub(super) fn op(&mut self, op: Operator, args: &[V], ty: WType) -> V {
        self.body.add_op(self.block, op, args, &[ty])
    }

    pub(super) fn c32(&mut self, value: u32) -> V {
        self.op(Operator::I32Const { value }, &[], WType::I32)
    }

    pub(super) fn c64(&mut self, value: u64) -> V {
        self.op(Operator::I64Const { value }, &[], WType::I64)
    }

    /// A constant of the carrier type of `int`. Only the bits of `int` are used.
    fn constant(&mut self, int: Int, value: u64) -> V {
        if int.is_wide() {
            self.c64(value)
        } else {
            self.c32(value as u32)
        }
    }

    pub(super) fn zero(&mut self, int: Int) -> V {
        self.constant(int, 0)
    }

    /// `if cond { a } else { b }` on values of the carrier of `int`.
    fn select(&mut self, int: Int, a: V, b: V, cond: V) -> V {
        self.op(Operator::Select, &[a, b, cond], int.carrier())
    }

    fn pick(&mut self, int: Int, narrow: Operator, wide: Operator, args: &[V]) -> V {
        let op = if int.is_wide() { wide } else { narrow };
        self.op(op, args, int.carrier())
    }

    fn pick_cmp(&mut self, int: Int, narrow: Operator, wide: Operator, args: &[V]) -> V {
        let op = if int.is_wide() { wide } else { narrow };
        self.op(op, args, WType::I32)
    }

    /// Clear the bits above the width of a narrow integer.
    pub(super) fn canonicalize(&mut self, int: Int, value: V) -> V {
        if int.is_narrow() {
            let mask = self.c32(int.all_ones() as u32);
            self.op(Operator::I32And, &[value, mask], WType::I32)
        } else {
            value
        }
    }

    /// Sign-extend a canonical value to its full carrier.
    fn sign_extend(&mut self, int: Int, value: V) -> V {
        match int {
            Int::I1 => {
                let zero = self.c32(0);
                self.op(Operator::I32Sub, &[zero, value], WType::I32)
            }
            Int::I8 => self.op(Operator::I32Extend8S, &[value], WType::I32),
            Int::I16 => self.op(Operator::I32Extend16S, &[value], WType::I32),
            Int::I32 | Int::I64 => value,
        }
    }

    pub(super) fn add_sub_mul(&mut self, int: Int, arith: Arith, lhs: V, rhs: V) -> V {
        let raw = self.raw_arith(int, arith, lhs, rhs);
        self.canonicalize(int, raw)
    }

    /// The wrapping operation on the carrier, without canonicalization.
    fn raw_arith(&mut self, int: Int, arith: Arith, lhs: V, rhs: V) -> V {
        let (narrow, wide) = match arith {
            Arith::Add => (Operator::I32Add, Operator::I64Add),
            Arith::Sub => (Operator::I32Sub, Operator::I64Sub),
            Arith::Mul => (Operator::I32Mul, Operator::I64Mul),
        };
        self.pick(int, narrow, wide, &[lhs, rhs])
    }

    pub(super) fn neg(&mut self, int: Int, value: V) -> V {
        let zero = self.zero(int);
        self.add_sub_mul(int, Arith::Sub, zero, value)
    }

    pub(super) fn not(&mut self, int: Int, value: V) -> V {
        let ones = self.constant(int, int.all_ones());
        self.pick(int, Operator::I32Xor, Operator::I64Xor, &[value, ones])
    }

    pub(super) fn bitwise(&mut self, int: Int, narrow: Operator, wide: Operator, l: V, r: V) -> V {
        self.pick(int, narrow, wide, &[l, r])
    }

    /// Byte reversal. `i1` has no bytes to reverse and is rejected by the caller.
    pub(super) fn bswap(&mut self, int: Int, value: V) -> V {
        match int {
            Int::I1 | Int::I8 => value,
            Int::I16 => {
                let eight = self.c32(8);
                let high = self.op(Operator::I32Shl, &[value, eight], WType::I32);
                let low = self.op(Operator::I32ShrU, &[value, eight], WType::I32);
                let both = self.op(Operator::I32Or, &[high, low], WType::I32);
                self.canonicalize(Int::I16, both)
            }
            Int::I32 => self.bswap32(value),
            Int::I64 => {
                let thirty_two = self.c64(32);
                let high_word = self.op(Operator::I64ShrU, &[value, thirty_two], WType::I64);
                let high = self.op(Operator::I32WrapI64, &[high_word], WType::I32);
                let low = self.op(Operator::I32WrapI64, &[value], WType::I32);
                let new_high = self.bswap32(low);
                let new_low = self.bswap32(high);
                let new_high = self.op(Operator::I64ExtendI32U, &[new_high], WType::I64);
                let new_low = self.op(Operator::I64ExtendI32U, &[new_low], WType::I64);
                let shifted = self.op(Operator::I64Shl, &[new_high, thirty_two], WType::I64);
                self.op(Operator::I64Or, &[shifted, new_low], WType::I64)
            }
        }
    }

    /// Leading zero bits at the width of `int`. A canonical narrow value is
    /// zero-extended, so the 32-bit count is reduced by the padding.
    pub(super) fn clz(&mut self, int: Int, value: V) -> V {
        match int {
            Int::I1 => {
                let one = self.c32(1);
                self.op(Operator::I32Xor, &[value, one], WType::I32)
            }
            Int::I8 | Int::I16 => {
                let padding = self.c32(32 - int.bits());
                let count = self.op(Operator::I32Clz, &[value], WType::I32);
                self.op(Operator::I32Sub, &[count, padding], WType::I32)
            }
            Int::I32 => self.op(Operator::I32Clz, &[value], WType::I32),
            Int::I64 => self.op(Operator::I64Clz, &[value], WType::I64),
        }
    }

    fn bswap32(&mut self, value: V) -> V {
        // [a b c d] -> rotate -> [c d a b] -> swap adjacent bytes -> [d c b a]
        let sixteen = self.c32(16);
        let eight = self.c32(8);
        let mask = self.c32(0x00ff_00ff);
        let rotated = self.op(Operator::I32Rotl, &[value, sixteen], WType::I32);
        let even = self.op(Operator::I32And, &[rotated, mask], WType::I32);
        let even = self.op(Operator::I32Shl, &[even, eight], WType::I32);
        let odd = self.op(Operator::I32ShrU, &[rotated, eight], WType::I32);
        let odd = self.op(Operator::I32And, &[odd, mask], WType::I32);
        self.op(Operator::I32Or, &[even, odd], WType::I32)
    }

    /// Shifts saturate: a count of at least the width gives zero, or the sign
    /// fill for an arithmetic shift. WebAssembly instead masks the count.
    pub(super) fn shift(&mut self, int: Int, kind: Shift, value: V, count: V) -> V {
        let width = self.constant(int, u64::from(int.bits()));
        let in_range = self.pick_cmp(int, Operator::I32LtU, Operator::I64LtU, &[count, width]);
        match kind {
            Shift::Shl => {
                let shifted = self.pick(int, Operator::I32Shl, Operator::I64Shl, &[value, count]);
                let shifted = self.canonicalize(int, shifted);
                let zero = self.zero(int);
                self.select(int, shifted, zero, in_range)
            }
            Shift::Shr => {
                let shifted = self.pick(int, Operator::I32ShrU, Operator::I64ShrU, &[value, count]);
                let zero = self.zero(int);
                self.select(int, shifted, zero, in_range)
            }
            Shift::Sar => {
                let signed = self.sign_extend(int, value);
                let last = self.constant(int, u64::from(int.bits() - 1));
                let count = self.select(int, count, last, in_range);
                let shifted =
                    self.pick(int, Operator::I32ShrS, Operator::I64ShrS, &[signed, count]);
                self.canonicalize(int, shifted)
            }
        }
    }

    /// Division and remainder trap on a zero divisor, which the IR leaves
    /// undefined. Signed division wraps `MIN / -1` to `MIN`, as the native
    /// backend does, instead of trapping.
    pub(super) fn div_rem(&mut self, int: Int, kind: DivRem, lhs: V, rhs: V) -> V {
        match kind {
            DivRem::Udiv => self.pick(int, Operator::I32DivU, Operator::I64DivU, &[lhs, rhs]),
            DivRem::Umod => self.pick(int, Operator::I32RemU, Operator::I64RemU, &[lhs, rhs]),
            DivRem::Smod => {
                let lhs = self.sign_extend(int, lhs);
                let rhs = self.sign_extend(int, rhs);
                let rem = self.pick(int, Operator::I32RemS, Operator::I64RemS, &[lhs, rhs]);
                self.canonicalize(int, rem)
            }
            DivRem::Sdiv => {
                let lhs = self.sign_extend(int, lhs);
                let rhs = self.sign_extend(int, rhs);
                let divisor = if int.is_narrow() {
                    // The quotient of the sign-extended minimum and -1 fits in
                    // an i32 and wraps when canonicalized.
                    rhs
                } else {
                    let min = self.constant(int, int.signed_min());
                    let minus_one = self.constant(int, int.all_ones());
                    let lhs_min = self.pick_cmp(int, Operator::I32Eq, Operator::I64Eq, &[lhs, min]);
                    let rhs_minus_one =
                        self.pick_cmp(int, Operator::I32Eq, Operator::I64Eq, &[rhs, minus_one]);
                    let overflow = self.op(Operator::I32And, &[lhs_min, rhs_minus_one], WType::I32);
                    let one = self.constant(int, 1);
                    self.select(int, one, rhs, overflow)
                };
                let quotient =
                    self.pick(int, Operator::I32DivS, Operator::I64DivS, &[lhs, divisor]);
                self.canonicalize(int, quotient)
            }
        }
    }

    pub(super) fn compare(&mut self, int: Int, cmp: Cmp, signed: bool, lhs: V, rhs: V) -> V {
        let (lhs, rhs) = if signed {
            (self.sign_extend(int, lhs), self.sign_extend(int, rhs))
        } else {
            (lhs, rhs)
        };
        let (narrow, wide) = match (cmp, signed) {
            (Cmp::Eq, _) => (Operator::I32Eq, Operator::I64Eq),
            (Cmp::Ne, _) => (Operator::I32Ne, Operator::I64Ne),
            (Cmp::Lt, false) => (Operator::I32LtU, Operator::I64LtU),
            (Cmp::Gt, false) => (Operator::I32GtU, Operator::I64GtU),
            (Cmp::Le, false) => (Operator::I32LeU, Operator::I64LeU),
            (Cmp::Ge, false) => (Operator::I32GeU, Operator::I64GeU),
            (Cmp::Lt, true) => (Operator::I32LtS, Operator::I64LtS),
            (Cmp::Gt, true) => (Operator::I32GtS, Operator::I64GtS),
            (Cmp::Le, true) => (Operator::I32LeS, Operator::I64LeS),
            (Cmp::Ge, true) => (Operator::I32GeS, Operator::I64GeS),
        };
        self.pick_cmp(int, narrow, wide, &[lhs, rhs])
    }

    pub(super) fn is_zero(&mut self, int: Int, value: V) -> V {
        self.pick_cmp(int, Operator::I32Eqz, Operator::I64Eqz, &[value])
    }

    /// Convert between integer types. Widening follows `signed`; narrowing
    /// discards the high bits.
    pub(super) fn resize(&mut self, from: Int, to: Int, signed: bool, value: V) -> V {
        match (from.is_wide(), to.is_wide()) {
            (true, true) => value,
            (true, false) => {
                let wrapped = self.op(Operator::I32WrapI64, &[value], WType::I32);
                self.canonicalize(to, wrapped)
            }
            (false, true) => {
                if signed {
                    let extended = self.sign_extend(from, value);
                    self.op(Operator::I64ExtendI32S, &[extended], WType::I64)
                } else {
                    self.op(Operator::I64ExtendI32U, &[value], WType::I64)
                }
            }
            (false, false) => {
                if to.bits() <= from.bits() {
                    self.canonicalize(to, value)
                } else if signed {
                    let extended = self.sign_extend(from, value);
                    self.canonicalize(to, extended)
                } else {
                    value
                }
            }
        }
    }

    /// The wrapped result and the overflow flag (an `i32` of 0 or 1).
    pub(super) fn overflow(
        &mut self,
        int: Int,
        arith: Arith,
        signed: bool,
        lhs: V,
        rhs: V,
    ) -> (V, V) {
        if signed {
            self.signed_overflow(int, arith, lhs, rhs)
        } else {
            self.unsigned_overflow(int, arith, lhs, rhs)
        }
    }

    fn unsigned_overflow(&mut self, int: Int, arith: Arith, lhs: V, rhs: V) -> (V, V) {
        if matches!((int, arith), (Int::I32, Arith::Mul)) {
            // The full product of two u32 values fits a u64.
            let lhs = self.op(Operator::I64ExtendI32U, &[lhs], WType::I64);
            let rhs = self.op(Operator::I64ExtendI32U, &[rhs], WType::I64);
            let wide = self.op(Operator::I64Mul, &[lhs, rhs], WType::I64);
            let result = self.op(Operator::I32WrapI64, &[wide], WType::I32);
            let shift = self.c64(32);
            let high = self.op(Operator::I64ShrU, &[wide, shift], WType::I64);
            let zero = self.c64(0);
            let overflow = self.op(Operator::I64Ne, &[high, zero], WType::I32);
            return (result, overflow);
        }

        let raw = self.raw_arith(int, arith, lhs, rhs);
        if int.is_narrow() {
            // The sum or product of two canonical narrow values fits an i32.
            let limit = self.c32(int.all_ones() as u32);
            let result = self.op(Operator::I32And, &[raw, limit], WType::I32);
            let overflow = match arith {
                Arith::Sub => self.op(Operator::I32LtU, &[lhs, rhs], WType::I32),
                Arith::Add | Arith::Mul => self.op(Operator::I32LtU, &[limit, raw], WType::I32),
            };
            return (result, overflow);
        }
        let overflow = match arith {
            Arith::Add => self.pick_cmp(int, Operator::I32LtU, Operator::I64LtU, &[raw, lhs]),
            Arith::Sub => self.pick_cmp(int, Operator::I32LtU, Operator::I64LtU, &[lhs, rhs]),
            Arith::Mul => {
                // Only i64 reaches here. Write each operand as hi * 2^32 + lo.
                // The product overflows iff both high halves are nonzero, or a
                // cross product (hi * lo) does not fit 32 bits, or adding the
                // two cross products shifted up by 32 carries out of 64 bits
                // when the low product is added. This costs three multiplications
                // and no division.
                let shift = self.c64(32);
                let mask = self.c64(0xffff_ffff);
                let zero = self.c64(0);
                let lhs_hi = self.op(Operator::I64ShrU, &[lhs, shift], WType::I64);
                let rhs_hi = self.op(Operator::I64ShrU, &[rhs, shift], WType::I64);
                let lhs_lo = self.op(Operator::I64And, &[lhs, mask], WType::I64);
                let rhs_lo = self.op(Operator::I64And, &[rhs, mask], WType::I64);
                let lhs_has_hi = self.op(Operator::I64Ne, &[lhs_hi, zero], WType::I32);
                let rhs_has_hi = self.op(Operator::I64Ne, &[rhs_hi, zero], WType::I32);
                let both_hi = self.op(Operator::I32And, &[lhs_has_hi, rhs_has_hi], WType::I32);
                let cross_a = self.op(Operator::I64Mul, &[lhs_hi, rhs_lo], WType::I64);
                let cross_b = self.op(Operator::I64Mul, &[lhs_lo, rhs_hi], WType::I64);
                let cross = self.op(Operator::I64Add, &[cross_a, cross_b], WType::I64);
                // Each cross product is below 2^64; when either has bits above 32
                // the sum is certainly too large, so test them together with
                // the sum itself.
                let cross_a_hi = self.op(Operator::I64ShrU, &[cross_a, shift], WType::I64);
                let cross_b_hi = self.op(Operator::I64ShrU, &[cross_b, shift], WType::I64);
                let cross_hi = self.op(Operator::I64Or, &[cross_a_hi, cross_b_hi], WType::I64);
                let cross_sum_hi = self.op(Operator::I64ShrU, &[cross, shift], WType::I64);
                let cross_big = self.op(Operator::I64Or, &[cross_hi, cross_sum_hi], WType::I64);
                let cross_overflow = self.op(Operator::I64Ne, &[cross_big, zero], WType::I32);
                let cross_up = self.op(Operator::I64Shl, &[cross, shift], WType::I64);
                let carry = self.op(Operator::I64LtU, &[raw, cross_up], WType::I32);
                let any_cross = self.op(Operator::I32Or, &[both_hi, cross_overflow], WType::I32);
                self.op(Operator::I32Or, &[any_cross, carry], WType::I32)
            }
        };
        (raw, overflow)
    }

    fn signed_overflow(&mut self, int: Int, arith: Arith, lhs: V, rhs: V) -> (V, V) {
        if !int.is_wide() {
            // The exact result of a signed operation on values of at most 32
            // bits fits an i64; compare it with the range of the type.
            let lhs = self.sign_extend(int, lhs);
            let rhs = self.sign_extend(int, rhs);
            let lhs = self.op(Operator::I64ExtendI32S, &[lhs], WType::I64);
            let rhs = self.op(Operator::I64ExtendI32S, &[rhs], WType::I64);
            let exact = self.raw_arith(Int::I64, arith, lhs, rhs);
            let min = self.c64(int.signed_min().wrapping_neg());
            let max = self.c64(int.signed_max());
            let below = self.op(Operator::I64LtS, &[exact, min], WType::I32);
            let above = self.op(Operator::I64LtS, &[max, exact], WType::I32);
            let overflow = self.op(Operator::I32Or, &[below, above], WType::I32);
            let wrapped = self.op(Operator::I32WrapI64, &[exact], WType::I32);
            let result = self.canonicalize(int, wrapped);
            return (result, overflow);
        }

        let raw = self.raw_arith(int, arith, lhs, rhs);
        let zero = self.c64(0);
        match arith {
            Arith::Add | Arith::Sub => {
                // Addition overflows iff both operands differ in sign from the
                // result; subtraction iff the operands differ in sign and the
                // result differs from the minuend.
                let lhs_changed = self.op(Operator::I64Xor, &[lhs, raw], WType::I64);
                let other = match arith {
                    Arith::Add => self.op(Operator::I64Xor, &[rhs, raw], WType::I64),
                    _ => self.op(Operator::I64Xor, &[lhs, rhs], WType::I64),
                };
                let flags = self.op(Operator::I64And, &[lhs_changed, other], WType::I64);
                let overflow = self.op(Operator::I64LtS, &[flags, zero], WType::I32);
                (raw, overflow)
            }
            Arith::Mul => {
                // Compare magnitudes before multiplying. |MIN| is representable
                // as an unsigned word and no signed MIN / -1 is evaluated.
                let shift = self.c64(63);
                let lhs_abs = self.magnitude(lhs, shift);
                let rhs_abs = self.magnitude(rhs, shift);
                let signs = self.op(Operator::I64Xor, &[lhs, rhs], WType::I64);
                let negative = self.op(Operator::I64LtS, &[signs, zero], WType::I32);
                let negative = self.op(Operator::I64ExtendI32U, &[negative], WType::I64);
                let max = self.c64(i64::MAX as u64);
                let limit = self.op(Operator::I64Add, &[max, negative], WType::I64);
                let lhs_zero = self.op(Operator::I64Eqz, &[lhs_abs], WType::I32);
                let lhs_zero_word = self.op(Operator::I64ExtendI32U, &[lhs_zero], WType::I64);
                let divisor = self.op(Operator::I64Or, &[lhs_abs, lhs_zero_word], WType::I64);
                let allowed = self.op(Operator::I64DivU, &[limit, divisor], WType::I64);
                let exceeds = self.op(Operator::I64LtU, &[allowed, rhs_abs], WType::I32);
                let lhs_nonzero = self.op(Operator::I32Eqz, &[lhs_zero], WType::I32);
                let overflow = self.op(Operator::I32And, &[exceeds, lhs_nonzero], WType::I32);
                (raw, overflow)
            }
        }
    }

    /// The absolute value of an i64 as an unsigned word.
    fn magnitude(&mut self, value: V, shift63: V) -> V {
        let sign = self.op(Operator::I64ShrS, &[value, shift63], WType::I64);
        let flipped = self.op(Operator::I64Xor, &[value, sign], WType::I64);
        self.op(Operator::I64Sub, &[flipped, sign], WType::I64)
    }

    /// Negation with a flag for the minimum value, which has no negation.
    pub(super) fn signed_neg_overflow(&mut self, int: Int, value: V) -> (V, V) {
        let result = self.neg(int, value);
        let min = self.constant(int, int.signed_min());
        let overflow = self.pick_cmp(int, Operator::I32Eq, Operator::I64Eq, &[value, min]);
        (result, overflow)
    }

    /// Saturating arithmetic: the overflowing result is replaced by the bound
    /// in the direction of the overflow.
    pub(super) fn saturating(&mut self, int: Int, arith: Arith, signed: bool, lhs: V, rhs: V) -> V {
        let (result, overflow) = self.overflow(int, arith, signed, lhs, rhs);
        let bound = if signed {
            // Overflow runs toward the sign of the left operand for addition
            // and subtraction, and toward the sign of the product for
            // multiplication.
            let sign_source = match arith {
                Arith::Mul => self.bitwise(int, Operator::I32Xor, Operator::I64Xor, lhs, rhs),
                Arith::Add | Arith::Sub => lhs,
            };
            let extended = self.sign_extend(int, sign_source);
            let zero = self.zero(int);
            let negative =
                self.pick_cmp(int, Operator::I32LtS, Operator::I64LtS, &[extended, zero]);
            let min = self.constant(int, int.signed_min());
            let max = self.constant(int, int.signed_max());
            self.select(int, min, max, negative)
        } else {
            match arith {
                Arith::Add | Arith::Mul => self.constant(int, int.all_ones()),
                Arith::Sub => self.zero(int),
            }
        };
        self.select(int, bound, result, overflow)
    }
}
