//! 128- and 256-bit integers.
//!
//! Fe's `usize` has 256 bits, so every array index and every loop counter over
//! an array is an `i256` in the IR, and Fe's `u128` and `i128` are `i128`. A
//! 256-bit value is held as four `i64` limbs, least significant first, which
//! are four WebAssembly values: a phi of this type has four block parameters, a
//! function takes or returns four values, and memory holds it as 32
//! little-endian bytes.
//!
//! A 128-bit value is held as four limbs too, zero-extended: its upper two
//! limbs are zero, as the bits above a narrow integer in its `i32` are. Calls,
//! returns and phis carry only the two lower limbs, and memory holds 16 bytes.
//! An operation extends its operands to 256 bits, with the sign for a signed
//! operation, and computes with the 256-bit code. The low 128 bits of the
//! result are the 128-bit result. A checked operation overflows when the
//! 256-bit result is not the extension of its low 128 bits: a sum, difference
//! or product of such operands that fits in 128 bits is exact at 256 bits.
//!
//! Supported: constants, `zext`, `sext`, `trunc`, `add`, `sub`, `neg`, `not`,
//! `and`, `or`, `xor`, the ten comparisons, `is_zero`, the checked forms
//! (`uaddo`, `usubo`, `umulo`, `saddo`, `ssubo`, `smulo`, `snego`), the
//! saturating forms (`uaddsat`, `usubsat`, `umulsat`, `saddsat`, `ssubsat`,
//! `smulsat`), `bswap`, `clz`, `ctz`, multiplication, division and shifts.

use waffle::{Operator, Type as WType};

use sonatina_ir::{I256, Type};

use super::arith::{Cmp, Emit, Int};

type V = waffle::Value;

/// The limbs of a 128- or 256-bit value, least significant first.
pub(super) type Limbs = [V; 4];

pub(super) const LIMBS: usize = 4;

/// The integer types held as limbs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Wide {
    I128,
    I256,
}

impl Wide {
    pub(super) fn from_type(ty: Type) -> Option<Self> {
        match ty {
            Type::I128 => Some(Self::I128),
            Type::I256 => Some(Self::I256),
            _ => None,
        }
    }

    pub(super) fn ty(self) -> Type {
        match self {
            Self::I128 => Type::I128,
            Self::I256 => Type::I256,
        }
    }

    /// The limbs that hold the value. The limbs above them are zero.
    pub(super) fn limbs(self) -> usize {
        match self {
            Self::I128 => 2,
            Self::I256 => LIMBS,
        }
    }
}

/// The four little-endian 64-bit words of a constant.
pub(super) fn limbs_of(value: I256) -> [u64; LIMBS] {
    let bytes = value.to_u256().to_little_endian();
    let mut limbs = [0u64; LIMBS];
    for (index, limb) in limbs.iter_mut().enumerate() {
        let chunk = &bytes[8 * index..8 * index + 8];
        *limb = u64::from_le_bytes(chunk.try_into().expect("a limb has eight bytes"));
    }
    limbs
}

impl Emit<'_> {
    fn c64_limbs(&mut self, limbs: [u64; LIMBS]) -> Limbs {
        limbs.map(|limb| self.c64(limb))
    }

    pub(super) fn wide_const(&mut self, value: I256) -> Limbs {
        self.c64_limbs(limbs_of(value))
    }

    pub(super) fn wide_zero(&mut self) -> Limbs {
        self.c64_limbs([0; LIMBS])
    }

    /// A value of `wide` from the limbs that hold it, as calls, phis and
    /// memory carry it.
    pub(super) fn wide_from_carried(&mut self, wide: Wide, carried: &[V]) -> Limbs {
        let mut limbs = [carried[0]; LIMBS];
        limbs[..wide.limbs()].copy_from_slice(&carried[..wide.limbs()]);
        self.wide_wrap(wide, limbs)
    }

    /// The value modulo 2^bits of `wide`: the limbs above those that hold it
    /// become zero.
    pub(super) fn wide_wrap(&mut self, wide: Wide, mut value: Limbs) -> Limbs {
        if wide.limbs() < LIMBS {
            let zero = self.c64(0);
            value[wide.limbs()..].fill(zero);
        }
        value
    }

    /// A value of `wide` sign-extended to 256 bits.
    pub(super) fn wide_sign_extend(&mut self, wide: Wide, mut value: Limbs) -> Limbs {
        let count = wide.limbs();
        if count < LIMBS {
            let fill = self.sign_fill(value[count - 1]);
            value[count..].fill(fill);
        }
        value
    }

    /// All ones if the top bit of `limb` is set, and zero otherwise.
    pub(super) fn sign_fill(&mut self, limb: V) -> V {
        let shift = self.c64(63);
        self.fold(Operator::I64ShrS, &[limb, shift], WType::I64)
    }

    /// An `i32` that is non-zero if a 256-bit value is not the extension of
    /// its low bits of `wide`, with the sign when `signed`.
    pub(super) fn wide_exceeds(&mut self, wide: Wide, signed: bool, value: Limbs) -> V {
        let count = wide.limbs();
        let fill = if signed {
            self.sign_fill(value[count - 1])
        } else {
            self.c64(0)
        };
        let mut diff = self.c64(0);
        for &limb in &value[count..] {
            let x = self.fold(Operator::I64Xor, &[limb, fill], WType::I64);
            diff = self.fold(Operator::I64Or, &[diff, x], WType::I64);
        }
        let zero = self.c64(0);
        self.fold(Operator::I64Ne, &[diff, zero], WType::I32)
    }

    fn cmp64(&mut self, op: Operator, a: V, b: V) -> V {
        self.fold(op, &[a, b], WType::I32)
    }

    /// `zext` or `sext` of an integer of at most 64 bits.
    pub(super) fn wide_extend(&mut self, from: Int, signed: bool, value: V) -> Limbs {
        let low = self.resize(from, Int::I64, signed, value);
        let fill = if signed {
            self.sign_fill(low)
        } else {
            self.c64(0)
        };
        [low, fill, fill, fill]
    }

    /// `trunc` to an integer of at most 64 bits.
    pub(super) fn wide_trunc(&mut self, to: Int, limbs: Limbs) -> V {
        self.resize(Int::I64, to, false, limbs[0])
    }

    pub(super) fn wide_add(&mut self, lhs: Limbs, rhs: Limbs) -> (Limbs, V) {
        let mut result = lhs;
        let mut carry: Option<V> = None;
        for index in 0..LIMBS {
            let sum = self.fold(Operator::I64Add, &[lhs[index], rhs[index]], WType::I64);
            let carry_a = self.cmp64(Operator::I64LtU, sum, lhs[index]);
            let (sum, carry_out) = match carry {
                None => (sum, carry_a),
                Some(carry_in) => {
                    let carry_in64 = self.fold(Operator::I64ExtendI32U, &[carry_in], WType::I64);
                    let with_carry = self.fold(Operator::I64Add, &[sum, carry_in64], WType::I64);
                    let carry_b = self.cmp64(Operator::I64LtU, with_carry, sum);
                    let carry_out = self.fold(Operator::I32Or, &[carry_a, carry_b], WType::I32);
                    (with_carry, carry_out)
                }
            };
            result[index] = sum;
            carry = Some(carry_out);
        }
        (result, carry.expect("a 256-bit value has limbs"))
    }

    pub(super) fn wide_sub(&mut self, lhs: Limbs, rhs: Limbs) -> (Limbs, V) {
        let mut result = lhs;
        let mut borrow: Option<V> = None;
        for index in 0..LIMBS {
            let diff = self.fold(Operator::I64Sub, &[lhs[index], rhs[index]], WType::I64);
            let borrow_a = self.cmp64(Operator::I64LtU, lhs[index], rhs[index]);
            let (diff, borrow_out) = match borrow {
                None => (diff, borrow_a),
                Some(borrow_in) => {
                    let borrow_in64 = self.fold(Operator::I64ExtendI32U, &[borrow_in], WType::I64);
                    let with_borrow = self.fold(Operator::I64Sub, &[diff, borrow_in64], WType::I64);
                    let borrow_b = self.cmp64(Operator::I64LtU, diff, borrow_in64);
                    let borrow_out = self.fold(Operator::I32Or, &[borrow_a, borrow_b], WType::I32);
                    (with_borrow, borrow_out)
                }
            };
            result[index] = diff;
            borrow = Some(borrow_out);
        }
        (result, borrow.expect("a 256-bit value has limbs"))
    }

    pub(super) fn wide_neg(&mut self, value: Limbs) -> Limbs {
        let zero = self.wide_zero();
        self.wide_sub(zero, value).0
    }

    /// Byte reversal: the limbs that hold the value in the opposite order,
    /// each reversed.
    pub(super) fn wide_bswap(&mut self, wide: Wide, value: Limbs) -> Limbs {
        let count = wide.limbs();
        let mut result = value;
        for index in 0..count {
            result[index] = self.bswap(Int::I64, value[count - 1 - index]);
        }
        result
    }

    /// Leading zero bits of a value of `wide`. The count is at most 256, so it
    /// is held in the lowest limb.
    pub(super) fn wide_clz(&mut self, wide: Wide, value: Limbs) -> Limbs {
        let count = wide.limbs();
        let zero = self.c64(0);
        // The zero bits above limb `index`.
        let above = |index: usize| 64 * (count - 1 - index) as u64;
        let base = self.c64(above(0));
        let low = self.fold(Operator::I64Clz, &[value[0]], WType::I64);
        let mut leading = self.fold(Operator::I64Add, &[low, base], WType::I64);
        for (index, &limb) in value.iter().enumerate().take(count).skip(1) {
            let mut here = self.fold(Operator::I64Clz, &[limb], WType::I64);
            if above(index) != 0 {
                let bits = self.c64(above(index));
                here = self.fold(Operator::I64Add, &[here, bits], WType::I64);
            }
            let nonzero = self.fold(Operator::I64Ne, &[limb, zero], WType::I32);
            leading = self.fold(Operator::Select, &[here, leading, nonzero], WType::I64);
        }
        let mut result = [zero; LIMBS];
        result[0] = leading;
        result
    }

    /// Trailing zero bits of a value of `wide`. The limbs above the value are
    /// zero, so zero counts to the width. The count is in the lowest limb.
    pub(super) fn wide_ctz(&mut self, wide: Wide, value: Limbs) -> Limbs {
        let count = wide.limbs();
        let zero = self.c64(0);
        let top = self.fold(Operator::I64Ctz, &[value[count - 1]], WType::I64);
        let base = self.c64(64 * (count - 1) as u64);
        let mut trailing = self.fold(Operator::I64Add, &[top, base], WType::I64);
        for (index, &limb) in value.iter().enumerate().take(count - 1).rev() {
            let mut here = self.fold(Operator::I64Ctz, &[limb], WType::I64);
            if index != 0 {
                let bits = self.c64(64 * index as u64);
                here = self.fold(Operator::I64Add, &[here, bits], WType::I64);
            }
            let nonzero = self.fold(Operator::I64Ne, &[limb, zero], WType::I32);
            trailing = self.fold(Operator::Select, &[here, trailing, nonzero], WType::I64);
        }
        let mut result = [zero; LIMBS];
        result[0] = trailing;
        result
    }

    pub(super) fn wide_not(&mut self, value: Limbs) -> Limbs {
        let ones = self.c64(u64::MAX);
        value.map(|limb| self.fold(Operator::I64Xor, &[limb, ones], WType::I64))
    }

    pub(super) fn wide_bitwise(&mut self, op: Operator, lhs: Limbs, rhs: Limbs) -> Limbs {
        let mut result = lhs;
        for index in 0..LIMBS {
            result[index] = self.fold(op, &[lhs[index], rhs[index]], WType::I64);
        }
        result
    }

    /// `value` shifted left or right by the constant `count`: each limb
    /// takes the bits of the two limbs that the count brings to it. A count
    /// of at least 256 gives zero.
    pub(super) fn wide_shift_by(&mut self, left: bool, value: Limbs, count: usize) -> Limbs {
        let (limbs, bits) = (count / 64, count as u64 % 64);
        let zero = self.c64(0);
        let (near, far) = (self.c64(bits), self.c64(64 - bits));
        let mut result = [zero; LIMBS];
        for (index, limb) in result.iter_mut().enumerate() {
            // The limb that supplies most of this one, and the one beyond it.
            let source = |offset: usize| {
                let from = if left {
                    index.checked_sub(limbs + offset)
                } else {
                    Some(index + limbs + offset)
                };
                from.and_then(|from| value.get(from).copied())
                    .unwrap_or(zero)
            };
            let (toward, away) = if left {
                (Operator::I64Shl, Operator::I64ShrU)
            } else {
                (Operator::I64ShrU, Operator::I64Shl)
            };
            let main = self.fold(toward, &[source(0), near], WType::I64);
            *limb = if bits == 0 {
                main
            } else {
                let spill = self.fold(away, &[source(1), far], WType::I64);
                self.fold(Operator::I64Or, &[main, spill], WType::I64)
            };
        }
        result
    }

    /// The low `limbs` limbs of `a * b` when at most three products of their
    /// limbs are not zero, as for values extended from 64 bits and for any
    /// 128-bit values. A longer product calls the multiplication function.
    pub(super) fn wide_mul_short(&mut self, limbs: usize, a: Limbs, b: Limbs) -> Option<Limbs> {
        let is_zero = |limb: V| self.constant_of(limb) == Some(0);
        let products: Vec<(usize, usize)> = (0..limbs)
            .flat_map(|i| (0..limbs - i).map(move |j| (i, j)))
            .filter(|&(i, j)| !is_zero(a[i]) && !is_zero(b[j]))
            .collect();
        if products.len() > 3 {
            return None;
        }
        let mut result = self.wide_zero();
        for (i, j) in products {
            let mut term = self.wide_zero();
            // The high half of a product in the top limb is not part of the result.
            if i + j + 1 < limbs {
                (term[i + j], term[i + j + 1]) = self.mul_wide(a[i], b[j]);
            } else {
                term[i + j] = self.op(Operator::I64Mul, &[a[i], b[j]], WType::I64);
            }
            result = self.wide_add(result, term).0;
        }
        Some(result)
    }

    /// Signed overflow of `lhs + rhs` (when `sub` is false) or `lhs - rhs`.
    pub(super) fn wide_signed_overflow(
        &mut self,
        sub: bool,
        lhs: Limbs,
        rhs: Limbs,
        result: Limbs,
    ) -> V {
        let top = LIMBS - 1;
        let (a, b, r) = (lhs[top], rhs[top], result[top]);
        // add: both operands differ in sign from the result.
        // sub: the operands differ in sign and the result differs from `lhs`.
        let (left, right) = if sub {
            (
                self.fold(Operator::I64Xor, &[a, b], WType::I64),
                self.fold(Operator::I64Xor, &[a, r], WType::I64),
            )
        } else {
            (
                self.fold(Operator::I64Xor, &[a, r], WType::I64),
                self.fold(Operator::I64Xor, &[b, r], WType::I64),
            )
        };
        let both = self.fold(Operator::I64And, &[left, right], WType::I64);
        let shift = self.c64(63);
        let bit = self.fold(Operator::I64ShrU, &[both, shift], WType::I64);
        self.fold(Operator::I32WrapI64, &[bit], WType::I32)
    }

    pub(super) fn wide_is_zero(&mut self, value: Limbs) -> V {
        let mut any = value[0];
        for &limb in &value[1..] {
            any = self.fold(Operator::I64Or, &[any, limb], WType::I64);
        }
        self.fold(Operator::I64Eqz, &[any], WType::I32)
    }

    fn wide_eq(&mut self, lhs: Limbs, rhs: Limbs) -> V {
        let mut diff = self.c64(0);
        for index in 0..LIMBS {
            let x = self.fold(Operator::I64Xor, &[lhs[index], rhs[index]], WType::I64);
            diff = self.fold(Operator::I64Or, &[diff, x], WType::I64);
        }
        self.fold(Operator::I64Eqz, &[diff], WType::I32)
    }

    /// `lhs < rhs`, unsigned or signed.
    fn wide_lt(&mut self, lhs: Limbs, rhs: Limbs, signed: bool) -> V {
        let mut less = self.cmp64(Operator::I64LtU, lhs[0], rhs[0]);
        for index in 1..LIMBS {
            let top = signed && index == LIMBS - 1;
            let limb_less = if top {
                self.cmp64(Operator::I64LtS, lhs[index], rhs[index])
            } else {
                self.cmp64(Operator::I64LtU, lhs[index], rhs[index])
            };
            let equal = self.cmp64(Operator::I64Eq, lhs[index], rhs[index]);
            // The higher limb decides unless the two limbs are equal.
            less = self.fold(Operator::Select, &[less, limb_less, equal], WType::I32);
        }
        less
    }

    pub(super) fn wide_compare(&mut self, cmp: Cmp, signed: bool, lhs: Limbs, rhs: Limbs) -> V {
        let not = |this: &mut Self, value: V| this.fold(Operator::I32Eqz, &[value], WType::I32);
        match cmp {
            Cmp::Eq => self.wide_eq(lhs, rhs),
            Cmp::Ne => {
                let equal = self.wide_eq(lhs, rhs);
                not(self, equal)
            }
            Cmp::Lt => self.wide_lt(lhs, rhs, signed),
            Cmp::Gt => self.wide_lt(rhs, lhs, signed),
            Cmp::Le => {
                let greater = self.wide_lt(rhs, lhs, signed);
                not(self, greater)
            }
            Cmp::Ge => {
                let less = self.wide_lt(lhs, rhs, signed);
                not(self, less)
            }
        }
    }

    /// An `i32` that is non-zero if the value does not fit in an unsigned
    /// 32-bit integer.
    pub(super) fn wide_exceeds_u32(&mut self, value: Limbs) -> V {
        let shift = self.c64(32);
        let mut high = self.fold(Operator::I64ShrU, &[value[0], shift], WType::I64);
        for &limb in &value[1..] {
            high = self.fold(Operator::I64Or, &[high, limb], WType::I64);
        }
        let zero = self.c64(0);
        self.fold(Operator::I64Ne, &[high, zero], WType::I32)
    }

    /// An `i32` that is non-zero if the value does not fit in a signed 32-bit
    /// integer.
    pub(super) fn wide_exceeds_i32(&mut self, value: Limbs) -> V {
        // The value fits if limb 0 sign-extends from 32 bits to itself and the
        // limbs above are its sign fill.
        let low = self.fold(Operator::I32WrapI64, &[value[0]], WType::I32);
        let extended = self.fold(Operator::I64ExtendI32S, &[low], WType::I64);
        let mut diff = self.fold(Operator::I64Xor, &[extended, value[0]], WType::I64);
        let fill = self.sign_fill(value[0]);
        for &limb in &value[1..] {
            let x = self.fold(Operator::I64Xor, &[limb, fill], WType::I64);
            diff = self.fold(Operator::I64Or, &[diff, x], WType::I64);
        }
        let zero = self.c64(0);
        self.fold(Operator::I64Ne, &[diff, zero], WType::I32)
    }
}

// Multiplication, division and shifts are too long to repeat at every use, so
// they are functions of the module that calls them with four limbs per operand.

impl Emit<'_> {
    pub(super) fn select64(&mut self, if_true: V, if_false: V, cond: V) -> V {
        self.fold(Operator::Select, &[if_true, if_false, cond], WType::I64)
    }

    fn zero_extend(&mut self, flag: V) -> V {
        self.fold(Operator::I64ExtendI32U, &[flag], WType::I64)
    }

    /// The 128-bit product of two 64-bit values, as (low, high).
    fn mul_wide(&mut self, x: V, y: V) -> (V, V) {
        let mask = self.c64(0xffff_ffff);
        let shift = self.c64(32);
        let x0 = self.op(Operator::I64And, &[x, mask], WType::I64);
        let x1 = self.op(Operator::I64ShrU, &[x, shift], WType::I64);
        let y0 = self.op(Operator::I64And, &[y, mask], WType::I64);
        let y1 = self.op(Operator::I64ShrU, &[y, shift], WType::I64);
        let p00 = self.op(Operator::I64Mul, &[x0, y0], WType::I64);
        let p01 = self.op(Operator::I64Mul, &[x0, y1], WType::I64);
        let p10 = self.op(Operator::I64Mul, &[x1, y0], WType::I64);
        let p11 = self.op(Operator::I64Mul, &[x1, y1], WType::I64);
        // The middle column holds three values below 2^32 plus a carry, which
        // fits in 64 bits.
        let p00_high = self.op(Operator::I64ShrU, &[p00, shift], WType::I64);
        let p01_low = self.op(Operator::I64And, &[p01, mask], WType::I64);
        let p10_low = self.op(Operator::I64And, &[p10, mask], WType::I64);
        let mid = self.op(Operator::I64Add, &[p00_high, p01_low], WType::I64);
        let mid = self.op(Operator::I64Add, &[mid, p10_low], WType::I64);
        let p00_low = self.op(Operator::I64And, &[p00, mask], WType::I64);
        let mid_low = self.op(Operator::I64Shl, &[mid, shift], WType::I64);
        let low = self.op(Operator::I64Or, &[p00_low, mid_low], WType::I64);
        let p01_high = self.op(Operator::I64ShrU, &[p01, shift], WType::I64);
        let p10_high = self.op(Operator::I64ShrU, &[p10, shift], WType::I64);
        let mid_high = self.op(Operator::I64ShrU, &[mid, shift], WType::I64);
        let high = self.op(Operator::I64Add, &[p11, p01_high], WType::I64);
        let high = self.op(Operator::I64Add, &[high, p10_high], WType::I64);
        let high = self.op(Operator::I64Add, &[high, mid_high], WType::I64);
        (low, high)
    }

    /// The quotient and remainder of `(high, low)` by `divisor`, for a divisor
    /// with its top bit set and `high` below it (Warren, Hacker's Delight,
    /// `divlu`): two digits of 32 bits, each from a 64-bit division by the
    /// divisor's top half.
    fn div_wide(&mut self, high: V, low: V, divisor: V) -> (V, V) {
        let mask = self.c64(0xffff_ffff);
        let shift = self.c64(32);
        let one = self.c64(1);
        let d1 = self.op(Operator::I64ShrU, &[divisor, shift], WType::I64);
        let d0 = self.op(Operator::I64And, &[divisor, mask], WType::I64);
        let low_high = self.op(Operator::I64ShrU, &[low, shift], WType::I64);
        let low_low = self.op(Operator::I64And, &[low, mask], WType::I64);
        let mut quotient = self.c64(0);
        let mut remainder = high;
        for part in [low_high, low_low] {
            // The digit of `remainder * 2^32 + part`. The estimate from the
            // divisor's top half leaves `rest` and is at most two too large.
            // An estimate is too large if it has more than 32 bits or its
            // product with the low half exceeds what is left, `rest * 2^32 +
            // part`, which a `rest` of more than 32 bits is always above.
            // The estimate less one leaves `rest` and the top half.
            let digit = self.op(Operator::I64DivU, &[remainder, d1], WType::I64);
            let product = self.op(Operator::I64Mul, &[digit, d1], WType::I64);
            let rest = self.op(Operator::I64Sub, &[remainder, product], WType::I64);
            let less = self.op(Operator::I64Sub, &[digit, one], WType::I64);
            let more = self.op(Operator::I64Add, &[rest, d1], WType::I64);
            let [over, again] = [(digit, rest), (less, more)].map(|(digit, rest)| {
                let long = self.cmp64(Operator::I64GtU, digit, mask);
                let product = self.op(Operator::I64Mul, &[digit, d0], WType::I64);
                let left = self.op(Operator::I64Shl, &[rest, shift], WType::I64);
                let left = self.op(Operator::I64Or, &[left, part], WType::I64);
                let exceeds = self.cmp64(Operator::I64GtU, product, left);
                let large = self.op(Operator::I32Or, &[long, exceeds], WType::I32);
                let fits = self.cmp64(Operator::I64LeU, rest, mask);
                self.op(Operator::I32And, &[large, fits], WType::I32)
            });
            let again = self.op(Operator::I32And, &[over, again], WType::I32);
            let excess = self.op(Operator::I32Add, &[over, again], WType::I32);
            let excess = self.zero_extend(excess);
            let digit = self.op(Operator::I64Sub, &[digit, excess], WType::I64);
            // The remainder fits in 64 bits, so the bits above cancel.
            let up = self.op(Operator::I64Shl, &[remainder, shift], WType::I64);
            let whole = self.op(Operator::I64Or, &[up, part], WType::I64);
            let product = self.op(Operator::I64Mul, &[digit, divisor], WType::I64);
            remainder = self.op(Operator::I64Sub, &[whole, product], WType::I64);
            let up = self.op(Operator::I64Shl, &[quotient, shift], WType::I64);
            quotient = self.op(Operator::I64Or, &[up, digit], WType::I64);
        }
        (quotient, remainder)
    }

    /// The reciprocal of a divisor with its top bit set:
    /// `(2^128 - 1) / divisor - 2^64`.
    fn reciprocal(&mut self, divisor: V) -> V {
        let ones = self.c64(u64::MAX);
        let high = self.op(Operator::I64Xor, &[divisor, ones], WType::I64);
        self.div_wide(high, ones, divisor).0
    }

    /// The quotient and remainder of `(high, low)` by `divisor`, for a divisor
    /// with its top bit set and `high` below it, from the divisor's
    /// reciprocal (Möller and Granlund, "Improved division by invariant
    /// integers", algorithm 4).
    fn div_by_reciprocal(&mut self, high: V, low: V, divisor: V, reciprocal: V) -> (V, V) {
        let zero = self.c64(0);
        let one = self.c64(1);
        // `(q1, q0) = reciprocal * high + (high, low)`, and `q1 + 1` is the
        // quotient or one off either way.
        let (q0, q1) = self.mul_wide(reciprocal, high);
        let q0 = self.op(Operator::I64Add, &[q0, low], WType::I64);
        let carry = self.cmp64(Operator::I64LtU, q0, low);
        let carry = self.zero_extend(carry);
        let q1 = self.op(Operator::I64Add, &[q1, high], WType::I64);
        let q1 = self.op(Operator::I64Add, &[q1, carry], WType::I64);
        let q1 = self.op(Operator::I64Add, &[q1, one], WType::I64);
        let product = self.op(Operator::I64Mul, &[q1, divisor], WType::I64);
        let r = self.op(Operator::I64Sub, &[low, product], WType::I64);
        // Too large: the remainder wrapped below zero.
        let over = self.cmp64(Operator::I64GtU, r, q0);
        let back = self.select64(divisor, zero, over);
        let r = self.op(Operator::I64Add, &[r, back], WType::I64);
        let over = self.zero_extend(over);
        let q1 = self.op(Operator::I64Sub, &[q1, over], WType::I64);
        // Too small: the remainder reaches the divisor.
        let under = self.cmp64(Operator::I64GeU, r, divisor);
        let off = self.select64(divisor, zero, under);
        let r = self.op(Operator::I64Sub, &[r, off], WType::I64);
        let under = self.zero_extend(under);
        let q1 = self.op(Operator::I64Add, &[q1, under], WType::I64);
        (q1, r)
    }

    /// Limb `index` of `limbs` shifted left by `shift` bits (0 to 63), given
    /// `back`, which is `63 - shift`. One past the top limb, it is the bits
    /// shifted out.
    fn shl_limb(&mut self, limbs: &[V], index: usize, shift: V, back: V) -> V {
        let high = limbs
            .get(index)
            .map(|&limb| self.op(Operator::I64Shl, &[limb, shift], WType::I64));
        // A shift right by `64 - shift` in two steps: one by 64 would be a
        // shift by 0.
        let low = index.checked_sub(1).map(|below| {
            let one = self.c64(1);
            let half = self.op(Operator::I64ShrU, &[limbs[below], one], WType::I64);
            self.op(Operator::I64ShrU, &[half, back], WType::I64)
        });
        high.into_iter()
            .chain(low)
            .reduce(|high, low| self.op(Operator::I64Or, &[high, low], WType::I64))
            .expect("the index is at most one past the top limb")
    }

    /// The low 256 bits of the product and whether the product has more.
    // The column of a partial product is the sum of two indices.
    #[allow(clippy::needless_range_loop)]
    fn wide_mulo_inline(&mut self, a: Limbs, b: Limbs) -> (Limbs, V) {
        let zero = self.c64(0);
        let mut result = [zero; LIMBS];
        let mut overflow = self.c32(0);
        for i in 0..LIMBS {
            let mut carry = zero;
            for j in 0..LIMBS {
                if i + j >= LIMBS {
                    // Any non-zero product here is at least 2^256.
                    let a_nonzero = self.op(Operator::I64Ne, &[a[i], zero], WType::I32);
                    let b_nonzero = self.op(Operator::I64Ne, &[b[j], zero], WType::I32);
                    let both = self.op(Operator::I32And, &[a_nonzero, b_nonzero], WType::I32);
                    overflow = self.op(Operator::I32Or, &[overflow, both], WType::I32);
                    continue;
                }
                let k = i + j;
                let (low, high) = self.mul_wide(a[i], b[j]);
                let sum = self.op(Operator::I64Add, &[result[k], low], WType::I64);
                let carry_a = self.cmp64(Operator::I64LtU, sum, result[k]);
                let sum_c = self.op(Operator::I64Add, &[sum, carry], WType::I64);
                let carry_b = self.cmp64(Operator::I64LtU, sum_c, sum);
                result[k] = sum_c;
                // `high` is at most 2^64 - 2, so adding two carries cannot wrap.
                let carry_a64 = self.zero_extend(carry_a);
                let carry_b64 = self.zero_extend(carry_b);
                let next = self.op(Operator::I64Add, &[high, carry_a64], WType::I64);
                carry = self.op(Operator::I64Add, &[next, carry_b64], WType::I64);
            }
            // The carry out of the last column of the row is beyond limb 3.
            let carried = self.op(Operator::I64Ne, &[carry, zero], WType::I32);
            overflow = self.op(Operator::I32Or, &[overflow, carried], WType::I32);
        }
        (result, overflow)
    }

    /// The limbs of `value` shifted left or right by `count` bits (0 to 255).
    fn wide_shift_in_range(&mut self, left: bool, value: Limbs, count: V) -> Limbs {
        // `count` is an i64 in 0..256.
        let six = self.c64(6);
        let limb_shift64 = self.op(Operator::I64ShrU, &[count, six], WType::I64);
        let limb_shift = self.op(Operator::I32WrapI64, &[limb_shift64], WType::I32);
        let sixty_three = self.c64(63);
        let bits = self.op(Operator::I64And, &[count, sixty_three], WType::I64);
        let sixty_four = self.c64(64);
        let back = self.op(Operator::I64Sub, &[sixty_four, bits], WType::I64);
        let zero = self.c64(0);
        let aligned = self.op(Operator::I64Eqz, &[bits], WType::I32);
        let mut result = [zero; LIMBS];
        for (k, out) in result.iter_mut().enumerate() {
            // The limb that supplies the main part and the one that supplies
            // the bits that cross the boundary.
            let mut main = zero;
            let mut cross = zero;
            for shift in 0..LIMBS {
                let is_shift = {
                    let value = self.c32(shift as u32);
                    self.op(Operator::I32Eq, &[limb_shift, value], WType::I32)
                };
                let (main_index, cross_index) = if left {
                    (k.checked_sub(shift), k.checked_sub(shift + 1))
                } else {
                    (
                        (k + shift < LIMBS).then_some(k + shift),
                        (k + shift + 1 < LIMBS).then_some(k + shift + 1),
                    )
                };
                if let Some(index) = main_index {
                    main = self.select64(value[index], main, is_shift);
                }
                if let Some(index) = cross_index {
                    cross = self.select64(value[index], cross, is_shift);
                }
            }
            let (main_op, cross_op) = if left {
                (Operator::I64Shl, Operator::I64ShrU)
            } else {
                (Operator::I64ShrU, Operator::I64Shl)
            };
            let main = self.op(main_op, &[main, bits], WType::I64);
            let cross = self.op(cross_op, &[cross, back], WType::I64);
            // A shift by 64 would be a shift by 0.
            let cross = self.select64(zero, cross, aligned);
            *out = self.op(Operator::I64Or, &[main, cross], WType::I64);
        }
        result
    }
}

/// The signature of the helper functions: how many `i64` values go in and out.
pub(super) fn helper_signature(
    wmod: &mut waffle::Module<'static>,
    params: usize,
    results: &[WType],
) -> waffle::Signature {
    wmod.signatures.push(waffle::SignatureData {
        params: vec![WType::I64; params],
        returns: results.to_vec(),
    })
}

fn helper_params(body: &waffle::FunctionBody, count: usize) -> Vec<V> {
    body.blocks[body.entry]
        .params
        .iter()
        .take(count)
        .map(|param| param.1)
        .collect()
}

fn limbs_at(values: &[V], start: usize) -> Limbs {
    [
        values[start],
        values[start + 1],
        values[start + 2],
        values[start + 3],
    ]
}

/// `mulo(a, b)` returns the low 256 bits of `a * b` and an `i32` that is 1 if
/// the product does not fit in 256 bits.
pub(super) fn build_mulo(
    wmod: &waffle::Module<'static>,
    sig: waffle::Signature,
) -> waffle::FunctionBody {
    let mut body = waffle::FunctionBody::new(wmod, sig);
    let entry = body.entry;
    let params = helper_params(&body, 2 * LIMBS);
    let (a, b) = (limbs_at(&params, 0), limbs_at(&params, LIMBS));
    let (limbs, overflow) = Emit {
        body: &mut body,
        block: entry,
    }
    .wide_mulo_inline(a, b);
    let mut values = limbs.to_vec();
    values.push(overflow);
    body.set_terminator(entry, waffle::Terminator::Return { values });
    body
}

/// `shl(a, n)` or `shr(a, n)`: shifts by the 256-bit count `n`. A count of 256
/// or more gives zero.
pub(super) fn build_shift(
    wmod: &waffle::Module<'static>,
    sig: waffle::Signature,
    left: bool,
) -> waffle::FunctionBody {
    let mut body = waffle::FunctionBody::new(wmod, sig);
    let entry = body.entry;
    let params = helper_params(&body, 2 * LIMBS);
    let (value, count) = (limbs_at(&params, 0), limbs_at(&params, LIMBS));
    let mut e = Emit {
        body: &mut body,
        block: entry,
    };
    let in_range = {
        let mut high = count[1];
        for &limb in &count[2..] {
            high = e.op(Operator::I64Or, &[high, limb], WType::I64);
        }
        let limit = e.c64(256);
        let high_zero = e.op(Operator::I64Eqz, &[high], WType::I32);
        let below = e.op(Operator::I64LtU, &[count[0], limit], WType::I32);
        e.op(Operator::I32And, &[high_zero, below], WType::I32)
    };
    let shifted = e.wide_shift_in_range(left, value, count[0]);
    let zero = e.c64(0);
    let result = shifted.map(|limb| e.select64(limb, zero, in_range));
    body.set_terminator(
        entry,
        waffle::Terminator::Return {
            values: result.to_vec(),
        },
    );
    body
}

/// Divides `dividend`, limbs least significant first, by a nonzero `divisor`
/// of one limb or four, from `block`. Returns the block that follows, the low
/// four digits of the quotient and the remainder.
///
/// This is long division on 64-bit digits (Knuth, 4.3.1, algorithm D). Both
/// operands are shifted left until the divisor's top bit is set, which moves
/// a divisor of four limbs up by whole limbs too: the dividend gets as many
/// zero limbs below it. The remainder so far has as many limbs as the divisor
/// and is below it. Each step takes one more limb of the dividend below the
/// remainder and subtracts the divisor times the next digit of the quotient.
fn divide_long(
    body: &mut waffle::FunctionBody,
    block: waffle::Block,
    dividend: &[V],
    divisor: &[V],
) -> (waffle::Block, Limbs, Limbs) {
    use waffle::{BlockTarget, Terminator};
    let target = |block, args: Vec<V>| BlockTarget { block, args };
    let [head, full, next, done] = [(); 4].map(|_| body.add_block());
    let wide = divisor.len() == LIMBS;
    let top = divisor.len() - 1;

    let mut e = Emit { body, block };
    let zero = e.c64(0);
    // Move the divisor up a limb while its top limb is zero.
    let mut d = divisor.to_vec();
    let mut moved = Vec::new();
    for _ in 0..top {
        let empty = e.op(Operator::I64Eqz, &[d[top]], WType::I32);
        let mut below = zero;
        for limb in &mut d {
            let up = e.select64(below, *limb, empty);
            below = std::mem::replace(limb, up);
        }
        moved.push(empty);
    }
    let shift = e.op(Operator::I64Clz, &[d[top]], WType::I64);
    let sixty_three = e.c64(63);
    let back = e.op(Operator::I64Xor, &[shift, sixty_three], WType::I64);
    let d: Vec<V> = (0..d.len())
        .map(|index| e.shl_limb(&d, index, shift, back))
        .collect();
    let reciprocal = e.reciprocal(d[top]);
    let u: Vec<V> = (0..=dividend.len())
        .map(|index| e.shl_limb(dividend, index, shift, back))
        .collect();
    // The remainder starts as the top limbs, which are below the divisor: the
    // top one holds only the bits shifted out. The limbs below them and the
    // zero limbs below the dividend each take a step.
    let (low, high) = u.split_at(u.len() - d.len());
    let mut steps = e.c64(low.len() as u64);
    for &empty in &moved {
        let empty = e.zero_extend(empty);
        steps = e.op(Operator::I64Add, &[steps, empty], WType::I64);
    }
    let start: Vec<V> = std::iter::once(steps)
        .chain(high.iter().copied())
        .chain(low.iter().rev().copied())
        .chain([zero; LIMBS])
        .collect();
    body.set_terminator(
        block,
        Terminator::Br {
            target: target(head, start),
        },
    );

    // The loop: the steps left, the remainder, the limbs of the dividend still
    // to take, from the top, and the quotient.
    let steps = body.add_blockparam(head, WType::I64);
    let mut params = |count: usize| -> Vec<V> {
        (0..count)
            .map(|_| body.add_blockparam(head, WType::I64))
            .collect()
    };
    let (r, pending, q) = (params(d.len()), params(low.len()), params(LIMBS));
    // The remainder with the next limb below it. Its two top limbs give the
    // digit.
    let window: Vec<V> = std::iter::once(pending[0])
        .chain(r[..top].iter().copied())
        .collect();
    // The digit is zero if the window is below the divisor, as when its top
    // limb is zero and the next is below the divisor's top limb.
    let mut e = Emit { body, block: head };
    let top_zero = e.op(Operator::I64Eqz, &[r[top]], WType::I32);
    let next_below = e.op(Operator::I64LtU, &[window[top], d[top]], WType::I32);
    let skip = e.op(Operator::I32And, &[top_zero, next_below], WType::I32);
    let args: Vec<V> = std::iter::once(zero)
        .chain(window.iter().copied())
        .collect();
    body.set_terminator(
        head,
        Terminator::CondBr {
            cond: skip,
            if_true: target(next, args),
            if_false: target(full, vec![]),
        },
    );

    let mut e = Emit { body, block: full };
    let (mut digit, remainder) = e.div_by_reciprocal(r[top], window[top], d[top], reciprocal);
    let rest = if wide {
        // The two top limbs divided by the divisor's top limb, or the largest
        // digit when the top limbs are equal, is the digit or at most two
        // more (Knuth, 4.3.1, theorem B).
        let ones = e.c64(u64::MAX);
        let largest = e.op(Operator::I64GeU, &[r[top], d[top]], WType::I32);
        digit = e.select64(ones, digit, largest);
        // Subtract the divisor times the estimate. `carry` is what the next
        // limb still owes: the high half of the product and the borrow.
        let mut rest = limbs_at(&window, 0);
        let mut carry = zero;
        for (limb, &factor) in rest.iter_mut().zip(&d) {
            let (low, high) = e.mul_wide(digit, factor);
            let low = e.op(Operator::I64Add, &[low, carry], WType::I64);
            let carried = e.cmp64(Operator::I64LtU, low, carry);
            let borrow = e.cmp64(Operator::I64LtU, *limb, low);
            *limb = e.op(Operator::I64Sub, &[*limb, low], WType::I64);
            let carried = e.zero_extend(carried);
            let borrow = e.zero_extend(borrow);
            let high = e.op(Operator::I64Add, &[high, carried], WType::I64);
            carry = e.op(Operator::I64Add, &[high, borrow], WType::I64);
        }
        // The difference is at least minus twice the divisor, so its limb
        // above the remainder is zero unless it is negative. Add the divisor
        // back for each unit that the estimate is too large.
        let mut above = e.op(Operator::I64Sub, &[r[top], carry], WType::I64);
        for _ in 0..2 {
            let negative = e.op(Operator::I64Ne, &[above, zero], WType::I32);
            let addend = limbs_at(&d, 0).map(|limb| e.select64(limb, zero, negative));
            let (sum, carry) = e.wide_add(rest, addend);
            rest = sum;
            let carry = e.zero_extend(carry);
            above = e.op(Operator::I64Add, &[above, carry], WType::I64);
            let negative = e.zero_extend(negative);
            digit = e.op(Operator::I64Sub, &[digit, negative], WType::I64);
        }
        rest.to_vec()
    } else {
        vec![remainder]
    };
    let args: Vec<V> = std::iter::once(digit).chain(rest).collect();
    body.set_terminator(
        full,
        Terminator::Br {
            target: target(next, args),
        },
    );

    let digit = body.add_blockparam(next, WType::I64);
    let rest: Vec<V> = d
        .iter()
        .map(|_| body.add_blockparam(next, WType::I64))
        .collect();
    let quotient = [digit, q[0], q[1], q[2]];
    let mut e = Emit { body, block: next };
    let one = e.c64(1);
    let steps = e.op(Operator::I64Sub, &[steps, one], WType::I64);
    let finished = e.op(Operator::I64Eqz, &[steps], WType::I32);
    let args: Vec<V> = std::iter::once(steps)
        .chain(rest.iter().copied())
        .chain(pending[1..].iter().copied())
        .chain([zero])
        .chain(quotient)
        .collect();
    body.set_terminator(
        next,
        Terminator::CondBr {
            cond: finished,
            if_true: target(done, vec![]),
            if_false: target(head, args),
        },
    );

    // The remainder is shifted as the divisor was.
    let mut e = Emit { body, block: done };
    let one = e.c64(1);
    let mut remainder = [zero; LIMBS];
    for (index, &limb) in rest.iter().enumerate() {
        remainder[index] = e.op(Operator::I64ShrU, &[limb, shift], WType::I64);
        if let Some(&above) = rest.get(index + 1) {
            let twice = e.op(Operator::I64Shl, &[above, one], WType::I64);
            let high = e.op(Operator::I64Shl, &[twice, back], WType::I64);
            remainder[index] = e.op(Operator::I64Or, &[remainder[index], high], WType::I64);
        }
    }
    for empty in moved {
        let mut above = zero;
        for limb in remainder.iter_mut().rev() {
            let down = e.select64(above, *limb, empty);
            above = std::mem::replace(limb, down);
        }
    }
    (done, quotient, remainder)
}

/// `udivrem(a, b)` returns the quotient and the remainder of unsigned
/// division, and traps if `b` is zero. Values that fit in 64 bits take one
/// division, and a dividend below the divisor is the remainder. Others take
/// [`divide_long`], by the divisor's low limb if its other limbs are zero.
pub(super) fn build_udivrem(
    wmod: &waffle::Module<'static>,
    sig: waffle::Signature,
) -> waffle::FunctionBody {
    use waffle::{BlockTarget, Terminator};
    let target = |block, args: Vec<V>| BlockTarget { block, args };

    let mut body = waffle::FunctionBody::new(wmod, sig);
    let entry = body.entry;
    let params = helper_params(&body, 2 * LIMBS);
    let (a, b) = (limbs_at(&params, 0), limbs_at(&params, LIMBS));

    let trap = body.add_block();
    body.set_terminator(trap, Terminator::Unreachable);
    let [checked, fast, wide, short, compare, below, long] = [(); 7].map(|_| body.add_block());

    let divisor_zero = Emit {
        body: &mut body,
        block: entry,
    }
    .wide_is_zero(b);
    body.set_terminator(
        entry,
        Terminator::CondBr {
            cond: divisor_zero,
            if_true: target(trap, vec![]),
            if_false: target(checked, vec![]),
        },
    );

    // Values of at most 64 bits.
    let mut e = Emit {
        body: &mut body,
        block: checked,
    };
    let divisor_high = e.op(Operator::I64Or, &[b[1], b[2]], WType::I64);
    let divisor_high = e.op(Operator::I64Or, &[divisor_high, b[3]], WType::I64);
    let mut high = divisor_high;
    for &limb in &a[1..] {
        high = e.op(Operator::I64Or, &[high, limb], WType::I64);
    }
    let small = e.op(Operator::I64Eqz, &[high], WType::I32);
    body.set_terminator(
        checked,
        Terminator::CondBr {
            cond: small,
            if_true: target(fast, vec![]),
            if_false: target(wide, vec![]),
        },
    );
    let mut e = Emit {
        body: &mut body,
        block: fast,
    };
    let quotient = e.op(Operator::I64DivU, &[a[0], b[0]], WType::I64);
    let remainder = e.op(Operator::I64RemU, &[a[0], b[0]], WType::I64);
    let zero = e.c64(0);
    body.set_terminator(
        fast,
        Terminator::Return {
            values: vec![quotient, zero, zero, zero, remainder, zero, zero, zero],
        },
    );

    let one_limb = Emit {
        body: &mut body,
        block: wide,
    }
    .op(Operator::I64Eqz, &[divisor_high], WType::I32);
    body.set_terminator(
        wide,
        Terminator::CondBr {
            cond: one_limb,
            if_true: target(short, vec![]),
            if_false: target(compare, vec![]),
        },
    );

    // A dividend below the divisor is the remainder, and the quotient is zero.
    let less = Emit {
        body: &mut body,
        block: compare,
    }
    .wide_compare(Cmp::Lt, false, a, b);
    body.set_terminator(
        compare,
        Terminator::CondBr {
            cond: less,
            if_true: target(below, vec![]),
            if_false: target(long, vec![]),
        },
    );
    let zero = Emit {
        body: &mut body,
        block: below,
    }
    .wide_zero();
    body.set_terminator(
        below,
        Terminator::Return {
            values: zero.into_iter().chain(a).collect(),
        },
    );

    for (block, divisor) in [(short, &b[..1]), (long, &b[..])] {
        let (done, quotient, remainder) = divide_long(&mut body, block, &a, divisor);
        body.set_terminator(
            done,
            Terminator::Return {
                values: quotient.into_iter().chain(remainder).collect(),
            },
        );
    }
    body
}

/// `(x + y) mod n` for `x` and `y` below `n`: one conditional subtraction,
/// taken when the sum carries out of 256 bits or reaches `n`.
fn add_below_modulus(e: &mut Emit<'_>, x: Limbs, y: Limbs, n: Limbs) -> Limbs {
    let (sum, carry) = e.wide_add(x, y);
    let reaches = e.wide_compare(Cmp::Ge, false, sum, n);
    let wrapped = e.op(Operator::I32Or, &[carry, reaches], WType::I32);
    let (reduced, _) = e.wide_sub(sum, n);
    let mut out = sum;
    for k in 0..LIMBS {
        out[k] = e.select64(reduced[k], sum[k], wrapped);
    }
    out
}

/// Starts `addmod` or `mulmod`, which are zero if the modulus is zero. Returns
/// the body, the operands and the modulus, and the block for a nonzero modulus.
fn modular_entry(
    wmod: &waffle::Module<'static>,
    sig: waffle::Signature,
) -> (waffle::FunctionBody, [Limbs; 3], waffle::Block) {
    use waffle::{BlockTarget, Terminator};
    let target = |block| BlockTarget {
        block,
        args: vec![],
    };

    let mut body = waffle::FunctionBody::new(wmod, sig);
    let entry = body.entry;
    let params = helper_params(&body, 3 * LIMBS);
    let operands = [0, 1, 2].map(|index| limbs_at(&params, index * LIMBS));
    let zero_block = body.add_block();
    let work = body.add_block();
    let modulus_zero = Emit {
        body: &mut body,
        block: entry,
    }
    .wide_is_zero(operands[2]);
    body.set_terminator(
        entry,
        Terminator::CondBr {
            cond: modulus_zero,
            if_true: target(zero_block),
            if_false: target(work),
        },
    );
    let zero = Emit {
        body: &mut body,
        block: zero_block,
    }
    .wide_zero();
    body.set_terminator(
        zero_block,
        Terminator::Return {
            values: zero.to_vec(),
        },
    );
    (body, operands, work)
}

/// `addmod(a, b, n)`: the sum of `a` and `b` modulo `n`, computed without
/// overflow, and zero if `n` is zero. The operands are reduced with `udivrem`.
/// The sum is then one addition and one conditional subtraction.
pub(super) fn build_addmod(
    wmod: &waffle::Module<'static>,
    sig: waffle::Signature,
    udivrem: waffle::Func,
) -> waffle::FunctionBody {
    let (mut body, [a, b, n], work) = modular_entry(wmod, sig);
    let [a, b] = [a, b].map(|operand| {
        let args: Vec<V> = operand.into_iter().chain(n).collect();
        let carriers = [WType::I64; 2 * LIMBS];
        let out = super::translate::emit_call(&mut body, work, udivrem, &args, &carriers);
        limbs_at(&out, LIMBS)
    });
    let sum = add_below_modulus(
        &mut Emit {
            body: &mut body,
            block: work,
        },
        a,
        b,
        n,
    );
    body.set_terminator(
        work,
        waffle::Terminator::Return {
            values: sum.to_vec(),
        },
    );
    body
}

/// `mulmod(a, b, n)`: the product of `a` and `b` modulo `n`, computed without
/// overflow, and zero if `n` is zero: the remainder of the 512-bit product by
/// [`divide_long`], by the modulus's low limb if its other limbs are zero.
pub(super) fn build_mulmod(
    wmod: &waffle::Module<'static>,
    sig: waffle::Signature,
) -> waffle::FunctionBody {
    use waffle::{BlockTarget, Terminator};
    let target = |block| BlockTarget {
        block,
        args: vec![],
    };

    let (mut body, [a, b, n], work) = modular_entry(wmod, sig);
    let mut e = Emit {
        body: &mut body,
        block: work,
    };
    let mut product = [None; 2 * LIMBS];
    for (i, &x) in a.iter().enumerate() {
        let mut carry = None;
        for (j, &y) in b.iter().enumerate() {
            // The high half is at most 2^64 - 2, so adding two carries cannot
            // wrap.
            let (mut low, mut high) = e.mul_wide(x, y);
            for addend in [product[i + j], carry].into_iter().flatten() {
                low = e.op(Operator::I64Add, &[low, addend], WType::I64);
                let carried = e.cmp64(Operator::I64LtU, low, addend);
                let carried = e.zero_extend(carried);
                high = e.op(Operator::I64Add, &[high, carried], WType::I64);
            }
            product[i + j] = Some(low);
            carry = Some(high);
        }
        product[i + LIMBS] = carry;
    }
    let product = product.map(|limb| limb.expect("every column has a product"));
    let modulus_high = e.op(Operator::I64Or, &[n[1], n[2]], WType::I64);
    let modulus_high = e.op(Operator::I64Or, &[modulus_high, n[3]], WType::I64);
    let one_limb = e.op(Operator::I64Eqz, &[modulus_high], WType::I32);
    let [short, long] = [(); 2].map(|_| body.add_block());
    body.set_terminator(
        work,
        Terminator::CondBr {
            cond: one_limb,
            if_true: target(short),
            if_false: target(long),
        },
    );
    for (block, modulus) in [(short, &n[..1]), (long, &n[..])] {
        let (done, _, remainder) = divide_long(&mut body, block, &product, modulus);
        body.set_terminator(
            done,
            Terminator::Return {
                values: remainder.to_vec(),
            },
        );
    }
    body
}
