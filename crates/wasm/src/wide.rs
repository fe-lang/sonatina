//! 256-bit integers, as far as indexing and counting need them.
//!
//! Fe's `usize` has 256 bits, so every array index and every loop counter over
//! an array is an `i256` in the IR. A 256-bit value is held as four `i64`
//! limbs, least significant first, which are four WebAssembly values: a phi of
//! this type has four block parameters, a function takes or returns four
//! values, and memory holds it as 32 little-endian bytes.
//!
//! Supported: constants, `zext`, `sext`, `trunc`, `add`, `sub`, `neg`, `not`,
//! `and`, `or`, `xor`, the ten comparisons, `is_zero`, `uaddo`, `usubo`,
//! `saddo`, `ssubo`, `snego`, `bswap`, multiplication, division and shifts. The
//! saturating forms are rejected with an error that names the instruction.

use waffle::{Operator, Type as WType};

use sonatina_ir::I256;

use super::arith::{Cmp, Emit, Int};

type V = waffle::Value;

/// The limbs of a 256-bit value, least significant first.
pub(super) type Limbs = [V; 4];

pub(super) const LIMBS: usize = 4;

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

    fn cmp64(&mut self, op: Operator, a: V, b: V) -> V {
        self.op(op, &[a, b], WType::I32)
    }

    /// `zext` or `sext` of an integer of at most 64 bits.
    pub(super) fn wide_extend(&mut self, from: Int, signed: bool, value: V) -> Limbs {
        let low = self.resize(from, Int::I64, signed, value);
        let fill = if signed {
            let shift = self.c64(63);
            self.op(Operator::I64ShrS, &[low, shift], WType::I64)
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
            let sum = self.op(Operator::I64Add, &[lhs[index], rhs[index]], WType::I64);
            let carry_a = self.cmp64(Operator::I64LtU, sum, lhs[index]);
            let (sum, carry_out) = match carry {
                None => (sum, carry_a),
                Some(carry_in) => {
                    let carry_in64 = self.op(Operator::I64ExtendI32U, &[carry_in], WType::I64);
                    let with_carry = self.op(Operator::I64Add, &[sum, carry_in64], WType::I64);
                    let carry_b = self.cmp64(Operator::I64LtU, with_carry, sum);
                    let carry_out = self.op(Operator::I32Or, &[carry_a, carry_b], WType::I32);
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
            let diff = self.op(Operator::I64Sub, &[lhs[index], rhs[index]], WType::I64);
            let borrow_a = self.cmp64(Operator::I64LtU, lhs[index], rhs[index]);
            let (diff, borrow_out) = match borrow {
                None => (diff, borrow_a),
                Some(borrow_in) => {
                    let borrow_in64 = self.op(Operator::I64ExtendI32U, &[borrow_in], WType::I64);
                    let with_borrow = self.op(Operator::I64Sub, &[diff, borrow_in64], WType::I64);
                    let borrow_b = self.cmp64(Operator::I64LtU, diff, borrow_in64);
                    let borrow_out = self.op(Operator::I32Or, &[borrow_a, borrow_b], WType::I32);
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

    /// Byte reversal: the limbs in the opposite order, each reversed.
    pub(super) fn wide_bswap(&mut self, value: Limbs) -> Limbs {
        let mut result = value;
        for index in 0..LIMBS {
            result[index] = self.bswap(Int::I64, value[LIMBS - 1 - index]);
        }
        result
    }

    /// Leading zero bits of a 256-bit value. The count is at most 256, so it
    /// is held in the lowest limb.
    pub(super) fn wide_clz(&mut self, value: Limbs) -> Limbs {
        let zero = self.c64(0);
        let base = self.c64(192);
        let low = self.op(Operator::I64Clz, &[value[0]], WType::I64);
        let mut count = self.op(Operator::I64Add, &[low, base], WType::I64);
        for (index, bits) in [(1, 128), (2, 64), (3, 0)] {
            let mut here = self.op(Operator::I64Clz, &[value[index]], WType::I64);
            if bits != 0 {
                let bits = self.c64(bits);
                here = self.op(Operator::I64Add, &[here, bits], WType::I64);
            }
            let nonzero = self.op(Operator::I64Ne, &[value[index], zero], WType::I32);
            count = self.op(Operator::Select, &[here, count, nonzero], WType::I64);
        }
        let mut result = [zero; LIMBS];
        result[0] = count;
        result
    }

    pub(super) fn wide_not(&mut self, value: Limbs) -> Limbs {
        let ones = self.c64(u64::MAX);
        value.map(|limb| self.op(Operator::I64Xor, &[limb, ones], WType::I64))
    }

    pub(super) fn wide_bitwise(&mut self, op: Operator, lhs: Limbs, rhs: Limbs) -> Limbs {
        let mut result = lhs;
        for index in 0..LIMBS {
            result[index] = self.op(op, &[lhs[index], rhs[index]], WType::I64);
        }
        result
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
                self.op(Operator::I64Xor, &[a, b], WType::I64),
                self.op(Operator::I64Xor, &[a, r], WType::I64),
            )
        } else {
            (
                self.op(Operator::I64Xor, &[a, r], WType::I64),
                self.op(Operator::I64Xor, &[b, r], WType::I64),
            )
        };
        let both = self.op(Operator::I64And, &[left, right], WType::I64);
        let shift = self.c64(63);
        let bit = self.op(Operator::I64ShrU, &[both, shift], WType::I64);
        self.op(Operator::I32WrapI64, &[bit], WType::I32)
    }

    pub(super) fn wide_snego(&mut self, value: Limbs) -> (Limbs, V) {
        let negated = self.wide_neg(value);
        // Only the minimum value is its own negation among non-zero values.
        let min_top = self.c64(1 << 63);
        let top_is_min = self.cmp64(Operator::I64Eq, value[LIMBS - 1], min_top);
        let mut rest = self.c64(0);
        for &limb in &value[..LIMBS - 1] {
            rest = self.op(Operator::I64Or, &[rest, limb], WType::I64);
        }
        let rest_is_zero = self.op(Operator::I64Eqz, &[rest], WType::I32);
        let overflow = self.op(Operator::I32And, &[top_is_min, rest_is_zero], WType::I32);
        (negated, overflow)
    }

    pub(super) fn wide_is_zero(&mut self, value: Limbs) -> V {
        let mut any = value[0];
        for &limb in &value[1..] {
            any = self.op(Operator::I64Or, &[any, limb], WType::I64);
        }
        self.op(Operator::I64Eqz, &[any], WType::I32)
    }

    fn wide_eq(&mut self, lhs: Limbs, rhs: Limbs) -> V {
        let mut diff = self.c64(0);
        for index in 0..LIMBS {
            let x = self.op(Operator::I64Xor, &[lhs[index], rhs[index]], WType::I64);
            diff = self.op(Operator::I64Or, &[diff, x], WType::I64);
        }
        self.op(Operator::I64Eqz, &[diff], WType::I32)
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
            less = self.op(Operator::Select, &[less, limb_less, equal], WType::I32);
        }
        less
    }

    pub(super) fn wide_compare(&mut self, cmp: Cmp, signed: bool, lhs: Limbs, rhs: Limbs) -> V {
        let not = |this: &mut Self, value: V| this.op(Operator::I32Eqz, &[value], WType::I32);
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
        let mut high = self.op(Operator::I64ShrU, &[value[0], shift], WType::I64);
        for &limb in &value[1..] {
            high = self.op(Operator::I64Or, &[high, limb], WType::I64);
        }
        let zero = self.c64(0);
        self.op(Operator::I64Ne, &[high, zero], WType::I32)
    }

    /// An `i32` that is non-zero if the value does not fit in a signed 32-bit
    /// integer.
    pub(super) fn wide_exceeds_i32(&mut self, value: Limbs) -> V {
        // The value fits if limb 0 sign-extends from 32 bits to itself and the
        // limbs above are its sign fill.
        let low = self.op(Operator::I32WrapI64, &[value[0]], WType::I32);
        let extended = self.op(Operator::I64ExtendI32S, &[low], WType::I64);
        let mut diff = self.op(Operator::I64Xor, &[extended, value[0]], WType::I64);
        let shift = self.c64(63);
        let fill = self.op(Operator::I64ShrS, &[value[0], shift], WType::I64);
        for &limb in &value[1..] {
            let x = self.op(Operator::I64Xor, &[limb, fill], WType::I64);
            diff = self.op(Operator::I64Or, &[diff, x], WType::I64);
        }
        let zero = self.c64(0);
        self.op(Operator::I64Ne, &[diff, zero], WType::I32)
    }
}

// Multiplication, division and shifts are too long to repeat at every use, so
// they are functions of the module that calls them with four limbs per operand.

impl Emit<'_> {
    fn select64(&mut self, if_true: V, if_false: V, cond: V) -> V {
        self.op(Operator::Select, &[if_true, if_false, cond], WType::I64)
    }

    fn zero_extend(&mut self, flag: V) -> V {
        self.op(Operator::I64ExtendI32U, &[flag], WType::I64)
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

    /// Select limb `index` of `limbs` (0 to 3) by a run-time `index`.
    fn pick_limb(&mut self, limbs: Limbs, index: V) -> V {
        let mut picked = self.c64(0);
        for (k, &limb) in limbs.iter().enumerate() {
            let k = self.c32(k as u32);
            let is_k = self.op(Operator::I32Eq, &[index, k], WType::I32);
            picked = self.select64(limb, picked, is_k);
        }
        picked
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
    body.convert_to_max_ssa(None);
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
    body.convert_to_max_ssa(None);
    body
}

/// `udivrem(a, b)` returns the quotient and the remainder of unsigned
/// division, and traps if `b` is zero. Values that fit in 64 bits take one
/// division. Others take one step per bit of `a`.
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
    let checked = body.add_block();
    let fast = body.add_block();
    let setup = body.add_block();
    let header = body.add_block();
    let step = body.add_block();
    let done = body.add_block();

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
    let mut high = a[1];
    for &limb in [a[2], a[3], b[1], b[2], b[3]].iter() {
        high = e.op(Operator::I64Or, &[high, limb], WType::I64);
    }
    let small = e.op(Operator::I64Eqz, &[high], WType::I32);
    body.set_terminator(
        checked,
        Terminator::CondBr {
            cond: small,
            if_true: target(fast, vec![]),
            if_false: target(setup, vec![]),
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

    // The number of bits of `a`.
    let mut e = Emit {
        body: &mut body,
        block: setup,
    };
    let zero = e.c64(0);
    let mut leading = e.c64(256);
    for (k, &limb) in a.iter().enumerate() {
        let clz = e.op(Operator::I64Clz, &[limb], WType::I64);
        let offset = e.c64(64 * (LIMBS - 1 - k) as u64);
        let count = e.op(Operator::I64Add, &[clz, offset], WType::I64);
        let nonzero = e.op(Operator::I64Ne, &[limb, zero], WType::I32);
        leading = e.select64(count, leading, nonzero);
    }
    let bits64 = {
        let total = e.c64(256);
        e.op(Operator::I64Sub, &[total, leading], WType::I64)
    };
    let bits = e.op(Operator::I32WrapI64, &[bits64], WType::I32);
    let start: Vec<V> = std::iter::once(bits)
        .chain(std::iter::repeat_n(zero, 2 * LIMBS))
        .collect();
    body.set_terminator(
        setup,
        Terminator::Br {
            target: target(header, start),
        },
    );

    // The loop: `remaining` bits of `a` are still to be taken from the top.
    let remaining = body.add_blockparam(header, WType::I32);
    let q: Vec<V> = (0..LIMBS)
        .map(|_| body.add_blockparam(header, WType::I64))
        .collect();
    let r: Vec<V> = (0..LIMBS)
        .map(|_| body.add_blockparam(header, WType::I64))
        .collect();
    let (q, r) = (limbs_at(&q, 0), limbs_at(&r, 0));
    let finished = Emit {
        body: &mut body,
        block: header,
    }
    .op(Operator::I32Eqz, &[remaining], WType::I32);
    body.set_terminator(
        header,
        Terminator::CondBr {
            cond: finished,
            if_true: target(done, vec![]),
            if_false: target(step, vec![]),
        },
    );

    let mut e = Emit {
        body: &mut body,
        block: step,
    };
    let one = e.c32(1);
    let index = e.op(Operator::I32Sub, &[remaining, one], WType::I32);
    let six = e.c32(6);
    let limb_index = e.op(Operator::I32ShrU, &[index, six], WType::I32);
    let sixty_three = e.c32(63);
    let bit_index32 = e.op(Operator::I32And, &[index, sixty_three], WType::I32);
    let bit_index = e.op(Operator::I64ExtendI32U, &[bit_index32], WType::I64);
    let source = e.pick_limb(a, limb_index);
    let moved = e.op(Operator::I64ShrU, &[source, bit_index], WType::I64);
    let one64 = e.c64(1);
    let bit = e.op(Operator::I64And, &[moved, one64], WType::I64);
    // r = (r << 1) | bit
    let sixty_three64 = e.c64(63);
    let mut shifted = r;
    for k in 0..LIMBS {
        let up = e.op(Operator::I64Shl, &[r[k], one64], WType::I64);
        let carry = if k == 0 {
            bit
        } else {
            e.op(Operator::I64ShrU, &[r[k - 1], sixty_three64], WType::I64)
        };
        shifted[k] = e.op(Operator::I64Or, &[up, carry], WType::I64);
    }
    let at_least = e.wide_compare(Cmp::Ge, false, shifted, b);
    let (reduced, _) = e.wide_sub(shifted, b);
    let mut next_r = shifted;
    let mut next_q = q;
    let place = e.op(Operator::I64Shl, &[one64, bit_index], WType::I64);
    let zero64 = e.c64(0);
    for k in 0..LIMBS {
        next_r[k] = e.select64(reduced[k], shifted[k], at_least);
        let kk = e.c32(k as u32);
        let in_limb = e.op(Operator::I32Eq, &[limb_index, kk], WType::I32);
        let chosen = e.op(Operator::I32And, &[in_limb, at_least], WType::I32);
        let bits = e.select64(place, zero64, chosen);
        next_q[k] = e.op(Operator::I64Or, &[q[k], bits], WType::I64);
    }
    let args: Vec<V> = std::iter::once(index).chain(next_q).chain(next_r).collect();
    body.set_terminator(
        step,
        Terminator::Br {
            target: target(header, args),
        },
    );

    body.set_terminator(
        done,
        Terminator::Return {
            values: q.into_iter().chain(r).collect(),
        },
    );
    body.convert_to_max_ssa(None);
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

/// `addmod(a, b, n)` or `mulmod(a, b, n)`: the sum or product of `a` and `b`
/// modulo `n`, computed without overflow, and zero if `n` is zero.
///
/// The operands are reduced with `udivrem`. The sum is then one addition and
/// one conditional subtraction. The product takes one step per bit of `b`, from
/// the top: double the running value modulo `n`, and add `a` modulo `n` when the
/// bit is set. No step exceeds the modulus.
pub(super) fn build_modular(
    wmod: &waffle::Module<'static>,
    sig: waffle::Signature,
    udivrem: waffle::Func,
    product: bool,
) -> waffle::FunctionBody {
    use waffle::{BlockTarget, Terminator};
    let target = |block, args: Vec<V>| BlockTarget { block, args };

    let mut body = waffle::FunctionBody::new(wmod, sig);
    let entry = body.entry;
    let params = helper_params(&body, 3 * LIMBS);
    let (a, b, n) = (
        limbs_at(&params, 0),
        limbs_at(&params, LIMBS),
        limbs_at(&params, 2 * LIMBS),
    );
    let remainder_carriers = [WType::I64; 2 * LIMBS];

    let zero_block = body.add_block();
    let work = body.add_block();
    let modulus_zero = Emit {
        body: &mut body,
        block: entry,
    }
    .wide_is_zero(n);
    body.set_terminator(
        entry,
        Terminator::CondBr {
            cond: modulus_zero,
            if_true: target(zero_block, vec![]),
            if_false: target(work, vec![]),
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

    // The operands modulo `n`.
    let args_a: Vec<V> = a.into_iter().chain(n).collect();
    let out_a = super::translate::emit_call(&mut body, work, udivrem, &args_a, &remainder_carriers);
    let a_reduced = limbs_at(&out_a, LIMBS);

    if !product {
        let args_b: Vec<V> = b.into_iter().chain(n).collect();
        let out_b =
            super::translate::emit_call(&mut body, work, udivrem, &args_b, &remainder_carriers);
        let b_reduced = limbs_at(&out_b, LIMBS);
        let sum = add_below_modulus(
            &mut Emit {
                body: &mut body,
                block: work,
            },
            a_reduced,
            b_reduced,
            n,
        );
        body.set_terminator(
            work,
            Terminator::Return {
                values: sum.to_vec(),
            },
        );
        body.convert_to_max_ssa(None);
        return body;
    }

    let header = body.add_block();
    let step = body.add_block();
    let done = body.add_block();
    let start: Vec<V> = {
        let mut e = Emit {
            body: &mut body,
            block: work,
        };
        let bits = e.c32(256);
        let zero = e.c64(0);
        std::iter::once(bits)
            .chain(std::iter::repeat_n(zero, LIMBS))
            .collect()
    };
    body.set_terminator(
        work,
        Terminator::Br {
            target: target(header, start),
        },
    );

    // The loop: `remaining` bits of `b` are still to be taken from the top.
    let remaining = body.add_blockparam(header, WType::I32);
    let r: Vec<V> = (0..LIMBS)
        .map(|_| body.add_blockparam(header, WType::I64))
        .collect();
    let r = limbs_at(&r, 0);
    let finished = Emit {
        body: &mut body,
        block: header,
    }
    .op(Operator::I32Eqz, &[remaining], WType::I32);
    body.set_terminator(
        header,
        Terminator::CondBr {
            cond: finished,
            if_true: target(done, vec![]),
            if_false: target(step, vec![]),
        },
    );

    let mut e = Emit {
        body: &mut body,
        block: step,
    };
    let one = e.c32(1);
    let index = e.op(Operator::I32Sub, &[remaining, one], WType::I32);
    let six = e.c32(6);
    let limb_index = e.op(Operator::I32ShrU, &[index, six], WType::I32);
    let sixty_three = e.c32(63);
    let bit_index32 = e.op(Operator::I32And, &[index, sixty_three], WType::I32);
    let bit_index = e.op(Operator::I64ExtendI32U, &[bit_index32], WType::I64);
    let source = e.pick_limb(b, limb_index);
    let moved = e.op(Operator::I64ShrU, &[source, bit_index], WType::I64);
    let one64 = e.c64(1);
    let masked = e.op(Operator::I64And, &[moved, one64], WType::I64);
    let bit = e.op(Operator::I32WrapI64, &[masked], WType::I32);
    let doubled = add_below_modulus(&mut e, r, r, n);
    let added = add_below_modulus(&mut e, doubled, a_reduced, n);
    let mut next = doubled;
    for k in 0..LIMBS {
        next[k] = e.select64(added[k], doubled[k], bit);
    }
    let args: Vec<V> = std::iter::once(index).chain(next).collect();
    body.set_terminator(
        step,
        Terminator::Br {
            target: target(header, args),
        },
    );

    body.set_terminator(done, Terminator::Return { values: r.to_vec() });
    body.convert_to_max_ssa(None);
    body
}
