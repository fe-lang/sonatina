//! 128- and 256-bit multiplication, division and shifts: calls to the helper
//! functions of the module, and the signed, checked and saturating forms built
//! from the unsigned ones.

use waffle::{Func, Operator, Type as WType};

use sonatina_ir::{Function, InstId, Type, ValueId};

use super::{FunctionTranslator, V, invalid};
use crate::{
    WasmError,
    arith::Arith,
    wide::{LIMBS, Limbs, Wide},
};

/// The helper functions that a module needs, declared before any body is
/// translated.
#[derive(Default, Clone, Copy)]
pub(super) struct WideHelpers {
    pub(super) mulo: Option<Func>,
    pub(super) udivrem: Option<Func>,
    pub(super) shl: Option<Func>,
    pub(super) shr: Option<Func>,
    pub(super) addmod: Option<Func>,
    pub(super) mulmod: Option<Func>,
}

/// The 128- or 256-bit operation that an instruction asks for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum WideOp {
    Mul,
    Umulo,
    Smulo,
    Umulsat,
    Smulsat,
    Udiv,
    Umod,
    Sdiv,
    Smod,
    Shl,
    Shr,
    Sar,
}

impl WideOp {
    pub(super) fn needs(self) -> (bool, bool, bool, bool) {
        // (mulo, udivrem, shl, shr)
        match self {
            Self::Mul | Self::Umulo | Self::Smulo | Self::Umulsat | Self::Smulsat => {
                (true, false, false, false)
            }
            Self::Udiv | Self::Umod | Self::Sdiv | Self::Smod => (false, true, false, false),
            Self::Shl => (false, false, true, false),
            Self::Shr | Self::Sar => (false, false, false, true),
        }
    }
}

impl FunctionTranslator<'_> {
    fn helper(&self, func: Option<Func>, what: &str) -> Result<Func, WasmError> {
        func.ok_or_else(|| {
            invalid(format!(
                "function `{}`: the module has no 256-bit {what} helper",
                self.name
            ))
        })
    }

    fn call_helper(
        &mut self,
        wb: waffle::Block,
        func: Func,
        args: &[V],
        carriers: &[WType],
    ) -> Vec<V> {
        super::emit_call(&mut self.body, wb, func, args, carriers)
    }

    fn sign_of(&mut self, wb: waffle::Block, value: Limbs) -> V {
        let shift = self.emit(wb).c64(63);
        let bit = self
            .emit(wb)
            .op(Operator::I64ShrU, &[value[LIMBS - 1], shift], WType::I64);
        self.emit(wb).op(Operator::I32WrapI64, &[bit], WType::I32)
    }

    /// `if flag { negated } else { value }`.
    fn negate_if(&mut self, wb: waffle::Block, flag: V, value: Limbs) -> Limbs {
        let negated = self.emit(wb).wide_neg(value);
        let mut out = value;
        for k in 0..LIMBS {
            out[k] = self
                .emit(wb)
                .op(Operator::Select, &[negated[k], value[k], flag], WType::I64);
        }
        out
    }

    fn unsigned_divrem(
        &mut self,
        wb: waffle::Block,
        func: Option<Func>,
        a: Limbs,
        b: Limbs,
    ) -> Result<(Limbs, Limbs), WasmError> {
        let func = self.helper(func, "division")?;
        let args: Vec<V> = a.into_iter().chain(b).collect();
        let out = self.call_helper(wb, func, &args, &[WType::I64; 2 * LIMBS]);
        Ok((
            [out[0], out[1], out[2], out[3]],
            [out[4], out[5], out[6], out[7]],
        ))
    }

    fn unsigned_mulo(
        &mut self,
        wb: waffle::Block,
        func: Option<Func>,
        a: Limbs,
        b: Limbs,
    ) -> Result<(Limbs, V), WasmError> {
        let func = self.helper(func, "multiplication")?;
        let args: Vec<V> = a.into_iter().chain(b).collect();
        let out = self.call_helper(
            wb,
            func,
            &args,
            &[WType::I64, WType::I64, WType::I64, WType::I64, WType::I32],
        );
        Ok(([out[0], out[1], out[2], out[3]], out[4]))
    }

    /// The result of an addition, subtraction or multiplication of `wide`, and
    /// whether the exact result does not fit, as unsigned or signed values. The
    /// operands are extended to 256 bits, with the sign when `signed`. A 128-bit
    /// result is the low 128 bits of the 256-bit one.
    pub(super) fn wide_overflowing(
        &mut self,
        wb: waffle::Block,
        wide: Wide,
        arith: Arith,
        signed: bool,
        a: Limbs,
        b: Limbs,
    ) -> Result<(Limbs, V), WasmError> {
        if wide == Wide::I128 {
            // The operands are below 2^128 in magnitude, so a result that fits
            // in 128 bits is exact at 256 bits. The low 256 bits of a product
            // are the same for signed operands as for unsigned ones.
            let result = match arith {
                Arith::Add => self.emit(wb).wide_add(a, b).0,
                Arith::Sub => self.emit(wb).wide_sub(a, b).0,
                Arith::Mul => self.unsigned_mulo(wb, self.wide_helpers.mulo, a, b)?.0,
            };
            let overflow = self.emit(wb).wide_exceeds(wide, signed, result);
            return Ok((result, overflow));
        }
        let sub = match arith {
            Arith::Add => false,
            Arith::Sub => true,
            Arith::Mul if signed => return self.signed_mulo(wb, a, b),
            Arith::Mul => return self.unsigned_mulo(wb, self.wide_helpers.mulo, a, b),
        };
        let mut emit = self.emit(wb);
        let (result, carry) = if sub {
            emit.wide_sub(a, b)
        } else {
            emit.wide_add(a, b)
        };
        let overflow = if signed {
            emit.wide_signed_overflow(sub, a, b, result)
        } else {
            carry
        };
        Ok((result, overflow))
    }

    /// Multiply the magnitudes. The product fits if it is below 2^255, or
    /// equal to 2^255 when the result is negative.
    fn signed_mulo(
        &mut self,
        wb: waffle::Block,
        a: Limbs,
        b: Limbs,
    ) -> Result<(Limbs, V), WasmError> {
        let (sign_a, sign_b) = (self.sign_of(wb, a), self.sign_of(wb, b));
        let magnitude_a = self.negate_if(wb, sign_a, a);
        let magnitude_b = self.negate_if(wb, sign_b, b);
        let (product, unsigned_overflow) =
            self.unsigned_mulo(wb, self.wide_helpers.mulo, magnitude_a, magnitude_b)?;
        let negative = self
            .emit(wb)
            .op(Operator::I32Xor, &[sign_a, sign_b], WType::I32);
        let top = product[LIMBS - 1];
        let min_top = self.emit(wb).c64(1 << 63);
        let above = self
            .emit(wb)
            .op(Operator::I64GeU, &[top, min_top], WType::I32);
        // Exactly 2^255: the top limb is 2^63 and the rest are zero.
        let is_min = {
            let mut rest = self.emit(wb).c64(0);
            for &limb in &product[..LIMBS - 1] {
                rest = self.emit(wb).op(Operator::I64Or, &[rest, limb], WType::I64);
            }
            let rest_zero = self.emit(wb).op(Operator::I64Eqz, &[rest], WType::I32);
            let top_min = self
                .emit(wb)
                .op(Operator::I64Eq, &[top, min_top], WType::I32);
            self.emit(wb)
                .op(Operator::I32And, &[rest_zero, top_min], WType::I32)
        };
        let not_negative = self.emit(wb).op(Operator::I32Eqz, &[negative], WType::I32);
        let too_big_positive =
            self.emit(wb)
                .op(Operator::I32And, &[not_negative, above], WType::I32);
        let not_min = self.emit(wb).op(Operator::I32Eqz, &[is_min], WType::I32);
        let too_big_negative = {
            let beyond = self
                .emit(wb)
                .op(Operator::I32And, &[above, not_min], WType::I32);
            self.emit(wb)
                .op(Operator::I32And, &[negative, beyond], WType::I32)
        };
        let mut overflow = self.emit(wb).op(
            Operator::I32Or,
            &[unsigned_overflow, too_big_positive],
            WType::I32,
        );
        overflow = self
            .emit(wb)
            .op(Operator::I32Or, &[overflow, too_big_negative], WType::I32);
        let result = self.negate_if(wb, negative, product);
        Ok((result, overflow))
    }

    /// The result of a saturating operation of `wide`: the wrapped result, or
    /// when it overflows, the bound in the direction of the overflow. The
    /// operands are as for [`Self::wide_overflowing`]. Unsigned operations
    /// saturate to zero for a subtraction and to the maximum otherwise. Signed
    /// ones saturate toward the sign of `a` for addition and subtraction, and
    /// toward the sign of the product for multiplication.
    pub(super) fn wide_saturating(
        &mut self,
        wb: waffle::Block,
        wide: Wide,
        arith: Arith,
        signed: bool,
        a: Limbs,
        b: Limbs,
    ) -> Result<Limbs, WasmError> {
        let (result, overflow) = self.wide_overflowing(wb, wide, arith, signed, a, b)?;
        let top = wide.limbs() - 1;
        let mut e = self.emit(wb);
        let fill = signed.then(|| {
            let sign = match arith {
                Arith::Mul => e.op(Operator::I64Xor, &[a[top], b[top]], WType::I64),
                Arith::Add | Arith::Sub => a[top],
            };
            e.sign_fill(sign)
        });
        let mut saturated = result;
        for (index, limb) in saturated.iter_mut().enumerate().take(top + 1) {
            let bound = match fill {
                // The minimum is the complement of the maximum, so flip the
                // maximum by the sign fill of the direction.
                Some(fill) => {
                    let max = e.c64(if index == top {
                        u64::MAX >> 1
                    } else {
                        u64::MAX
                    });
                    e.op(Operator::I64Xor, &[max, fill], WType::I64)
                }
                None => e.c64(match arith {
                    Arith::Sub => 0,
                    Arith::Add | Arith::Mul => u64::MAX,
                }),
            };
            *limb = e.op(Operator::Select, &[bound, *limb, overflow], WType::I64);
        }
        Ok(saturated)
    }

    /// Translate a 128- or 256-bit multiplication (wrapping, checked or
    /// saturating), division or shift.
    pub(super) fn wide_arith(
        &mut self,
        wb: waffle::Block,
        inst_id: InstId,
        wide: Wide,
        op: WideOp,
        (lhs, rhs): (ValueId, ValueId),
    ) -> Result<(), WasmError> {
        let name = self.function.dfg.inst(inst_id).as_text();
        let signed = matches!(
            op,
            WideOp::Smulo | WideOp::Smulsat | WideOp::Sdiv | WideOp::Smod
        );
        let (a, b) = self.wide_operands(wb, name, wide, signed, (lhs, rhs))?;
        let helpers = self.wide_helpers;
        match op {
            WideOp::Mul => {
                let result = match self.emit(wb).wide_mul_short(wide.limbs(), a, b) {
                    Some(result) => result,
                    None => self.unsigned_mulo(wb, helpers.mulo, a, b)?.0,
                };
                self.define_wide(wb, inst_id, 0, wide, result)
            }
            WideOp::Umulo | WideOp::Smulo => {
                let (result, overflow) =
                    self.wide_overflowing(wb, wide, Arith::Mul, signed, a, b)?;
                self.define_wide(wb, inst_id, 0, wide, result)?;
                self.define(inst_id, 1, overflow, Type::I1)
            }
            WideOp::Umulsat | WideOp::Smulsat => {
                let limbs = self.wide_saturating(wb, wide, Arith::Mul, signed, a, b)?;
                self.define_wide(wb, inst_id, 0, wide, limbs)
            }
            WideOp::Udiv | WideOp::Umod => {
                let (quotient, remainder) = self.unsigned_divrem(wb, helpers.udivrem, a, b)?;
                let result = if op == WideOp::Udiv {
                    quotient
                } else {
                    remainder
                };
                self.define_wide(wb, inst_id, 0, wide, result)
            }
            WideOp::Sdiv | WideOp::Smod => {
                let (sign_a, sign_b) = (self.sign_of(wb, a), self.sign_of(wb, b));
                let magnitude_a = self.negate_if(wb, sign_a, a);
                let magnitude_b = self.negate_if(wb, sign_b, b);
                let (quotient, remainder) =
                    self.unsigned_divrem(wb, helpers.udivrem, magnitude_a, magnitude_b)?;
                let result = if op == WideOp::Sdiv {
                    // The quotient is negative if the signs differ. The minimum
                    // divided by -1 wraps to the minimum, as on native: for
                    // 128 bits, the low bits of 2^127 are the minimum.
                    let differ = self
                        .emit(wb)
                        .op(Operator::I32Xor, &[sign_a, sign_b], WType::I32);
                    self.negate_if(wb, differ, quotient)
                } else {
                    // The remainder takes the sign of the dividend.
                    self.negate_if(wb, sign_a, remainder)
                };
                self.define_wide(wb, inst_id, 0, wide, result)
            }
            // A 128-bit shift by 128 to 255 bits leaves zero in the low 128
            // bits, as a shift by at least the width does.
            WideOp::Shl | WideOp::Shr => {
                // A constant count shifts in place.
                if let Some(count) = constant_shift(self.function, rhs) {
                    let shifted = self.emit(wb).wide_shift_by(op == WideOp::Shl, a, count);
                    return self.define_wide(wb, inst_id, 0, wide, shifted);
                }
                let func = if op == WideOp::Shl {
                    self.helper(helpers.shl, "shift")?
                } else {
                    self.helper(helpers.shr, "shift")?
                };
                let args: Vec<V> = a.into_iter().chain(b).collect();
                let out = self.call_helper(wb, func, &args, &[WType::I64; LIMBS]);
                self.define_wide(wb, inst_id, 0, wide, [out[0], out[1], out[2], out[3]])
            }
            WideOp::Sar => {
                // For a negative value, shift the complement and complement the
                // result, so the vacated bits are ones. The count is unsigned.
                let a = self.emit(wb).wide_sign_extend(wide, a);
                let func = self.helper(helpers.shr, "shift")?;
                let sign = self.sign_of(wb, a);
                let flipped = self.emit(wb).wide_not(a);
                let mut input = a;
                for k in 0..LIMBS {
                    input[k] =
                        self.emit(wb)
                            .op(Operator::Select, &[flipped[k], a[k], sign], WType::I64);
                }
                let args: Vec<V> = input.into_iter().chain(b).collect();
                let out = self.call_helper(wb, func, &args, &[WType::I64; LIMBS]);
                let shifted = [out[0], out[1], out[2], out[3]];
                let back = self.emit(wb).wide_not(shifted);
                let mut result = shifted;
                for k in 0..LIMBS {
                    result[k] = self.emit(wb).op(
                        Operator::Select,
                        &[back[k], shifted[k], sign],
                        WType::I64,
                    );
                }
                self.define_wide(wb, inst_id, 0, wide, result)
            }
        }
    }
}

/// The count of a wide shift when it is a constant, which the shift is then
/// built for, without the helper function.
pub(super) fn constant_shift(function: &Function, count: ValueId) -> Option<usize> {
    function.dfg.value_imm(count)?.to_nonnegative_usize()
}

impl FunctionTranslator<'_> {
    /// `evm_add_mod` or `evm_mul_mod`: a call to the 256-bit helper function,
    /// with narrower operands zero-extended, as on the native target. The sum
    /// or product is exact, and zero if the modulus is zero. The result is
    /// below the modulus, so it fits the operands' width. 128-bit operands are
    /// held zero-extended already.
    pub(super) fn wide_modular(
        &mut self,
        wb: waffle::Block,
        inst_id: InstId,
        product: bool,
        operands: [ValueId; 3],
    ) -> Result<(), WasmError> {
        let name = self.function.dfg.inst(inst_id).as_text();
        let ty = self.function.dfg.value_ty(operands[0]);
        if operands
            .iter()
            .any(|&value| self.function.dfg.value_ty(value) != ty)
        {
            return Err(super::invalid(format!(
                "function `{}`: `{name}` operands have different types",
                self.name
            )));
        }
        let func = if product {
            self.helper(self.wide_helpers.mulmod, "modular multiplication")?
        } else {
            self.helper(self.wide_helpers.addmod, "modular addition")?
        };
        let wide = Wide::from_type(ty);
        let mut args = Vec::with_capacity(3 * LIMBS);
        for value in operands {
            let limbs = match wide {
                Some(_) => self.wide_operand(wb, value)?,
                None => {
                    let int = self.int_ty(name, ty)?;
                    let value = self.operand(wb, value)?;
                    self.emit(wb).wide_extend(int, false, value)
                }
            };
            args.extend(limbs);
        }
        let out = self.call_helper(wb, func, &args, &[WType::I64; LIMBS]);
        let limbs = [out[0], out[1], out[2], out[3]];
        match wide {
            Some(wide) => self.define_wide(wb, inst_id, 0, wide, limbs),
            None => {
                let int = self.int_ty(name, ty)?;
                let value = self.emit(wb).wide_trunc(int, limbs);
                self.define(inst_id, 0, value, ty)
            }
        }
    }
}
