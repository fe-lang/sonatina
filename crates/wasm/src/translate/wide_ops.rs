//! 256-bit multiplication, division and shifts: calls to the helper functions
//! of the module, and the signed forms built from the unsigned ones.

use waffle::{Func, Operator, Type as WType};

use sonatina_ir::{InstId, Type, ValueId};

use super::{FunctionTranslator, V, invalid};
use crate::{
    WasmError,
    wide::{LIMBS, Limbs},
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

/// The 256-bit operation that an instruction asks for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum WideOp {
    Mul,
    Umulo,
    Smulo,
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
            Self::Mul | Self::Umulo | Self::Smulo => (true, false, false, false),
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

    /// Translate a 256-bit multiplication, division or shift.
    pub(super) fn wide_arith(
        &mut self,
        wb: waffle::Block,
        helpers: WideHelpers,
        inst_id: InstId,
        op: WideOp,
        lhs: ValueId,
        rhs: ValueId,
    ) -> Result<(), WasmError> {
        let name = self.function.dfg.inst(inst_id).as_text();
        let (a, b) = self.wide_operands(wb, name, lhs, rhs)?;
        match op {
            WideOp::Mul => {
                let (result, _) = self.unsigned_mulo(wb, helpers.mulo, a, b)?;
                self.define_wide(inst_id, 0, result)
            }
            WideOp::Umulo => {
                let (result, overflow) = self.unsigned_mulo(wb, helpers.mulo, a, b)?;
                self.define_wide(inst_id, 0, result)?;
                self.define(inst_id, 1, overflow, Type::I1)
            }
            WideOp::Smulo => {
                // Multiply the magnitudes. The product fits if it is below 2^255,
                // or equal to 2^255 when the result is negative.
                let (sign_a, sign_b) = (self.sign_of(wb, a), self.sign_of(wb, b));
                let magnitude_a = self.negate_if(wb, sign_a, a);
                let magnitude_b = self.negate_if(wb, sign_b, b);
                let (product, unsigned_overflow) =
                    self.unsigned_mulo(wb, helpers.mulo, magnitude_a, magnitude_b)?;
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
                overflow =
                    self.emit(wb)
                        .op(Operator::I32Or, &[overflow, too_big_negative], WType::I32);
                let result = self.negate_if(wb, negative, product);
                self.define_wide(inst_id, 0, result)?;
                self.define(inst_id, 1, overflow, Type::I1)
            }
            WideOp::Udiv | WideOp::Umod => {
                let (quotient, remainder) = self.unsigned_divrem(wb, helpers.udivrem, a, b)?;
                self.define_wide(
                    inst_id,
                    0,
                    if op == WideOp::Udiv {
                        quotient
                    } else {
                        remainder
                    },
                )
            }
            WideOp::Sdiv | WideOp::Smod => {
                let (sign_a, sign_b) = (self.sign_of(wb, a), self.sign_of(wb, b));
                let magnitude_a = self.negate_if(wb, sign_a, a);
                let magnitude_b = self.negate_if(wb, sign_b, b);
                let (quotient, remainder) =
                    self.unsigned_divrem(wb, helpers.udivrem, magnitude_a, magnitude_b)?;
                let result = if op == WideOp::Sdiv {
                    // The quotient is negative if the signs differ. The minimum
                    // divided by -1 wraps to the minimum, as on native.
                    let differ = self
                        .emit(wb)
                        .op(Operator::I32Xor, &[sign_a, sign_b], WType::I32);
                    self.negate_if(wb, differ, quotient)
                } else {
                    // The remainder takes the sign of the dividend.
                    self.negate_if(wb, sign_a, remainder)
                };
                self.define_wide(inst_id, 0, result)
            }
            WideOp::Shl => {
                let func = self.helper(helpers.shl, "shift")?;
                let args: Vec<V> = a.into_iter().chain(b).collect();
                let out = self.call_helper(wb, func, &args, &[WType::I64; LIMBS]);
                self.define_wide(inst_id, 0, [out[0], out[1], out[2], out[3]])
            }
            WideOp::Shr => {
                let func = self.helper(helpers.shr, "shift")?;
                let args: Vec<V> = a.into_iter().chain(b).collect();
                let out = self.call_helper(wb, func, &args, &[WType::I64; LIMBS]);
                self.define_wide(inst_id, 0, [out[0], out[1], out[2], out[3]])
            }
            WideOp::Sar => {
                // For a negative value, shift the complement and complement the
                // result, so the vacated bits are ones.
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
                self.define_wide(inst_id, 0, result)
            }
        }
    }
}

impl FunctionTranslator<'_> {
    /// `evm_add_mod` or `evm_mul_mod` on 256-bit operands: a call to the helper
    /// function. The sum or product is exact, and zero if the modulus is zero.
    pub(super) fn wide_modular(
        &mut self,
        wb: waffle::Block,
        inst_id: InstId,
        product: bool,
        operands: [ValueId; 3],
    ) -> Result<(), WasmError> {
        let name = self.function.dfg.inst(inst_id).as_text();
        if operands
            .iter()
            .any(|&value| self.function.dfg.value_ty(value) != Type::I256)
        {
            return Err(super::unsupported(format!(
                "function `{}`: `{name}` is lowered for 256-bit operands only",
                self.name
            )));
        }
        let func = if product {
            self.helper(self.wide_helpers.mulmod, "modular multiplication")?
        } else {
            self.helper(self.wide_helpers.addmod, "modular addition")?
        };
        let mut args = Vec::with_capacity(3 * LIMBS);
        for value in operands {
            args.extend(self.wide_operand(wb, value)?);
        }
        let out = self.call_helper(wb, func, &args, &[WType::I64; LIMBS]);
        self.define_wide(inst_id, 0, [out[0], out[1], out[2], out[3]])
    }
}
