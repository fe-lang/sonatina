//! Carry chains over 64-bit limbs.
//!
//! Fe spells one limb of a multi-word addition as
//! `(a as u128) + (b as u128) + (carry as u128)`, its low word the sum and
//! its high word the carry out, and one limb of a subtraction as
//! `(a as u128) - (b as u128) - (borrow as u128)`, bit 127 the borrow out.
//! As i128 arithmetic, each limb is a 128-bit addition and a carry fix-up.
//! When the incoming carry is 0 or 1, a limb is one `uadd_overflow_cin` (or
//! `usub_overflow_bin`), and the next limb takes its carry as the flag that
//! produced it.

use std::collections::HashMap;

use cranelift_codegen::ir::{
    self as clif, InstBuilder,
    types::{I8, I64},
};
use cranelift_frontend::FunctionBuilder;
use smallvec::SmallVec;
use sonatina_codegen::analysis::known_bits::KnownBitsQuery;
use sonatina_ir::{
    Function, Type, ValueId,
    inst::{
        InstId,
        arith::{Add, Shr, Sub},
        cast::{Trunc, Zext},
    },
};

use super::{ValueMap, resolve_value};

/// One limb: `a + b + carry` or `a - b - carry` of 64-bit words, where
/// `carry` is 0 or 1.
pub(super) struct Limb {
    a: Word,
    b: Word,
    carry: Option<Word>,
}

/// A 64-bit word of a limb: an i64 value, or a constant.
#[derive(Clone, Copy)]
enum Word {
    Value(ValueId),
    Const(u64),
}

#[derive(Default)]
pub(super) struct CarryChains {
    /// Whether an i64 value is 0 or 1.
    bits: HashMap<ValueId, bool>,
    /// The carry flag out of each translated addition limb, by its result.
    carries: HashMap<ValueId, clif::Value>,
    /// The borrow flag out of each translated subtraction limb, by its result.
    borrows: HashMap<ValueId, clif::Value>,
}

impl CarryChains {
    /// The limb an i128 `add` computes: two zero-extended i64s and, at most,
    /// one more that is 0 or 1.
    pub fn add_limb(
        &mut self,
        function: &Function,
        inst: InstId,
        known_bits: &mut Option<KnownBitsQuery>,
    ) -> Option<Limb> {
        let add = function.dfg.downcast::<&Add>(inst)?;
        let mut terms = SmallVec::<[_; 4]>::new();
        for operand in [*add.lhs(), *add.rhs()] {
            match function
                .dfg
                .value_inst(operand)
                .and_then(|inst| function.dfg.downcast::<&Add>(inst))
            {
                Some(inner) => terms.extend([*inner.lhs(), *inner.rhs()]),
                None => terms.push(operand),
            }
        }
        let terms = terms
            .into_iter()
            .map(|term| widened_word(function, term))
            .collect::<Option<SmallVec<[_; 4]>>>()?;
        match terms[..] {
            [a, b] => Some(Limb { a, b, carry: None }),
            // The carry is a term that is 0 or 1, the last one first.
            [x, y, z] => [(x, y, z), (x, z, y), (y, z, x)]
                .into_iter()
                .find(|&(_, _, carry)| self.is_bit(function, carry, known_bits))
                .map(|(a, b, carry)| Limb {
                    a,
                    b,
                    carry: Some(carry),
                }),
            _ => None,
        }
    }

    /// The limb an i128 `sub` computes: a zero-extended i64 less another and,
    /// at most, a third that is 0 or 1.
    pub fn sub_limb(
        &mut self,
        function: &Function,
        inst: InstId,
        known_bits: &mut Option<KnownBitsQuery>,
    ) -> Option<Limb> {
        let sub = function.dfg.downcast::<&Sub>(inst)?;
        let subtrahend = widened_word(function, *sub.rhs())?;
        let minuend = *sub.lhs();
        if let Some(inner) = function
            .dfg
            .value_inst(minuend)
            .and_then(|inst| function.dfg.downcast::<&Sub>(inst))
            && let Some(a) = widened_word(function, *inner.lhs())
            && let Some(b) = widened_word(function, *inner.rhs())
        {
            return self
                .is_bit(function, subtrahend, known_bits)
                .then_some(Limb {
                    a,
                    b,
                    carry: Some(subtrahend),
                });
        }
        Some(Limb {
            a: widened_word(function, minuend)?,
            b: subtrahend,
            carry: None,
        })
    }

    pub fn translate_add(
        &mut self,
        function: &Function,
        inst: InstId,
        limb: Limb,
        value_map: &mut ValueMap,
        builder: &mut FunctionBuilder,
    ) -> Result<(), String> {
        let a = word(function, limb.a, value_map, builder)?;
        let b = word(function, limb.b, value_map, builder)?;
        let (sum, carry) = match limb.carry {
            Some(carry) => {
                let carry = self.flag(function, carry, value_map, builder)?;
                builder.ins().uadd_overflow_cin(a, b, carry)
            }
            None => builder.ins().uadd_overflow(a, b),
        };
        let high = builder.ins().uextend(I64, carry);
        let result = function.dfg.inst_result(inst).ok_or("add has no result")?;
        value_map.insert(result, builder.ins().iconcat(sum, high));
        self.carries.insert(result, carry);
        Ok(())
    }

    pub fn translate_sub(
        &mut self,
        function: &Function,
        inst: InstId,
        limb: Limb,
        value_map: &mut ValueMap,
        builder: &mut FunctionBuilder,
    ) -> Result<(), String> {
        let a = word(function, limb.a, value_map, builder)?;
        let b = word(function, limb.b, value_map, builder)?;
        let (difference, borrow) = match limb.carry {
            Some(borrow) => {
                let borrow = self.flag(function, borrow, value_map, builder)?;
                builder.ins().usub_overflow_bin(a, b, borrow)
            }
            None => builder.ins().usub_overflow(a, b),
        };
        // The 128-bit difference's high word is all ones exactly on a borrow.
        let borrow_word = builder.ins().uextend(I64, borrow);
        let high = builder.ins().ineg(borrow_word);
        let result = function.dfg.inst_result(inst).ok_or("sub has no result")?;
        value_map.insert(result, builder.ins().iconcat(difference, high));
        self.borrows.insert(result, borrow);
        Ok(())
    }

    /// A translated limb's carry or borrow, shifted down to bit 0 as an
    /// i128: the high word of an addition limb, or bit 127 of a subtraction
    /// limb.
    pub fn shifted_flag(
        &self,
        function: &Function,
        shr: &Shr,
        builder: &mut FunctionBuilder,
    ) -> Option<clif::Value> {
        let flag = self.flag_out(*shr.value(), shift_count(function, *shr.bits())?)?;
        let low = builder.ins().uextend(I64, flag);
        let high = builder.ins().iconst(I64, 0);
        Some(builder.ins().iconcat(low, high))
    }

    /// Whether `word` is 0 or 1.
    fn is_bit(
        &mut self,
        function: &Function,
        word: Word,
        known_bits: &mut Option<KnownBitsQuery>,
    ) -> bool {
        let value = match word {
            Word::Value(value) => value,
            Word::Const(constant) => return constant <= 1,
        };
        if let Some(&bit) = self.bits.get(&value) {
            return bit;
        }
        let bit = self.is_carry_out(function, value, known_bits)
            || known_bits
                .get_or_insert_with(|| KnownBitsQuery::new(function))
                .fits_in_low_bits(function, value, 1);
        self.bits.insert(value, bit);
        bit
    }

    /// Whether `value` is the carry out of an addition limb: its i128 high
    /// word, at most 1 since the limb's sum is below 2^65.
    fn is_carry_out(
        &mut self,
        function: &Function,
        value: ValueId,
        known_bits: &mut Option<KnownBitsQuery>,
    ) -> bool {
        let Some((limb, 64)) = truncated_shift(function, value) else {
            return false;
        };
        function
            .dfg
            .value_inst(limb)
            .is_some_and(|inst| self.add_limb(function, inst, known_bits).is_some())
    }

    /// The flag of a translated limb that `limb >> count` shifts down to
    /// bit 0.
    fn flag_out(&self, limb: ValueId, count: u32) -> Option<clif::Value> {
        match count {
            64 => self.carries.get(&limb).copied(),
            127 => self.borrows.get(&limb).copied(),
            _ => None,
        }
    }

    /// The carry (or borrow) `carry` as a flag: the flag of the limb it
    /// comes out of, or its low byte.
    fn flag(
        &self,
        function: &Function,
        carry: Word,
        value_map: &ValueMap,
        builder: &mut FunctionBuilder,
    ) -> Result<clif::Value, String> {
        if let Word::Value(value) = carry
            && let Some((limb, count)) = truncated_shift(function, value)
            && let Some(flag) = self.flag_out(limb, count)
        {
            return Ok(flag);
        }
        let carry = word(function, carry, value_map, builder)?;
        Ok(builder.ins().ireduce(I8, carry))
    }
}

/// The word that `value`, an i128, zero-extends: an i64 value or a constant
/// below 2^64.
fn widened_word(function: &Function, value: ValueId) -> Option<Word> {
    if function.dfg.value_ty(value) != Type::I128 {
        return None;
    }
    if let Some(constant) = function.dfg.value_imm(value) {
        let constant = constant.as_i256().to_u256();
        return (constant <= u64::MAX.into()).then(|| Word::Const(constant.low_u64()));
    }
    let zext = function
        .dfg
        .downcast::<&Zext>(function.dfg.value_inst(value)?)?;
    (function.dfg.value_ty(*zext.from()) == Type::I64).then_some(Word::Value(*zext.from()))
}

fn word(
    function: &Function,
    word: Word,
    value_map: &ValueMap,
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    match word {
        Word::Value(value) => resolve_value(function, value, value_map, builder),
        Word::Const(constant) => Ok(builder.ins().iconst(I64, constant as i64)),
    }
}

/// The i128 `limb` and constant count of `trunc (shr limb count)` that
/// `value` is.
fn truncated_shift(function: &Function, value: ValueId) -> Option<(ValueId, u32)> {
    let trunc = function
        .dfg
        .downcast::<&Trunc>(function.dfg.value_inst(value)?)?;
    let shr = function
        .dfg
        .downcast::<&Shr>(function.dfg.value_inst(*trunc.from())?)?;
    let count = shift_count(function, *shr.bits())?;
    (function.dfg.value_ty(*shr.value()) == Type::I128).then_some((*shr.value(), count))
}

/// The constant count of an i128 shift.
fn shift_count(function: &Function, bits: ValueId) -> Option<u32> {
    let count = function.dfg.value_imm(bits)?.as_i256().to_u256();
    (count < 128.into()).then(|| count.low_u32())
}
