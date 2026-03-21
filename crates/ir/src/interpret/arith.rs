use super::{Action, EvalValue, Interpret, State, single_result};
use crate::inst::arith::*;

impl Interpret for Neg {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let val = state.lookup_val(*self.arg());
        single_result(val.with_imm(|value| -value))
    }
}

impl Interpret for Add {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        single_result(EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| lhs + rhs))
    }
}

impl Interpret for Uaddo {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        let (EvalValue::Imm(lhs), EvalValue::Imm(rhs)) = (lhs, rhs) else {
            return smallvec::smallvec![EvalValue::Undef, EvalValue::Undef];
        };

        let (sum, overflow) = lhs.overflowing_uadd(rhs);
        smallvec::smallvec![EvalValue::Imm(sum), EvalValue::Imm(overflow.into())]
    }
}

impl Interpret for Uaddsat {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        single_result(EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| {
            lhs.saturating_uadd(rhs)
        }))
    }
}

impl Interpret for Saddo {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        let (EvalValue::Imm(lhs), EvalValue::Imm(rhs)) = (lhs, rhs) else {
            return smallvec::smallvec![EvalValue::Undef, EvalValue::Undef];
        };

        let (sum, overflow) = lhs.overflowing_sadd(rhs);
        smallvec::smallvec![EvalValue::Imm(sum), EvalValue::Imm(overflow.into())]
    }
}

impl Interpret for Saddsat {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        single_result(EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| {
            lhs.saturating_sadd(rhs)
        }))
    }
}

impl Interpret for Sub {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        single_result(EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| {
            EvalValue::Imm(lhs - rhs)
        }))
    }
}

impl Interpret for Usubo {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        let (EvalValue::Imm(lhs), EvalValue::Imm(rhs)) = (lhs, rhs) else {
            return smallvec::smallvec![EvalValue::Undef, EvalValue::Undef];
        };

        let (diff, overflow) = lhs.overflowing_usub(rhs);
        smallvec::smallvec![EvalValue::Imm(diff), EvalValue::Imm(overflow.into())]
    }
}

impl Interpret for Usubsat {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        single_result(EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| {
            lhs.saturating_usub(rhs)
        }))
    }
}

impl Interpret for Ssubo {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        let (EvalValue::Imm(lhs), EvalValue::Imm(rhs)) = (lhs, rhs) else {
            return smallvec::smallvec![EvalValue::Undef, EvalValue::Undef];
        };

        let (diff, overflow) = lhs.overflowing_ssub(rhs);
        smallvec::smallvec![EvalValue::Imm(diff), EvalValue::Imm(overflow.into())]
    }
}

impl Interpret for Ssubsat {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        single_result(EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| {
            lhs.saturating_ssub(rhs)
        }))
    }
}

impl Interpret for Mul {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        state.set_action(Action::Continue);

        single_result(EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| lhs * rhs))
    }
}

impl Interpret for Umulo {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        let (EvalValue::Imm(lhs), EvalValue::Imm(rhs)) = (lhs, rhs) else {
            return smallvec::smallvec![EvalValue::Undef, EvalValue::Undef];
        };

        let (product, overflow) = lhs.overflowing_umul(rhs);
        smallvec::smallvec![EvalValue::Imm(product), EvalValue::Imm(overflow.into())]
    }
}

impl Interpret for Umulsat {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        single_result(EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| {
            lhs.saturating_umul(rhs)
        }))
    }
}

impl Interpret for Smulo {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        let (EvalValue::Imm(lhs), EvalValue::Imm(rhs)) = (lhs, rhs) else {
            return smallvec::smallvec![EvalValue::Undef, EvalValue::Undef];
        };

        let (product, overflow) = lhs.overflowing_smul(rhs);
        smallvec::smallvec![EvalValue::Imm(product), EvalValue::Imm(overflow.into())]
    }
}

impl Interpret for Smulsat {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        single_result(EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| {
            lhs.saturating_smul(rhs)
        }))
    }
}

impl Interpret for Snego {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let value = state.lookup_val(*self.arg());
        let EvalValue::Imm(value) = value else {
            return smallvec::smallvec![EvalValue::Undef, EvalValue::Undef];
        };

        let (negated, overflow) = value.overflowing_sneg();
        smallvec::smallvec![EvalValue::Imm(negated), EvalValue::Imm(overflow.into())]
    }
}

impl Interpret for Sdiv {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        single_result(EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| {
            if rhs.is_zero() {
                return EvalValue::Undef;
            }
            lhs.sdiv(rhs).into()
        }))
    }
}

impl Interpret for Udiv {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        single_result(EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| {
            if rhs.is_zero() {
                return EvalValue::Undef;
            }
            lhs.udiv(rhs).into()
        }))
    }
}

impl Interpret for Umod {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        single_result(EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| {
            if rhs.is_zero() {
                return EvalValue::Undef;
            }
            lhs.urem(rhs).into()
        }))
    }
}

impl Interpret for Smod {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        single_result(EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| {
            if rhs.is_zero() {
                return EvalValue::Undef;
            }
            lhs.srem(rhs).into()
        }))
    }
}

impl Interpret for Shl {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let bits = state.lookup_val(*self.bits());
        let value = state.lookup_val(*self.value());
        single_result(EvalValue::zip_with_imm(bits, value, |bits, value| {
            value << bits
        }))
    }
}

impl Interpret for Shr {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let bits = state.lookup_val(*self.bits());
        let value = state.lookup_val(*self.value());

        single_result(EvalValue::zip_with_imm(bits, value, |bits, value| {
            value >> bits
        }))
    }
}

impl Interpret for Sar {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let bits = state.lookup_val(*self.bits());
        let value = state.lookup_val(*self.value());

        single_result(EvalValue::zip_with_imm(bits, value, |bits, value| {
            value.ashr(bits)
        }))
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::{
        DataFlowGraph, HasInst, Immediate, Type,
        builder::test_util::test_isa,
        interpret::EvalResults,
        module::{FuncRef, ModuleCtx},
    };

    use super::*;

    struct TestHasInst;
    impl<I: crate::Inst> HasInst<I> for TestHasInst {}

    struct TestState {
        dfg: DataFlowGraph,
        values: HashMap<crate::ValueId, EvalValue>,
    }

    impl TestState {
        fn new(values: impl IntoIterator<Item = (crate::ValueId, EvalValue)>) -> Self {
            let isa = test_isa();
            let dfg = DataFlowGraph::new(ModuleCtx::new(&isa));
            Self {
                dfg,
                values: values.into_iter().collect(),
            }
        }
    }

    impl State for TestState {
        fn lookup_val(&mut self, value: crate::ValueId) -> EvalValue {
            self.values.get(&value).cloned().unwrap_or_default()
        }

        fn call_func(&mut self, _func: FuncRef, _args: Vec<EvalValue>) -> EvalResults {
            unreachable!()
        }

        fn set_action(&mut self, action: Action) {
            assert_eq!(action, Action::Continue);
        }

        fn prev_block(&mut self) -> crate::BlockId {
            unreachable!()
        }

        fn load(&mut self, _addr: EvalValue, _ty: Type) -> EvalValue {
            unreachable!()
        }

        fn store(&mut self, _addr: EvalValue, _value: EvalValue, _ty: Type) -> EvalValue {
            unreachable!()
        }

        fn alloca(&mut self, _ty: Type) -> EvalValue {
            unreachable!()
        }

        fn dfg(&self) -> &DataFlowGraph {
            &self.dfg
        }
    }

    #[test]
    fn div_mod_by_zero_returns_undef() {
        let hi = TestHasInst;
        let lhs = crate::ValueId::from_u32(0);
        let rhs = crate::ValueId::from_u32(1);

        let mut state = TestState::new([
            (lhs, EvalValue::Imm(Immediate::I32(1))),
            (rhs, EvalValue::Imm(Immediate::I32(0))),
        ]);

        assert_eq!(
            Sdiv::new(&hi, lhs, rhs).interpret(&mut state),
            super::single_result(EvalValue::Undef)
        );
        assert_eq!(
            Udiv::new(&hi, lhs, rhs).interpret(&mut state),
            super::single_result(EvalValue::Undef)
        );
        assert_eq!(
            Umod::new(&hi, lhs, rhs).interpret(&mut state),
            super::single_result(EvalValue::Undef)
        );
        assert_eq!(
            Smod::new(&hi, lhs, rhs).interpret(&mut state),
            super::single_result(EvalValue::Undef)
        );
    }

    #[test]
    fn shift_right_uses_expected_signedness() {
        let hi = TestHasInst;
        let bits = crate::ValueId::from_u32(0);
        let value = crate::ValueId::from_u32(1);
        let mut state = TestState::new([
            (bits, EvalValue::Imm(Immediate::I8(1))),
            (value, EvalValue::Imm(Immediate::I8(-8))),
        ]);

        assert_eq!(
            Shr::new(&hi, bits, value).interpret(&mut state),
            super::single_result(EvalValue::Imm(Immediate::I8(124)))
        );
        assert_eq!(
            Sar::new(&hi, bits, value).interpret(&mut state),
            super::single_result(EvalValue::Imm(Immediate::I8(-4)))
        );
    }

    #[test]
    fn uaddo_returns_sum_and_overflow_flag() {
        let hi = TestHasInst;
        let lhs = crate::ValueId::from_u32(0);
        let rhs = crate::ValueId::from_u32(1);
        let mut state = TestState::new([
            (lhs, EvalValue::Imm(Immediate::I8(-1))),
            (rhs, EvalValue::Imm(Immediate::I8(1))),
        ]);

        assert_eq!(
            Uaddo::new(&hi, lhs, rhs).interpret(&mut state),
            crate::interpret::EvalResults::from_vec(vec![
                EvalValue::Imm(Immediate::I8(0)),
                EvalValue::Imm(Immediate::I1(true))
            ])
        );
    }

    #[test]
    fn signed_overflow_ops_return_wrapped_values_and_flags() {
        let hi = TestHasInst;
        let lhs = crate::ValueId::from_u32(0);
        let rhs = crate::ValueId::from_u32(1);
        let mut state = TestState::new([
            (lhs, EvalValue::Imm(Immediate::I8(-128))),
            (rhs, EvalValue::Imm(Immediate::I8(-1))),
        ]);

        assert_eq!(
            Saddo::new(&hi, lhs, rhs).interpret(&mut state),
            crate::interpret::EvalResults::from_vec(vec![
                EvalValue::Imm(Immediate::I8(127)),
                EvalValue::Imm(Immediate::I1(true))
            ])
        );
        assert_eq!(
            Ssubo::new(&hi, lhs, rhs).interpret(&mut state),
            crate::interpret::EvalResults::from_vec(vec![
                EvalValue::Imm(Immediate::I8(-127)),
                EvalValue::Imm(Immediate::I1(false))
            ])
        );
        assert_eq!(
            Snego::new(&hi, lhs).interpret(&mut state),
            crate::interpret::EvalResults::from_vec(vec![
                EvalValue::Imm(Immediate::I8(-128)),
                EvalValue::Imm(Immediate::I1(true))
            ])
        );
    }

    #[test]
    fn unsigned_and_signed_mul_sub_ops_cover_overflow_cases() {
        let hi = TestHasInst;
        let lhs = crate::ValueId::from_u32(0);
        let rhs = crate::ValueId::from_u32(1);
        let mut state = TestState::new([
            (lhs, EvalValue::Imm(Immediate::I8(-1))),
            (rhs, EvalValue::Imm(Immediate::I8(2))),
        ]);

        assert_eq!(
            Usubo::new(&hi, rhs, lhs).interpret(&mut state),
            crate::interpret::EvalResults::from_vec(vec![
                EvalValue::Imm(Immediate::I8(3)),
                EvalValue::Imm(Immediate::I1(true))
            ])
        );
        assert_eq!(
            Umulo::new(&hi, lhs, rhs).interpret(&mut state),
            crate::interpret::EvalResults::from_vec(vec![
                EvalValue::Imm(Immediate::I8(-2)),
                EvalValue::Imm(Immediate::I1(true))
            ])
        );
        assert_eq!(
            Smulo::new(&hi, lhs, rhs).interpret(&mut state),
            crate::interpret::EvalResults::from_vec(vec![
                EvalValue::Imm(Immediate::I8(-2)),
                EvalValue::Imm(Immediate::I1(false))
            ])
        );
    }

    #[test]
    fn saturating_ops_clamp_at_bounds() {
        let hi = TestHasInst;
        let lhs = crate::ValueId::from_u32(0);
        let rhs = crate::ValueId::from_u32(1);

        let mut state = TestState::new([
            (lhs, EvalValue::Imm(Immediate::I8(120))),
            (rhs, EvalValue::Imm(Immediate::I8(20))),
        ]);
        assert_eq!(
            Saddsat::new(&hi, lhs, rhs).interpret(&mut state),
            super::single_result(EvalValue::Imm(Immediate::I8(127)))
        );

        state.values.insert(lhs, EvalValue::Imm(Immediate::I8(3)));
        state.values.insert(rhs, EvalValue::Imm(Immediate::I8(5)));
        assert_eq!(
            Usubsat::new(&hi, lhs, rhs).interpret(&mut state),
            super::single_result(EvalValue::Imm(Immediate::I8(0)))
        );

        state
            .values
            .insert(lhs, EvalValue::Imm(Immediate::I8(-120)));
        state.values.insert(rhs, EvalValue::Imm(Immediate::I8(20)));
        assert_eq!(
            Ssubsat::new(&hi, lhs, rhs).interpret(&mut state),
            super::single_result(EvalValue::Imm(Immediate::I8(-128)))
        );

        state.values.insert(lhs, EvalValue::Imm(Immediate::I8(-56)));
        state.values.insert(rhs, EvalValue::Imm(Immediate::I8(3)));
        assert_eq!(
            Umulsat::new(&hi, lhs, rhs).interpret(&mut state),
            super::single_result(EvalValue::Imm(Immediate::I8(-1)))
        );

        state.values.insert(lhs, EvalValue::Imm(Immediate::I8(100)));
        state.values.insert(rhs, EvalValue::Imm(Immediate::I8(2)));
        assert_eq!(
            Smulsat::new(&hi, lhs, rhs).interpret(&mut state),
            super::single_result(EvalValue::Imm(Immediate::I8(127)))
        );

        state.values.insert(lhs, EvalValue::Imm(Immediate::I8(-6)));
        state.values.insert(rhs, EvalValue::Imm(Immediate::I8(10)));
        assert_eq!(
            Uaddsat::new(&hi, lhs, rhs).interpret(&mut state),
            super::single_result(EvalValue::Imm(Immediate::I8(-1)))
        );
    }
}
