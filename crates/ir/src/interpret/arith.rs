use super::{Action, EvalValue, Interpret, State};
use crate::inst::arith::*;

impl Interpret for Neg {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let val = state.lookup_val(*self.arg());
        val.with_imm(|value| -value)
    }
}

impl Interpret for Add {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| lhs + rhs)
    }
}

impl Interpret for Sub {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| EvalValue::Imm(lhs - rhs))
    }
}

impl Interpret for Mul {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        state.set_action(Action::Continue);

        EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| lhs * rhs)
    }
}

impl Interpret for Sdiv {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| {
            if rhs.is_zero() {
                return EvalValue::Undef;
            }
            lhs.sdiv(rhs).into()
        })
    }
}

impl Interpret for Udiv {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| {
            if rhs.is_zero() {
                return EvalValue::Undef;
            }
            lhs.udiv(rhs).into()
        })
    }
}

impl Interpret for Umod {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| {
            if rhs.is_zero() {
                return EvalValue::Undef;
            }
            lhs.urem(rhs).into()
        })
    }
}

impl Interpret for Smod {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| {
            if rhs.is_zero() {
                return EvalValue::Undef;
            }
            lhs.srem(rhs).into()
        })
    }
}

impl Interpret for Shl {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let bits = state.lookup_val(*self.bits());
        let value = state.lookup_val(*self.value());
        EvalValue::zip_with_imm(bits, value, |bits, value| value << bits)
    }
}

impl Interpret for Shr {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let bits = state.lookup_val(*self.bits());
        let value = state.lookup_val(*self.value());

        EvalValue::zip_with_imm(bits, value, |bits, value| value >> bits)
    }
}

impl Interpret for Sar {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let bits = state.lookup_val(*self.bits());
        let value = state.lookup_val(*self.value());

        EvalValue::zip_with_imm(bits, value, |bits, value| {
            let shifted = value >> bits;
            if value.is_positive() {
                shifted
            } else {
                -shifted
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::{
        DataFlowGraph, HasInst, Immediate, Type,
        builder::test_util::test_isa,
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

        fn call_func(&mut self, _func: FuncRef, _args: Vec<EvalValue>) -> EvalValue {
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
            EvalValue::Undef
        );
        assert_eq!(
            Udiv::new(&hi, lhs, rhs).interpret(&mut state),
            EvalValue::Undef
        );
        assert_eq!(
            Umod::new(&hi, lhs, rhs).interpret(&mut state),
            EvalValue::Undef
        );
        assert_eq!(
            Smod::new(&hi, lhs, rhs).interpret(&mut state),
            EvalValue::Undef
        );
    }
}
