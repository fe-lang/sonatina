use super::{Action, EvalValue, Interpret, State, no_result, single_result};
use crate::{I256, Immediate, Type, U256, inst::data::*, types::CompoundType};

impl Interpret for Mload {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let addr = state.lookup_val(*self.addr());
        single_result(state.load(addr, *self.ty()))
    }
}

impl Interpret for Mstore {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let addr = state.lookup_val(*self.addr());
        let value = state.lookup_val(*self.value());
        let _ = state.store(addr, value, *self.ty());
        no_result()
    }
}

impl Interpret for Gep {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let Some(base_addr) = state.lookup_val(self.values()[0]).as_imm() else {
            return single_result(EvalValue::Undef);
        };

        let mut current_ty = state.dfg().value_ty(self.values()[0]);

        assert!(
            state.dfg().ctx.with_ty_store(|s| s.is_ptr(current_ty)),
            "GEP must start with a pointer type"
        );

        let mut offset = I256::zero();
        for value in self.values()[1..].iter() {
            let Some(idx_value) = state.lookup_val(*value).as_imm() else {
                return single_result(EvalValue::Undef);
            };

            let cmpd = match current_ty {
                Type::I1
                | Type::I16
                | Type::I8
                | Type::I32
                | Type::I64
                | Type::I128
                | Type::I256
                | Type::EnumTag(_)
                | Type::Unit => {
                    panic!(
                        "Invalid GEP: indexing into a scalar type or unit with more indices remaining"
                    );
                }
                Type::Compound(cmpd) => cmpd,
            };

            let cmpd_data = state
                .dfg()
                .ctx
                .with_ty_store(|s| s.resolve_compound(cmpd).clone());

            match cmpd_data {
                CompoundType::Array { elem, .. } => {
                    let elem_size = state.dfg().ctx.size_of_unchecked(elem);
                    let step = idx_value.as_i256().overflowing_mul(I256::from(elem_size)).0;
                    offset = offset.overflowing_add(step).0;
                    current_ty = elem;
                }

                CompoundType::Ptr(ty) => {
                    let size = state.dfg().ctx.size_of_unchecked(ty);
                    let step = idx_value.as_i256().overflowing_mul(I256::from(size)).0;
                    offset = offset.overflowing_add(step).0;
                    current_ty = ty;
                }

                CompoundType::ObjRef(_) => {
                    panic!("Invalid GEP: indexing into an object reference");
                }

                CompoundType::ConstRef(_) => {
                    panic!("Invalid GEP: indexing into a const reference");
                }

                CompoundType::Enum(_) => {
                    panic!("Invalid GEP: indexing into an enum type");
                }

                CompoundType::Struct(s) => {
                    let Some((field_offset, field_ty)) =
                        struct_field_offset(state, s.fields.as_slice(), idx_value)
                    else {
                        return single_result(EvalValue::Undef);
                    };
                    offset = offset.overflowing_add(I256::from(field_offset)).0;
                    current_ty = field_ty;
                }

                CompoundType::Func { .. } => {
                    panic!(
                        "Invalid GEP: indexing into a function type with more indices remaining"
                    );
                }
            }
        }

        let tl = state.dfg().ctx.type_layout;
        let res = base_addr + Immediate::from_i256(offset, tl.pointer_repl());
        single_result(EvalValue::Imm(res))
    }
}

impl Interpret for GetFunctionPtr {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);
        single_result(EvalValue::Undef)
    }
}

impl Interpret for SymAddr {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);
        single_result(EvalValue::Undef)
    }
}

impl Interpret for SymSize {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);
        single_result(EvalValue::Undef)
    }
}

impl Interpret for Alloca {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        single_result(state.alloca(*self.ty()))
    }
}

impl Interpret for InsertValue {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let dest = state.lookup_val(*self.dest());
        let ty = state.dfg().value_ty(*self.dest());

        let mut fields = match dest {
            EvalValue::Aggregate { fields, .. } => fields.clone(),

            EvalValue::Undef => {
                let len = match ty.resolve_compound(&state.dfg().ctx).unwrap() {
                    CompoundType::Array { len, .. } => len,
                    CompoundType::Struct(s) => s.fields.len(),
                    CompoundType::Enum(_) => unreachable!(),
                    CompoundType::Ptr(_) => unreachable!(),
                    CompoundType::ObjRef(_) => unreachable!(),
                    CompoundType::ConstRef(_) => unreachable!(),
                    CompoundType::Func { .. } => unreachable!(),
                };
                vec![EvalValue::Undef; len]
            }

            EvalValue::Imm(_) => {
                unreachable!()
            }
        };

        let idx_val = state.lookup_val(*self.idx());
        let Some(idx_imm) = idx_val.as_imm() else {
            debug_assert!(
                idx_val.is_undef(),
                "insert_value index must be an immediate"
            );
            return single_result(EvalValue::Undef);
        };
        let Some(idx) = nonnegative_imm_usize(idx_imm) else {
            debug_assert!(
                idx_imm.is_negative(),
                "insert_value index must be non-negative"
            );
            return single_result(EvalValue::Undef);
        };
        if idx >= fields.len() {
            debug_assert!(
                false,
                "insert_value index out of bounds: idx={idx} len={}",
                fields.len()
            );
            return single_result(EvalValue::Undef);
        }
        fields[idx] = state.lookup_val(*self.value());

        single_result(EvalValue::Aggregate { fields, ty })
    }
}

impl Interpret for ExtractValue {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let dest = state.lookup_val(*self.dest());
        let dest = match dest {
            EvalValue::Aggregate { fields, .. } => fields,

            EvalValue::Undef => {
                return single_result(EvalValue::Undef);
            }

            EvalValue::Imm(_) => {
                unreachable!()
            }
        };

        let idx_val = state.lookup_val(*self.idx());
        let Some(idx_imm) = idx_val.as_imm() else {
            debug_assert!(
                idx_val.is_undef(),
                "extract_value index must be an immediate"
            );
            return single_result(EvalValue::Undef);
        };
        let Some(idx) = nonnegative_imm_usize(idx_imm) else {
            debug_assert!(
                idx_imm.is_negative(),
                "extract_value index must be non-negative"
            );
            return single_result(EvalValue::Undef);
        };
        single_result(dest.get(idx).cloned().unwrap_or_else(|| {
            debug_assert!(
                false,
                "extract_value index out of bounds: idx={idx} len={}",
                dest.len()
            );
            EvalValue::Undef
        }))
    }
}

fn align_to(offset: usize, alignment: usize) -> usize {
    assert!(alignment & (alignment - 1) == 0);
    (offset + alignment - 1) & !(alignment - 1)
}

fn nonnegative_imm_usize(imm: Immediate) -> Option<usize> {
    if imm.is_negative() {
        return None;
    }

    let value = imm.as_i256().to_u256();
    (value <= U256::from(usize::MAX)).then_some(value.as_usize())
}

fn struct_field_offset(
    state: &dyn State,
    fields: &[Type],
    idx_value: Immediate,
) -> Option<(usize, Type)> {
    let idx = nonnegative_imm_usize(idx_value)?;
    let mut offset = 0usize;
    for (field_idx, &field_ty) in fields.iter().enumerate() {
        offset = align_to(offset, state.dfg().ctx.align_of_unchecked(field_ty));
        if field_idx == idx {
            return Some((offset, field_ty));
        }
        offset = offset.checked_add(state.dfg().ctx.size_of_unchecked(field_ty))?;
    }
    None
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use smallvec::smallvec;

    use super::*;
    use crate::{
        DataFlowGraph, HasInst, Type, Value, ValueId,
        builder::test_util::test_isa,
        interpret::EvalResults,
        module::{FuncRef, ModuleCtx},
    };

    struct TestHasInst;

    impl<I: crate::Inst> HasInst<I> for TestHasInst {}

    struct TestState {
        dfg: DataFlowGraph,
        values: HashMap<ValueId, EvalValue>,
    }

    impl TestState {
        fn new(dfg: DataFlowGraph, values: impl IntoIterator<Item = (ValueId, EvalValue)>) -> Self {
            Self {
                dfg,
                values: values.into_iter().collect(),
            }
        }
    }

    impl State for TestState {
        fn lookup_val(&mut self, value: ValueId) -> EvalValue {
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
    fn gep_pointer_indices_use_signed_offsets() {
        let isa = test_isa();
        let mut dfg = DataFlowGraph::new(ModuleCtx::new(&isa));
        let base = dfg.make_value(Value::Arg {
            ty: Type::I32.to_ptr(&dfg.ctx),
            idx: 0,
        });
        let idx = dfg.make_value(Value::Arg {
            ty: Type::I32,
            idx: 1,
        });
        let mut state = TestState::new(
            dfg,
            [
                (base, EvalValue::Imm(Immediate::I256(I256::from(64)))),
                (idx, EvalValue::Imm(Immediate::I32(-1))),
            ],
        );

        assert_eq!(
            Gep::new(&TestHasInst, smallvec![base, idx]).interpret(&mut state),
            single_result(EvalValue::Imm(Immediate::I256(I256::from(32))))
        );
    }

    #[test]
    fn aggregate_value_indices_reject_negative_immediates() {
        let isa = test_isa();
        let mut dfg = DataFlowGraph::new(ModuleCtx::new(&isa));
        let array_ty = dfg
            .ctx
            .with_ty_store_mut(|store| store.make_array(Type::I32, 2));
        let dest = dfg.make_value(Value::Arg {
            ty: array_ty,
            idx: 0,
        });
        let idx = dfg.make_value(Value::Arg {
            ty: Type::I32,
            idx: 1,
        });
        let value = dfg.make_value(Value::Arg {
            ty: Type::I32,
            idx: 2,
        });
        let aggregate = EvalValue::Aggregate {
            fields: vec![
                EvalValue::Imm(Immediate::I32(1)),
                EvalValue::Imm(Immediate::I32(2)),
            ],
            ty: array_ty,
        };
        let mut state = TestState::new(
            dfg,
            [
                (dest, aggregate),
                (idx, EvalValue::Imm(Immediate::I32(-1))),
                (value, EvalValue::Imm(Immediate::I32(7))),
            ],
        );

        assert_eq!(
            InsertValue::new(&TestHasInst, dest, idx, value).interpret(&mut state),
            single_result(EvalValue::Undef)
        );
        assert_eq!(
            ExtractValue::new(&TestHasInst, dest, idx).interpret(&mut state),
            single_result(EvalValue::Undef)
        );
    }
}
