use super::{Action, EvalValue, Interpret, State};
use crate::{inst::data::*, types::CompoundTypeData, Immediate, Type, I256};

impl Interpret for Mload {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let addr = state.lookup_val(*self.addr());
        state.load(addr, *self.ty())
    }
}

impl Interpret for Mstore {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let value = state.lookup_val(*self.addr());
        let addr = state.lookup_val(*self.addr());
        state.store(addr, value, *self.ty())
    }
}

impl Interpret for Gep {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let Some(base_addr) = state.lookup_val(self.values()[0]).as_imm() else {
            return EvalValue::Undef;
        };

        let mut current_ty = state.dfg().value_ty(self.values()[0]);

        assert!(
            state.dfg().ctx.with_ty_store(|s| s.is_ptr(current_ty)),
            "GEP must start with a pointer type"
        );

        let mut offset = 0;
        for value in self.values()[1..].iter() {
            let Some(idx_value) = state.lookup_val(*value).as_imm() else {
                return EvalValue::Undef;
            };
            let idx_value = idx_value.as_usize();

            let cmpd = match current_ty {
                Type::I1
                | Type::I16
                | Type::I8
                | Type::I32
                | Type::I64
                | Type::I128
                | Type::I256
                | Type::Unit => {
                    panic!("Invalid GEP: indexing into a scalar type or unit with more indices remaining");
                }
                Type::Compound(cmpd) => cmpd,
            };

            let cmpd_data = state
                .dfg()
                .ctx
                .with_ty_store(|s| s.resolve_compound(cmpd).clone());

            match cmpd_data {
                CompoundTypeData::Array { elem, .. } => {
                    let elem_size = state.dfg().ctx.size_of(elem);
                    offset += elem_size * idx_value;
                    current_ty = elem;
                }

                CompoundTypeData::Ptr(ty) => {
                    let size = state.dfg().ctx.size_of(ty);
                    offset += size * idx_value;
                    current_ty = ty;
                }

                CompoundTypeData::Struct(s) => {
                    let mut local_offset = 0;
                    for i in 0..idx_value {
                        let field_ty = s.fields[i];
                        let size = state.dfg().ctx.size_of(field_ty);
                        let align = state.dfg().ctx.align_of(field_ty);
                        local_offset += align_to(offset + size, align);
                    }
                    offset += local_offset;
                    current_ty = s.fields[idx_value];
                }
            }
        }

        let tl = state.dfg().ctx.type_layout;
        let res = base_addr + Immediate::from_i256(I256::from(offset), tl.pointer_repl());
        EvalValue::Imm(res)
    }
}

fn align_to(offset: usize, alignment: usize) -> usize {
    assert!(alignment & (alignment - 1) == 0);
    (offset + alignment - 1) & !(alignment - 1)
}
