use cranelift_entity::{packed_option::PackedOption, SecondaryMap};

use sonatina_ir::{module::ModuleCtx, DataFlowGraph, Type, ValueId, I256};

use crate::{types, EvalValue, ProgramCounter};

#[derive(Default)]
pub struct Frame {
    pub ret_addr: PackedOption<ProgramCounter>,
    local_values: SecondaryMap<ValueId, EvalValue>, // 256-bit register
    alloca_region: Vec<u8>,                         // big endian
}

impl Frame {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn set_ret_addr(&mut self, ret_addr: ProgramCounter) {
        self.ret_addr = ret_addr.into();
    }

    pub fn load_args(&mut self, args: &[ValueId], arg_literals: impl Iterator<Item = I256>) {
        for (v, literal_value) in args.iter().zip(arg_literals) {
            self.local_values[*v] = EvalValue::from_i256(literal_value)
        }
    }

    pub fn load(&mut self, v: ValueId, dfg: &DataFlowGraph) -> I256 {
        if !self.is_assigned(v) {
            if let Some(gv) = dfg.value_gv(v) {
                dfg.ctx.with_gv_store(|s| {
                    if !s.is_const(gv) {
                        todo!()
                    }
                })
            }
            let i256 = dfg.value_imm(v).unwrap().as_i256();
            self.local_values[v] = EvalValue::from_i256(i256);
        }
        self.local_values[v].i256()
    }

    pub fn map(&mut self, literal: I256, v: ValueId) {
        debug_assert!(!self.is_assigned(v));
        self.local_values[v] = EvalValue::from_i256(literal)
    }

    pub fn alloca(&mut self, ctx: &ModuleCtx, ty: Type, v: ValueId) {
        debug_assert!(!self.is_assigned(v));

        let addr = self.alloca_region.len();

        let size = types::size_of_ty_data(ctx, ty);
        self.alloca_region.resize(addr + size, 0);
        self.local_values[v] = EvalValue::from_usize(addr);
    }

    pub fn ldr(&mut self, ctx: &ModuleCtx, addr: I256, v: ValueId, ty: Type) {
        let addr = addr.to_u256().as_usize();
        debug_assert!(addr < self.alloca_region.len());

        let size = types::size_of_ty_data(ctx, ty);
        let literal_b = &self.alloca_region[addr..addr + size];
        let Some(data) = EvalValue::deserialize(ctx, ty, literal_b) else {
            return;
        };
        self.map(data.i256(), v);
    }

    pub fn str(&mut self, ctx: &ModuleCtx, addr: I256, data: I256, ty: Type) {
        let addr = addr.to_u256().as_usize();
        let size = types::size_of_ty_data(ctx, ty);
        let reg_value = EvalValue::from_i256(data);
        reg_value.serialize(ctx, ty, &mut self.alloca_region[addr..size]);
    }

    pub fn is_assigned(&self, v: ValueId) -> bool {
        for (local_v, local) in self.local_values.iter() {
            if v == local_v {
                return matches!(local, EvalValue::Literal(_));
            }
        }
        false
    }
}
