use cranelift_entity::SecondaryMap;

use sonatina_ir::{module::ModuleCtx, DataFlowGraph, Type, Value, I256};

use crate::{types, value::EvalValue, ProgramCounter};

pub struct Frame {
    pub ret_addr: ProgramCounter,
    local_values: SecondaryMap<Value, EvalValue>, // 256-bit register
    alloca_region: Vec<u8>,                       // big endian
}

impl Frame {
    pub fn new(
        ret_addr: ProgramCounter,
        args: impl Iterator<Item = Value>,
        arg_literals: impl Iterator<Item = I256>,
    ) -> Self {
        let mut local_values = SecondaryMap::new();
        for (v, literal_value) in args.zip(arg_literals) {
            local_values[v] = EvalValue::from_i256(literal_value)
        }
        let alloca_region = Vec::new();

        Self {
            ret_addr,
            local_values,
            alloca_region,
        }
    }

    pub fn load(&mut self, ctx: &ModuleCtx, v: Value, dfg: &DataFlowGraph) -> I256 {
        if !self.is_assigned(v) {
            if let Some(gv) = dfg.value_gv(v) {
                ctx.with_gv_store(|s| {
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

    pub fn map(&mut self, literal: I256, v: Value) {
        debug_assert!(!self.is_assigned(v));
        self.local_values[v] = EvalValue::from_i256(literal)
    }

    pub fn alloca(&mut self, ctx: &ModuleCtx, ty: Type, v: Value) {
        debug_assert!(!self.is_assigned(v));

        let addr = self.alloca_region.len();

        for _ in 0..types::byte_size_of_ty(ctx, ty) {
            self.alloca_region.push(0u8);
        }
        self.local_values[v] = EvalValue::from_usize(addr);
    }

    pub fn ldr(&mut self, ctx: &ModuleCtx, addr: I256, v: Value, ty: Type) {
        let addr = addr.to_u256().as_usize();
        debug_assert!(addr < self.alloca_region.len());

        let size = types::byte_size_of_ty(ctx, ty);
        let mut literal_b = Vec::new();
        for b in &self.alloca_region[addr..addr + size] {
            literal_b.push(*b)
        }
        let Some(data) = EvalValue::deserialize(ctx, ty, literal_b) else {
            return;
        };
        self.map(data.i256(), v);
    }

    pub fn str(&mut self, ctx: &ModuleCtx, addr: I256, data: I256, ty: Type) {
        let addr = addr.to_u256().as_usize();
        let data_b = EvalValue::from_i256(data).serialize(ctx, ty);
        for (i, b) in data_b.into_iter().enumerate() {
            self.alloca_region[addr + i] = b;
        }
    }

    pub fn eq(&mut self, ctx: &ModuleCtx, lhs: Value, rhs: Value, dfg: &DataFlowGraph) -> bool {
        self.load(ctx, lhs, dfg) == self.load(ctx, rhs, dfg)
    }

    pub fn is_assigned(&self, v: Value) -> bool {
        for (local_v, local) in self.local_values.iter() {
            if v == local_v {
                return matches!(local, EvalValue::Literal(_));
            }
        }
        false
    }
}
