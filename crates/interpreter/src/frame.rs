use std::mem;

use cranelift_entity::SecondaryMap;

use sonatina_ir::{
    module::ModuleCtx,
    types::{CompoundType, CompoundTypeData},
    DataFlowGraph, Function, Insn, Type, Value, ValueData, I256,
};

use crate::{Literal, ProgramCounter};

pub struct Frame {
    pub ret_addr: ProgramCounter,
    local_values: SecondaryMap<Value, Literal>, // 256-bit register
    alloca_region: Vec<u8>,                     // big endian
}

impl Frame {
    pub fn new(func: &Function, ret_addr: ProgramCounter, args: Vec<Literal>) -> Self {
        let mut local_values = SecondaryMap::new();
        for (v, literal_value) in func.arg_values.iter().zip(args.into_iter()) {
            local_values[*v] = literal_value
        }
        let alloca_region = Vec::new();

        Self {
            ret_addr,
            local_values,
            alloca_region,
        }
    }

    pub fn load(&mut self, /*ctx: Context,*/ v: Value, dfg: &DataFlowGraph) -> Literal {
        if !self.is_assigned(v) {
            let v = match dfg.value_data(v) {
                ValueData::Insn { insn, .. } => {
                    let result_v = dfg.insn_result(*insn).unwrap();
                    if self.is_assigned(result_v) {
                        return self.local_values[result_v];
                    }
                    result_v
                }
                _ => v,
            };
            let i256 = dfg.value_imm(v).unwrap().as_i256();
            self.local_values[v] = Literal(i256);
        }
        self.local_values[v]
    }

    pub fn map(&mut self, literal: Literal, insn: Insn, dfg: &DataFlowGraph) {
        let v = dfg.insn_result(insn).unwrap();
        debug_assert!(!self.is_assigned(v));
        self.local_values[v] = literal
    }

    pub fn alloca(&mut self, ctx: &ModuleCtx, ty: Type, insn: Insn, dfg: &DataFlowGraph) {
        let v = dfg.insn_result(insn).unwrap();
        debug_assert!(!self.is_assigned(v));

        let addr = self.alloca_region.len();

        let size_of_data = byte_size_of_ty(ctx, ty);
        for _ in 0..size_of_data {
            self.alloca_region.push(0u8);
        }
        self.local_values[v] = Literal::from_usize(addr);
    }

    pub fn gep(&mut self, ctx: &ModuleCtx, args: &[Value], dfg: &DataFlowGraph) -> Literal {
        let ptr_v = args[0];
        let ptr = self.load(ptr_v, dfg);
        let base_addr = ptr.as_usize();
        let ptr_ty = dfg.value_ty(ptr_v);
        debug_assert!(ctx.with_ty_store(|s| s.is_ptr(ptr_ty)));

        let pointee_ty = ctx.with_ty_store(|s| s.deref(ptr_ty)).unwrap();
        debug_assert!(!pointee_ty.is_integral() && !ctx.with_ty_store(|s| s.is_ptr(ptr_ty)));

        let mut cmpd_ty = to_cmpd_ty(pointee_ty);
        let mut offset = 0usize;
        for arg in &args[1..] {
            let index = self.load(*arg, dfg).as_usize();

            ctx.with_ty_store(|s| match s.resolve_compound(cmpd_ty.unwrap()) {
                CompoundTypeData::Array { elem, .. } => {
                    offset += index * byte_size_of_ty(ctx, *elem);
                    cmpd_ty = to_cmpd_ty(*elem);
                }
                CompoundTypeData::Struct(data) => {
                    for ty in &data.fields[..index] {
                        offset += byte_size_of_ty(ctx, *ty);
                    }
                    cmpd_ty = to_cmpd_ty(data.fields[index]);
                }
                _ => unreachable!(),
            })
        }
        Literal::from_usize(base_addr + offset)
    }

    pub fn ldr(&mut self, ctx: &ModuleCtx, ptr: Value, insn: Insn, dfg: &DataFlowGraph) {
        let addr = self.load(ptr, dfg).as_usize();
        debug_assert!(self.is_alloca(addr));

        let ty = dfg.insn_result_ty(insn).unwrap();
        let size = byte_size_of_ty(ctx, ty);
        let mut literal_b = Vec::new();
        for b in &self.alloca_region[addr..addr + size] {
            literal_b.push(*b)
        }
        let Some(data) = Literal::deserialize(ctx, ty, literal_b) else {
            return;
        };
        self.map(data, insn, dfg);
    }

    pub fn str(&mut self, ctx: &ModuleCtx, ptr: Value, v: Value, dfg: &DataFlowGraph) {
        let addr = self.load(ptr, dfg).as_usize();
        let data = self.load(v, dfg);
        let data_ty = dfg.value_ty(v);
        let data_b = data.serialize(ctx, data_ty);
        for (i, b) in data_b.into_iter().enumerate() {
            self.alloca_region[addr + i] = b;
        }
    }

    pub fn eq(&mut self, lhs: Value, rhs: Value, dfg: &DataFlowGraph) -> bool {
        self.load(lhs, dfg) == self.load(rhs, dfg)
    }

    fn is_assigned(&self, v: Value) -> bool {
        for local_v in self.local_values.keys() {
            if v == local_v {
                return true;
            }
        }
        false
    }

    fn is_alloca(&self, addr: usize) -> bool {
        addr < self.alloca_region.len()
    }
}

pub fn byte_size_of_ty(ctx: &ModuleCtx, ty: Type) -> usize {
    match ty {
        Type::I1 => mem::size_of::<bool>(),
        Type::I8 => mem::size_of::<i8>(),
        Type::I16 => mem::size_of::<i16>(),
        Type::I32 => mem::size_of::<i32>(),
        Type::I64 => mem::size_of::<i64>(),
        Type::I128 => mem::size_of::<i128>(),
        Type::I256 => mem::size_of::<I256>(),
        Type::Compound(ty) => {
            use CompoundTypeData::*;
            ctx.with_ty_store(|s| match s.resolve_compound(ty) {
                Array { len, elem } => len * byte_size_of_ty(ctx, *elem),
                Ptr(_) => mem::size_of::<usize>(),
                Struct(data) => data
                    .fields
                    .iter()
                    .fold(0usize, |acc, ty| acc + byte_size_of_ty(ctx, *ty)),
            })
        }
        Type::Void => mem::size_of::<()>(),
    }
}

fn to_cmpd_ty(ty: Type) -> Option<CompoundType> {
    match ty {
        Type::Compound(ty) => Some(ty),
        _ => None,
    }
}
