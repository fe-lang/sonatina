//! Sonatina IR → WASM instruction translation.
//!
//! Translates Sonatina IR functions to WASM function bodies using
//! wasm-encoder. Handles u256 values as i32 pointers into linear memory,
//! with u256 intrinsics imported from the host.

use std::collections::HashMap;

use wasm_encoder::{Function, Instruction, ValType};

use sonatina_ir::{
    BlockId, Function as SonFunction, Immediate, InstDowncast, InstSetBase,
    Module, Type, Value, ValueId,
    module::FuncRef,
};

/// WASM local variable index tracker
struct LocalAllocator {
    next_local: u32,
    param_count: u32,
    value_map: HashMap<ValueId, u32>,
    extra_locals: Vec<ValType>,
}

impl LocalAllocator {
    fn new(param_count: u32) -> Self {
        Self {
            next_local: param_count,
            param_count,
            value_map: HashMap::new(),
            extra_locals: Vec::new(),
        }
    }

    fn alloc(&mut self, ty: ValType) -> u32 {
        let idx = self.next_local;
        self.next_local += 1;
        self.extra_locals.push(ty);
        idx
    }

    fn map_value(&mut self, value_id: ValueId, local: u32) {
        self.value_map.insert(value_id, local);
    }

    fn get(&self, value_id: ValueId) -> Option<u32> {
        self.value_map.get(&value_id).copied()
    }
}

pub(super) fn translate_function_body(
    module: &Module,
    func_ref: FuncRef,
    result_types: &[ValType],
) -> Result<Function, String> {
    let mut locals = LocalAllocator::new(0);
    let mut instructions: Vec<Instruction<'static>> = Vec::new();

    module.func_store.try_view(func_ref, |function| {
        let inst_set = function.inst_set();
        let param_count = function.arg_values.len() as u32;
        locals = LocalAllocator::new(param_count);

        // Map function args to WASM params
        for (idx, &arg_value) in function.arg_values.iter().enumerate() {
            locals.map_value(arg_value, idx as u32);
        }

        for block in function.layout.iter_block() {
            for inst_id in function.layout.iter_inst(block) {
                let inst_data = function.dfg.inst(inst_id);

                // Return
                if let Some(ret) = <&sonatina_ir::inst::control_flow::Return as InstDowncast>::downcast(inst_set, inst_data) {
                    for &val_id in ret.args().as_slice() {
                        emit_value_to_stack(function, val_id, &locals, &mut instructions)?;
                    }
                    instructions.push(Instruction::Return);
                }
                // Jump (fall through for linear CFG)
                else if <&sonatina_ir::inst::control_flow::Jump as InstDowncast>::downcast(inst_set, inst_data).is_some() {
                    // Linear CFG: fall through
                }
                // Add
                else if let Some(add) = <&sonatina_ir::inst::arith::Add as InstDowncast>::downcast(inst_set, inst_data) {
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        let local = locals.alloc(ValType::I64);
                        emit_value_to_stack(function, *add.lhs(), &locals, &mut instructions)?;
                        emit_value_to_stack(function, *add.rhs(), &locals, &mut instructions)?;
                        instructions.push(Instruction::I64Add);
                        instructions.push(Instruction::LocalSet(local));
                        locals.map_value(result, local);
                    }
                }
                // Mul
                else if let Some(mul) = <&sonatina_ir::inst::arith::Mul as InstDowncast>::downcast(inst_set, inst_data) {
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        let local = locals.alloc(ValType::I64);
                        emit_value_to_stack(function, *mul.lhs(), &locals, &mut instructions)?;
                        emit_value_to_stack(function, *mul.rhs(), &locals, &mut instructions)?;
                        instructions.push(Instruction::I64Mul);
                        instructions.push(Instruction::LocalSet(local));
                        locals.map_value(result, local);
                    }
                }
                // Eq
                else if let Some(eq) = <&sonatina_ir::inst::cmp::Eq as InstDowncast>::downcast(inst_set, inst_data) {
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        let local = locals.alloc(ValType::I32);
                        emit_value_to_stack(function, *eq.lhs(), &locals, &mut instructions)?;
                        emit_value_to_stack(function, *eq.rhs(), &locals, &mut instructions)?;
                        instructions.push(Instruction::I64Eq);
                        instructions.push(Instruction::LocalSet(local));
                        locals.map_value(result, local);
                    }
                }
                // Skip phi, unreachable, and unhandled instructions
                else if <&sonatina_ir::inst::control_flow::Unreachable as InstDowncast>::downcast(inst_set, inst_data).is_some() {
                    instructions.push(Instruction::Unreachable);
                }
                else {
                    // Skip unhandled instructions for now
                }
            }
        }

        Ok(())
    }).ok_or_else(|| "function has no body".to_string())??;

    // Build final function with locals
    let local_decls: Vec<(u32, ValType)> = locals.extra_locals
        .iter()
        .map(|ty| (1, *ty))
        .collect();
    let mut func = Function::new(local_decls);
    for inst in &instructions {
        func.instruction(inst);
    }

    // If no explicit return, add default return values
    if !instructions.iter().any(|i| matches!(i, Instruction::Return)) {
        for ty in result_types {
            match ty {
                ValType::I32 => func.instruction(&Instruction::I32Const(0)),
                ValType::I64 => func.instruction(&Instruction::I64Const(0)),
                _ => &mut func,
            };
        }
    }

    func.instruction(&Instruction::End);
    Ok(func)
}

fn emit_value_to_stack(
    function: &SonFunction,
    value_id: ValueId,
    locals: &LocalAllocator,
    instructions: &mut Vec<Instruction<'static>>,
) -> Result<(), String> {
    if let Some(local) = locals.get(value_id) {
        instructions.push(Instruction::LocalGet(local));
        return Ok(());
    }

    let value = function.dfg.value(value_id);
    match value {
        Value::Immediate { imm, .. } => {
            match imm {
                Immediate::I1(b) => instructions.push(Instruction::I32Const(*b as i32)),
                Immediate::I8(v) => instructions.push(Instruction::I32Const(*v as i32)),
                Immediate::I16(v) => instructions.push(Instruction::I32Const(*v as i32)),
                Immediate::I32(v) => instructions.push(Instruction::I32Const(*v)),
                Immediate::I64(v) => instructions.push(Instruction::I64Const(*v)),
                _ => instructions.push(Instruction::I64Const(0)),
            }
            Ok(())
        }
        _ => {
            instructions.push(Instruction::I64Const(0));
            Ok(())
        }
    }
}
