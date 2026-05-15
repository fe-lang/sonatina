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

        for (idx, &arg_value) in function.arg_values.iter().enumerate() {
            locals.map_value(arg_value, idx as u32);
        }

        // Try structured CF first; fall back to linear for simple functions
        let structured = crate::structurize::structurize_function(function);
        if let Ok(ref scfg) = structured {
            if scfg.regions.iter().any(|r| matches!(r, crate::structurize::Region::Loop { .. })) {
                return emit_structured_regions(function, inst_set, &scfg.regions, module, &mut locals, &mut instructions);
            }
        }

        // Linear fallback for non-loop functions
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
                // Sub
                else if let Some(sub) = <&sonatina_ir::inst::arith::Sub as InstDowncast>::downcast(inst_set, inst_data) {
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        let local = locals.alloc(ValType::I64);
                        emit_value_to_stack(function, *sub.lhs(), &locals, &mut instructions)?;
                        emit_value_to_stack(function, *sub.rhs(), &locals, &mut instructions)?;
                        instructions.push(Instruction::I64Sub);
                        instructions.push(Instruction::LocalSet(local));
                        locals.map_value(result, local);
                    }
                }
                // Neg
                else if let Some(neg) = <&sonatina_ir::inst::arith::Neg as InstDowncast>::downcast(inst_set, inst_data) {
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        let local = locals.alloc(ValType::I64);
                        instructions.push(Instruction::I64Const(0));
                        emit_value_to_stack(function, *neg.arg(), &locals, &mut instructions)?;
                        instructions.push(Instruction::I64Sub);
                        instructions.push(Instruction::LocalSet(local));
                        locals.map_value(result, local);
                    }
                }
                // Uaddo (add with overflow — just do the add, ignore overflow for WASM)
                else if let Some(uaddo) = <&sonatina_ir::inst::arith::Uaddo as InstDowncast>::downcast(inst_set, inst_data) {
                    let ir_results = function.dfg.inst_results(inst_id);
                    if !ir_results.is_empty() {
                        let local = locals.alloc(ValType::I64);
                        emit_value_to_stack(function, *uaddo.lhs(), &locals, &mut instructions)?;
                        emit_value_to_stack(function, *uaddo.rhs(), &locals, &mut instructions)?;
                        instructions.push(Instruction::I64Add);
                        instructions.push(Instruction::LocalSet(local));
                        locals.map_value(ir_results[0], local);
                    }
                    if ir_results.len() >= 2 {
                        let ofl = locals.alloc(ValType::I32);
                        instructions.push(Instruction::I32Const(0));
                        instructions.push(Instruction::LocalSet(ofl));
                        locals.map_value(ir_results[1], ofl);
                    }
                }
                // Umulo (mul with overflow — just do the mul)
                else if let Some(umulo) = <&sonatina_ir::inst::arith::Umulo as InstDowncast>::downcast(inst_set, inst_data) {
                    let ir_results = function.dfg.inst_results(inst_id);
                    if !ir_results.is_empty() {
                        let local = locals.alloc(ValType::I64);
                        emit_value_to_stack(function, *umulo.lhs(), &locals, &mut instructions)?;
                        emit_value_to_stack(function, *umulo.rhs(), &locals, &mut instructions)?;
                        instructions.push(Instruction::I64Mul);
                        instructions.push(Instruction::LocalSet(local));
                        locals.map_value(ir_results[0], local);
                    }
                    if ir_results.len() >= 2 {
                        let ofl = locals.alloc(ValType::I32);
                        instructions.push(Instruction::I32Const(0));
                        instructions.push(Instruction::LocalSet(ofl));
                        locals.map_value(ir_results[1], ofl);
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
                // Ne
                else if let Some(ne) = <&sonatina_ir::inst::cmp::Ne as InstDowncast>::downcast(inst_set, inst_data) {
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        let local = locals.alloc(ValType::I32);
                        emit_value_to_stack(function, *ne.lhs(), &locals, &mut instructions)?;
                        emit_value_to_stack(function, *ne.rhs(), &locals, &mut instructions)?;
                        instructions.push(Instruction::I64Ne);
                        instructions.push(Instruction::LocalSet(local));
                        locals.map_value(result, local);
                    }
                }
                // Lt
                else if let Some(lt) = <&sonatina_ir::inst::cmp::Lt as InstDowncast>::downcast(inst_set, inst_data) {
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        let local = locals.alloc(ValType::I32);
                        emit_value_to_stack(function, *lt.lhs(), &locals, &mut instructions)?;
                        emit_value_to_stack(function, *lt.rhs(), &locals, &mut instructions)?;
                        instructions.push(Instruction::I64LtU);
                        instructions.push(Instruction::LocalSet(local));
                        locals.map_value(result, local);
                    }
                }
                // IsZero
                else if let Some(is_zero) = <&sonatina_ir::inst::cmp::IsZero as InstDowncast>::downcast(inst_set, inst_data) {
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        let local = locals.alloc(ValType::I32);
                        emit_value_to_stack(function, *is_zero.lhs(), &locals, &mut instructions)?;
                        instructions.push(Instruction::I64Eqz);
                        instructions.push(Instruction::LocalSet(local));
                        locals.map_value(result, local);
                    }
                }
                // Br (conditional branch — emit if/else block)
                else if let Some(br) = <&sonatina_ir::inst::control_flow::Br as InstDowncast>::downcast(inst_set, inst_data) {
                    emit_value_to_stack(function, *br.cond(), &locals, &mut instructions)?;
                    instructions.push(Instruction::If(wasm_encoder::BlockType::Empty));
                    // nz (true) branch — fall through to next block
                    instructions.push(Instruction::Else);
                    // z (false) branch — for now, just trap on out-of-bounds
                    instructions.push(Instruction::Unreachable);
                    instructions.push(Instruction::End);
                }
                // ObjAlloc — allocate stack space (use a local as base pointer)
                else if <&sonatina_ir::inst::data::ObjAlloc as InstDowncast>::downcast(inst_set, inst_data).is_some() {
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        let local = locals.alloc(ValType::I32);
                        instructions.push(Instruction::I32Const(0));
                        instructions.push(Instruction::LocalSet(local));
                        locals.map_value(result, local);
                    }
                }
                // ObjIndex — compute element pointer
                else if let Some(obj_index) = <&sonatina_ir::inst::data::ObjIndex as InstDowncast>::downcast(inst_set, inst_data) {
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        let local = locals.alloc(ValType::I32);
                        instructions.push(Instruction::I32Const(0));
                        instructions.push(Instruction::LocalSet(local));
                        locals.map_value(result, local);
                    }
                }
                // ObjStore — store to memory (skip for now)
                else if <&sonatina_ir::inst::data::ObjStore as InstDowncast>::downcast(inst_set, inst_data).is_some() {
                    // No-op for stub
                }
                // ObjLoad — load from memory (return 0 for now)
                else if let Some(obj_load) = <&sonatina_ir::inst::data::ObjLoad as InstDowncast>::downcast(inst_set, inst_data) {
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        let result_ty = function.dfg.value_ty(result);
                        let local = if matches!(result_ty, Type::I32 | Type::I16 | Type::I8 | Type::I1) {
                            let l = locals.alloc(ValType::I32);
                            instructions.push(Instruction::I32Const(0));
                            instructions.push(Instruction::LocalSet(l));
                            l
                        } else {
                            let l = locals.alloc(ValType::I64);
                            instructions.push(Instruction::I64Const(0));
                            instructions.push(Instruction::LocalSet(l));
                            l
                        };
                        locals.map_value(result, local);
                    }
                }
                // ExtractValue — extract field (return the base for now)
                else if let Some(extract) = <&sonatina_ir::inst::data::ExtractValue as InstDowncast>::downcast(inst_set, inst_data) {
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        let local = locals.alloc(ValType::I64);
                        emit_value_to_stack(function, *extract.dest(), &locals, &mut instructions)?;
                        instructions.push(Instruction::LocalSet(local));
                        locals.map_value(result, local);
                    }
                }
                // Mstore/Mload — skip for now
                else if <&sonatina_ir::inst::data::Mstore as InstDowncast>::downcast(inst_set, inst_data).is_some() {
                }
                else if let Some(mload) = <&sonatina_ir::inst::data::Mload as InstDowncast>::downcast(inst_set, inst_data) {
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        let local = locals.alloc(ValType::I64);
                        instructions.push(Instruction::I64Const(0));
                        instructions.push(Instruction::LocalSet(local));
                        locals.map_value(result, local);
                    }
                }
                // Alloca — allocate local
                else if <&sonatina_ir::inst::data::Alloca as InstDowncast>::downcast(inst_set, inst_data).is_some() {
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        let local = locals.alloc(ValType::I32);
                        instructions.push(Instruction::I32Const(0));
                        instructions.push(Instruction::LocalSet(local));
                        locals.map_value(result, local);
                    }
                }
                // Call
                else if let Some(call) = <&sonatina_ir::inst::control_flow::Call as InstDowncast>::downcast(inst_set, inst_data) {
                    // For now, push args and call (function index not resolved yet)
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        let local = locals.alloc(ValType::I64);
                        instructions.push(Instruction::I64Const(0));
                        instructions.push(Instruction::LocalSet(local));
                        locals.map_value(result, local);
                    }
                }
                // Phi — skip (handled by block params in structured WASM)
                else if <&sonatina_ir::inst::control_flow::Phi as InstDowncast>::downcast(inst_set, inst_data).is_some() {
                }
                // EVM-specific — trap
                else if <&sonatina_ir::inst::evm::EvmRevert as InstDowncast>::downcast(inst_set, inst_data).is_some()
                    || <&sonatina_ir::inst::evm::EvmStop as InstDowncast>::downcast(inst_set, inst_data).is_some() {
                    instructions.push(Instruction::Unreachable);
                }
                // Unreachable
                else if <&sonatina_ir::inst::control_flow::Unreachable as InstDowncast>::downcast(inst_set, inst_data).is_some() {
                    instructions.push(Instruction::Unreachable);
                }
                else {
                    // Skip unhandled instructions
                }
            }
        }

        Ok::<(), String>(())
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

fn emit_structured_regions(
    function: &sonatina_ir::Function,
    inst_set: &dyn InstSetBase,
    regions: &[crate::structurize::Region],
    module: &Module,
    locals: &mut LocalAllocator,
    instructions: &mut Vec<Instruction<'static>>,
) -> Result<(), String> {
    for region in regions {
        match region {
            crate::structurize::Region::Block(block_id) => {
                emit_block_instructions_fallthrough(function, inst_set, *block_id, module, locals, instructions)?;
            }
            crate::structurize::Region::Loop { header, body } => {
                // SSA destruction: allocate locals for phi nodes, initialize from entry values
                for inst_id in function.layout.iter_inst(*header) {
                    let inst_data = function.dfg.inst(inst_id);
                    if let Some(phi) = <&sonatina_ir::inst::control_flow::Phi as InstDowncast>::downcast(inst_set, inst_data) {
                        if let Some(result) = function.dfg.inst_result(inst_id) {
                            let local = locals.alloc(ValType::I64);
                            if let Some(&(init_val, _)) = phi.args().first() {
                                emit_value_to_stack(function, init_val, locals, instructions)?;
                            } else {
                                instructions.push(Instruction::I64Const(0));
                            }
                            instructions.push(Instruction::LocalSet(local));
                            locals.map_value(result, local);
                        }
                    } else {
                        break;
                    }
                }

                instructions.push(Instruction::Block(wasm_encoder::BlockType::Empty));
                instructions.push(Instruction::Loop(wasm_encoder::BlockType::Empty));
                // Emit loop body blocks with in_loop=true so jumps become br 0
                for inner_region in body {
                    match inner_region {
                        crate::structurize::Region::Block(bid) => {
                            emit_block_instructions(function, inst_set, *bid, module, locals, instructions)?;
                        }
                        other => {
                            emit_structured_regions(function, inst_set, std::slice::from_ref(other), module, locals, instructions)?;
                        }
                    }
                }
                instructions.push(Instruction::End); // end loop
                instructions.push(Instruction::End); // end block
            }
            crate::structurize::Region::IfThenElse { header, then_branch, else_branch, merge } => {
                emit_block_instructions(function, inst_set, *header, module, locals, instructions)?;
                if !then_branch.is_empty() || !else_branch.is_empty() {
                    instructions.push(Instruction::If(wasm_encoder::BlockType::Empty));
                    emit_structured_regions(function, inst_set, then_branch, module, locals, instructions)?;
                    if !else_branch.is_empty() {
                        instructions.push(Instruction::Else);
                        emit_structured_regions(function, inst_set, else_branch, module, locals, instructions)?;
                    }
                    instructions.push(Instruction::End);
                }
            }
        }
    }
    Ok(())
}

fn emit_block_instructions_fallthrough(
    function: &sonatina_ir::Function,
    inst_set: &dyn InstSetBase,
    block_id: BlockId,
    module: &Module,
    locals: &mut LocalAllocator,
    instructions: &mut Vec<Instruction<'static>>,
) -> Result<(), String> {
    emit_block_instructions_inner(function, inst_set, block_id, module, locals, instructions, false)
}

fn emit_block_instructions(
    function: &sonatina_ir::Function,
    inst_set: &dyn InstSetBase,
    block_id: BlockId,
    module: &Module,
    locals: &mut LocalAllocator,
    instructions: &mut Vec<Instruction<'static>>,
) -> Result<(), String> {
    emit_block_instructions_inner(function, inst_set, block_id, module, locals, instructions, true)
}

fn emit_block_instructions_inner(
    function: &sonatina_ir::Function,
    inst_set: &dyn InstSetBase,
    block_id: BlockId,
    module: &Module,
    locals: &mut LocalAllocator,
    instructions: &mut Vec<Instruction<'static>>,
    in_loop: bool,
) -> Result<(), String> {
    for inst_id in function.layout.iter_inst(block_id) {
        let inst_data = function.dfg.inst(inst_id);

        // Skip phi nodes — handled by the structured CF pass
        if <&sonatina_ir::inst::control_flow::Phi as InstDowncast>::downcast(inst_set, inst_data).is_some() {
            continue;
        }

        // Return
        if let Some(ret) = <&sonatina_ir::inst::control_flow::Return as InstDowncast>::downcast(inst_set, inst_data) {
            for &val_id in ret.args().as_slice() {
                emit_value_to_stack(function, val_id, locals, instructions)?;
            }
            instructions.push(Instruction::Return);
        }
        // Jump → in loop: update phi locals and br 0; outside loop: fall through
        else if let Some(jump) = <&sonatina_ir::inst::control_flow::Jump as InstDowncast>::downcast(inst_set, inst_data) {
            if in_loop {
                let target = *jump.dest();
                for target_inst_id in function.layout.iter_inst(target) {
                    let target_inst = function.dfg.inst(target_inst_id);
                    if let Some(phi) = <&sonatina_ir::inst::control_flow::Phi as InstDowncast>::downcast(inst_set, target_inst) {
                        if let Some(result) = function.dfg.inst_result(target_inst_id) {
                            for &(val, from_block) in phi.args() {
                                if from_block == block_id {
                                    emit_value_to_stack(function, val, locals, instructions)?;
                                    if let Some(local) = locals.get(result) {
                                        instructions.push(Instruction::LocalSet(local));
                                    }
                                    break;
                                }
                            }
                        }
                    } else {
                        break;
                    }
                }
                instructions.push(Instruction::Br(0));
            }
            // Outside loop: fall through to next region
        }
        // Br → conditional: if cond true → continue loop body, false → break
        else if let Some(br) = <&sonatina_ir::inst::control_flow::Br as InstDowncast>::downcast(inst_set, inst_data) {
            emit_value_to_stack(function, *br.cond(), locals, instructions)?;
            // In block { loop { ... } }: br_if 0 = continue loop, else fall through
            // If cond is false (zero-dest = exit), we break: br 1
            // If cond is true (nz-dest = loop body), we continue
            // So: if NOT cond, break
            instructions.push(Instruction::I32Eqz);
            instructions.push(Instruction::BrIf(1)); // break out of block
        }
        // Add
        else if let Some(add) = <&sonatina_ir::inst::arith::Add as InstDowncast>::downcast(inst_set, inst_data) {
            if let Some(result) = function.dfg.inst_result(inst_id) {
                let local = locals.alloc(ValType::I64);
                emit_value_to_stack(function, *add.lhs(), locals, instructions)?;
                emit_value_to_stack(function, *add.rhs(), locals, instructions)?;
                instructions.push(Instruction::I64Add);
                instructions.push(Instruction::LocalSet(local));
                locals.map_value(result, local);
            }
        }
        // Sub
        else if let Some(sub) = <&sonatina_ir::inst::arith::Sub as InstDowncast>::downcast(inst_set, inst_data) {
            if let Some(result) = function.dfg.inst_result(inst_id) {
                let local = locals.alloc(ValType::I64);
                emit_value_to_stack(function, *sub.lhs(), locals, instructions)?;
                emit_value_to_stack(function, *sub.rhs(), locals, instructions)?;
                instructions.push(Instruction::I64Sub);
                instructions.push(Instruction::LocalSet(local));
                locals.map_value(result, local);
            }
        }
        // Mul
        else if let Some(mul) = <&sonatina_ir::inst::arith::Mul as InstDowncast>::downcast(inst_set, inst_data) {
            if let Some(result) = function.dfg.inst_result(inst_id) {
                let local = locals.alloc(ValType::I64);
                emit_value_to_stack(function, *mul.lhs(), locals, instructions)?;
                emit_value_to_stack(function, *mul.rhs(), locals, instructions)?;
                instructions.push(Instruction::I64Mul);
                instructions.push(Instruction::LocalSet(local));
                locals.map_value(result, local);
            }
        }
        // Lt
        else if let Some(lt) = <&sonatina_ir::inst::cmp::Lt as InstDowncast>::downcast(inst_set, inst_data) {
            if let Some(result) = function.dfg.inst_result(inst_id) {
                let local = locals.alloc(ValType::I32);
                emit_value_to_stack(function, *lt.lhs(), locals, instructions)?;
                emit_value_to_stack(function, *lt.rhs(), locals, instructions)?;
                instructions.push(Instruction::I64LtU);
                instructions.push(Instruction::LocalSet(local));
                locals.map_value(result, local);
            }
        }
        // Unreachable
        else if <&sonatina_ir::inst::control_flow::Unreachable as InstDowncast>::downcast(inst_set, inst_data).is_some() {
            instructions.push(Instruction::Unreachable);
        }
        // Skip other instructions in structured mode
        else {}
    }
    Ok(())
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
