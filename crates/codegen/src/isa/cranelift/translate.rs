mod abi;
mod globals;
mod i256;
mod memory;
mod scalar;

use std::collections::HashMap;

use cranelift_codegen::ir::{
    self as clif, InstBuilder, MemFlagsData, TrapCode, condcodes::IntCC, instructions::BlockArg,
};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{FuncId, Linkage, Module as ClifModule};

use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, Linkage as SonatinaLinkage, Module, Type, Value, ValueId,
    inst::{inst_set::InstSetExt, native::inst_set::NativeInstKind},
    isa::native::inst_set as native_inst_set,
    module::FuncRef,
};

use self::{abi::*, globals::*, i256::*, memory::*, scalar::*};

pub(super) fn translate_module(
    module: &Module,
    clif_module: &mut impl ClifModule,
) -> Result<HashMap<String, FuncId>, String> {
    let mut defined_func_map: HashMap<String, FuncId> = HashMap::new();
    let mut func_id_map: HashMap<FuncRef, FuncId> = HashMap::new();
    let data_ids = define_globals(&module.ctx, clif_module)?;

    let funcs = module.funcs();

    for &func_ref in &funcs {
        let (name, sig) = module.ctx.func_sig(func_ref, |sig| -> Result<_, String> {
            validate_cranelift_signature(&module.ctx, sig)?;
            let name = sig.name().to_string();
            let clif_sig = sonatina_sig_to_clif(&module.ctx, sig, clif_module);
            Ok((name, clif_sig))
        })?;

        let linkage = translate_linkage(module.ctx.func_linkage(func_ref));
        let func_id = clif_module
            .declare_function(&name, linkage, &sig)
            .map_err(|e| format!("failed to declare function {name}: {e}"))?;

        func_id_map.insert(func_ref, func_id);
    }

    for &func_ref in &funcs {
        let name = module.ctx.func_sig(func_ref, |sig| sig.name().to_string());
        let translated = module
            .func_store
            .try_view(func_ref, |function| -> Result<bool, String> {
                if module.ctx.func_linkage(func_ref).is_external() {
                    return Ok(false);
                }
                if function.layout.entry_block().is_none() {
                    return Ok(false);
                }
                let func_id = func_id_map[&func_ref];
                translate_function(
                    module,
                    function,
                    func_ref,
                    func_id,
                    &func_id_map,
                    &data_ids,
                    clif_module,
                )?;
                Ok(true)
            });
        match translated {
            Some(Ok(true)) => {
                defined_func_map.insert(name, func_id_map[&func_ref]);
            }
            Some(Ok(false)) | None => {}
            Some(Err(error)) => {
                return Err(format!("failed to translate function {name}: {error}"));
            }
        }
    }

    Ok(defined_func_map)
}

fn emit_trap(builder: &mut FunctionBuilder, code: TrapCode) {
    builder.ins().trap(code);
}

fn translate_linkage(linkage: SonatinaLinkage) -> Linkage {
    match linkage {
        SonatinaLinkage::Public => Linkage::Export,
        SonatinaLinkage::Private => Linkage::Local,
        SonatinaLinkage::External => Linkage::Import,
    }
}

fn translate_function(
    module: &Module,
    function: &Function,
    func_ref: FuncRef,
    func_id: FuncId,
    func_id_map: &HashMap<FuncRef, FuncId>,
    data_ids: &GlobalDataMap,
    clif_module: &mut impl ClifModule,
) -> Result<(), String> {
    let target_config = clif_module.target_config();
    let pointer_type = target_config.pointer_type();
    let mut ctx = clif_module.make_context();
    let sig = module.ctx.func_sig(func_ref, |sig| -> Result<_, String> {
        validate_cranelift_signature(&module.ctx, sig)?;
        Ok(sonatina_sig_to_clif(&module.ctx, sig, clif_module))
    })?;
    ctx.func.signature = sig;

    let mut builder_ctx = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_ctx);

    let mut cfg = ControlFlowGraph::default();
    cfg.compute(function);
    let mut block_order: Vec<_> = cfg.post_order().collect();
    block_order.reverse();

    let mut block_map: HashMap<BlockId, clif::Block> = HashMap::new();
    let mut value_map: HashMap<ValueId, clif::Value> = HashMap::new();
    for &block in &block_order {
        let clif_block = builder.create_block();
        block_map.insert(block, clif_block);
    }

    let has_sret = module
        .ctx
        .func_sig(func_ref, |sig| returns_indirect(&module.ctx, sig));

    let entry = function.layout.entry_block().ok_or("no entry block")?;
    let clif_entry = block_map[&entry];
    builder.append_block_params_for_function_params(clif_entry);
    builder.switch_to_block(clif_entry);

    let sret_ptr = if has_sret {
        Some(builder.block_params(clif_entry)[0])
    } else {
        None
    };

    let arg_offset = if has_sret { 1 } else { 0 };
    for (idx, &arg_value) in function.arg_values.iter().enumerate() {
        let param = builder.block_params(clif_entry)[idx + arg_offset];
        let param = normalize_scalar(param, function.dfg.value_ty(arg_value), &mut builder);
        value_map.insert(arg_value, param);
    }

    // Materialize global addresses in the entry block so they dominate all
    // uses, including phi edges. const.ref uses these same module definitions.
    for (value_id, value) in function.dfg.values_iter() {
        if let Value::Global { gv, .. } = value
            && function.dfg.users(value_id).next().is_some()
        {
            let address = global_address(*gv, data_ids, clif_module, &mut builder)?;
            value_map.insert(value_id, address);
        }
    }

    let inst_set = function.inst_set();
    let mut indirect_phi_stores: HashMap<BlockId, Vec<_>> = HashMap::new();

    for &block in &block_order {
        let clif_block = block_map[&block];
        for inst_id in function.layout.iter_inst(block) {
            let inst_data = function.dfg.inst(inst_id);
            if <&sonatina_ir::inst::control_flow::Phi as sonatina_ir::InstDowncast>::downcast(
                inst_set, inst_data,
            )
            .is_some()
            {
                let result = function
                    .dfg
                    .inst_result(inst_id)
                    .ok_or("phi has no result")?;
                let ty = function.dfg.value_ty(result);
                if uses_indirect_value_representation(&module.ctx, ty) {
                    let addr = create_stack_slot_for_type(ty, &module.ctx, &mut builder)?;
                    value_map.insert(result, addr);
                    for (offset, chunk_ty) in storage_chunks(value_storage_size(ty, &module.ctx)?) {
                        let param = builder.append_block_param(clif_block, chunk_ty);
                        indirect_phi_stores
                            .entry(block)
                            .or_default()
                            .push((addr, param, offset));
                    }
                } else {
                    let clif_ty = sonatina_type_to_clif_or_err(ty, pointer_type)?;
                    let param = builder.append_block_param(clif_block, clif_ty);
                    value_map.insert(result, param);
                }
            } else {
                break;
            }
        }
    }

    for &block in &block_order {
        let clif_block = block_map[&block];
        if block != entry {
            builder.switch_to_block(clif_block);
        }
        // Incoming contents are SSA block parameters, not pointers into a
        // previous iteration's reusable result slots. Capture all phi inputs
        // on the edge before writing any destination, including phi swaps.
        if let Some(stores) = indirect_phi_stores.get(&block) {
            for &(addr, param, offset) in stores {
                builder
                    .ins()
                    .store(MemFlagsData::new(), param, addr, offset);
            }
        }

        for inst_id in function.layout.iter_inst(block) {
            let inst_data = function.dfg.inst(inst_id);

            match native_inst_set().resolve_inst(inst_data) {
                NativeInstKind::Add(add) => {
                    let result_val = if function.dfg.value_ty(*add.lhs()) == Type::I256 {
                        emit_i256_add(function, *add.lhs(), *add.rhs(), &value_map, &mut builder)?
                    } else {
                        let lhs = resolve_value(function, *add.lhs(), &value_map, &mut builder)?;
                        let rhs = resolve_value(function, *add.rhs(), &value_map, &mut builder)?;
                        builder.ins().iadd(lhs, rhs)
                    };
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Sub(sub) => {
                    let result_val = if function.dfg.value_ty(*sub.lhs()) == Type::I256 {
                        emit_i256_sub(function, *sub.lhs(), *sub.rhs(), &value_map, &mut builder)?
                    } else {
                        let lhs = resolve_value(function, *sub.lhs(), &value_map, &mut builder)?;
                        let rhs = resolve_value(function, *sub.rhs(), &value_map, &mut builder)?;
                        builder.ins().isub(lhs, rhs)
                    };
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Mul(mul) => {
                    let result_val = if function.dfg.value_ty(*mul.lhs()) == Type::I256 {
                        emit_i256_mul(function, *mul.lhs(), *mul.rhs(), &value_map, &mut builder)?
                    } else {
                        let lhs = resolve_value(function, *mul.lhs(), &value_map, &mut builder)?;
                        let rhs = resolve_value(function, *mul.rhs(), &value_map, &mut builder)?;
                        builder.ins().imul(lhs, rhs)
                    };
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Neg(neg) => {
                    let result_val = if function.dfg.value_ty(*neg.arg()) == Type::I256 {
                        emit_i256_neg(function, *neg.arg(), &value_map, &mut builder)?
                    } else {
                        let val = resolve_value(function, *neg.arg(), &value_map, &mut builder)?;
                        builder.ins().ineg(val)
                    };
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Udiv(div) => {
                    let result_val = if function.dfg.value_ty(*div.lhs()) == Type::I256 {
                        emit_i256_div_rem(
                            function,
                            *div.lhs(),
                            *div.rhs(),
                            DivRemKind::Udiv,
                            &value_map,
                            &mut builder,
                        )?
                    } else {
                        let lhs = resolve_value(function, *div.lhs(), &value_map, &mut builder)?;
                        let rhs = resolve_value(function, *div.rhs(), &value_map, &mut builder)?;
                        emit_scalar_div_rem(
                            lhs,
                            rhs,
                            function.dfg.value_ty(*div.lhs()),
                            DivRemKind::Udiv,
                            &mut builder,
                        )
                    };
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Sdiv(div) => {
                    let result_val = if function.dfg.value_ty(*div.lhs()) == Type::I256 {
                        emit_i256_div_rem(
                            function,
                            *div.lhs(),
                            *div.rhs(),
                            DivRemKind::Sdiv,
                            &value_map,
                            &mut builder,
                        )?
                    } else {
                        let lhs = resolve_value(function, *div.lhs(), &value_map, &mut builder)?;
                        let rhs = resolve_value(function, *div.rhs(), &value_map, &mut builder)?;
                        emit_scalar_div_rem(
                            lhs,
                            rhs,
                            function.dfg.value_ty(*div.lhs()),
                            DivRemKind::Sdiv,
                            &mut builder,
                        )
                    };
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Umod(rem) => {
                    let result_val = if function.dfg.value_ty(*rem.lhs()) == Type::I256 {
                        emit_i256_div_rem(
                            function,
                            *rem.lhs(),
                            *rem.rhs(),
                            DivRemKind::Umod,
                            &value_map,
                            &mut builder,
                        )?
                    } else {
                        let lhs = resolve_value(function, *rem.lhs(), &value_map, &mut builder)?;
                        let rhs = resolve_value(function, *rem.rhs(), &value_map, &mut builder)?;
                        emit_scalar_div_rem(
                            lhs,
                            rhs,
                            function.dfg.value_ty(*rem.lhs()),
                            DivRemKind::Umod,
                            &mut builder,
                        )
                    };
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Smod(rem) => {
                    let result_val = if function.dfg.value_ty(*rem.lhs()) == Type::I256 {
                        emit_i256_div_rem(
                            function,
                            *rem.lhs(),
                            *rem.rhs(),
                            DivRemKind::Smod,
                            &value_map,
                            &mut builder,
                        )?
                    } else {
                        let lhs = resolve_value(function, *rem.lhs(), &value_map, &mut builder)?;
                        let rhs = resolve_value(function, *rem.rhs(), &value_map, &mut builder)?;
                        emit_scalar_div_rem(
                            lhs,
                            rhs,
                            function.dfg.value_ty(*rem.lhs()),
                            DivRemKind::Smod,
                            &mut builder,
                        )
                    };
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Shl(shl) => {
                    let result_val = if function.dfg.value_ty(*shl.value()) == Type::I256 {
                        emit_i256_shift(
                            function,
                            *shl.value(),
                            *shl.bits(),
                            I256ShiftKind::Shl,
                            &value_map,
                            &mut builder,
                        )?
                    } else {
                        let val = resolve_value(function, *shl.value(), &value_map, &mut builder)?;
                        let bits = resolve_value(function, *shl.bits(), &value_map, &mut builder)?;
                        emit_scalar_shift(
                            val,
                            bits,
                            function.dfg.value_ty(*shl.value()),
                            ScalarShift::Shl,
                            &mut builder,
                        )
                    };
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Shr(shr) => {
                    let result_val = if function.dfg.value_ty(*shr.value()) == Type::I256 {
                        emit_i256_shift(
                            function,
                            *shr.value(),
                            *shr.bits(),
                            I256ShiftKind::Shr,
                            &value_map,
                            &mut builder,
                        )?
                    } else {
                        let val = resolve_value(function, *shr.value(), &value_map, &mut builder)?;
                        let bits = resolve_value(function, *shr.bits(), &value_map, &mut builder)?;
                        emit_scalar_shift(
                            val,
                            bits,
                            function.dfg.value_ty(*shr.value()),
                            ScalarShift::Shr,
                            &mut builder,
                        )
                    };
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Sar(sar) => {
                    let result_val = if function.dfg.value_ty(*sar.value()) == Type::I256 {
                        emit_i256_shift(
                            function,
                            *sar.value(),
                            *sar.bits(),
                            I256ShiftKind::Sar,
                            &value_map,
                            &mut builder,
                        )?
                    } else {
                        let val = resolve_value(function, *sar.value(), &value_map, &mut builder)?;
                        let bits = resolve_value(function, *sar.bits(), &value_map, &mut builder)?;
                        emit_scalar_shift(
                            val,
                            bits,
                            function.dfg.value_ty(*sar.value()),
                            ScalarShift::Sar,
                            &mut builder,
                        )
                    };
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::And(and) => {
                    let result_val = if function.dfg.value_ty(*and.lhs()) == Type::I256 {
                        emit_i256_bitwise(
                            function,
                            *and.lhs(),
                            *and.rhs(),
                            I256BitwiseOp::And,
                            &value_map,
                            &mut builder,
                        )?
                    } else {
                        let lhs = resolve_value(function, *and.lhs(), &value_map, &mut builder)?;
                        let rhs = resolve_value(function, *and.rhs(), &value_map, &mut builder)?;
                        builder.ins().band(lhs, rhs)
                    };
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Or(or) => {
                    let result_val = if function.dfg.value_ty(*or.lhs()) == Type::I256 {
                        emit_i256_bitwise(
                            function,
                            *or.lhs(),
                            *or.rhs(),
                            I256BitwiseOp::Or,
                            &value_map,
                            &mut builder,
                        )?
                    } else {
                        let lhs = resolve_value(function, *or.lhs(), &value_map, &mut builder)?;
                        let rhs = resolve_value(function, *or.rhs(), &value_map, &mut builder)?;
                        builder.ins().bor(lhs, rhs)
                    };
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Xor(xor) => {
                    let result_val = if function.dfg.value_ty(*xor.lhs()) == Type::I256 {
                        emit_i256_bitwise(
                            function,
                            *xor.lhs(),
                            *xor.rhs(),
                            I256BitwiseOp::Xor,
                            &value_map,
                            &mut builder,
                        )?
                    } else {
                        let lhs = resolve_value(function, *xor.lhs(), &value_map, &mut builder)?;
                        let rhs = resolve_value(function, *xor.rhs(), &value_map, &mut builder)?;
                        builder.ins().bxor(lhs, rhs)
                    };
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Not(not) => {
                    let result_val = if function.dfg.value_ty(*not.arg()) == Type::I256 {
                        emit_i256_not(function, *not.arg(), &value_map, &mut builder)?
                    } else {
                        let val = resolve_value(function, *not.arg(), &value_map, &mut builder)?;
                        if function.dfg.value_ty(*not.arg()) == Type::I1 {
                            builder.ins().bxor_imm_s(val, 1)
                        } else {
                            builder.ins().bnot(val)
                        }
                    };
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Lt(lt) => {
                    translate_icmp(
                        IntCC::UnsignedLessThan,
                        *lt.lhs(),
                        *lt.rhs(),
                        inst_id,
                        module,
                        function,
                        &mut value_map,
                        pointer_type,
                        &mut builder,
                    )?;
                }
                NativeInstKind::Gt(gt) => {
                    translate_icmp(
                        IntCC::UnsignedGreaterThan,
                        *gt.lhs(),
                        *gt.rhs(),
                        inst_id,
                        module,
                        function,
                        &mut value_map,
                        pointer_type,
                        &mut builder,
                    )?;
                }
                NativeInstKind::Le(le) => {
                    translate_icmp(
                        IntCC::UnsignedLessThanOrEqual,
                        *le.lhs(),
                        *le.rhs(),
                        inst_id,
                        module,
                        function,
                        &mut value_map,
                        pointer_type,
                        &mut builder,
                    )?;
                }
                NativeInstKind::Ge(ge) => {
                    translate_icmp(
                        IntCC::UnsignedGreaterThanOrEqual,
                        *ge.lhs(),
                        *ge.rhs(),
                        inst_id,
                        module,
                        function,
                        &mut value_map,
                        pointer_type,
                        &mut builder,
                    )?;
                }
                NativeInstKind::Slt(slt) => {
                    translate_icmp(
                        IntCC::SignedLessThan,
                        *slt.lhs(),
                        *slt.rhs(),
                        inst_id,
                        module,
                        function,
                        &mut value_map,
                        pointer_type,
                        &mut builder,
                    )?;
                }
                NativeInstKind::Sgt(sgt) => {
                    translate_icmp(
                        IntCC::SignedGreaterThan,
                        *sgt.lhs(),
                        *sgt.rhs(),
                        inst_id,
                        module,
                        function,
                        &mut value_map,
                        pointer_type,
                        &mut builder,
                    )?;
                }
                NativeInstKind::Eq(eq) => {
                    translate_icmp(
                        IntCC::Equal,
                        *eq.lhs(),
                        *eq.rhs(),
                        inst_id,
                        module,
                        function,
                        &mut value_map,
                        pointer_type,
                        &mut builder,
                    )?;
                }
                NativeInstKind::Ne(ne) => {
                    translate_icmp(
                        IntCC::NotEqual,
                        *ne.lhs(),
                        *ne.rhs(),
                        inst_id,
                        module,
                        function,
                        &mut value_map,
                        pointer_type,
                        &mut builder,
                    )?;
                }
                NativeInstKind::IsZero(is_zero) => {
                    let val_ty = function.dfg.value_ty(*is_zero.lhs());
                    let result_val = if val_ty == Type::I256 {
                        let val =
                            resolve_value(function, *is_zero.lhs(), &value_map, &mut builder)?;
                        emit_i256_is_zero(val, &mut builder)
                    } else {
                        let val =
                            resolve_value(function, *is_zero.lhs(), &value_map, &mut builder)?;
                        let clif_ty =
                            sonatina_type_to_clif(val_ty, pointer_type).ok_or_else(|| {
                                format!("unsupported is_zero operand type: {val_ty:?}")
                            })?;
                        let zero = scalar_constant(clif_ty, 0, &mut builder);
                        builder.ins().icmp(IntCC::Equal, val, zero)
                    };
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Sle(sle) => {
                    translate_icmp(
                        IntCC::SignedLessThanOrEqual,
                        *sle.lhs(),
                        *sle.rhs(),
                        inst_id,
                        module,
                        function,
                        &mut value_map,
                        pointer_type,
                        &mut builder,
                    )?;
                }
                NativeInstKind::Sge(sge) => {
                    translate_icmp(
                        IntCC::SignedGreaterThanOrEqual,
                        *sge.lhs(),
                        *sge.rhs(),
                        inst_id,
                        module,
                        function,
                        &mut value_map,
                        pointer_type,
                        &mut builder,
                    )?;
                }
                NativeInstKind::Sext(sext) => {
                    let val = resolve_value(function, *sext.from(), &value_map, &mut builder)?;
                    let to_ty = sonatina_type_to_clif_or_err(*sext.ty(), pointer_type)?;
                    let result_val = if *sext.ty() == Type::I256 {
                        materialize_scalar_as_i256(
                            val,
                            function.dfg.value_ty(*sext.from()),
                            true,
                            &mut builder,
                        )
                    } else if function.dfg.value_ty(*sext.from()) == Type::I1 {
                        bool_to_int_value(val, to_ty, true, &mut builder)
                    } else {
                        resize_int_value(val, to_ty, true, &mut builder)
                    };
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Zext(zext) => {
                    let val = resolve_value(function, *zext.from(), &value_map, &mut builder)?;
                    let to_ty = sonatina_type_to_clif_or_err(*zext.ty(), pointer_type)?;
                    let result_val = if *zext.ty() == Type::I256 {
                        materialize_scalar_as_i256(
                            val,
                            function.dfg.value_ty(*zext.from()),
                            false,
                            &mut builder,
                        )
                    } else if function.dfg.value_ty(*zext.from()) == Type::I1 {
                        bool_to_int_value(val, to_ty, false, &mut builder)
                    } else {
                        resize_int_value(val, to_ty, false, &mut builder)
                    };
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Trunc(trunc) => {
                    let from_ty = function.dfg.value_ty(*trunc.from());
                    let val = resolve_value(function, *trunc.from(), &value_map, &mut builder)?;
                    let to_ty = sonatina_type_to_clif_or_err(*trunc.ty(), pointer_type)?;
                    let result_val = if from_ty == Type::I256 {
                        // i256 values are pointers — load the target-sized value from the pointer
                        builder.ins().load(to_ty, MemFlagsData::new(), val, 0)
                    } else {
                        resize_int_value(val, to_ty, false, &mut builder)
                    };
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Bitcast(bitcast) => {
                    let val = resolve_value(function, *bitcast.from(), &value_map, &mut builder)?;
                    let result_val = translate_bitcast(
                        val,
                        function.dfg.value_ty(*bitcast.from()),
                        *bitcast.ty(),
                        &module.ctx,
                        pointer_type,
                        &mut builder,
                    )?;
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::IntToPtr(cast) => {
                    let val = resolve_value(function, *cast.from(), &value_map, &mut builder)?;
                    let to_ty = sonatina_type_to_clif_or_err(*cast.ty(), pointer_type)?;
                    let result_val = if function.dfg.value_ty(*cast.from()) == Type::I256 {
                        let scalar = load_i256_limb(val, 0, &mut builder);
                        resize_int_value(scalar, to_ty, false, &mut builder)
                    } else {
                        resize_int_value(val, to_ty, false, &mut builder)
                    };
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::PtrToInt(cast) => {
                    let val = resolve_value(function, *cast.from(), &value_map, &mut builder)?;
                    let to_ty = sonatina_type_to_clif_or_err(*cast.ty(), pointer_type)?;
                    let result_val = if *cast.ty() == Type::I256 {
                        materialize_scalar_as_i256(
                            val,
                            function.dfg.value_ty(*cast.from()),
                            false,
                            &mut builder,
                        )
                    } else {
                        resize_int_value(val, to_ty, false, &mut builder)
                    };
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Jump(jump) => {
                    let dest = block_map[jump.dest()];
                    let phi_args = collect_phi_args_for_block(
                        function,
                        *jump.dest(),
                        block,
                        inst_set,
                        &value_map,
                        &mut builder,
                    )?;
                    builder.ins().jump(dest, &phi_args);
                }
                NativeInstKind::Br(br) => {
                    let cond = resolve_value(function, *br.cond(), &value_map, &mut builder)?;
                    let nz_block = block_map[br.nz_dest()];
                    let z_block = block_map[br.z_dest()];
                    let nz_args = collect_phi_args_for_block(
                        function,
                        *br.nz_dest(),
                        block,
                        inst_set,
                        &value_map,
                        &mut builder,
                    )?;
                    let z_args = collect_phi_args_for_block(
                        function,
                        *br.z_dest(),
                        block,
                        inst_set,
                        &value_map,
                        &mut builder,
                    )?;
                    builder
                        .ins()
                        .brif(cond, nz_block, &nz_args, z_block, &z_args);
                }
                NativeInstKind::BrTable(br_table) => {
                    let scrutinee_id = *br_table.scrutinee();
                    let scrutinee_ty = function.dfg.value_ty(scrutinee_id);
                    let scrutinee = if scrutinee_ty == Type::I256 {
                        resolve_value(function, scrutinee_id, &value_map, &mut builder)?
                    } else {
                        resolve_scalar_value(
                            module,
                            function,
                            scrutinee_id,
                            &value_map,
                            pointer_type,
                            &mut builder,
                        )?
                    };
                    if br_table.table().is_empty() {
                        let default = br_table
                            .default()
                            .ok_or("empty br_table requires a default destination")?;
                        let default_args = collect_phi_args_for_block(
                            function,
                            default,
                            block,
                            inst_set,
                            &value_map,
                            &mut builder,
                        )?;
                        builder.ins().jump(block_map[&default], &default_args);
                    } else {
                        for (idx, &(case, dest)) in br_table.table().iter().enumerate() {
                            let cond = if scrutinee_ty == Type::I256 {
                                let case = resolve_value(function, case, &value_map, &mut builder)?;
                                emit_i256_icmp(IntCC::Equal, scrutinee, case, &mut builder)?
                            } else {
                                let case = resolve_scalar_value(
                                    module,
                                    function,
                                    case,
                                    &value_map,
                                    pointer_type,
                                    &mut builder,
                                )?;
                                builder.ins().icmp(IntCC::Equal, scrutinee, case)
                            };
                            let dest_block = block_map[&dest];
                            let dest_args = collect_phi_args_for_block(
                                function,
                                dest,
                                block,
                                inst_set,
                                &value_map,
                                &mut builder,
                            )?;
                            let next_block = builder.create_block();
                            builder
                                .ins()
                                .brif(cond, dest_block, &dest_args, next_block, &[]);
                            builder.switch_to_block(next_block);

                            if idx + 1 == br_table.table().len() {
                                if let Some(default) = br_table.default() {
                                    let default_block = block_map[default];
                                    let default_args = collect_phi_args_for_block(
                                        function,
                                        *default,
                                        block,
                                        inst_set,
                                        &value_map,
                                        &mut builder,
                                    )?;
                                    builder.ins().jump(default_block, &default_args);
                                } else {
                                    emit_trap(&mut builder, TrapCode::user(3).unwrap());
                                }
                            }
                        }
                    }
                }
                NativeInstKind::Return(ret) => {
                    if let Some(sret) = sret_ptr {
                        let [val_id] = ret.args().as_slice() else {
                            return Err("indirect return requires exactly one value".to_string());
                        };
                        let val = resolve_value(function, *val_id, &value_map, &mut builder)?;
                        let val_ty = function.dfg.value_ty(*val_id);
                        let storage_ty = indirect_return_storage_type(&module.ctx, val_ty)
                            .ok_or("indirect return value has no storage type")?;
                        copy_bytes(
                            val,
                            sret,
                            value_storage_size(storage_ty, &module.ctx)?,
                            &mut builder,
                        );
                        builder.ins().return_(&[]);
                    } else {
                        let args: Result<Vec<_>, _> = ret
                            .args()
                            .as_slice()
                            .iter()
                            .map(|v| resolve_value(function, *v, &value_map, &mut builder))
                            .collect();
                        let args = args?;
                        builder.ins().return_(&args);
                    }
                }
                NativeInstKind::Call(call) => {
                    let callee = *call.callee();
                    let clif_func_id = func_id_map
                        .get(&callee)
                        .ok_or_else(|| format!("unknown callee {callee:?}"))?;
                    let clif_func_ref =
                        clif_module.declare_func_in_func(*clif_func_id, builder.func);
                    let ir_results = function.dfg.inst_results(inst_id);
                    let indirect_storage_ty = match ir_results {
                        [result] => indirect_return_storage_type(
                            &module.ctx,
                            function.dfg.value_ty(*result),
                        ),
                        _ => None,
                    };

                    let mut call_args = Vec::new();
                    let sret_slot = if let Some(storage_ty) = indirect_storage_ty {
                        let slot = builder
                            .create_sized_stack_slot(stack_slot_data(storage_ty, &module.ctx)?);
                        let addr = builder.ins().stack_addr(pointer_type, slot, 0);
                        call_args.push(addr);
                        Some(addr)
                    } else {
                        None
                    };

                    let args: Result<Vec<_>, _> = call
                        .args()
                        .iter()
                        .map(|value| resolve_value(function, *value, &value_map, &mut builder))
                        .collect();
                    call_args.extend(args?);

                    let clif_call = builder.ins().call(clif_func_ref, &call_args);
                    if let Some(sret_addr) = sret_slot {
                        if let Some(result) = ir_results.first() {
                            value_map.insert(*result, sret_addr);
                        }
                    } else {
                        let results = builder.inst_results(clif_call);
                        for (ir_result, clif_result) in ir_results.iter().zip(results) {
                            value_map.insert(*ir_result, *clif_result);
                        }
                    }
                }
                NativeInstKind::Uaddo(uaddo) => {
                    if function.dfg.value_ty(*uaddo.lhs()) == Type::I256 {
                        let (result_val, overflow) = emit_i256_uaddo(
                            function,
                            *uaddo.lhs(),
                            *uaddo.rhs(),
                            &value_map,
                            &mut builder,
                        )?;
                        insert_clif_results(
                            function,
                            inst_id,
                            [result_val, overflow],
                            &mut value_map,
                        );
                    } else {
                        let lhs = resolve_value(function, *uaddo.lhs(), &value_map, &mut builder)?;
                        let rhs = resolve_value(function, *uaddo.rhs(), &value_map, &mut builder)?;
                        let (result_val, overflow) = emit_scalar_overflow(
                            lhs,
                            rhs,
                            function.dfg.value_ty(*uaddo.lhs()),
                            ScalarArithmetic::Add,
                            false,
                            &mut builder,
                        );
                        insert_clif_results(
                            function,
                            inst_id,
                            [result_val, overflow],
                            &mut value_map,
                        );
                    }
                }
                NativeInstKind::Saddo(saddo) => {
                    if function.dfg.value_ty(*saddo.lhs()) == Type::I256 {
                        let (result_val, overflow) = emit_i256_saddo(
                            function,
                            *saddo.lhs(),
                            *saddo.rhs(),
                            &value_map,
                            &mut builder,
                        )?;
                        insert_clif_results(
                            function,
                            inst_id,
                            [result_val, overflow],
                            &mut value_map,
                        );
                    } else {
                        let lhs = resolve_value(function, *saddo.lhs(), &value_map, &mut builder)?;
                        let rhs = resolve_value(function, *saddo.rhs(), &value_map, &mut builder)?;
                        let (result_val, overflow) = emit_scalar_overflow(
                            lhs,
                            rhs,
                            function.dfg.value_ty(*saddo.lhs()),
                            ScalarArithmetic::Add,
                            true,
                            &mut builder,
                        );
                        insert_clif_results(
                            function,
                            inst_id,
                            [result_val, overflow],
                            &mut value_map,
                        );
                    }
                }
                NativeInstKind::Usubo(usubo) => {
                    if function.dfg.value_ty(*usubo.lhs()) == Type::I256 {
                        let (result_val, overflow) = emit_i256_usubo(
                            function,
                            *usubo.lhs(),
                            *usubo.rhs(),
                            &value_map,
                            &mut builder,
                        )?;
                        insert_clif_results(
                            function,
                            inst_id,
                            [result_val, overflow],
                            &mut value_map,
                        );
                    } else {
                        let lhs = resolve_value(function, *usubo.lhs(), &value_map, &mut builder)?;
                        let rhs = resolve_value(function, *usubo.rhs(), &value_map, &mut builder)?;
                        let (result_val, overflow) = emit_scalar_overflow(
                            lhs,
                            rhs,
                            function.dfg.value_ty(*usubo.lhs()),
                            ScalarArithmetic::Sub,
                            false,
                            &mut builder,
                        );
                        insert_clif_results(
                            function,
                            inst_id,
                            [result_val, overflow],
                            &mut value_map,
                        );
                    }
                }
                NativeInstKind::Ssubo(ssubo) => {
                    if function.dfg.value_ty(*ssubo.lhs()) == Type::I256 {
                        let (result_val, overflow) = emit_i256_ssubo(
                            function,
                            *ssubo.lhs(),
                            *ssubo.rhs(),
                            &value_map,
                            &mut builder,
                        )?;
                        insert_clif_results(
                            function,
                            inst_id,
                            [result_val, overflow],
                            &mut value_map,
                        );
                    } else {
                        let lhs = resolve_value(function, *ssubo.lhs(), &value_map, &mut builder)?;
                        let rhs = resolve_value(function, *ssubo.rhs(), &value_map, &mut builder)?;
                        let (result_val, overflow) = emit_scalar_overflow(
                            lhs,
                            rhs,
                            function.dfg.value_ty(*ssubo.lhs()),
                            ScalarArithmetic::Sub,
                            true,
                            &mut builder,
                        );
                        insert_clif_results(
                            function,
                            inst_id,
                            [result_val, overflow],
                            &mut value_map,
                        );
                    }
                }
                NativeInstKind::Umulo(umulo) => {
                    if function.dfg.value_ty(*umulo.lhs()) == Type::I256 {
                        let (result_val, overflow) = emit_i256_umulo(
                            function,
                            *umulo.lhs(),
                            *umulo.rhs(),
                            &value_map,
                            &mut builder,
                        )?;
                        insert_clif_results(
                            function,
                            inst_id,
                            [result_val, overflow],
                            &mut value_map,
                        );
                    } else {
                        let lhs = resolve_value(function, *umulo.lhs(), &value_map, &mut builder)?;
                        let rhs = resolve_value(function, *umulo.rhs(), &value_map, &mut builder)?;
                        let (result_val, overflow) = emit_scalar_overflow(
                            lhs,
                            rhs,
                            function.dfg.value_ty(*umulo.lhs()),
                            ScalarArithmetic::Mul,
                            false,
                            &mut builder,
                        );
                        insert_clif_results(
                            function,
                            inst_id,
                            [result_val, overflow],
                            &mut value_map,
                        );
                    }
                }
                NativeInstKind::Smulo(smulo) => {
                    if function.dfg.value_ty(*smulo.lhs()) == Type::I256 {
                        let (result_val, overflow) = emit_i256_smulo(
                            function,
                            *smulo.lhs(),
                            *smulo.rhs(),
                            &value_map,
                            &mut builder,
                        )?;
                        insert_clif_results(
                            function,
                            inst_id,
                            [result_val, overflow],
                            &mut value_map,
                        );
                    } else {
                        let lhs = resolve_value(function, *smulo.lhs(), &value_map, &mut builder)?;
                        let rhs = resolve_value(function, *smulo.rhs(), &value_map, &mut builder)?;
                        let (result_val, overflow) = emit_scalar_overflow(
                            lhs,
                            rhs,
                            function.dfg.value_ty(*smulo.lhs()),
                            ScalarArithmetic::Mul,
                            true,
                            &mut builder,
                        );
                        insert_clif_results(
                            function,
                            inst_id,
                            [result_val, overflow],
                            &mut value_map,
                        );
                    }
                }
                NativeInstKind::Snego(snego) => {
                    if function.dfg.value_ty(*snego.arg()) == Type::I256 {
                        let (result_val, overflow) =
                            emit_i256_snego(function, *snego.arg(), &value_map, &mut builder)?;
                        insert_clif_results(
                            function,
                            inst_id,
                            [result_val, overflow],
                            &mut value_map,
                        );
                    } else {
                        let val = resolve_value(function, *snego.arg(), &value_map, &mut builder)?;
                        let ty = builder.func.dfg.value_type(val);
                        let zero = scalar_constant(ty, 0, &mut builder);
                        let (result_val, overflow) = emit_scalar_overflow(
                            zero,
                            val,
                            function.dfg.value_ty(*snego.arg()),
                            ScalarArithmetic::Sub,
                            true,
                            &mut builder,
                        );
                        insert_clif_results(
                            function,
                            inst_id,
                            [result_val, overflow],
                            &mut value_map,
                        );
                    }
                }
                NativeInstKind::Uaddsat(uaddsat) => {
                    let result_val = if function.dfg.value_ty(*uaddsat.lhs()) == Type::I256 {
                        emit_i256_saturating_binary(
                            function,
                            *uaddsat.lhs(),
                            *uaddsat.rhs(),
                            I256SaturatingOp::Uadd,
                            &value_map,
                            &mut builder,
                        )?
                    } else {
                        let lhs =
                            resolve_value(function, *uaddsat.lhs(), &value_map, &mut builder)?;
                        let rhs =
                            resolve_value(function, *uaddsat.rhs(), &value_map, &mut builder)?;
                        let (raw, overflow) = builder.ins().uadd_overflow(lhs, rhs);
                        let max =
                            unsigned_max_value(builder.func.dfg.value_type(lhs), &mut builder);
                        builder.ins().select(overflow, max, raw)
                    };
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Saddsat(saddsat) => {
                    let result_val = if function.dfg.value_ty(*saddsat.lhs()) == Type::I256 {
                        emit_i256_saturating_binary(
                            function,
                            *saddsat.lhs(),
                            *saddsat.rhs(),
                            I256SaturatingOp::Sadd,
                            &value_map,
                            &mut builder,
                        )?
                    } else {
                        let lhs =
                            resolve_value(function, *saddsat.lhs(), &value_map, &mut builder)?;
                        let rhs =
                            resolve_value(function, *saddsat.rhs(), &value_map, &mut builder)?;
                        let (raw, overflow) = builder.ins().sadd_overflow(lhs, rhs);
                        let ty = builder.func.dfg.value_type(lhs);
                        let zero = scalar_constant(ty, 0, &mut builder);
                        let lhs_neg = builder.ins().icmp(IntCC::SignedLessThan, lhs, zero);
                        let min = signed_min_value(ty, &mut builder);
                        let max = signed_max_value(ty, &mut builder);
                        let sat = builder.ins().select(lhs_neg, min, max);
                        builder.ins().select(overflow, sat, raw)
                    };
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Usubsat(usubsat) => {
                    let result_val = if function.dfg.value_ty(*usubsat.lhs()) == Type::I256 {
                        emit_i256_saturating_binary(
                            function,
                            *usubsat.lhs(),
                            *usubsat.rhs(),
                            I256SaturatingOp::Usub,
                            &value_map,
                            &mut builder,
                        )?
                    } else {
                        let lhs =
                            resolve_value(function, *usubsat.lhs(), &value_map, &mut builder)?;
                        let rhs =
                            resolve_value(function, *usubsat.rhs(), &value_map, &mut builder)?;
                        let (raw, overflow) = builder.ins().usub_overflow(lhs, rhs);
                        let ty = builder.func.dfg.value_type(lhs);
                        let zero = scalar_constant(ty, 0, &mut builder);
                        builder.ins().select(overflow, zero, raw)
                    };
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Ssubsat(ssubsat) => {
                    let result_val = if function.dfg.value_ty(*ssubsat.lhs()) == Type::I256 {
                        emit_i256_saturating_binary(
                            function,
                            *ssubsat.lhs(),
                            *ssubsat.rhs(),
                            I256SaturatingOp::Ssub,
                            &value_map,
                            &mut builder,
                        )?
                    } else {
                        let lhs =
                            resolve_value(function, *ssubsat.lhs(), &value_map, &mut builder)?;
                        let rhs =
                            resolve_value(function, *ssubsat.rhs(), &value_map, &mut builder)?;
                        let (raw, overflow) = builder.ins().ssub_overflow(lhs, rhs);
                        let ty = builder.func.dfg.value_type(lhs);
                        let zero = scalar_constant(ty, 0, &mut builder);
                        let lhs_neg = builder.ins().icmp(IntCC::SignedLessThan, lhs, zero);
                        let min = signed_min_value(ty, &mut builder);
                        let max = signed_max_value(ty, &mut builder);
                        let sat = builder.ins().select(lhs_neg, min, max);
                        builder.ins().select(overflow, sat, raw)
                    };
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Umulsat(umulsat) => {
                    let result_val = if function.dfg.value_ty(*umulsat.lhs()) == Type::I256 {
                        emit_i256_saturating_binary(
                            function,
                            *umulsat.lhs(),
                            *umulsat.rhs(),
                            I256SaturatingOp::Umul,
                            &value_map,
                            &mut builder,
                        )?
                    } else {
                        let lhs =
                            resolve_value(function, *umulsat.lhs(), &value_map, &mut builder)?;
                        let rhs =
                            resolve_value(function, *umulsat.rhs(), &value_map, &mut builder)?;
                        let (raw, overflow) =
                            emit_scalar_mul_overflow(lhs, rhs, false, &mut builder);
                        let max =
                            unsigned_max_value(builder.func.dfg.value_type(lhs), &mut builder);
                        builder.ins().select(overflow, max, raw)
                    };
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Smulsat(smulsat) => {
                    let result_val = if function.dfg.value_ty(*smulsat.lhs()) == Type::I256 {
                        emit_i256_saturating_binary(
                            function,
                            *smulsat.lhs(),
                            *smulsat.rhs(),
                            I256SaturatingOp::Smul,
                            &value_map,
                            &mut builder,
                        )?
                    } else {
                        let lhs =
                            resolve_value(function, *smulsat.lhs(), &value_map, &mut builder)?;
                        let rhs =
                            resolve_value(function, *smulsat.rhs(), &value_map, &mut builder)?;
                        let (raw, overflow) =
                            emit_scalar_mul_overflow(lhs, rhs, true, &mut builder);
                        let ty = builder.func.dfg.value_type(lhs);
                        let zero = scalar_constant(ty, 0, &mut builder);
                        let lhs_neg = builder.ins().icmp(IntCC::SignedLessThan, lhs, zero);
                        let rhs_neg = builder.ins().icmp(IntCC::SignedLessThan, rhs, zero);
                        let same_sign = builder.ins().icmp(IntCC::Equal, lhs_neg, rhs_neg);
                        let min = signed_min_value(ty, &mut builder);
                        let max = signed_max_value(ty, &mut builder);
                        let sat = builder.ins().select(same_sign, max, min);
                        builder.ins().select(overflow, sat, raw)
                    };
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::ObjLoad(obj_load) => {
                    let addr =
                        resolve_value(function, *obj_load.object(), &value_map, &mut builder)?;
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        let result_ty = function.dfg.value_ty(result);
                        if uses_indirect_value_representation(&module.ctx, result_ty) {
                            let result_addr =
                                create_stack_slot_for_type(result_ty, &module.ctx, &mut builder)?;
                            copy_bytes(
                                addr,
                                result_addr,
                                value_storage_size(result_ty, &module.ctx)?,
                                &mut builder,
                            );
                            value_map.insert(result, result_addr);
                        } else {
                            let clif_ty = sonatina_type_to_clif_or_err(result_ty, pointer_type)?;
                            let loaded = builder.ins().load(clif_ty, MemFlagsData::new(), addr, 0);
                            value_map.insert(result, loaded);
                        }
                    }
                }
                NativeInstKind::ExtractValue(extract) => {
                    let base = resolve_value(function, *extract.dest(), &value_map, &mut builder)?;
                    let idx = constant_value_index(function, *extract.idx(), "extract_value")?;
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        let result_ty = function.dfg.value_ty(result);
                        let dest_ty = function.dfg.value_ty(*extract.dest());
                        let (offset, elem_ty) = aggregate_elem_offset(&module.ctx, dest_ty, idx)?;
                        if result_ty != elem_ty {
                            return Err(format!(
                                "extract_value element type mismatch: expected {elem_ty:?}, got {result_ty:?}"
                            ));
                        }
                        if uses_indirect_value_representation(&module.ctx, result_ty) {
                            let addr = builder.ins().iadd_imm_s(base, offset as i64);
                            value_map.insert(result, addr);
                        } else {
                            let clif_ty = sonatina_type_to_clif_or_err(result_ty, pointer_type)?;
                            let loaded =
                                builder
                                    .ins()
                                    .load(clif_ty, MemFlagsData::new(), base, offset);
                            value_map.insert(result, loaded);
                        }
                    }
                }
                NativeInstKind::InsertValue(insert) => {
                    let Some(result) = function.dfg.inst_result(inst_id) else {
                        continue;
                    };
                    let result_ty = function.dfg.value_ty(result);
                    let result_addr =
                        create_stack_slot_for_type(result_ty, &module.ctx, &mut builder)?;
                    let source = resolve_value(function, *insert.dest(), &value_map, &mut builder)?;
                    copy_bytes(
                        source,
                        result_addr,
                        value_storage_size(result_ty, &module.ctx)?,
                        &mut builder,
                    );

                    let idx = constant_value_index(function, *insert.idx(), "insert_value")?;
                    let (offset, elem_ty) = aggregate_elem_offset(&module.ctx, result_ty, idx)?;
                    let value_ty = function.dfg.value_ty(*insert.value());
                    if value_ty != elem_ty {
                        return Err(format!(
                            "insert_value element type mismatch: expected {elem_ty:?}, got {value_ty:?}"
                        ));
                    }

                    let value = resolve_value(function, *insert.value(), &value_map, &mut builder)?;
                    if uses_indirect_value_representation(&module.ctx, value_ty) {
                        let field_addr = builder.ins().iadd_imm_s(result_addr, i64::from(offset));
                        copy_bytes(
                            value,
                            field_addr,
                            value_storage_size(value_ty, &module.ctx)?,
                            &mut builder,
                        );
                    } else {
                        builder
                            .ins()
                            .store(MemFlagsData::new(), value, result_addr, offset);
                    }
                    value_map.insert(result, result_addr);
                }
                NativeInstKind::Gep(gep) => {
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        let addr = translate_gep(
                            &module.ctx,
                            function,
                            gep.values(),
                            &value_map,
                            &mut builder,
                        )?;
                        value_map.insert(result, addr);
                    }
                }
                NativeInstKind::Alloca(alloca) => {
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        let slot = builder
                            .create_sized_stack_slot(stack_slot_data(*alloca.ty(), &module.ctx)?);
                        let addr = builder.ins().stack_addr(pointer_type, slot, 0);
                        value_map.insert(result, addr);
                    }
                }
                NativeInstKind::Mstore(mstore) => {
                    let addr = resolve_pointer_sized_value(
                        function,
                        *mstore.addr(),
                        &value_map,
                        pointer_type,
                        &mut builder,
                    )?;
                    let val = resolve_value(function, *mstore.value(), &value_map, &mut builder)?;
                    let store_ty = *mstore.ty();
                    if uses_indirect_value_representation(&module.ctx, store_ty) {
                        copy_bytes(
                            val,
                            addr,
                            value_storage_size(store_ty, &module.ctx)?,
                            &mut builder,
                        );
                    } else {
                        builder.ins().store(MemFlagsData::new(), val, addr, 0);
                    }
                }
                NativeInstKind::Memzero(memzero) => {
                    let dest = resolve_pointer_sized_value(
                        function,
                        *memzero.dest(),
                        &value_map,
                        pointer_type,
                        &mut builder,
                    )?;
                    let len = resolve_pointer_sized_value(
                        function,
                        *memzero.len(),
                        &value_map,
                        pointer_type,
                        &mut builder,
                    )?;
                    let zero = builder.ins().iconst(clif::types::I8, 0);
                    builder.call_memset(target_config, dest, zero, len);
                }
                NativeInstKind::Mload(mload) => {
                    let addr = resolve_pointer_sized_value(
                        function,
                        *mload.addr(),
                        &value_map,
                        pointer_type,
                        &mut builder,
                    )?;
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        let result_ty = function.dfg.value_ty(result);
                        if uses_indirect_value_representation(&module.ctx, result_ty) {
                            let result_addr =
                                create_stack_slot_for_type(result_ty, &module.ctx, &mut builder)?;
                            copy_bytes(
                                addr,
                                result_addr,
                                value_storage_size(result_ty, &module.ctx)?,
                                &mut builder,
                            );
                            value_map.insert(result, result_addr);
                        } else {
                            let clif_ty = sonatina_type_to_clif_or_err(result_ty, pointer_type)?;
                            let loaded = builder.ins().load(clif_ty, MemFlagsData::new(), addr, 0);
                            value_map.insert(result, loaded);
                        }
                    }
                }
                NativeInstKind::ObjStore(obj_store) => {
                    let dest =
                        resolve_value(function, *obj_store.object(), &value_map, &mut builder)?;
                    let val =
                        resolve_value(function, *obj_store.value(), &value_map, &mut builder)?;
                    let val_ty = function.dfg.value_ty(*obj_store.value());
                    if uses_indirect_value_representation(&module.ctx, val_ty) {
                        copy_bytes(
                            val,
                            dest,
                            value_storage_size(val_ty, &module.ctx)?,
                            &mut builder,
                        );
                    } else {
                        builder.ins().store(MemFlagsData::new(), val, dest, 0);
                    }
                }
                NativeInstKind::ObjAlloc(obj_alloc) => {
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        let slot = builder.create_sized_stack_slot(stack_slot_data(
                            *obj_alloc.ty(),
                            &module.ctx,
                        )?);
                        let addr = builder.ins().stack_addr(pointer_type, slot, 0);
                        value_map.insert(result, addr);
                    }
                }
                NativeInstKind::ObjInitConst(obj_init_const) => {
                    let object = resolve_value(
                        function,
                        *obj_init_const.object(),
                        &value_map,
                        &mut builder,
                    )?;
                    let value =
                        resolve_value(function, *obj_init_const.value(), &value_map, &mut builder)?;
                    let object_ty = function.dfg.value_ty(*obj_init_const.object());
                    copy_bytes(
                        value,
                        object,
                        referenced_value_storage_size(object_ty, &module.ctx)?,
                        &mut builder,
                    );
                }
                NativeInstKind::ObjProj(obj_proj) => {
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        let addr = translate_aggregate_projection(
                            &module.ctx,
                            function,
                            obj_proj.values(),
                            "obj.proj",
                            &value_map,
                            &mut builder,
                        )?;
                        value_map.insert(result, addr);
                    }
                }
                NativeInstKind::ObjIndex(obj_index) => {
                    let base =
                        resolve_value(function, *obj_index.object(), &value_map, &mut builder)?;
                    let index = resolve_index(
                        function,
                        *obj_index.index(),
                        false,
                        &value_map,
                        &mut builder,
                    )?;
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        let obj_ty = function.dfg.value_ty(*obj_index.object());
                        let elem_size = compute_element_size(obj_ty, &module.ctx)?;
                        let elem_size = i64::try_from(elem_size)
                            .map_err(|_| "array element size overflows i64".to_string())?;
                        let stride = builder.ins().iconst(clif::types::I64, elem_size);
                        let offset = builder.ins().imul(index, stride);
                        let addr = builder.ins().iadd(base, offset);
                        value_map.insert(result, addr);
                    }
                }
                NativeInstKind::ConstRef(const_ref) => {
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        let addr = global_address(
                            const_ref.global().gv(),
                            data_ids,
                            clif_module,
                            &mut builder,
                        )?;
                        value_map.insert(result, addr);
                    }
                }
                NativeInstKind::ConstProj(const_proj) => {
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        let addr = translate_aggregate_projection(
                            &module.ctx,
                            function,
                            const_proj.values(),
                            "const.proj",
                            &value_map,
                            &mut builder,
                        )?;
                        value_map.insert(result, addr);
                    }
                }
                NativeInstKind::ConstIndex(const_index) => {
                    let base =
                        resolve_value(function, *const_index.object(), &value_map, &mut builder)?;
                    let index = resolve_index(
                        function,
                        *const_index.index(),
                        false,
                        &value_map,
                        &mut builder,
                    )?;
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        let obj_ty = function.dfg.value_ty(*const_index.object());
                        let elem_size = compute_element_size(obj_ty, &module.ctx)?;
                        let elem_size = i64::try_from(elem_size)
                            .map_err(|_| "array element size overflows i64".to_string())?;
                        let stride = builder.ins().iconst(clif::types::I64, elem_size);
                        let offset = builder.ins().imul(index, stride);
                        let ptr = builder.ins().iadd(base, offset);
                        value_map.insert(result, ptr);
                    }
                }
                NativeInstKind::ConstLoad(const_load) => {
                    let addr =
                        resolve_value(function, *const_load.object(), &value_map, &mut builder)?;
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        let result_ty = function.dfg.value_ty(result);
                        if uses_indirect_value_representation(&module.ctx, result_ty) {
                            value_map.insert(result, addr);
                        } else {
                            let clif_ty = sonatina_type_to_clif_or_err(result_ty, pointer_type)?;
                            let loaded = builder.ins().load(clif_ty, MemFlagsData::new(), addr, 0);
                            value_map.insert(result, loaded);
                        }
                    }
                }
                NativeInstKind::Unreachable(_) => {
                    emit_trap(&mut builder, TrapCode::user(1).unwrap());
                }
                NativeInstKind::Phi(_) => continue,
                NativeInstKind::EnumMake(_)
                | NativeInstKind::EnumTag(_)
                | NativeInstKind::EnumIsVariant(_)
                | NativeInstKind::EnumAssertVariant(_)
                | NativeInstKind::EnumAssertVariantRef(_)
                | NativeInstKind::EnumExtract(_)
                | NativeInstKind::EnumSetTag(_)
                | NativeInstKind::EnumWriteVariant(_)
                | NativeInstKind::EnumGetTag(_)
                | NativeInstKind::EnumProj(_) => {
                    return Err(format!(
                        "enum instruction {:?} survived EnumLowerToProduct",
                        inst_data.kind()
                    ));
                }
                NativeInstKind::GetFunctionPtr(_)
                | NativeInstKind::SymAddr(_)
                | NativeInstKind::SymSize(_) => {
                    return Err(format!(
                        "symbolic instruction {:?} is not supported by the host-native Cranelift backend",
                        inst_data.kind()
                    ));
                }
                NativeInstKind::ObjMaterializeStack(_)
                | NativeInstKind::ObjMaterializeHeap(_)
                | NativeInstKind::MemAllocDynamic(_) => {
                    return Err(format!(
                        "allocation instruction {:?} requires lowering before host-native Cranelift translation",
                        inst_data.kind()
                    ));
                }
            }
            // Canonicalize every producer, including loads, casts, and call
            // results. Phi inputs are already canonical on their incoming edges.
            for &result in function.dfg.inst_results(inst_id) {
                let value = value_map[&result];
                let value = normalize_scalar(value, function.dfg.value_ty(result), &mut builder);
                value_map.insert(result, value);
            }
        }
    }

    builder.seal_all_blocks();
    builder.finalize(clif_module.target_config());

    if std::env::var("DUMP_CLIF").is_ok() {
        let name = module.ctx.func_sig(func_ref, |sig| sig.name().to_string());
        eprintln!("[cranelift] CLIF IR for {name}:\n{}", ctx.func.display());
    }

    if let Err(e) = clif_module.define_function(func_id, &mut ctx) {
        eprintln!("[cranelift] CLIF IR (error):\n{}", ctx.func.display());
        return Err(format!("cranelift define_function failed: {e}"));
    }

    Ok(())
}

fn resolve_scalar_value(
    module: &Module,
    function: &Function,
    value_id: ValueId,
    value_map: &HashMap<ValueId, clif::Value>,
    pointer_type: clif::Type,
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    let ty = function.dfg.value_ty(value_id);
    let val = resolve_value(function, value_id, value_map, builder)?;
    if ty.is_obj_ref(&module.ctx)
        && let Some(sonatina_ir::types::CompoundType::ObjRef(elem)) =
            ty.resolve_compound(&module.ctx)
        && let Some(clif_ty) = sonatina_type_to_clif(elem, pointer_type)
    {
        return Ok(builder.ins().load(clif_ty, MemFlagsData::new(), val, 0));
    }
    Ok(val)
}

fn resolve_pointer_sized_value(
    function: &Function,
    value_id: ValueId,
    value_map: &HashMap<ValueId, clif::Value>,
    pointer_type: clif::Type,
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    let val = resolve_value(function, value_id, value_map, builder)?;
    let val = if function.dfg.value_ty(value_id) == Type::I256 {
        load_i256_limb(val, 0, builder)
    } else {
        val
    };
    Ok(resize_int_value(val, pointer_type, false, builder))
}

#[allow(clippy::too_many_arguments)]
fn translate_icmp(
    cc: IntCC,
    lhs: ValueId,
    rhs: ValueId,
    inst_id: sonatina_ir::inst::InstId,
    module: &Module,
    function: &Function,
    value_map: &mut HashMap<ValueId, clif::Value>,
    pointer_type: clif::Type,
    builder: &mut FunctionBuilder,
) -> Result<(), String> {
    let lhs_ty = function.dfg.value_ty(lhs);
    let rhs_ty = function.dfg.value_ty(rhs);
    let result_val = if lhs_ty == Type::I256 || rhs_ty == Type::I256 {
        if lhs_ty != Type::I256 || rhs_ty != Type::I256 {
            return Err(format!(
                "cannot compare mismatched i256 and scalar values: {lhs_ty:?}, {rhs_ty:?}"
            ));
        }
        let lhs_val = resolve_value(function, lhs, value_map, builder)?;
        let rhs_val = resolve_value(function, rhs, value_map, builder)?;
        emit_i256_icmp(cc, lhs_val, rhs_val, builder)?
    } else {
        let mut lhs_val =
            resolve_scalar_value(module, function, lhs, value_map, pointer_type, builder)?;
        let mut rhs_val =
            resolve_scalar_value(module, function, rhs, value_map, pointer_type, builder)?;
        if matches!(
            cc,
            IntCC::SignedLessThan
                | IntCC::SignedGreaterThan
                | IntCC::SignedLessThanOrEqual
                | IntCC::SignedGreaterThanOrEqual
        ) {
            lhs_val = signed_scalar(lhs_val, lhs_ty, builder);
            rhs_val = signed_scalar(rhs_val, rhs_ty, builder);
        }
        builder.ins().icmp(cc, lhs_val, rhs_val)
    };
    if let Some(result) = function.dfg.inst_result(inst_id) {
        value_map.insert(result, result_val);
    }
    Ok(())
}

fn collect_phi_args_for_block(
    function: &Function,
    target_block: BlockId,
    source_block: BlockId,
    inst_set: &dyn sonatina_ir::InstSetBase,
    value_map: &HashMap<ValueId, clif::Value>,
    builder: &mut FunctionBuilder,
) -> Result<Vec<BlockArg>, String> {
    let mut args = Vec::new();
    for inst_id in function.layout.iter_inst(target_block) {
        let inst_data = function.dfg.inst(inst_id);
        if let Some(phi) =
            <&sonatina_ir::inst::control_flow::Phi as sonatina_ir::InstDowncast>::downcast(
                inst_set, inst_data,
            )
        {
            for &(value, from_block) in phi.args() {
                if from_block == source_block {
                    let clif_val = resolve_value(function, value, value_map, builder)?;
                    let ty = function.dfg.value_ty(value);
                    if uses_indirect_value_representation(function.ctx(), ty) {
                        for (offset, chunk_ty) in
                            storage_chunks(value_storage_size(ty, function.ctx())?)
                        {
                            let chunk =
                                builder
                                    .ins()
                                    .load(chunk_ty, MemFlagsData::new(), clif_val, offset);
                            args.push(BlockArg::Value(chunk));
                        }
                    } else {
                        args.push(BlockArg::Value(clif_val));
                    }
                    break;
                }
            }
        } else {
            break;
        }
    }
    Ok(args)
}
