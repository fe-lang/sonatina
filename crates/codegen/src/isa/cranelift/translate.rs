use std::{cmp::Ordering, collections::HashMap};

use cranelift_codegen::ir::{
    self as clif, InstBuilder, MemFlags, StackSlotData, StackSlotKind, condcodes::IntCC,
    instructions::BlockArg,
};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{FuncId, Linkage, Module as ClifModule};

use sonatina_ir::{
    BlockId, Function, Immediate, Linkage as SonatinaLinkage, Module, Signature, Type, Value,
    ValueId,
    module::{FuncRef, ModuleCtx},
};

pub(super) fn translate_module(
    module: &Module,
    clif_module: &mut impl ClifModule,
    fail_on_unsupported: bool,
) -> Result<HashMap<String, FuncId>, String> {
    let mut func_map: HashMap<String, FuncId> = HashMap::new();
    let mut func_id_map: HashMap<FuncRef, FuncId> = HashMap::new();

    let funcs = module.funcs();

    for &func_ref in &funcs {
        let (name, sig) = module.ctx.func_sig(func_ref, |sig| {
            let name = sig.name().to_string();
            let clif_sig = sonatina_sig_to_clif(sig, clif_module);
            (name, clif_sig)
        });

        let linkage = match module.ctx.func_linkage(func_ref) {
            SonatinaLinkage::Public => Linkage::Export,
            SonatinaLinkage::Private => Linkage::Local,
            SonatinaLinkage::External => Linkage::Import,
        };
        let func_id = clif_module
            .declare_function(&name, linkage, &sig)
            .map_err(|e| format!("failed to declare function {name}: {e}"))?;

        func_map.insert(name, func_id);
        func_id_map.insert(func_ref, func_id);
    }

    for &func_ref in &funcs {
        let name = module.ctx.func_sig(func_ref, |sig| sig.name().to_string());
        // Skip intrinsic functions (intercepted at call sites as runtime calls)
        if name.contains("addmod") || name.contains("mulmod") {
            continue;
        }

        let translated = module.func_store.try_view(func_ref, |function| {
            if module.ctx.func_linkage(func_ref).is_external() {
                return Ok(());
            }
            if function.layout.entry_block().is_none() {
                return Ok(());
            }
            let func_id = func_id_map[&func_ref];
            translate_function(
                module,
                function,
                func_ref,
                func_id,
                &func_id_map,
                clif_module,
            )
        });
        if let Some(Err(e)) = translated {
            if fail_on_unsupported {
                return Err(format!("failed to translate function {name}: {e}"));
            } else {
                // Skip functions with unsupported instructions rather than
                // failing the whole module. They'll error at call time if needed.
                eprintln!("[cranelift] skipping function {name}: {e}");
            }
        }
    }

    Ok(func_map)
}

fn returns_struct(sig: &Signature) -> bool {
    sig.ret_tys()
        .iter()
        .any(|ty| matches!(ty, Type::Compound(_)))
}

fn sonatina_sig_to_clif(sig: &Signature, clif_module: &impl ClifModule) -> clif::Signature {
    let mut clif_sig = clif_module.make_signature();

    // If returning a struct, add hidden sret pointer as first param
    if returns_struct(sig) {
        clif_sig.params.push(clif::AbiParam::new(clif::types::I64));
    }

    for &arg_ty in sig.args() {
        if let Some(clif_ty) = sonatina_type_to_clif(arg_ty) {
            clif_sig.params.push(clif::AbiParam::new(clif_ty));
        }
    }

    if returns_struct(sig) {
        // Struct return via sret pointer — no return values in signature
    } else {
        for &ret_ty in sig.ret_tys() {
            if let Some(clif_ty) = sonatina_type_to_clif(ret_ty) {
                clif_sig.returns.push(clif::AbiParam::new(clif_ty));
            }
        }
    }
    clif_sig
}

fn sonatina_type_to_clif(ty: Type) -> Option<clif::Type> {
    match ty {
        Type::Unit => None,
        Type::I1 => Some(clif::types::I8),
        Type::I8 => Some(clif::types::I8),
        Type::I16 => Some(clif::types::I16),
        Type::I32 => Some(clif::types::I32),
        Type::I64 => Some(clif::types::I64),
        Type::I128 => Some(clif::types::I128),
        // I256: represent as pointer to 32 bytes on stack
        Type::I256 => Some(clif::types::I64),
        // Compound types (objref, constref, ptr) → native pointer
        Type::Compound(_) => Some(clif::types::I64),
        _ => None,
    }
}

fn sonatina_type_to_clif_or_err(ty: Type) -> Result<clif::Type, String> {
    sonatina_type_to_clif(ty).ok_or_else(|| format!("unsupported type for cranelift: {ty:?}"))
}

fn translate_function(
    module: &Module,
    function: &Function,
    func_ref: FuncRef,
    func_id: FuncId,
    func_id_map: &HashMap<FuncRef, FuncId>,
    clif_module: &mut impl ClifModule,
) -> Result<(), String> {
    let mut ctx = clif_module.make_context();
    let sig = module
        .ctx
        .func_sig(func_ref, |sig| sonatina_sig_to_clif(sig, clif_module));
    ctx.func.signature = sig;

    let mut builder_ctx = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_ctx);

    let mut block_map: HashMap<BlockId, clif::Block> = HashMap::new();
    let mut value_map: HashMap<ValueId, clif::Value> = HashMap::new();
    for block in function.layout.iter_block() {
        let clif_block = builder.create_block();
        block_map.insert(block, clif_block);
    }

    let has_sret = module.ctx.func_sig(func_ref, returns_struct);

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
        value_map.insert(arg_value, param);
    }

    let inst_set = function.inst_set();

    // No blanket ISA rejection — the translator handles each instruction
    // individually, emitting intrinsic calls for EVM-specific operations
    // (addmod, mulmod) and errors for truly unsupported ones.

    for block in function.layout.iter_block() {
        let clif_block = block_map[&block];
        if block != entry {
            builder.switch_to_block(clif_block);

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
                    let clif_ty = sonatina_type_to_clif_or_err(ty)?;
                    let param = builder.append_block_param(clif_block, clif_ty);
                    value_map.insert(result, param);
                } else {
                    break;
                }
            }
        }

        for inst_id in function.layout.iter_inst(block) {
            let inst_data = function.dfg.inst(inst_id);

            if <&sonatina_ir::inst::control_flow::Phi as sonatina_ir::InstDowncast>::downcast(
                inst_set, inst_data,
            )
            .is_some()
            {
                continue;
            }

            if let Some(add) = <&sonatina_ir::inst::arith::Add as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
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
            } else if let Some(sub) = <&sonatina_ir::inst::arith::Sub as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
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
            } else if let Some(mul) = <&sonatina_ir::inst::arith::Mul as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                if function.dfg.value_ty(*mul.lhs()) == Type::I256 {
                    return Err("i256 multiplication is not supported by CraneliftBackend object lowering yet".to_string());
                }
                let lhs = resolve_value(function, *mul.lhs(), &value_map, &mut builder)?;
                let rhs = resolve_value(function, *mul.rhs(), &value_map, &mut builder)?;
                let result_val = builder.ins().imul(lhs, rhs);
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    value_map.insert(result, result_val);
                }
            } else if let Some(neg) = <&sonatina_ir::inst::arith::Neg as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let val = resolve_value(function, *neg.arg(), &value_map, &mut builder)?;
                let result_val = builder.ins().ineg(val);
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    value_map.insert(result, result_val);
                }
            } else if let Some(div) = <&sonatina_ir::inst::arith::Udiv as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let lhs = resolve_value(function, *div.lhs(), &value_map, &mut builder)?;
                let rhs = resolve_value(function, *div.rhs(), &value_map, &mut builder)?;
                let result_val = builder.ins().udiv(lhs, rhs);
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    value_map.insert(result, result_val);
                }
            } else if let Some(div) = <&sonatina_ir::inst::arith::Sdiv as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let lhs = resolve_value(function, *div.lhs(), &value_map, &mut builder)?;
                let rhs = resolve_value(function, *div.rhs(), &value_map, &mut builder)?;
                let result_val = builder.ins().sdiv(lhs, rhs);
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    value_map.insert(result, result_val);
                }
            } else if let Some(rem) = <&sonatina_ir::inst::arith::Umod as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let lhs = resolve_value(function, *rem.lhs(), &value_map, &mut builder)?;
                let rhs = resolve_value(function, *rem.rhs(), &value_map, &mut builder)?;
                let result_val = builder.ins().urem(lhs, rhs);
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    value_map.insert(result, result_val);
                }
            } else if let Some(rem) = <&sonatina_ir::inst::arith::Smod as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let lhs = resolve_value(function, *rem.lhs(), &value_map, &mut builder)?;
                let rhs = resolve_value(function, *rem.rhs(), &value_map, &mut builder)?;
                let result_val = builder.ins().srem(lhs, rhs);
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    value_map.insert(result, result_val);
                }
            } else if let Some(shl) = <&sonatina_ir::inst::arith::Shl as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let val = resolve_value(function, *shl.value(), &value_map, &mut builder)?;
                let bits = resolve_value(function, *shl.bits(), &value_map, &mut builder)?;
                let result_val = builder.ins().ishl(val, bits);
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    value_map.insert(result, result_val);
                }
            } else if let Some(shr) = <&sonatina_ir::inst::arith::Shr as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let val = resolve_value(function, *shr.value(), &value_map, &mut builder)?;
                let bits = resolve_value(function, *shr.bits(), &value_map, &mut builder)?;
                let result_val = builder.ins().ushr(val, bits);
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    value_map.insert(result, result_val);
                }
            } else if let Some(sar) = <&sonatina_ir::inst::arith::Sar as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let val = resolve_value(function, *sar.value(), &value_map, &mut builder)?;
                let bits = resolve_value(function, *sar.bits(), &value_map, &mut builder)?;
                let result_val = builder.ins().sshr(val, bits);
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    value_map.insert(result, result_val);
                }
            } else if let Some(and) = <&sonatina_ir::inst::logic::And as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let lhs = resolve_value(function, *and.lhs(), &value_map, &mut builder)?;
                let rhs = resolve_value(function, *and.rhs(), &value_map, &mut builder)?;
                let result_val = builder.ins().band(lhs, rhs);
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    value_map.insert(result, result_val);
                }
            } else if let Some(or) = <&sonatina_ir::inst::logic::Or as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let lhs = resolve_value(function, *or.lhs(), &value_map, &mut builder)?;
                let rhs = resolve_value(function, *or.rhs(), &value_map, &mut builder)?;
                let result_val = builder.ins().bor(lhs, rhs);
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    value_map.insert(result, result_val);
                }
            } else if let Some(xor) = <&sonatina_ir::inst::logic::Xor as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let lhs = resolve_value(function, *xor.lhs(), &value_map, &mut builder)?;
                let rhs = resolve_value(function, *xor.rhs(), &value_map, &mut builder)?;
                let result_val = builder.ins().bxor(lhs, rhs);
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    value_map.insert(result, result_val);
                }
            } else if let Some(not) = <&sonatina_ir::inst::logic::Not as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let val = resolve_value(function, *not.arg(), &value_map, &mut builder)?;
                let result_val = builder.ins().bnot(val);
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    value_map.insert(result, result_val);
                }
            } else if let Some(lt) = <&sonatina_ir::inst::cmp::Lt as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                translate_icmp(IntCC::UnsignedLessThan, *lt.lhs(), *lt.rhs(), inst_id, module, function, &mut value_map, &mut builder)?;
            } else if let Some(gt) = <&sonatina_ir::inst::cmp::Gt as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                translate_icmp(IntCC::UnsignedGreaterThan, *gt.lhs(), *gt.rhs(), inst_id, module, function, &mut value_map, &mut builder)?;
            } else if let Some(le) = <&sonatina_ir::inst::cmp::Le as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                translate_icmp(IntCC::UnsignedLessThanOrEqual, *le.lhs(), *le.rhs(), inst_id, module, function, &mut value_map, &mut builder)?;
            } else if let Some(ge) = <&sonatina_ir::inst::cmp::Ge as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                translate_icmp(IntCC::UnsignedGreaterThanOrEqual, *ge.lhs(), *ge.rhs(), inst_id, module, function, &mut value_map, &mut builder)?;
            } else if let Some(slt) = <&sonatina_ir::inst::cmp::Slt as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                translate_icmp(IntCC::SignedLessThan, *slt.lhs(), *slt.rhs(), inst_id, module, function, &mut value_map, &mut builder)?;
            } else if let Some(sgt) = <&sonatina_ir::inst::cmp::Sgt as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                translate_icmp(IntCC::SignedGreaterThan, *sgt.lhs(), *sgt.rhs(), inst_id, module, function, &mut value_map, &mut builder)?;
            } else if let Some(eq) = <&sonatina_ir::inst::cmp::Eq as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                translate_icmp(IntCC::Equal, *eq.lhs(), *eq.rhs(), inst_id, module, function, &mut value_map, &mut builder)?;
            } else if let Some(ne) = <&sonatina_ir::inst::cmp::Ne as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                translate_icmp(IntCC::NotEqual, *ne.lhs(), *ne.rhs(), inst_id, module, function, &mut value_map, &mut builder)?;
            } else if let Some(is_zero) = <&sonatina_ir::inst::cmp::IsZero as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let val_ty = function.dfg.value_ty(*is_zero.lhs());
                let result_val = if val_ty == Type::I256 {
                    let val = resolve_value(function, *is_zero.lhs(), &value_map, &mut builder)?;
                    emit_i256_is_zero(val, &mut builder)
                } else {
                    let val = resolve_value(function, *is_zero.lhs(), &value_map, &mut builder)?;
                    let clif_ty = sonatina_type_to_clif(val_ty).unwrap_or(clif::types::I64);
                    let zero = builder.ins().iconst(clif_ty, 0);
                    builder.ins().icmp(IntCC::Equal, val, zero)
                };
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    value_map.insert(result, result_val);
                }
            } else if let Some(sle) = <&sonatina_ir::inst::cmp::Sle as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                translate_icmp(IntCC::SignedLessThanOrEqual, *sle.lhs(), *sle.rhs(), inst_id, module, function, &mut value_map, &mut builder)?;
            } else if let Some(sge) = <&sonatina_ir::inst::cmp::Sge as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                translate_icmp(IntCC::SignedGreaterThanOrEqual, *sge.lhs(), *sge.rhs(), inst_id, module, function, &mut value_map, &mut builder)?;
            } else if let Some(sext) = <&sonatina_ir::inst::cast::Sext as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let val = resolve_value(function, *sext.from(), &value_map, &mut builder)?;
                let to_ty = sonatina_type_to_clif_or_err(*sext.ty())?;
                let result_val = if *sext.ty() == Type::I256 {
                    materialize_scalar_as_i256(
                        val,
                        function.dfg.value_ty(*sext.from()),
                        true,
                        &mut builder,
                    )
                } else if function.dfg.value_ty(*sext.from()) == Type::I1 {
                    bool_to_int_value(val, to_ty, &mut builder)
                } else {
                    resize_int_value(val, to_ty, true, &mut builder)
                };
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    value_map.insert(result, result_val);
                }
            } else if let Some(zext) = <&sonatina_ir::inst::cast::Zext as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let val = resolve_value(function, *zext.from(), &value_map, &mut builder)?;
                let to_ty = sonatina_type_to_clif_or_err(*zext.ty())?;
                let result_val = if *zext.ty() == Type::I256 {
                    materialize_scalar_as_i256(
                        val,
                        function.dfg.value_ty(*zext.from()),
                        false,
                        &mut builder,
                    )
                } else if function.dfg.value_ty(*zext.from()) == Type::I1 {
                    bool_to_int_value(val, to_ty, &mut builder)
                } else {
                    resize_int_value(val, to_ty, false, &mut builder)
                };
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    value_map.insert(result, result_val);
                }
            } else if let Some(trunc) = <&sonatina_ir::inst::cast::Trunc as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let from_ty = function.dfg.value_ty(*trunc.from());
                let val = resolve_value(function, *trunc.from(), &value_map, &mut builder)?;
                let to_ty = sonatina_type_to_clif_or_err(*trunc.ty())?;
                let result_val = if from_ty == Type::I256 {
                    // i256 values are pointers — load the target-sized value from the pointer
                    builder.ins().load(to_ty, cranelift_codegen::ir::MemFlags::new(), val, 0)
                } else {
                    builder.ins().ireduce(to_ty, val)
                };
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    value_map.insert(result, result_val);
                }
            } else if let Some(bitcast) = <&sonatina_ir::inst::cast::Bitcast as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let val = resolve_value(function, *bitcast.from(), &value_map, &mut builder)?;
                let to_ty = sonatina_type_to_clif_or_err(*bitcast.ty())?;
                let result_val = translate_bitcast(val, to_ty, &mut builder)?;
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    value_map.insert(result, result_val);
                }
            } else if let Some(cast) = <&sonatina_ir::inst::cast::IntToPtr as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let val = resolve_value(function, *cast.from(), &value_map, &mut builder)?;
                let to_ty = sonatina_type_to_clif_or_err(*cast.ty())?;
                let result_val = if function.dfg.value_ty(*cast.from()) == Type::I256 {
                    let scalar = load_i256_limb(val, 0, &mut builder);
                    resize_int_value(scalar, to_ty, false, &mut builder)
                } else {
                    resize_int_value(val, to_ty, false, &mut builder)
                };
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    value_map.insert(result, result_val);
                }
            } else if let Some(cast) = <&sonatina_ir::inst::cast::PtrToInt as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let val = resolve_value(function, *cast.from(), &value_map, &mut builder)?;
                let to_ty = sonatina_type_to_clif_or_err(*cast.ty())?;
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
            } else if let Some(jump) = <&sonatina_ir::inst::control_flow::Jump as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let dest = block_map[jump.dest()];
                let phi_args = collect_phi_args_for_block(function, *jump.dest(), block, inst_set, &value_map, &mut builder)?;
                builder.ins().jump(dest, &phi_args);
            } else if let Some(br) = <&sonatina_ir::inst::control_flow::Br as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let cond = resolve_value(function, *br.cond(), &value_map, &mut builder)?;
                let nz_block = block_map[br.nz_dest()];
                let z_block = block_map[br.z_dest()];
                let nz_args = collect_phi_args_for_block(function, *br.nz_dest(), block, inst_set, &value_map, &mut builder)?;
                let z_args = collect_phi_args_for_block(function, *br.z_dest(), block, inst_set, &value_map, &mut builder)?;
                builder.ins().brif(cond, nz_block, &nz_args, z_block, &z_args);
            } else if let Some(ret) = <&sonatina_ir::inst::control_flow::Return as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                if let Some(sret) = sret_ptr {
                    for &val_id in ret.args().as_slice() {
                        let val = resolve_value(function, val_id, &value_map, &mut builder)?;
                        let val_ty = function.dfg.value_ty(val_id);
                        copy_bytes(val, sret, compute_alloc_size(val_ty, &module.ctx), &mut builder);
                    }
                    builder.ins().return_(&[]);
                } else {
                    let args: Vec<clif::Value> = ret.args().as_slice()
                        .iter()
                        .filter_map(|v| resolve_value(function, *v, &value_map, &mut builder).ok())
                        .collect();
                    builder.ins().return_(&args);
                }
            } else if let Some(call) = <&sonatina_ir::inst::control_flow::Call as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let callee = *call.callee();
                let callee_name = module.ctx.func_sig(callee, |sig| sig.name().to_string());

                // Intercept known u256 intrinsic functions (name may be mangled)
                let is_addmod = callee_name == "addmod" || callee_name.contains("addmod");
                let is_mulmod = callee_name == "mulmod" || callee_name.contains("mulmod");
                if is_addmod || is_mulmod {
                    let intrinsic_name = if is_addmod { "__u256_addmod" } else { "__u256_mulmod" };
                    let args: Result<Vec<_>, _> = call.args()
                        .iter()
                        .map(|v| resolve_value(function, *v, &value_map, &mut builder))
                        .collect();
                    // Args are already pointers to 32-byte u256 buffers
                    // (from obj.load passthrough or emit_i256_immediate stack slots)
                    let result_val = emit_u256_intrinsic_call(
                        clif_module, &mut builder, intrinsic_name, &args?, true,
                    )?;
                    let ir_results = function.dfg.inst_results(inst_id);
                    if !ir_results.is_empty() {
                        value_map.insert(ir_results[0], result_val);
                    }
                } else {
                    let clif_func_id = func_id_map.get(&callee)
                        .ok_or_else(|| format!("unknown callee {:?}", callee))?;
                    let clif_func_ref = clif_module.declare_func_in_func(*clif_func_id, builder.func);
                    let ir_results = function.dfg.inst_results(inst_id);
                    let callee_returns_struct = !ir_results.is_empty()
                        && matches!(function.dfg.value_ty(ir_results[0]), Type::Compound(_));

                    let mut call_args: Vec<clif::Value> = Vec::new();
                    let sret_slot = if callee_returns_struct {
                        let result_ty = function.dfg.value_ty(ir_results[0]);
                        let slot = builder.create_sized_stack_slot(
                            cranelift_codegen::ir::StackSlotData::new(
                                cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
                                compute_alloc_size(result_ty, &module.ctx),
                                0,
                            ),
                        );
                        let addr = builder.ins().stack_addr(clif::types::I64, slot, 0);
                        call_args.push(addr);
                        Some(addr)
                    } else {
                        None
                    };

                    let args: Result<Vec<_>, _> = call.args()
                        .iter()
                        .map(|v| resolve_value(function, *v, &value_map, &mut builder))
                        .collect();
                    call_args.extend(args?);

                    let clif_call = builder.ins().call(clif_func_ref, &call_args);

                    if let Some(sret_addr) = sret_slot {
                        // Result is in the sret buffer we allocated
                        if !ir_results.is_empty() {
                            value_map.insert(ir_results[0], sret_addr);
                        }
                    } else {
                        let results = builder.inst_results(clif_call).to_vec();
                        for (ir_result, clif_result) in ir_results.iter().zip(results.iter()) {
                            value_map.insert(*ir_result, *clif_result);
                        }
                    }
                }
            } else if let Some(uaddo) = <&sonatina_ir::inst::arith::Uaddo as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let lhs = resolve_value(function, *uaddo.lhs(), &value_map, &mut builder)?;
                let rhs = resolve_value(function, *uaddo.rhs(), &value_map, &mut builder)?;
                let (result_val, overflow) = builder.ins().uadd_overflow(lhs, rhs);
                insert_clif_results(function, inst_id, [result_val, overflow], &mut value_map);
            } else if let Some(saddo) = <&sonatina_ir::inst::arith::Saddo as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let lhs = resolve_value(function, *saddo.lhs(), &value_map, &mut builder)?;
                let rhs = resolve_value(function, *saddo.rhs(), &value_map, &mut builder)?;
                let (result_val, overflow) = builder.ins().sadd_overflow(lhs, rhs);
                insert_clif_results(function, inst_id, [result_val, overflow], &mut value_map);
            } else if let Some(usubo) = <&sonatina_ir::inst::arith::Usubo as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let lhs = resolve_value(function, *usubo.lhs(), &value_map, &mut builder)?;
                let rhs = resolve_value(function, *usubo.rhs(), &value_map, &mut builder)?;
                let (result_val, overflow) = builder.ins().usub_overflow(lhs, rhs);
                insert_clif_results(function, inst_id, [result_val, overflow], &mut value_map);
            } else if let Some(ssubo) = <&sonatina_ir::inst::arith::Ssubo as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let lhs = resolve_value(function, *ssubo.lhs(), &value_map, &mut builder)?;
                let rhs = resolve_value(function, *ssubo.rhs(), &value_map, &mut builder)?;
                let (result_val, overflow) = builder.ins().ssub_overflow(lhs, rhs);
                insert_clif_results(function, inst_id, [result_val, overflow], &mut value_map);
            } else if let Some(umulo) = <&sonatina_ir::inst::arith::Umulo as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let lhs = resolve_value(function, *umulo.lhs(), &value_map, &mut builder)?;
                let rhs = resolve_value(function, *umulo.rhs(), &value_map, &mut builder)?;
                let (result_val, overflow) = builder.ins().umul_overflow(lhs, rhs);
                insert_clif_results(function, inst_id, [result_val, overflow], &mut value_map);
            } else if let Some(smulo) = <&sonatina_ir::inst::arith::Smulo as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let lhs = resolve_value(function, *smulo.lhs(), &value_map, &mut builder)?;
                let rhs = resolve_value(function, *smulo.rhs(), &value_map, &mut builder)?;
                let (result_val, overflow) = builder.ins().smul_overflow(lhs, rhs);
                insert_clif_results(function, inst_id, [result_val, overflow], &mut value_map);
            } else if let Some(snego) = <&sonatina_ir::inst::arith::Snego as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let val = resolve_value(function, *snego.arg(), &value_map, &mut builder)?;
                let result_val = builder.ins().ineg(val);
                let ty = builder.func.dfg.value_type(val);
                let min = signed_min_value(ty, &mut builder)?;
                let overflow = builder.ins().icmp(IntCC::Equal, val, min);
                insert_clif_results(function, inst_id, [result_val, overflow], &mut value_map);
            } else if let Some(uaddsat) = <&sonatina_ir::inst::arith::Uaddsat as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let lhs = resolve_value(function, *uaddsat.lhs(), &value_map, &mut builder)?;
                let rhs = resolve_value(function, *uaddsat.rhs(), &value_map, &mut builder)?;
                let (raw, overflow) = builder.ins().uadd_overflow(lhs, rhs);
                let max = unsigned_max_value(builder.func.dfg.value_type(lhs), &mut builder);
                let result_val = builder.ins().select(overflow, max, raw);
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    value_map.insert(result, result_val);
                }
            } else if let Some(saddsat) = <&sonatina_ir::inst::arith::Saddsat as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let lhs = resolve_value(function, *saddsat.lhs(), &value_map, &mut builder)?;
                let rhs = resolve_value(function, *saddsat.rhs(), &value_map, &mut builder)?;
                let (raw, overflow) = builder.ins().sadd_overflow(lhs, rhs);
                let ty = builder.func.dfg.value_type(lhs);
                let zero = builder.ins().iconst(ty, 0);
                let lhs_neg = builder.ins().icmp(IntCC::SignedLessThan, lhs, zero);
                let min = signed_min_value(ty, &mut builder)?;
                let max = signed_max_value(ty, &mut builder)?;
                let sat = builder.ins().select(lhs_neg, min, max);
                let result_val = builder.ins().select(overflow, sat, raw);
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    value_map.insert(result, result_val);
                }
            } else if let Some(usubsat) = <&sonatina_ir::inst::arith::Usubsat as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let lhs = resolve_value(function, *usubsat.lhs(), &value_map, &mut builder)?;
                let rhs = resolve_value(function, *usubsat.rhs(), &value_map, &mut builder)?;
                let (raw, overflow) = builder.ins().usub_overflow(lhs, rhs);
                let ty = builder.func.dfg.value_type(lhs);
                let zero = builder.ins().iconst(ty, 0);
                let result_val = builder.ins().select(overflow, zero, raw);
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    value_map.insert(result, result_val);
                }
            } else if let Some(ssubsat) = <&sonatina_ir::inst::arith::Ssubsat as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let lhs = resolve_value(function, *ssubsat.lhs(), &value_map, &mut builder)?;
                let rhs = resolve_value(function, *ssubsat.rhs(), &value_map, &mut builder)?;
                let (raw, overflow) = builder.ins().ssub_overflow(lhs, rhs);
                let ty = builder.func.dfg.value_type(lhs);
                let zero = builder.ins().iconst(ty, 0);
                let lhs_neg = builder.ins().icmp(IntCC::SignedLessThan, lhs, zero);
                let min = signed_min_value(ty, &mut builder)?;
                let max = signed_max_value(ty, &mut builder)?;
                let sat = builder.ins().select(lhs_neg, min, max);
                let result_val = builder.ins().select(overflow, sat, raw);
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    value_map.insert(result, result_val);
                }
            } else if let Some(umulsat) = <&sonatina_ir::inst::arith::Umulsat as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let lhs = resolve_value(function, *umulsat.lhs(), &value_map, &mut builder)?;
                let rhs = resolve_value(function, *umulsat.rhs(), &value_map, &mut builder)?;
                let (raw, overflow) = builder.ins().umul_overflow(lhs, rhs);
                let max = unsigned_max_value(builder.func.dfg.value_type(lhs), &mut builder);
                let result_val = builder.ins().select(overflow, max, raw);
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    value_map.insert(result, result_val);
                }
            } else if let Some(smulsat) = <&sonatina_ir::inst::arith::Smulsat as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let lhs = resolve_value(function, *smulsat.lhs(), &value_map, &mut builder)?;
                let rhs = resolve_value(function, *smulsat.rhs(), &value_map, &mut builder)?;
                let (raw, overflow) = builder.ins().smul_overflow(lhs, rhs);
                let ty = builder.func.dfg.value_type(lhs);
                let zero = builder.ins().iconst(ty, 0);
                let lhs_neg = builder.ins().icmp(IntCC::SignedLessThan, lhs, zero);
                let rhs_neg = builder.ins().icmp(IntCC::SignedLessThan, rhs, zero);
                let same_sign = builder.ins().icmp(IntCC::Equal, lhs_neg, rhs_neg);
                let min = signed_min_value(ty, &mut builder)?;
                let max = signed_max_value(ty, &mut builder)?;
                let sat = builder.ins().select(same_sign, max, min);
                let result_val = builder.ins().select(overflow, sat, raw);
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    value_map.insert(result, result_val);
                }
            } else if let Some(obj_load) = <&sonatina_ir::inst::data::ObjLoad as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let addr = resolve_value(function, *obj_load.object(), &value_map, &mut builder)?;
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    let result_ty = function.dfg.value_ty(result);
                    if result_ty == Type::I256 || matches!(result_ty, Type::Compound(_)) {
                        // For i256/struct: passthrough the pointer
                        value_map.insert(result, addr);
                    } else {
                        let clif_ty = sonatina_type_to_clif_or_err(result_ty)?;
                        let loaded = builder.ins().load(clif_ty, cranelift_codegen::ir::MemFlags::new(), addr, 0);
                        value_map.insert(result, loaded);
                    }
                }
            } else if let Some(extract) = <&sonatina_ir::inst::data::ExtractValue as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
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
                    if result_ty == Type::I256 || matches!(result_ty, Type::Compound(_)) {
                        let addr = builder.ins().iadd_imm(base, offset as i64);
                        value_map.insert(result, addr);
                    } else {
                        let clif_ty = sonatina_type_to_clif_or_err(result_ty)?;
                        let loaded = builder.ins().load(clif_ty, cranelift_codegen::ir::MemFlags::new(), base, offset);
                        value_map.insert(result, loaded);
                    }
                }
            } else if let Some(insert) = <&sonatina_ir::inst::data::InsertValue as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let Some(result) = function.dfg.inst_result(inst_id) else {
                    continue;
                };
                let result_ty = function.dfg.value_ty(result);
                let result_addr = create_stack_slot_for_type(result_ty, &module.ctx, &mut builder);
                if !is_undef_value(function, *insert.dest()) {
                    let source = resolve_value(function, *insert.dest(), &value_map, &mut builder)?;
                    copy_bytes(source, result_addr, compute_alloc_size(result_ty, &module.ctx), &mut builder);
                }

                let idx = constant_value_index(function, *insert.idx(), "insert_value")?;
                let (offset, elem_ty) = aggregate_elem_offset(&module.ctx, result_ty, idx)?;
                let value_ty = function.dfg.value_ty(*insert.value());
                if value_ty != elem_ty {
                    return Err(format!(
                        "insert_value element type mismatch: expected {elem_ty:?}, got {value_ty:?}"
                    ));
                }

                let value = resolve_value(function, *insert.value(), &value_map, &mut builder)?;
                if value_ty == Type::I256 || matches!(value_ty, Type::Compound(_)) {
                    let field_addr = builder.ins().iadd_imm(result_addr, i64::from(offset));
                    copy_bytes(value, field_addr, compute_alloc_size(value_ty, &module.ctx), &mut builder);
                } else {
                    builder.ins().store(MemFlags::new(), value, result_addr, offset);
                }
                value_map.insert(result, result_addr);
            } else if <&sonatina_ir::inst::data::Alloca as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data).is_some() {
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    let slot = builder.create_sized_stack_slot(
                        cranelift_codegen::ir::StackSlotData::new(
                            cranelift_codegen::ir::StackSlotKind::ExplicitSlot, 32, 0,
                        ),
                    );
                    let addr = builder.ins().stack_addr(clif::types::I64, slot, 0);
                    value_map.insert(result, addr);
                }
            } else if let Some(mstore) = <&sonatina_ir::inst::data::Mstore as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let addr = resolve_address_value(module, function, *mstore.addr(), &value_map, &mut builder)?;
                let val = resolve_value(function, *mstore.value(), &value_map, &mut builder)?;
                let store_ty = function.dfg.value_ty(*mstore.value());
                if store_ty == Type::I256 {
                    copy_i256(val, addr, &mut builder);
                } else {
                    builder.ins().store(MemFlags::new(), val, addr, 0);
                }
            } else if let Some(mload) = <&sonatina_ir::inst::data::Mload as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let addr = resolve_address_value(module, function, *mload.addr(), &value_map, &mut builder)?;
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    let result_ty = function.dfg.value_ty(result);
                    if result_ty == Type::I256 {
                        let result_addr = create_i256_slot(&mut builder);
                        copy_i256(addr, result_addr, &mut builder);
                        value_map.insert(result, result_addr);
                    } else {
                        let clif_ty = sonatina_type_to_clif_or_err(result_ty)?;
                        let loaded = builder.ins().load(clif_ty, MemFlags::new(), addr, 0);
                        value_map.insert(result, loaded);
                    }
                }
            } else if let Some(addmod) = <&sonatina_ir::inst::evm::EvmAddMod as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let a = resolve_value(function, *addmod.lhs(), &value_map, &mut builder)?;
                let b = resolve_value(function, *addmod.rhs(), &value_map, &mut builder)?;
                let m = resolve_value(function, *addmod.modulus(), &value_map, &mut builder)?;
                let result_val = emit_u256_intrinsic_call(
                    clif_module, &mut builder, "__u256_addmod",
                    &[a, b, m], true,
                )?;
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    value_map.insert(result, result_val);
                }
            } else if let Some(mulmod) = <&sonatina_ir::inst::evm::EvmMulMod as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let a = resolve_value(function, *mulmod.lhs(), &value_map, &mut builder)?;
                let b = resolve_value(function, *mulmod.rhs(), &value_map, &mut builder)?;
                let m = resolve_value(function, *mulmod.modulus(), &value_map, &mut builder)?;
                let result_val = emit_u256_intrinsic_call(
                    clif_module, &mut builder, "__u256_mulmod",
                    &[a, b, m], true,
                )?;
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    value_map.insert(result, result_val);
                }
            } else if let Some(obj_store) = <&sonatina_ir::inst::data::ObjStore as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let dest = resolve_value(function, *obj_store.object(), &value_map, &mut builder)?;
                let val = resolve_value(function, *obj_store.value(), &value_map, &mut builder)?;
                let val_ty = function.dfg.value_ty(*obj_store.value());
                if val_ty == Type::I256 {
                    copy_i256(val, dest, &mut builder);
                } else {
                    builder.ins().store(MemFlags::new(), val, dest, 0);
                }
            } else if <&sonatina_ir::inst::data::ObjAlloc as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data).is_some() {
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    let result_ty = function.dfg.value_ty(result);
                    let alloc_size = compute_alloc_size(result_ty, &module.ctx);
                    let slot = builder.create_sized_stack_slot(cranelift_codegen::ir::StackSlotData::new(
                        cranelift_codegen::ir::StackSlotKind::ExplicitSlot, alloc_size, 0,
                    ));
                    let addr = builder.ins().stack_addr(clif::types::I64, slot, 0);
                    value_map.insert(result, addr);
                }
            } else if let Some(obj_proj) = <&sonatina_ir::inst::data::ObjProj as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let vals = obj_proj.values();
                let base = resolve_value(function, vals[0], &value_map, &mut builder)?;
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    let mut offset = 0i64;
                    let mut current_ty = function.dfg.value_ty(vals[0]);
                    for idx_value in vals.iter().skip(1) {
                        let idx = constant_value_index(function, *idx_value, "obj.proj")?;
                        let (field_offset, elem_ty) =
                            aggregate_elem_offset(&module.ctx, current_ty, idx)?;
                        offset += i64::from(field_offset);
                        current_ty = elem_ty;
                    }
                    let addr = if offset == 0 {
                        base
                    } else {
                        builder.ins().iadd_imm(base, offset)
                    };
                    value_map.insert(result, addr);
                }
            } else if let Some(obj_index) = <&sonatina_ir::inst::data::ObjIndex as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let base = resolve_value(function, *obj_index.object(), &value_map, &mut builder)?;
                let index_val_id = *obj_index.index();
                let index_ty = function.dfg.value_ty(index_val_id);
                let index = if index_ty == Type::I256 {
                    if let Some(imm) = function.dfg.value_imm(index_val_id) {
                        let idx_i64 = match imm {
                            Immediate::I256(v) => {
                                let u = v.to_u256();
                                u.low_u64() as i64
                            }
                            _ => 0,
                        };
                        builder.ins().iconst(clif::types::I64, idx_i64)
                    } else {
                        let raw = resolve_value(function, index_val_id, &value_map, &mut builder)?;
                        builder.ins().load(clif::types::I64, cranelift_codegen::ir::MemFlags::new(), raw, 0)
                    }
                } else {
                    resolve_scalar_value(module, function, index_val_id, &value_map, &mut builder)?
                };
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    let obj_ty = function.dfg.value_ty(*obj_index.object());
                    let elem_size = compute_element_size(obj_ty, &module.ctx);
                    let stride = builder.ins().iconst(clif::types::I64, elem_size as i64);
                    let offset = builder.ins().imul(index, stride);
                    let addr = builder.ins().iadd(base, offset);
                    value_map.insert(result, addr);
                }
            } else if let Some(evm_umod) = <&sonatina_ir::inst::evm::EvmUmod as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let lhs = resolve_value(function, *evm_umod.lhs(), &value_map, &mut builder)?;
                let rhs = resolve_value(function, *evm_umod.rhs(), &value_map, &mut builder)?;
                let result_val = builder.ins().urem(lhs, rhs);
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    value_map.insert(result, result_val);
                }
            } else if <&sonatina_ir::inst::evm::EvmRevert as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data).is_some() {
                builder.ins().trap(cranelift_codegen::ir::TrapCode::user(2).unwrap());
            } else if <&sonatina_ir::inst::evm::EvmStop as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data).is_some() {
                builder.ins().return_(&[]);
            } else if let Some(const_ref) = <&sonatina_ir::inst::data::ConstRef as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    let gv_ref = const_ref.global().gv();
                    let result_ty = function.dfg.value_ty(result);
                    let data_size = compute_alloc_size(result_ty, &module.ctx);
                    let slot = builder.create_sized_stack_slot(
                        cranelift_codegen::ir::StackSlotData::new(
                            cranelift_codegen::ir::StackSlotKind::ExplicitSlot, data_size, 0,
                        ),
                    );
                    let addr = builder.ins().stack_addr(clif::types::I64, slot, 0);
                    let init_data = module.ctx.with_gv_store(|store| store.init_data(gv_ref).cloned());
                    if let Some(init) = init_data {
                        let gv_ty = module.ctx.with_gv_store(|store| store.ty(gv_ref));
                        materialize_gv_initializer(&init, gv_ty, addr, 0, &module.ctx, &mut builder);
                    }
                    value_map.insert(result, addr);
                }
            } else if let Some(const_index) = <&sonatina_ir::inst::data::ConstIndex as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let base = resolve_value(function, *const_index.object(), &value_map, &mut builder)?;
                let index_val_id = *const_index.index();
                let index_ty = function.dfg.value_ty(index_val_id);
                let index = if index_ty == Type::I256 {
                    if let Some(imm) = function.dfg.value_imm(index_val_id) {
                        let idx = match imm {
                            Immediate::I256(v) => v.to_u256().low_u64() as i64,
                            _ => 0,
                        };
                        builder.ins().iconst(clif::types::I64, idx)
                    } else {
                        let raw = resolve_value(function, index_val_id, &value_map, &mut builder)?;
                        builder.ins().load(clif::types::I64, cranelift_codegen::ir::MemFlags::new(), raw, 0)
                    }
                } else {
                    resolve_scalar_value(module, function, index_val_id, &value_map, &mut builder)?
                };
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    let obj_ty = function.dfg.value_ty(*const_index.object());
                    let elem_size = compute_element_size(obj_ty, &module.ctx);
                    let stride = builder.ins().iconst(clif::types::I64, elem_size as i64);
                    let offset = builder.ins().imul(index, stride);
                    let ptr = builder.ins().iadd(base, offset);
                    value_map.insert(result, ptr);
                }
            } else if let Some(const_load) = <&sonatina_ir::inst::data::ConstLoad as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let addr = resolve_value(function, *const_load.object(), &value_map, &mut builder)?;
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    let result_ty = function.dfg.value_ty(result);
                    if result_ty == Type::I256 || matches!(result_ty, Type::Compound(_)) {
                        value_map.insert(result, addr);
                    } else {
                        let clif_ty = sonatina_type_to_clif_or_err(result_ty)?;
                        let loaded = builder.ins().load(clif_ty, cranelift_codegen::ir::MemFlags::new(), addr, 0);
                        value_map.insert(result, loaded);
                    }
                }
            } else if <&sonatina_ir::inst::control_flow::Unreachable as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data).is_some() {
                builder.ins().trap(cranelift_codegen::ir::TrapCode::user(1).unwrap());
            } else {
                return Err(format!(
                    "unsupported instruction for CraneliftBackend: {:?}",
                    inst_data.kind()
                ));
            }
        }
    }

    builder.seal_all_blocks();
    builder.finalize();

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
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    let ty = function.dfg.value_ty(value_id);
    let val = resolve_value(function, value_id, value_map, builder)?;
    if ty.is_obj_ref(&module.ctx)
        && let Some(sonatina_ir::types::CompoundType::ObjRef(elem)) =
            ty.resolve_compound(&module.ctx)
        && let Some(clif_ty) = sonatina_type_to_clif(elem)
    {
        return Ok(builder.ins().load(clif_ty, MemFlags::new(), val, 0));
    }
    Ok(val)
}

fn resolve_address_value(
    module: &Module,
    function: &Function,
    value_id: ValueId,
    value_map: &HashMap<ValueId, clif::Value>,
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    let val = resolve_scalar_value(module, function, value_id, value_map, builder)?;
    if function.dfg.value_ty(value_id) == Type::I256 {
        Ok(load_i256_limb(val, 0, builder))
    } else {
        Ok(val)
    }
}

fn create_i256_slot(builder: &mut FunctionBuilder) -> clif::Value {
    let slot =
        builder.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, 32, 0));
    builder.ins().stack_addr(clif::types::I64, slot, 0)
}

fn create_stack_slot_for_type(
    ty: Type,
    ctx: &ModuleCtx,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    let slot = builder.create_sized_stack_slot(StackSlotData::new(
        StackSlotKind::ExplicitSlot,
        compute_alloc_size(ty, ctx),
        0,
    ));
    builder.ins().stack_addr(clif::types::I64, slot, 0)
}

fn load_i256_limb(addr: clif::Value, limb: usize, builder: &mut FunctionBuilder) -> clif::Value {
    builder
        .ins()
        .load(clif::types::I64, MemFlags::new(), addr, (limb * 8) as i32)
}

fn store_i256_limb(
    addr: clif::Value,
    limb: usize,
    value: clif::Value,
    builder: &mut FunctionBuilder,
) {
    builder
        .ins()
        .store(MemFlags::new(), value, addr, (limb * 8) as i32);
}

fn copy_i256(src: clif::Value, dst: clif::Value, builder: &mut FunctionBuilder) {
    for limb in 0..4 {
        let value = load_i256_limb(src, limb, builder);
        store_i256_limb(dst, limb, value, builder);
    }
}

fn copy_bytes(src: clif::Value, dst: clif::Value, size: u32, builder: &mut FunctionBuilder) {
    let mut offset = 0;
    for (chunk, ty) in [
        (8, clif::types::I64),
        (4, clif::types::I32),
        (2, clif::types::I16),
        (1, clif::types::I8),
    ] {
        while offset + chunk <= size {
            let value = builder.ins().load(ty, MemFlags::new(), src, offset as i32);
            builder
                .ins()
                .store(MemFlags::new(), value, dst, offset as i32);
            offset += chunk;
        }
    }
}

fn materialize_scalar_as_i256(
    value: clif::Value,
    source_ty: Type,
    signed: bool,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    let result = create_i256_slot(builder);
    let value_ty = builder.func.dfg.value_type(value);
    let low = if !value_ty.is_int() {
        bool_to_int_value(value, clif::types::I64, builder)
    } else {
        resize_int_value(value, clif::types::I64, signed, builder)
    };
    store_i256_limb(result, 0, low, builder);

    let zero = builder.ins().iconst(clif::types::I64, 0);
    let fill = if signed {
        let sign = if !value_ty.is_int() || source_ty == Type::I1 {
            bool_const(false, builder)
        } else {
            let sign_zero = builder.ins().iconst(value_ty, 0);
            builder.ins().icmp(IntCC::SignedLessThan, value, sign_zero)
        };
        let minus_one = builder.ins().iconst(clif::types::I64, -1);
        builder.ins().select(sign, minus_one, zero)
    } else {
        zero
    };

    for limb in 1..4 {
        store_i256_limb(result, limb, fill, builder);
    }
    result
}

fn emit_i256_add(
    function: &Function,
    lhs: ValueId,
    rhs: ValueId,
    value_map: &HashMap<ValueId, clif::Value>,
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    let lhs = resolve_value(function, lhs, value_map, builder)?;
    let rhs = resolve_value(function, rhs, value_map, builder)?;
    let result = create_i256_slot(builder);
    let zero = builder.ins().iconst(clif::types::I64, 0);
    let one = builder.ins().iconst(clif::types::I64, 1);
    let mut carry = zero;

    for limb in 0..4 {
        let lhs_limb = load_i256_limb(lhs, limb, builder);
        let rhs_limb = load_i256_limb(rhs, limb, builder);
        let (sum, carry_from_sum) = builder.ins().uadd_overflow(lhs_limb, rhs_limb);
        let (sum, carry_from_carry) = builder.ins().uadd_overflow(sum, carry);
        store_i256_limb(result, limb, sum, builder);
        let carry_from_sum = builder.ins().select(carry_from_sum, one, zero);
        let carry_from_carry = builder.ins().select(carry_from_carry, one, zero);
        carry = builder.ins().bor(carry_from_sum, carry_from_carry);
    }

    Ok(result)
}

fn emit_i256_sub(
    function: &Function,
    lhs: ValueId,
    rhs: ValueId,
    value_map: &HashMap<ValueId, clif::Value>,
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    let lhs = resolve_value(function, lhs, value_map, builder)?;
    let rhs = resolve_value(function, rhs, value_map, builder)?;
    let result = create_i256_slot(builder);
    let zero = builder.ins().iconst(clif::types::I64, 0);
    let one = builder.ins().iconst(clif::types::I64, 1);
    let mut borrow = zero;

    for limb in 0..4 {
        let lhs_limb = load_i256_limb(lhs, limb, builder);
        let rhs_limb = load_i256_limb(rhs, limb, builder);
        let (diff, borrow_from_diff) = builder.ins().usub_overflow(lhs_limb, rhs_limb);
        let (diff, borrow_from_borrow) = builder.ins().usub_overflow(diff, borrow);
        store_i256_limb(result, limb, diff, builder);
        let borrow_from_diff = builder.ins().select(borrow_from_diff, one, zero);
        let borrow_from_borrow = builder.ins().select(borrow_from_borrow, one, zero);
        borrow = builder.ins().bor(borrow_from_diff, borrow_from_borrow);
    }

    Ok(result)
}

fn bool_const(value: bool, builder: &mut FunctionBuilder) -> clif::Value {
    let zero = builder.ins().iconst(clif::types::I8, 0);
    let rhs = builder.ins().iconst(clif::types::I8, (!value) as i64);
    builder.ins().icmp(IntCC::Equal, zero, rhs)
}

fn bool_not(value: clif::Value, builder: &mut FunctionBuilder) -> clif::Value {
    let yes = bool_const(true, builder);
    let no = bool_const(false, builder);
    builder.ins().select(value, no, yes)
}

fn bool_and(lhs: clif::Value, rhs: clif::Value, builder: &mut FunctionBuilder) -> clif::Value {
    let no = bool_const(false, builder);
    builder.ins().select(lhs, rhs, no)
}

fn bool_or(lhs: clif::Value, rhs: clif::Value, builder: &mut FunctionBuilder) -> clif::Value {
    let yes = bool_const(true, builder);
    builder.ins().select(lhs, yes, rhs)
}

fn emit_i256_eq(lhs: clif::Value, rhs: clif::Value, builder: &mut FunctionBuilder) -> clif::Value {
    let mut result = bool_const(true, builder);
    for limb in 0..4 {
        let lhs_limb = load_i256_limb(lhs, limb, builder);
        let rhs_limb = load_i256_limb(rhs, limb, builder);
        let limbs_equal = builder.ins().icmp(IntCC::Equal, lhs_limb, rhs_limb);
        result = bool_and(result, limbs_equal, builder);
    }
    result
}

fn emit_i256_unsigned_lt(
    lhs: clif::Value,
    rhs: clif::Value,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    let mut result = bool_const(false, builder);
    let mut equal_prefix = bool_const(true, builder);
    for limb in (0..4).rev() {
        let lhs_limb = load_i256_limb(lhs, limb, builder);
        let rhs_limb = load_i256_limb(rhs, limb, builder);
        let limb_lt = builder
            .ins()
            .icmp(IntCC::UnsignedLessThan, lhs_limb, rhs_limb);
        let limb_eq = builder.ins().icmp(IntCC::Equal, lhs_limb, rhs_limb);
        result = builder.ins().select(equal_prefix, limb_lt, result);
        equal_prefix = bool_and(equal_prefix, limb_eq, builder);
    }
    result
}

fn emit_i256_signed_lt(
    lhs: clif::Value,
    rhs: clif::Value,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    let lhs_high = load_i256_limb(lhs, 3, builder);
    let rhs_high = load_i256_limb(rhs, 3, builder);
    let high_lt = builder
        .ins()
        .icmp(IntCC::SignedLessThan, lhs_high, rhs_high);
    let high_eq = builder.ins().icmp(IntCC::Equal, lhs_high, rhs_high);
    let lower_lt = emit_i256_unsigned_lt(lhs, rhs, builder);
    let equal_high_lower_lt = bool_and(high_eq, lower_lt, builder);
    bool_or(high_lt, equal_high_lower_lt, builder)
}

fn emit_i256_icmp(
    cc: IntCC,
    lhs: clif::Value,
    rhs: clif::Value,
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    let result = match cc {
        IntCC::Equal => emit_i256_eq(lhs, rhs, builder),
        IntCC::NotEqual => {
            let equal = emit_i256_eq(lhs, rhs, builder);
            bool_not(equal, builder)
        }
        IntCC::UnsignedLessThan => emit_i256_unsigned_lt(lhs, rhs, builder),
        IntCC::UnsignedGreaterThan => emit_i256_unsigned_lt(rhs, lhs, builder),
        IntCC::UnsignedLessThanOrEqual => {
            let greater = emit_i256_unsigned_lt(rhs, lhs, builder);
            bool_not(greater, builder)
        }
        IntCC::UnsignedGreaterThanOrEqual => {
            let less = emit_i256_unsigned_lt(lhs, rhs, builder);
            bool_not(less, builder)
        }
        IntCC::SignedLessThan => emit_i256_signed_lt(lhs, rhs, builder),
        IntCC::SignedGreaterThan => emit_i256_signed_lt(rhs, lhs, builder),
        IntCC::SignedLessThanOrEqual => {
            let greater = emit_i256_signed_lt(rhs, lhs, builder);
            bool_not(greater, builder)
        }
        IntCC::SignedGreaterThanOrEqual => {
            let less = emit_i256_signed_lt(lhs, rhs, builder);
            bool_not(less, builder)
        }
    };
    Ok(result)
}

fn emit_i256_is_zero(value: clif::Value, builder: &mut FunctionBuilder) -> clif::Value {
    let zero = builder.ins().iconst(clif::types::I64, 0);
    let mut result = bool_const(true, builder);
    for limb in 0..4 {
        let limb = load_i256_limb(value, limb, builder);
        let limb_is_zero = builder.ins().icmp(IntCC::Equal, limb, zero);
        result = bool_and(result, limb_is_zero, builder);
    }
    result
}

fn resize_int_value(
    value: clif::Value,
    to_ty: clif::Type,
    signed: bool,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    let from_ty = builder.func.dfg.value_type(value);
    if !from_ty.is_int() && to_ty.is_int() {
        let zero = builder.ins().iconst(to_ty, 0);
        let one = builder.ins().iconst(to_ty, 1);
        return builder.ins().select(value, one, zero);
    }
    match from_ty.bits().cmp(&to_ty.bits()) {
        Ordering::Equal => value,
        Ordering::Less if signed => builder.ins().sextend(to_ty, value),
        Ordering::Less => builder.ins().uextend(to_ty, value),
        Ordering::Greater => builder.ins().ireduce(to_ty, value),
    }
}

fn bool_to_int_value(
    value: clif::Value,
    to_ty: clif::Type,
    builder: &mut FunctionBuilder,
) -> clif::Value {
    let value_ty = builder.func.dfg.value_type(value);
    let cond = if value_ty.is_int() {
        let zero = builder.ins().iconst(value_ty, 0);
        builder.ins().icmp(IntCC::NotEqual, value, zero)
    } else {
        value
    };
    let zero = builder.ins().iconst(to_ty, 0);
    let one = builder.ins().iconst(to_ty, 1);
    builder.ins().select(cond, one, zero)
}

fn translate_bitcast(
    value: clif::Value,
    to_ty: clif::Type,
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    let from_ty = builder.func.dfg.value_type(value);
    if from_ty == to_ty {
        Ok(value)
    } else if from_ty.bits() == to_ty.bits() {
        Ok(builder
            .ins()
            .bitcast(to_ty, cranelift_codegen::ir::MemFlags::new(), value))
    } else {
        Err(format!(
            "cannot bitcast Cranelift value from {from_ty} to {to_ty}"
        ))
    }
}

fn insert_clif_results(
    function: &Function,
    inst_id: sonatina_ir::inst::InstId,
    values: impl IntoIterator<Item = clif::Value>,
    value_map: &mut HashMap<ValueId, clif::Value>,
) {
    for (ir_result, clif_result) in function.dfg.inst_results(inst_id).iter().zip(values) {
        value_map.insert(*ir_result, clif_result);
    }
}

fn unsigned_max_value(ty: clif::Type, builder: &mut FunctionBuilder) -> clif::Value {
    builder.ins().iconst(ty, -1)
}

fn signed_min_value(ty: clif::Type, builder: &mut FunctionBuilder) -> Result<clif::Value, String> {
    let bits = ty.bits();
    if bits > i64::BITS {
        return Err(format!(
            "signed minimum constant for {bits}-bit Cranelift integers is unsupported"
        ));
    }
    let value = if bits == i64::BITS {
        i64::MIN
    } else {
        1i64 << (bits - 1)
    };
    Ok(builder.ins().iconst(ty, value))
}

fn signed_max_value(ty: clif::Type, builder: &mut FunctionBuilder) -> Result<clif::Value, String> {
    let bits = ty.bits();
    if bits > i64::BITS {
        return Err(format!(
            "signed maximum constant for {bits}-bit Cranelift integers is unsupported"
        ));
    }
    let value = if bits == i64::BITS {
        i64::MAX
    } else {
        (1i64 << (bits - 1)) - 1
    };
    Ok(builder.ins().iconst(ty, value))
}

fn resolve_value(
    function: &Function,
    value_id: ValueId,
    value_map: &HashMap<ValueId, clif::Value>,
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    if let Some(&clif_val) = value_map.get(&value_id) {
        return Ok(clif_val);
    }
    // Check if there's a Variable for this (phi values in loops)
    // Variables are looked up via the FunctionBuilder's SSA system

    let value = function.dfg.value(value_id);
    match value {
        Value::Immediate { imm, ty } => {
            if matches!(imm, Immediate::I256(_) | Immediate::I128(_)) {
                match imm {
                    Immediate::I256(i256_val) => Ok(emit_i256_immediate(i256_val, builder)),
                    _ => Err(format!("unsupported large immediate: {imm:?}")),
                }
            } else {
                let clif_ty = sonatina_type_to_clif_or_err(*ty)?;
                let i64_val = imm_to_i64(imm)?;
                let val = builder.ins().iconst(clif_ty, i64_val);
                Ok(val)
            }
        }
        _ => Err(format!("unresolved value v{}", value_id.0)),
    }
}

fn imm_to_i64(imm: &Immediate) -> Result<i64, String> {
    match imm {
        Immediate::I1(b) => Ok(*b as i64),
        Immediate::I8(v) => Ok(*v as i64),
        Immediate::I16(v) => Ok(*v as i64),
        Immediate::I32(v) => Ok(*v as i64),
        Immediate::I64(v) => Ok(*v),
        _ => Err(format!("unsupported immediate type for cranelift: {imm:?}")),
    }
}

fn emit_i256_immediate(imm: &sonatina_ir::I256, builder: &mut FunctionBuilder) -> clif::Value {
    let slot = builder.create_sized_stack_slot(cranelift_codegen::ir::StackSlotData::new(
        cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
        32,
        0,
    ));
    let addr = builder.ins().stack_addr(clif::types::I64, slot, 0);

    let u256 = imm.to_u256();
    let bytes = u256.to_little_endian();
    for i in 0..4 {
        let limb = u64::from_le_bytes(bytes[i * 8..(i + 1) * 8].try_into().unwrap());
        let val = builder.ins().iconst(clif::types::I64, limb as i64);
        builder.ins().store(
            cranelift_codegen::ir::MemFlags::new(),
            val,
            addr,
            (i * 8) as i32,
        );
    }

    addr
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
        let lhs_val = resolve_scalar_value(module, function, lhs, value_map, builder)?;
        let rhs_val = resolve_scalar_value(module, function, rhs, value_map, builder)?;
        builder.ins().icmp(cc, lhs_val, rhs_val)
    };
    if let Some(result) = function.dfg.inst_result(inst_id) {
        value_map.insert(result, result_val);
    }
    Ok(())
}

fn emit_u256_intrinsic_call(
    clif_module: &mut impl ClifModule,
    builder: &mut FunctionBuilder,
    name: &str,
    args: &[clif::Value],
    has_result: bool,
) -> Result<clif::Value, String> {
    let ptr_ty = clif::types::I64;

    // Build the intrinsic signature: all args are pointers, optional result pointer
    let mut sig = clif_module.make_signature();
    for _ in args {
        sig.params.push(clif::AbiParam::new(ptr_ty));
    }
    if has_result {
        sig.params.push(clif::AbiParam::new(ptr_ty)); // result pointer
    }

    let func_id = clif_module
        .declare_function(name, Linkage::Import, &sig)
        .map_err(|e| format!("failed to declare {name}: {e}"))?;
    let func_ref = clif_module.declare_func_in_func(func_id, builder.func);

    if has_result {
        // Allocate 32-byte stack slot for the result
        let result_slot =
            builder.create_sized_stack_slot(cranelift_codegen::ir::StackSlotData::new(
                cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
                32,
                0,
            ));
        let result_addr = builder.ins().stack_addr(ptr_ty, result_slot, 0);

        let mut call_args: Vec<clif::Value> = args.to_vec();
        call_args.push(result_addr);
        builder.ins().call(func_ref, &call_args);

        Ok(result_addr)
    } else {
        builder.ins().call(func_ref, args);
        Ok(builder.ins().iconst(ptr_ty, 0))
    }
}

fn materialize_gv_initializer(
    init: &sonatina_ir::global_variable::GvInitializer,
    ty: Type,
    base: clif::Value,
    offset: i32,
    ctx: &sonatina_ir::module::ModuleCtx,
    builder: &mut FunctionBuilder,
) {
    use sonatina_ir::global_variable::GvInitializer;
    match init {
        GvInitializer::Immediate(imm) => match imm {
            Immediate::I8(v) => {
                let val = builder.ins().iconst(clif::types::I8, *v as i64);
                builder
                    .ins()
                    .store(cranelift_codegen::ir::MemFlags::new(), val, base, offset);
            }
            Immediate::I16(v) => {
                let val = builder.ins().iconst(clif::types::I16, *v as i64);
                builder
                    .ins()
                    .store(cranelift_codegen::ir::MemFlags::new(), val, base, offset);
            }
            Immediate::I32(v) => {
                let val = builder.ins().iconst(clif::types::I32, *v as i64);
                builder
                    .ins()
                    .store(cranelift_codegen::ir::MemFlags::new(), val, base, offset);
            }
            Immediate::I64(v) => {
                let val = builder.ins().iconst(clif::types::I64, *v);
                builder
                    .ins()
                    .store(cranelift_codegen::ir::MemFlags::new(), val, base, offset);
            }
            Immediate::I256(v) => {
                let u = v.to_u256();
                let bytes = u.to_little_endian();
                for i in 0..4 {
                    let limb = u64::from_le_bytes(bytes[i * 8..(i + 1) * 8].try_into().unwrap());
                    let val = builder.ins().iconst(clif::types::I64, limb as i64);
                    builder.ins().store(
                        cranelift_codegen::ir::MemFlags::new(),
                        val,
                        base,
                        offset + (i * 8) as i32,
                    );
                }
            }
            _ => {}
        },
        GvInitializer::Array(elems) => {
            if let Some(
                sonatina_ir::types::CompoundType::Array { elem, .. }
                | sonatina_ir::types::CompoundType::ConstRef(elem),
            ) = ty.resolve_compound(ctx)
            {
                let elem_size = ctx.size_of_unchecked(elem) as i32;
                for (i, elem_init) in elems.iter().enumerate() {
                    materialize_gv_initializer(
                        elem_init,
                        elem,
                        base,
                        offset + i as i32 * elem_size,
                        ctx,
                        builder,
                    );
                }
            }
        }
        GvInitializer::Struct(fields) => {
            if let Some(sonatina_ir::types::CompoundType::Struct(s)) = ty.resolve_compound(ctx) {
                for (idx, (field_init, &field_ty)) in fields.iter().zip(s.fields.iter()).enumerate()
                {
                    let Some((field_offset, _)) = ctx.aggregate_elem_offset(ty, idx) else {
                        continue;
                    };
                    materialize_gv_initializer(
                        field_init,
                        field_ty,
                        base,
                        offset + field_offset as i32,
                        ctx,
                        builder,
                    );
                }
            }
        }
    }
}

fn compute_alloc_size(ty: Type, ctx: &sonatina_ir::module::ModuleCtx) -> u32 {
    if let Type::Compound(_) = ty
        && let Some(cmpd) = ty.resolve_compound(ctx)
    {
        match cmpd {
            sonatina_ir::types::CompoundType::ObjRef(inner)
            | sonatina_ir::types::CompoundType::ConstRef(inner) => {
                return compute_alloc_size(inner, ctx);
            }
            _ => {}
        }
    }
    let size = ctx.size_of_unchecked(ty);
    size.max(8) as u32
}

fn aggregate_elem_offset(
    ctx: &ModuleCtx,
    aggregate_ty: Type,
    idx: usize,
) -> Result<(i32, Type), String> {
    if let Some((offset, ty)) = ctx.aggregate_elem_offset(aggregate_ty, idx) {
        return Ok((
            i32::try_from(offset)
                .map_err(|_| format!("aggregate offset {offset} overflows i32"))?,
            ty,
        ));
    }
    if let Some(
        sonatina_ir::types::CompoundType::ObjRef(inner)
        | sonatina_ir::types::CompoundType::ConstRef(inner),
    ) = aggregate_ty.resolve_compound(ctx)
    {
        return aggregate_elem_offset(ctx, inner, idx);
    }
    Err(format!(
        "cannot compute aggregate element offset for {aggregate_ty:?}[{idx}]"
    ))
}

fn constant_value_index(
    function: &Function,
    value_id: ValueId,
    inst_name: &str,
) -> Result<usize, String> {
    function
        .dfg
        .value_imm(value_id)
        .and_then(|imm| imm.to_nonnegative_usize())
        .ok_or_else(|| format!("{inst_name} index must be a nonnegative constant"))
}

fn is_undef_value(function: &Function, value_id: ValueId) -> bool {
    matches!(function.dfg.value(value_id), Value::Undef { .. })
}

fn compute_element_size(obj_ty: Type, ctx: &sonatina_ir::module::ModuleCtx) -> usize {
    if let Some(cmpd) = obj_ty.resolve_compound(ctx) {
        match cmpd {
            sonatina_ir::types::CompoundType::Array { elem, .. } => {
                return ctx.size_of_unchecked(elem);
            }
            sonatina_ir::types::CompoundType::ObjRef(inner)
            | sonatina_ir::types::CompoundType::ConstRef(inner) => {
                return compute_element_size(inner, ctx);
            }
            _ => {}
        }
    }
    // Fallback: 32 bytes (i256 size)
    32
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
                    args.push(BlockArg::Value(clif_val));
                    break;
                }
            }
        } else {
            break;
        }
    }
    Ok(args)
}
