use std::collections::HashMap;

use cranelift_codegen::ir::{self as clif, InstBuilder, condcodes::IntCC, instructions::BlockArg};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_jit::JITModule;
use cranelift_module::{FuncId, Linkage, Module as ClifModule};

use sonatina_ir::{
    BlockId, Function, Immediate, InstSetExt, Module, Signature, Type, Value, ValueId,
    inst::native::inst_set::{NativeInstKind, NativeInstSet},
    module::FuncRef,
};

pub(super) fn translate_module(
    module: &Module,
    jit: &mut JITModule,
) -> Result<HashMap<String, FuncId>, String> {
    let mut func_map: HashMap<String, FuncId> = HashMap::new();
    let mut func_id_map: HashMap<FuncRef, FuncId> = HashMap::new();

    let funcs = module.funcs();

    for &func_ref in &funcs {
        let (name, sig) = module.ctx.func_sig(func_ref, |sig| {
            let name = sig.name().to_string();
            let clif_sig = sonatina_sig_to_clif(sig, jit);
            (name, clif_sig)
        });

        let func_id = jit
            .declare_function(&name, Linkage::Export, &sig)
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
            if function.layout.entry_block().is_none() {
                return Ok(());
            }
            let func_id = func_id_map[&func_ref];
            translate_function(module, function, func_ref, func_id, &func_id_map, jit)
        });
        if let Some(result) = translated {
            if let Err(e) = result {
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

fn sonatina_sig_to_clif(sig: &Signature, jit: &JITModule) -> clif::Signature {
    let mut clif_sig = jit.make_signature();

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
    jit: &mut JITModule,
) -> Result<(), String> {
    let mut ctx = jit.make_context();
    let sig = module
        .ctx
        .func_sig(func_ref, |sig| sonatina_sig_to_clif(sig, jit));
    ctx.func.signature = sig;

    let mut builder_ctx = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_ctx);

    let mut block_map: HashMap<BlockId, clif::Block> = HashMap::new();
    let mut value_map: HashMap<ValueId, clif::Value> = HashMap::new();
    let mut var_map: HashMap<ValueId, Variable> = HashMap::new();
    let mut next_var: u32 = 0;

    for block in function.layout.iter_block() {
        let clif_block = builder.create_block();
        block_map.insert(block, clif_block);
    }

    let has_sret = module.ctx.func_sig(func_ref, |sig| returns_struct(sig));

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
                if let Some(phi) =
                    <&sonatina_ir::inst::control_flow::Phi as sonatina_ir::InstDowncast>::downcast(
                        inst_set, inst_data,
                    )
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
                let lhs = resolve_value(function, *add.lhs(), &value_map, &mut builder)?;
                let rhs = resolve_value(function, *add.rhs(), &value_map, &mut builder)?;
                let result_val = builder.ins().iadd(lhs, rhs);
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    value_map.insert(result, result_val);
                }
            } else if let Some(sub) = <&sonatina_ir::inst::arith::Sub as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let lhs = resolve_value(function, *sub.lhs(), &value_map, &mut builder)?;
                let rhs = resolve_value(function, *sub.rhs(), &value_map, &mut builder)?;
                let result_val = builder.ins().isub(lhs, rhs);
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    value_map.insert(result, result_val);
                }
            } else if let Some(mul) = <&sonatina_ir::inst::arith::Mul as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
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
                let lhs_ty = function.dfg.value_ty(*eq.lhs());
                if lhs_ty == Type::I256 {
                    let lhs = resolve_value(function, *eq.lhs(), &value_map, &mut builder)?;
                    let rhs = resolve_value(function, *eq.rhs(), &value_map, &mut builder)?;
                    let mut sig = jit.make_signature();
                    sig.params.push(clif::AbiParam::new(clif::types::I64));
                    sig.params.push(clif::AbiParam::new(clif::types::I64));
                    sig.returns.push(clif::AbiParam::new(clif::types::I64));
                    let func_id = jit.declare_function("__u256_eq", Linkage::Import, &sig)
                        .map_err(|e| format!("failed to declare __u256_eq: {e}"))?;
                    let func_ref = jit.declare_func_in_func(func_id, builder.func);
                    let clif_call = builder.ins().call(func_ref, &[lhs, rhs]);
                    let raw_result = builder.inst_results(clif_call)[0];
                    let bool_result = builder.ins().ireduce(clif::types::I8, raw_result);
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, bool_result);
                    }
                } else {
                    translate_icmp(IntCC::Equal, *eq.lhs(), *eq.rhs(), inst_id, module, function, &mut value_map, &mut builder)?;
                }
            } else if let Some(ne) = <&sonatina_ir::inst::cmp::Ne as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                translate_icmp(IntCC::NotEqual, *ne.lhs(), *ne.rhs(), inst_id, module, function, &mut value_map, &mut builder)?;
            } else if let Some(is_zero) = <&sonatina_ir::inst::cmp::IsZero as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let val = resolve_value(function, *is_zero.lhs(), &value_map, &mut builder)?;
                let val_ty = function.dfg.value_ty(*is_zero.lhs());
                let clif_ty = sonatina_type_to_clif(val_ty).unwrap_or(clif::types::I64);
                let zero = builder.ins().iconst(clif_ty, 0);
                let result_val = builder.ins().icmp(IntCC::Equal, val, zero);
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
                let result_val = builder.ins().sextend(to_ty, val);
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    value_map.insert(result, result_val);
                }
            } else if let Some(zext) = <&sonatina_ir::inst::cast::Zext as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let val = resolve_value(function, *zext.from(), &value_map, &mut builder)?;
                let to_ty = sonatina_type_to_clif_or_err(*zext.ty())?;
                let result_val = builder.ins().uextend(to_ty, val);
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
                    // Write return value to sret pointer, then return void
                    for &val_id in ret.args().as_slice() {
                        let val = resolve_value(function, val_id, &value_map, &mut builder)?;
                        // Copy 32 bytes from val (pointer) to sret (pointer)
                        for i in 0..4 {
                            let limb = builder.ins().load(
                                clif::types::I64,
                                cranelift_codegen::ir::MemFlags::new(),
                                val, (i * 8) as i32,
                            );
                            builder.ins().store(
                                cranelift_codegen::ir::MemFlags::new(),
                                limb, sret, (i * 8) as i32,
                            );
                        }
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
                        jit, &mut builder, intrinsic_name, &args?, true,
                    )?;
                    let ir_results = function.dfg.inst_results(inst_id);
                    if !ir_results.is_empty() {
                        value_map.insert(ir_results[0], result_val);
                    }
                } else {
                    let clif_func_id = func_id_map.get(&callee)
                        .ok_or_else(|| format!("unknown callee {:?}", callee))?;
                    let clif_func_ref = jit.declare_func_in_func(*clif_func_id, builder.func);
                    let ir_results = function.dfg.inst_results(inst_id);
                    let callee_returns_struct = !ir_results.is_empty()
                        && matches!(function.dfg.value_ty(ir_results[0]), Type::Compound(_));

                    let mut call_args: Vec<clif::Value> = Vec::new();
                    let sret_slot = if callee_returns_struct {
                        // Allocate caller-owned space for struct return
                        let slot = builder.create_sized_stack_slot(
                            cranelift_codegen::ir::StackSlotData::new(
                                cranelift_codegen::ir::StackSlotKind::ExplicitSlot, 32, 0,
                            ),
                        );
                        let addr = builder.ins().stack_addr(clif::types::I64, slot, 0);
                        call_args.push(addr); // hidden sret param
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
                let result_val = builder.ins().iadd(lhs, rhs);
                let ir_results = function.dfg.inst_results(inst_id);
                if ir_results.len() >= 1 {
                    value_map.insert(ir_results[0], result_val);
                }
                if ir_results.len() >= 2 {
                    // Overflow: result < lhs (unsigned overflow detection)
                    let overflow = builder.ins().icmp(IntCC::UnsignedLessThan, result_val, lhs);
                    value_map.insert(ir_results[1], overflow);
                }
            } else if let Some(umulo) = <&sonatina_ir::inst::arith::Umulo as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let lhs = resolve_value(function, *umulo.lhs(), &value_map, &mut builder)?;
                let rhs = resolve_value(function, *umulo.rhs(), &value_map, &mut builder)?;
                let result_val = builder.ins().imul(lhs, rhs);
                let ir_results = function.dfg.inst_results(inst_id);
                if ir_results.len() >= 1 {
                    value_map.insert(ir_results[0], result_val);
                }
                if ir_results.len() >= 2 {
                    // Overflow: result/lhs != rhs when lhs != 0; no overflow when lhs == 0
                    let lhs_ty = builder.func.dfg.value_type(lhs);
                    let zero = builder.ins().iconst(lhs_ty, 0);
                    let lhs_nonzero = builder.ins().icmp(IntCC::NotEqual, lhs, zero);
                    let one = builder.ins().iconst(lhs_ty, 1);
                    let safe_divisor = builder.ins().select(lhs_nonzero, lhs, one);
                    let div = builder.ins().udiv(result_val, safe_divisor);
                    let not_eq = builder.ins().icmp(IntCC::NotEqual, div, rhs);
                    let overflow = builder.ins().band(not_eq, lhs_nonzero);
                    value_map.insert(ir_results[1], overflow);
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
                let idx_val = function.dfg.value_imm(*extract.idx())
                    .map(|imm| match imm {
                        Immediate::I8(v) => v as i32,
                        Immediate::I32(v) => v,
                        Immediate::I64(v) => v as i32,
                        Immediate::I256(v) => v.to_u256().low_u64() as i32,
                        _ => 0,
                    })
                    .unwrap_or(0);
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    let result_ty = function.dfg.value_ty(result);
                    let elem_size = module.ctx.size_of_unchecked(result_ty) as i32;
                    let offset = idx_val * elem_size;
                    if result_ty == Type::I256 || matches!(result_ty, Type::Compound(_)) {
                        let addr = builder.ins().iadd_imm(base, offset as i64);
                        value_map.insert(result, addr);
                    } else {
                        let clif_ty = sonatina_type_to_clif_or_err(result_ty)?;
                        let loaded = builder.ins().load(clif_ty, cranelift_codegen::ir::MemFlags::new(), base, offset);
                        value_map.insert(result, loaded);
                    }
                }
            } else if let Some(alloca) = <&sonatina_ir::inst::data::Alloca as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
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
                let addr = resolve_value(function, *mstore.addr(), &value_map, &mut builder)?;
                let val = resolve_value(function, *mstore.value(), &value_map, &mut builder)?;
                let store_ty = function.dfg.value_ty(*mstore.value());
                if store_ty == Type::I256 {
                    for i in 0..4 {
                        let limb = builder.ins().load(clif::types::I64, cranelift_codegen::ir::MemFlags::new(), val, (i * 8) as i32);
                        builder.ins().store(cranelift_codegen::ir::MemFlags::new(), limb, addr, (i * 8) as i32);
                    }
                } else {
                    builder.ins().store(cranelift_codegen::ir::MemFlags::new(), val, addr, 0);
                }
            } else if let Some(mload) = <&sonatina_ir::inst::data::Mload as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let addr = resolve_value(function, *mload.addr(), &value_map, &mut builder)?;
                if let Some(result) = function.dfg.inst_result(inst_id) {
                    let result_ty = function.dfg.value_ty(result);
                    if result_ty == Type::I256 {
                        value_map.insert(result, addr);
                    } else {
                        let clif_ty = sonatina_type_to_clif_or_err(result_ty)?;
                        let loaded = builder.ins().load(clif_ty, cranelift_codegen::ir::MemFlags::new(), addr, 0);
                        value_map.insert(result, loaded);
                    }
                }
            } else if let Some(addmod) = <&sonatina_ir::inst::evm::EvmAddMod as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                let a = resolve_value(function, *addmod.lhs(), &value_map, &mut builder)?;
                let b = resolve_value(function, *addmod.rhs(), &value_map, &mut builder)?;
                let m = resolve_value(function, *addmod.modulus(), &value_map, &mut builder)?;
                let result_val = emit_u256_intrinsic_call(
                    jit, &mut builder, "__u256_addmod",
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
                    jit, &mut builder, "__u256_mulmod",
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
                    // i256 store: copy 32 bytes from val (pointer) to dest (pointer)
                    for i in 0..4 {
                        let limb = builder.ins().load(clif::types::I64, cranelift_codegen::ir::MemFlags::new(), val, (i * 8) as i32);
                        builder.ins().store(cranelift_codegen::ir::MemFlags::new(), limb, dest, (i * 8) as i32);
                    }
                } else {
                    builder.ins().store(cranelift_codegen::ir::MemFlags::new(), val, dest, 0);
                }
            } else if let Some(obj_alloc) = <&sonatina_ir::inst::data::ObjAlloc as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
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
                    value_map.insert(result, base);
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

    if let Err(e) = jit.define_function(func_id, &mut ctx) {
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
    if ty.is_obj_ref(&module.ctx) {
        if let Some(inner) = ty.resolve_compound(&module.ctx) {
            if let sonatina_ir::types::CompoundType::ObjRef(elem) = inner {
                if let Some(clif_ty) = sonatina_type_to_clif(elem) {
                    return Ok(builder.ins().load(
                        clif_ty,
                        cranelift_codegen::ir::MemFlags::new(),
                        val,
                        0,
                    ));
                }
            }
        }
    }
    Ok(val)
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
    let lhs_val = resolve_scalar_value(module, function, lhs, value_map, builder)?;
    let rhs_val = resolve_scalar_value(module, function, rhs, value_map, builder)?;
    let result_val = builder.ins().icmp(cc, lhs_val, rhs_val);
    if let Some(result) = function.dfg.inst_result(inst_id) {
        value_map.insert(result, result_val);
    }
    Ok(())
}

/// If `val` is a raw i64 (loaded from obj.load of i256), write it to a
/// 32-byte stack slot and return the slot's address. If `val` is already
/// a stack address (from emit_i256_immediate), return it as-is.
///
/// This ensures u256 intrinsics always receive valid pointers to 32-byte buffers.
fn ensure_u256_on_stack(val: clif::Value, builder: &mut FunctionBuilder) -> clif::Value {
    // Always write to a fresh stack slot — safe for any value
    let slot = builder.create_sized_stack_slot(cranelift_codegen::ir::StackSlotData::new(
        cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
        32,
        0,
    ));
    let addr = builder.ins().stack_addr(clif::types::I64, slot, 0);
    // Store the i64 value at offset 0, zero the rest
    builder
        .ins()
        .store(cranelift_codegen::ir::MemFlags::new(), val, addr, 0);
    let zero = builder.ins().iconst(clif::types::I64, 0);
    builder
        .ins()
        .store(cranelift_codegen::ir::MemFlags::new(), zero, addr, 8);
    builder
        .ins()
        .store(cranelift_codegen::ir::MemFlags::new(), zero, addr, 16);
    builder
        .ins()
        .store(cranelift_codegen::ir::MemFlags::new(), zero, addr, 24);
    addr
}

fn emit_u256_intrinsic_call(
    jit: &mut JITModule,
    builder: &mut FunctionBuilder,
    name: &str,
    args: &[clif::Value],
    has_result: bool,
) -> Result<clif::Value, String> {
    let ptr_ty = clif::types::I64;

    // Build the intrinsic signature: all args are pointers, optional result pointer
    let mut sig = jit.make_signature();
    for _ in args {
        sig.params.push(clif::AbiParam::new(ptr_ty));
    }
    if has_result {
        sig.params.push(clif::AbiParam::new(ptr_ty)); // result pointer
    }

    let func_id = jit
        .declare_function(name, Linkage::Import, &sig)
        .map_err(|e| format!("failed to declare {name}: {e}"))?;
    let func_ref = jit.declare_func_in_func(func_id, builder.func);

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
            if let Some(cmpd) = ty.resolve_compound(ctx) {
                if let sonatina_ir::types::CompoundType::Array { elem, .. }
                | sonatina_ir::types::CompoundType::ConstRef(elem) = cmpd
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
        }
        GvInitializer::Struct(fields) => {
            if let Some(cmpd) = ty.resolve_compound(ctx) {
                if let sonatina_ir::types::CompoundType::Struct(s) = cmpd {
                    let mut field_offset = offset;
                    for (i, (field_init, &field_ty)) in
                        fields.iter().zip(s.fields.iter()).enumerate()
                    {
                        materialize_gv_initializer(
                            field_init,
                            field_ty,
                            base,
                            field_offset,
                            ctx,
                            builder,
                        );
                        field_offset += ctx.size_of_unchecked(field_ty) as i32;
                    }
                }
            }
        }
    }
}

fn compute_alloc_size(ty: Type, ctx: &sonatina_ir::module::ModuleCtx) -> u32 {
    if let Type::Compound(_) = ty {
        if let Some(cmpd) = ty.resolve_compound(ctx) {
            match cmpd {
                sonatina_ir::types::CompoundType::Array { elem, len } => {
                    let elem_size = ctx.size_of_unchecked(elem);
                    return (elem_size * len).max(8) as u32;
                }
                sonatina_ir::types::CompoundType::ObjRef(inner)
                | sonatina_ir::types::CompoundType::ConstRef(inner) => {
                    return compute_alloc_size(inner, ctx);
                }
                sonatina_ir::types::CompoundType::Struct(s) => {
                    let total: usize = s.fields.iter().map(|f| ctx.size_of_unchecked(*f)).sum();
                    return total.max(8) as u32;
                }
                _ => {}
            }
        }
    }
    let size = ctx.size_of_unchecked(ty);
    size.max(8) as u32
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
