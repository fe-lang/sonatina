mod abi;
mod division;
mod frame;
mod globals;
mod i256;
mod memory;
mod phi;
mod scalar;
mod values;

use std::collections::HashMap;

use cranelift_codegen::{
    Context,
    control::ControlPlane,
    ir::{self as clif, InstBuilder, MemFlagsData, TrapCode, condcodes::IntCC},
    settings,
};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Switch};
use cranelift_module::{FuncId, Linkage, Module as ClifModule, ModuleReloc};

use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, Linkage as SonatinaLinkage, Module, Type, Value, ValueId,
    inst::{InstId, inst_set::InstSetExt, native::inst_set::NativeInstKind},
    isa::native::inst_set as native_inst_set,
    module::FuncRef,
    parallel,
};
use sonatina_triple::TargetTriple;

use crate::analysis::known_bits::KnownBitsQuery;

use self::{
    abi::*,
    division::{Divider, DividerCall, Numerator, addmod, div_rem, div_rem_i128, mulmod},
    frame::FrameSlots,
    globals::*,
    i256::*,
    memory::*,
    phi::Edges,
    scalar::*,
    values::*,
};

pub(super) fn translate_module(
    module: &Module,
    clif_module: &mut impl ClifModule,
) -> Result<HashMap<String, FuncId>, String> {
    let mut defined_func_map: HashMap<String, FuncId> = HashMap::new();
    let mut func_id_map: HashMap<FuncRef, FuncId> = HashMap::new();
    let data_ids = define_globals(&module.ctx, clif_module)?;

    let funcs = module.funcs();
    let mut divider = Divider::default();

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

    let mut translated = Vec::new();
    for &func_ref in &funcs {
        let name = module.ctx.func_sig(func_ref, |sig| sig.name().to_string());
        let ctx =
            module
                .func_store
                .try_view(func_ref, |function| -> Result<Option<Context>, String> {
                    if module.ctx.func_linkage(func_ref).is_external() {
                        return Ok(None);
                    }
                    if function.layout.entry_block().is_none() {
                        return Ok(None);
                    }
                    divider.start_function();
                    translate_function(
                        module,
                        function,
                        func_ref,
                        &func_id_map,
                        &data_ids,
                        &mut divider,
                        clif_module,
                    )
                    .map(Some)
                });
        match ctx {
            Some(Ok(Some(ctx))) => {
                let func_id = func_id_map[&func_ref];
                defined_func_map.insert(name.clone(), func_id);
                translated.push((format!("function {name}"), func_id, ctx));
            }
            Some(Ok(None)) | None => {}
            Some(Err(error)) => {
                return Err(format!("failed to translate function {name}: {error}"));
            }
        }
    }
    translated.extend(
        divider
            .finish(clif_module)
            .into_iter()
            .map(|(func_id, ctx)| ("the divider".to_string(), func_id, ctx)),
    );

    // Functions compile independently; defining them in order keeps the
    // output deterministic.
    let isa = clif_module.isa();
    let compiled = parallel::map_owned(
        &module.func_store,
        translated,
        |(name, func_id, mut ctx)| {
            let compiled = ctx
                .compile(isa, &mut ControlPlane::default())
                .map(|_| ())
                .map_err(|error| error.inner.to_string());
            (name, func_id, ctx, compiled)
        },
    );
    for (name, func_id, ctx, compiled) in compiled {
        if let Err(error) = compiled {
            eprintln!("[cranelift] CLIF IR (error):\n{}", ctx.func.display());
            return Err(format!("cranelift failed to compile {name}: {error}"));
        }
        let code = ctx
            .compiled_code()
            .ok_or_else(|| format!("cranelift compiled no code for {name}"))?;
        let relocs: Vec<_> = code
            .buffer
            .relocs()
            .iter()
            .map(|reloc| ModuleReloc::from_mach_reloc(reloc, &ctx.func, func_id))
            .collect();
        clif_module
            .define_function_bytes(
                func_id,
                code.buffer.alignment.into(),
                code.code_buffer(),
                &relocs,
            )
            .map_err(|error| format!("failed to define {name}: {error}"))?;
    }

    Ok(defined_func_map)
}

/// Whether a shift's count is always below its operand's width, which its
/// known bits show when every bit above the width's low bits is zero.
fn shift_count_in_range(
    function: &Function,
    count: ValueId,
    value: ValueId,
    known_bits: &mut Option<KnownBitsQuery>,
) -> bool {
    let log2_width = match function.dfg.value_ty(value) {
        Type::I8 => 3,
        Type::I16 => 4,
        Type::I32 => 5,
        Type::I64 => 6,
        Type::I128 => 7,
        _ => return false,
    };
    known_bits
        .get_or_insert_with(|| KnownBitsQuery::new(function))
        .fits_in_low_bits(function, count, log2_width)
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

#[allow(clippy::too_many_arguments)]
fn translate_function(
    module: &Module,
    function: &Function,
    func_ref: FuncRef,
    func_id_map: &HashMap<FuncRef, FuncId>,
    data_ids: &GlobalDataMap,
    divider: &mut Divider,
    clif_module: &mut impl ClifModule,
) -> Result<Context, String> {
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
    let mut value_map = ValueMap::default();
    let mut i256_storage = I256Storage::default();
    for &block in &block_order {
        let clif_block = builder.create_block();
        block_map.insert(block, clif_block);
    }

    let has_sret = module
        .ctx
        .func_sig(func_ref, |sig| returns_indirect(&module.ctx, sig));

    let entry = function.layout.entry_block().ok_or("no entry block")?;
    // Cranelift forbids branches to its entry block, so a Sonatina entry block
    // that is also a loop header is entered through a separate prologue.
    let clif_entry = if cfg.preds_of(entry).any(|pred| block_map.contains_key(pred)) {
        builder.create_block()
    } else {
        block_map[&entry]
    };
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
        let ty = function.dfg.value_ty(arg_value);
        if ty == Type::I256 {
            let limbs = i256_storage.incoming(arg_value, param, &mut builder);
            value_map.insert_limbs(arg_value, limbs);
        } else {
            let param = normalize_scalar(param, ty, &mut builder);
            value_map.insert(arg_value, param);
        }
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

    let frame = FrameSlots::new(function, &cfg, &block_order, sret_ptr, &mut builder)?;
    let mut known_bits = None;
    // A jump table's entries per key: at least 10% of a run's entries are
    // keys when optimizing for speed and 40% for size, as in LLVM.
    let (table_entries, per_keys) = match clif_module.isa().flags().opt_level() {
        settings::OptLevel::SpeedAndSize => (5, 2),
        settings::OptLevel::None | settings::OptLevel::Speed => (10, 1),
    };
    for &block in &block_order {
        let clif_block = block_map[&block];
        for inst_id in function.layout.iter_inst(block) {
            if !function.dfg.is_phi(inst_id) {
                break;
            }
            let result = function
                .dfg
                .inst_result(inst_id)
                .ok_or("phi has no result")?;
            let ty = function.dfg.value_ty(result);
            if ty == Type::I256 {
                let limbs = std::array::from_fn(|_| {
                    builder.append_block_param(clif_block, clif::types::I64)
                });
                value_map.insert_limbs(result, limbs);
            } else if !uses_indirect_value_representation(&module.ctx, ty) {
                let clif_ty = sonatina_type_to_clif_or_err(ty, pointer_type)?;
                let param = builder.append_block_param(clif_block, clif_ty);
                value_map.insert(result, param);
            }
        }
    }
    let edges = Edges {
        function,
        block_map: &block_map,
        frame: &frame,
        config: target_config,
    };

    if clif_entry != block_map[&entry] {
        builder.ins().jump(block_map[&entry], &[]);
    }

    for &block in &block_order {
        let clif_block = block_map[&block];
        if clif_block != clif_entry {
            builder.switch_to_block(clif_block);
        }
        // Incoming edges copy aggregate phi inputs into the phis' own slots,
        // never aliasing the reusable result slot of an input's producer.
        for inst_id in function.layout.iter_inst(block) {
            if !function.dfg.is_phi(inst_id) {
                break;
            }
            if let Some(result) = function.dfg.inst_result(inst_id)
                && uses_indirect_value_representation(&module.ctx, function.dfg.value_ty(result))
            {
                value_map.insert(result, frame.address(result, &mut builder)?);
            }
        }

        for inst_id in function.layout.iter_inst(block) {
            let inst_data = function.dfg.inst(inst_id);
            let i256_op = translate_i256_op(
                function,
                inst_id,
                &mut value_map,
                &mut builder,
                &mut known_bits,
            )?;

            match native_inst_set().resolve_inst(inst_data) {
                _ if i256_op => {}
                NativeInstKind::Add(add) => {
                    let lhs = resolve_value(function, *add.lhs(), &value_map, &mut builder)?;
                    let rhs = resolve_value(function, *add.rhs(), &value_map, &mut builder)?;
                    let result_val = builder.ins().iadd(lhs, rhs);
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Sub(sub) => {
                    let lhs = resolve_value(function, *sub.lhs(), &value_map, &mut builder)?;
                    let rhs = resolve_value(function, *sub.rhs(), &value_map, &mut builder)?;
                    let result_val = builder.ins().isub(lhs, rhs);
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Mul(mul) => {
                    let lhs = resolve_value(function, *mul.lhs(), &value_map, &mut builder)?;
                    let rhs = resolve_value(function, *mul.rhs(), &value_map, &mut builder)?;
                    let result_val = builder.ins().imul(lhs, rhs);
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Neg(neg) => {
                    let val = resolve_value(function, *neg.arg(), &value_map, &mut builder)?;
                    let result_val = builder.ins().ineg(val);
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Udiv(div) => translate_div_rem(
                    DivRemKind::Udiv,
                    *div.lhs(),
                    *div.rhs(),
                    inst_id,
                    function,
                    &mut value_map,
                    divider,
                    clif_module,
                    &mut builder,
                )?,
                NativeInstKind::Sdiv(div) => translate_div_rem(
                    DivRemKind::Sdiv,
                    *div.lhs(),
                    *div.rhs(),
                    inst_id,
                    function,
                    &mut value_map,
                    divider,
                    clif_module,
                    &mut builder,
                )?,
                NativeInstKind::Umod(rem) => translate_div_rem(
                    DivRemKind::Umod,
                    *rem.lhs(),
                    *rem.rhs(),
                    inst_id,
                    function,
                    &mut value_map,
                    divider,
                    clif_module,
                    &mut builder,
                )?,
                NativeInstKind::Smod(rem) => translate_div_rem(
                    DivRemKind::Smod,
                    *rem.lhs(),
                    *rem.rhs(),
                    inst_id,
                    function,
                    &mut value_map,
                    divider,
                    clif_module,
                    &mut builder,
                )?,
                NativeInstKind::EvmAddMod(op) => translate_modular(
                    addmod,
                    [*op.lhs(), *op.rhs(), *op.modulus()],
                    inst_id,
                    function,
                    &mut value_map,
                    divider,
                    clif_module,
                    &mut builder,
                )?,
                NativeInstKind::EvmMulMod(op) => translate_modular(
                    mulmod,
                    [*op.lhs(), *op.rhs(), *op.modulus()],
                    inst_id,
                    function,
                    &mut value_map,
                    divider,
                    clif_module,
                    &mut builder,
                )?,
                NativeInstKind::Shl(shl) => {
                    let val = resolve_value(function, *shl.value(), &value_map, &mut builder)?;
                    let bits = resolve_value(function, *shl.bits(), &value_map, &mut builder)?;
                    let result_val = emit_scalar_shift(
                        val,
                        bits,
                        function.dfg.value_ty(*shl.value()),
                        ScalarShift::Shl,
                        shift_count_in_range(function, *shl.bits(), *shl.value(), &mut known_bits),
                        &mut builder,
                    );
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Shr(shr) => {
                    let val = resolve_value(function, *shr.value(), &value_map, &mut builder)?;
                    let bits = resolve_value(function, *shr.bits(), &value_map, &mut builder)?;
                    let result_val = emit_scalar_shift(
                        val,
                        bits,
                        function.dfg.value_ty(*shr.value()),
                        ScalarShift::Shr,
                        shift_count_in_range(function, *shr.bits(), *shr.value(), &mut known_bits),
                        &mut builder,
                    );
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Sar(sar) => {
                    let val = resolve_value(function, *sar.value(), &value_map, &mut builder)?;
                    let bits = resolve_value(function, *sar.bits(), &value_map, &mut builder)?;
                    let result_val = emit_scalar_shift(
                        val,
                        bits,
                        function.dfg.value_ty(*sar.value()),
                        ScalarShift::Sar,
                        shift_count_in_range(function, *sar.bits(), *sar.value(), &mut known_bits),
                        &mut builder,
                    );
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::And(and) => {
                    let lhs = resolve_value(function, *and.lhs(), &value_map, &mut builder)?;
                    let rhs = resolve_value(function, *and.rhs(), &value_map, &mut builder)?;
                    let result_val = builder.ins().band(lhs, rhs);
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Or(or) => {
                    let lhs = resolve_value(function, *or.lhs(), &value_map, &mut builder)?;
                    let rhs = resolve_value(function, *or.rhs(), &value_map, &mut builder)?;
                    let result_val = builder.ins().bor(lhs, rhs);
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Xor(xor) => {
                    let lhs = resolve_value(function, *xor.lhs(), &value_map, &mut builder)?;
                    let rhs = resolve_value(function, *xor.rhs(), &value_map, &mut builder)?;
                    let result_val = builder.ins().bxor(lhs, rhs);
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Not(not) => {
                    let val = resolve_value(function, *not.arg(), &value_map, &mut builder)?;
                    let result_val = if function.dfg.value_ty(*not.arg()) == Type::I1 {
                        builder.ins().bxor_imm_s(val, 1)
                    } else {
                        builder.ins().bnot(val)
                    };
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Bswap(bswap) => {
                    let arg = *bswap.arg();
                    let result_val = match function.dfg.value_ty(arg) {
                        // A single byte has no order to reverse.
                        Type::I8 => resolve_value(function, arg, &value_map, &mut builder)?,
                        _ => {
                            let val = resolve_value(function, arg, &value_map, &mut builder)?;
                            builder.ins().bswap(val)
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
                    let val = resolve_value(function, *is_zero.lhs(), &value_map, &mut builder)?;
                    let clif_ty = sonatina_type_to_clif(val_ty, pointer_type)
                        .ok_or_else(|| format!("unsupported is_zero operand type: {val_ty:?}"))?;
                    let zero = scalar_constant(clif_ty, 0, &mut builder);
                    let result_val = builder.ins().icmp(IntCC::Equal, val, zero);
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
                NativeInstKind::Sext(sext) => translate_extend(
                    *sext.from(),
                    *sext.ty(),
                    true,
                    inst_id,
                    function,
                    &mut value_map,
                    pointer_type,
                    &mut builder,
                )?,
                NativeInstKind::Zext(zext) => translate_extend(
                    *zext.from(),
                    *zext.ty(),
                    false,
                    inst_id,
                    function,
                    &mut value_map,
                    pointer_type,
                    &mut builder,
                )?,
                NativeInstKind::Trunc(trunc) => {
                    let to_ty = sonatina_type_to_clif_or_err(*trunc.ty(), pointer_type)?;
                    let result_val = if function.dfg.value_ty(*trunc.from()) == Type::I256 {
                        let limbs =
                            resolve_i256(function, *trunc.from(), &value_map, &mut builder)?;
                        truncate_limbs(limbs, to_ty, &mut builder)
                    } else {
                        let val = resolve_value(function, *trunc.from(), &value_map, &mut builder)?;
                        resize_int_value(val, to_ty, false, &mut builder)
                    };
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                // Every use of a translated value sees one value, and an
                // undefined one reads as zero, so freezing changes nothing.
                NativeInstKind::Freeze(freeze) => {
                    let result = function
                        .dfg
                        .inst_result(inst_id)
                        .ok_or("freeze has no result")?;
                    if function.dfg.value_ty(result) == Type::I256 {
                        let limbs =
                            resolve_i256(function, *freeze.arg(), &value_map, &mut builder)?;
                        value_map.insert_limbs(result, limbs);
                    } else {
                        let arg = resolve_value(function, *freeze.arg(), &value_map, &mut builder)?;
                        value_map.insert(result, arg);
                    }
                }
                NativeInstKind::Bitcast(bitcast) => {
                    let from_ty = function.dfg.value_ty(*bitcast.from());
                    let to_ty = *bitcast.ty();
                    let result = function
                        .dfg
                        .inst_result(inst_id)
                        .ok_or("bitcast has no result")?;
                    if from_ty == Type::I256 && to_ty == Type::I256 {
                        let limbs =
                            resolve_i256(function, *bitcast.from(), &value_map, &mut builder)?;
                        value_map.insert_limbs(result, limbs);
                    } else if from_ty == Type::I256 {
                        // A cast creates a value in storage of its own.
                        if value_storage_size(to_ty, &module.ctx)? != 32 {
                            return Err(format!(
                                "bitcast requires equal-sized types: {from_ty:?} to {to_ty:?}"
                            ));
                        }
                        let limbs =
                            resolve_i256(function, *bitcast.from(), &value_map, &mut builder)?;
                        let dest = create_stack_slot_for_type(to_ty, &module.ctx, &mut builder)?;
                        store_limbs(limbs, dest, 0, MemFlagsData::trusted(), &mut builder);
                        value_map.insert(result, dest);
                    } else if to_ty == Type::I256 {
                        if value_storage_size(from_ty, &module.ctx)? != 32 {
                            return Err(format!(
                                "bitcast requires equal-sized types: {from_ty:?} to {to_ty:?}"
                            ));
                        }
                        let source = resolve_operand(
                            function,
                            *bitcast.from(),
                            &value_map,
                            target_config,
                            &mut builder,
                        )?;
                        let limbs = load_limbs(source, 0, MemFlagsData::new(), &mut builder);
                        value_map.insert_limbs(result, limbs);
                    } else {
                        let val = resolve_operand(
                            function,
                            *bitcast.from(),
                            &value_map,
                            target_config,
                            &mut builder,
                        )?;
                        let result_val = translate_bitcast(
                            val,
                            from_ty,
                            to_ty,
                            &module.ctx,
                            target_config,
                            &mut builder,
                        )?;
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::IntToPtr(cast) => {
                    let to_ty = sonatina_type_to_clif_or_err(*cast.ty(), pointer_type)?;
                    let val = if function.dfg.value_ty(*cast.from()) == Type::I256 {
                        resolve_i256(function, *cast.from(), &value_map, &mut builder)?[0]
                    } else {
                        resolve_value(function, *cast.from(), &value_map, &mut builder)?
                    };
                    let result_val = resize_int_value(val, to_ty, false, &mut builder);
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::PtrToInt(cast) => translate_extend(
                    *cast.from(),
                    *cast.ty(),
                    false,
                    inst_id,
                    function,
                    &mut value_map,
                    pointer_type,
                    &mut builder,
                )?,
                NativeInstKind::Jump(jump) => {
                    edges.jump(block, *jump.dest(), &value_map, &mut builder)?;
                }
                NativeInstKind::Br(br) => {
                    let cond = resolve_value(function, *br.cond(), &value_map, &mut builder)?;
                    let nz = edges.target(block, *br.nz_dest(), &value_map, &mut builder)?;
                    let z = edges.target(block, *br.z_dest(), &value_map, &mut builder)?;
                    builder
                        .ins()
                        .brif(cond, nz.block, &nz.args, z.block, &z.args);
                    edges.fill(nz, block, *br.nz_dest(), &value_map, &mut builder)?;
                    edges.fill(z, block, *br.z_dest(), &value_map, &mut builder)?;
                }
                NativeInstKind::BrTable(br_table) => {
                    // A switch's branches pass no block arguments, so an edge
                    // with phi inputs runs them in a block of its own.
                    let mut edge_blocks = Vec::new();
                    let mut dest_blocks = HashMap::new();
                    let mut dest_block = |dest: BlockId, builder: &mut FunctionBuilder| {
                        *dest_blocks.entry(dest).or_insert_with(|| {
                            if edges.has_inputs(block, dest) {
                                let edge_block = builder.create_block();
                                edge_blocks.push((edge_block, dest));
                                edge_block
                            } else {
                                block_map[&dest]
                            }
                        })
                    };
                    let (otherwise, traps) = match *br_table.default() {
                        Some(default) => (dest_block(default, &mut builder), false),
                        None => (builder.create_block(), true),
                    };
                    // Each key as the unsigned bits of the scrutinee's type.
                    let keys = br_table
                        .table()
                        .iter()
                        .map(|&(key, dest)| {
                            let key = function
                                .dfg
                                .value_imm(key)
                                .ok_or("br_table key is not an immediate")?;
                            Ok((key.zext(Type::I256).as_i256().to_u256(), dest))
                        })
                        .collect::<Result<Vec<_>, String>>()?;
                    let scrutinee_id = *br_table.scrutinee();
                    let limbs = (function.dfg.value_ty(scrutinee_id) == Type::I256)
                        .then(|| resolve_i256(function, scrutinee_id, &value_map, &mut builder))
                        .transpose()?;
                    let scrutinee = match limbs {
                        Some(limbs) => limbs[0],
                        None => resolve_scalar_value(
                            module,
                            function,
                            scrutinee_id,
                            &value_map,
                            pointer_type,
                            &mut builder,
                        )?,
                    };
                    // From four keys up, Cranelift's switch gives each run of
                    // consecutive keys a jump table and searches the runs; a
                    // run's holes take the default while it stays dense
                    // enough, so one table covers it, and a run that may
                    // start at zero does, saving its lower bound check.
                    // Fewer keys, or i256 keys beyond the low limb, are
                    // compared in turn.
                    if keys.len() >= 4
                        && limbs.is_none_or(|_| keys.iter().all(|(key, _)| key.0[1..] == [0; 3]))
                    {
                        if let Some(limbs) = limbs {
                            // The keys lie in the low limb, so a scrutinee
                            // with any upper bit set takes the default.
                            let upper = builder.ins().bor(limbs[1], limbs[2]);
                            let upper = builder.ins().bor(upper, limbs[3]);
                            let low = builder.create_block();
                            builder.ins().brif(upper, otherwise, &[], low, &[]);
                            builder.switch_to_block(low);
                        }
                        let mut switch = Switch::new();
                        for &(key, dest) in &keys {
                            switch.set_entry(key.low_u128(), dest_block(dest, &mut builder));
                        }
                        let mut sorted: Vec<_> =
                            keys.iter().map(|(key, _)| key.low_u128()).collect();
                        sorted.sort_unstable();
                        let dense = |first: u128, last: u128, count: u128| {
                            (last - first).saturating_add(1).saturating_mul(per_keys)
                                <= count * table_entries
                        };
                        let mut runs = Vec::new();
                        let mut run: Option<(u128, u128, u128)> = None;
                        for key in sorted {
                            run = match run {
                                Some((first, _, count)) if dense(first, key, count + 1) => {
                                    Some((first, key, count + 1))
                                }
                                _ => {
                                    runs.extend(run);
                                    Some((key, key, 1))
                                }
                            };
                        }
                        runs.extend(run);
                        if let Some((first, last, count)) = runs.first_mut()
                            && dense(0, *last, *count)
                        {
                            *first = 0;
                        }
                        for (first, last, _) in runs {
                            for hole in first..=last {
                                if !switch.entries().contains_key(&hole) {
                                    switch.set_entry(hole, otherwise);
                                }
                            }
                        }
                        switch.emit(&mut builder, scrutinee, otherwise);
                    } else {
                        let ty = builder.func.dfg.value_type(scrutinee);
                        for &(key, dest) in &keys {
                            let matches = match limbs {
                                Some(limbs) => {
                                    let key = constant_limbs(key, &mut builder);
                                    eq(limbs, key, &mut builder)
                                }
                                None => {
                                    let key =
                                        scalar_constant(ty, key.low_u128() as i128, &mut builder);
                                    builder.ins().icmp(IntCC::Equal, scrutinee, key)
                                }
                            };
                            let dest = dest_block(dest, &mut builder);
                            let next = builder.create_block();
                            builder.ins().brif(matches, dest, &[], next, &[]);
                            builder.switch_to_block(next);
                        }
                        builder.ins().jump(otherwise, &[]);
                    }
                    for (edge_block, dest) in edge_blocks {
                        builder.switch_to_block(edge_block);
                        edges.jump(block, dest, &value_map, &mut builder)?;
                    }
                    if traps {
                        builder.switch_to_block(otherwise);
                        emit_trap(&mut builder, TrapCode::user(3).unwrap());
                    }
                }
                NativeInstKind::Return(ret) => {
                    if let Some(sret) = sret_ptr {
                        let [val_id] = ret.args().as_slice() else {
                            return Err("indirect return requires exactly one value".to_string());
                        };
                        let val_ty = function.dfg.value_ty(*val_id);
                        let storage_ty = indirect_return_storage_type(&module.ctx, val_ty)
                            .ok_or("indirect return value has no storage type")?;
                        if val_ty == Type::I256 {
                            store_value(function, *val_id, sret, 0, &value_map, &mut builder)?;
                        } else if !frame.in_return_buffer(*val_id) {
                            store_indirect(
                                function,
                                *val_id,
                                sret,
                                value_storage_size(storage_ty, &module.ctx)?,
                                &value_map,
                                target_config,
                                &mut builder,
                            )?;
                        }
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
                        let result_ty = function.dfg.value_ty(ir_results[0]);
                        // A constref result's copy of its referent stays
                        // in a slot of its own.
                        let addr = if result_ty == Type::I256 {
                            i256_storage.result(&mut builder)
                        } else if storage_ty == result_ty {
                            frame.address(ir_results[0], &mut builder)?
                        } else {
                            let slot = builder
                                .create_sized_stack_slot(stack_slot_data(storage_ty, &module.ctx)?);
                            builder.ins().stack_addr(pointer_type, slot, 0)
                        };
                        call_args.push(addr);
                        Some(addr)
                    } else {
                        None
                    };

                    let mut i256_args = 0;
                    for &arg in call.args() {
                        let value = if function.dfg.value_ty(arg) == Type::I256 {
                            i256_args += 1;
                            i256_storage.outgoing(
                                function,
                                arg,
                                i256_args - 1,
                                &value_map,
                                &mut builder,
                            )?
                        } else {
                            resolve_operand(function, arg, &value_map, target_config, &mut builder)?
                        };
                        call_args.push(value);
                    }

                    let clif_call = builder.ins().call(clif_func_ref, &call_args);
                    if let Some(sret_addr) = sret_slot {
                        let result = ir_results[0];
                        if function.dfg.value_ty(result) == Type::I256 {
                            let limbs =
                                load_limbs(sret_addr, 0, MemFlagsData::trusted(), &mut builder);
                            value_map.insert_limbs(result, limbs);
                        } else {
                            value_map.insert(result, sret_addr);
                        }
                    } else {
                        let results = builder.inst_results(clif_call);
                        for (ir_result, clif_result) in ir_results.iter().zip(results) {
                            value_map.insert(*ir_result, *clif_result);
                        }
                    }
                }
                NativeInstKind::Uaddo(uaddo) => {
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
                    insert_clif_results(function, inst_id, [result_val, overflow], &mut value_map);
                }
                NativeInstKind::Saddo(saddo) => {
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
                    insert_clif_results(function, inst_id, [result_val, overflow], &mut value_map);
                }
                NativeInstKind::Usubo(usubo) => {
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
                    insert_clif_results(function, inst_id, [result_val, overflow], &mut value_map);
                }
                NativeInstKind::Ssubo(ssubo) => {
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
                    insert_clif_results(function, inst_id, [result_val, overflow], &mut value_map);
                }
                NativeInstKind::Umulo(umulo) => {
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
                    insert_clif_results(function, inst_id, [result_val, overflow], &mut value_map);
                }
                NativeInstKind::Smulo(smulo) => {
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
                    insert_clif_results(function, inst_id, [result_val, overflow], &mut value_map);
                }
                NativeInstKind::Snego(snego) => {
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
                    insert_clif_results(function, inst_id, [result_val, overflow], &mut value_map);
                }
                NativeInstKind::Uaddsat(uaddsat) => {
                    let lhs = resolve_value(function, *uaddsat.lhs(), &value_map, &mut builder)?;
                    let rhs = resolve_value(function, *uaddsat.rhs(), &value_map, &mut builder)?;
                    let (raw, overflow) = builder.ins().uadd_overflow(lhs, rhs);
                    let max = unsigned_max_value(builder.func.dfg.value_type(lhs), &mut builder);
                    let result_val = builder.ins().select(overflow, max, raw);
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Saddsat(saddsat) => {
                    let lhs = resolve_value(function, *saddsat.lhs(), &value_map, &mut builder)?;
                    let rhs = resolve_value(function, *saddsat.rhs(), &value_map, &mut builder)?;
                    let (raw, overflow) = builder.ins().sadd_overflow(lhs, rhs);
                    let ty = builder.func.dfg.value_type(lhs);
                    let zero = scalar_constant(ty, 0, &mut builder);
                    let lhs_neg = builder.ins().icmp(IntCC::SignedLessThan, lhs, zero);
                    let min = signed_min_value(ty, &mut builder);
                    let max = signed_max_value(ty, &mut builder);
                    let sat = builder.ins().select(lhs_neg, min, max);
                    let result_val = builder.ins().select(overflow, sat, raw);
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Usubsat(usubsat) => {
                    let lhs = resolve_value(function, *usubsat.lhs(), &value_map, &mut builder)?;
                    let rhs = resolve_value(function, *usubsat.rhs(), &value_map, &mut builder)?;
                    let (raw, overflow) = builder.ins().usub_overflow(lhs, rhs);
                    let ty = builder.func.dfg.value_type(lhs);
                    let zero = scalar_constant(ty, 0, &mut builder);
                    let result_val = builder.ins().select(overflow, zero, raw);
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Ssubsat(ssubsat) => {
                    let lhs = resolve_value(function, *ssubsat.lhs(), &value_map, &mut builder)?;
                    let rhs = resolve_value(function, *ssubsat.rhs(), &value_map, &mut builder)?;
                    let (raw, overflow) = builder.ins().ssub_overflow(lhs, rhs);
                    let ty = builder.func.dfg.value_type(lhs);
                    let zero = scalar_constant(ty, 0, &mut builder);
                    let lhs_neg = builder.ins().icmp(IntCC::SignedLessThan, lhs, zero);
                    let min = signed_min_value(ty, &mut builder);
                    let max = signed_max_value(ty, &mut builder);
                    let sat = builder.ins().select(lhs_neg, min, max);
                    let result_val = builder.ins().select(overflow, sat, raw);
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Umulsat(umulsat) => {
                    let lhs = resolve_value(function, *umulsat.lhs(), &value_map, &mut builder)?;
                    let rhs = resolve_value(function, *umulsat.rhs(), &value_map, &mut builder)?;
                    let (raw, overflow) = emit_scalar_mul_overflow(lhs, rhs, false, &mut builder);
                    let max = unsigned_max_value(builder.func.dfg.value_type(lhs), &mut builder);
                    let result_val = builder.ins().select(overflow, max, raw);
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::Smulsat(smulsat) => {
                    let lhs = resolve_value(function, *smulsat.lhs(), &value_map, &mut builder)?;
                    let rhs = resolve_value(function, *smulsat.rhs(), &value_map, &mut builder)?;
                    let (raw, overflow) = emit_scalar_mul_overflow(lhs, rhs, true, &mut builder);
                    let ty = builder.func.dfg.value_type(lhs);
                    let zero = scalar_constant(ty, 0, &mut builder);
                    let lhs_neg = builder.ins().icmp(IntCC::SignedLessThan, lhs, zero);
                    let rhs_neg = builder.ins().icmp(IntCC::SignedLessThan, rhs, zero);
                    let same_sign = builder.ins().icmp(IntCC::Equal, lhs_neg, rhs_neg);
                    let min = signed_min_value(ty, &mut builder);
                    let max = signed_max_value(ty, &mut builder);
                    let sat = builder.ins().select(same_sign, max, min);
                    let result_val = builder.ins().select(overflow, sat, raw);
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, result_val);
                    }
                }
                NativeInstKind::ObjLoad(obj_load) => {
                    let addr =
                        resolve_value(function, *obj_load.object(), &value_map, &mut builder)?;
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        let result_ty = function.dfg.value_ty(result);
                        if frame.forwards(result) {
                            value_map.insert(result, addr);
                        } else if uses_indirect_value_representation(&module.ctx, result_ty) {
                            let result_addr = frame.address(result, &mut builder)?;
                            copy_bytes(
                                addr,
                                result_addr,
                                value_storage_size(result_ty, &module.ctx)?,
                                target_config,
                                &mut builder,
                            );
                            value_map.insert(result, result_addr);
                        } else {
                            load_value(
                                result,
                                result_ty,
                                addr,
                                0,
                                &mut value_map,
                                pointer_type,
                                &mut builder,
                            )?;
                        }
                    }
                }
                NativeInstKind::ExtractValue(extract) => {
                    let base = resolve_operand(
                        function,
                        *extract.dest(),
                        &value_map,
                        target_config,
                        &mut builder,
                    )?;
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
                            load_value(
                                result,
                                result_ty,
                                base,
                                offset,
                                &mut value_map,
                                pointer_type,
                                &mut builder,
                            )?;
                        }
                    }
                }
                NativeInstKind::InsertValue(insert) => {
                    let Some(result) = function.dfg.inst_result(inst_id) else {
                        continue;
                    };
                    let result_ty = function.dfg.value_ty(result);
                    let source_value = *insert.dest();
                    // An insert result owns its storage. Its sole consumer in
                    // the same block continues construction there without
                    // changing an observable SSA snapshot (see `FrameSlots`).
                    let result_addr = if frame.continues_source(inst_id, source_value) {
                        resolve_value(function, source_value, &value_map, &mut builder)?
                    } else {
                        let address = frame.address(result, &mut builder)?;
                        let size = value_storage_size(result_ty, &module.ctx)?;
                        if is_undef(function, source_value) {
                            // An undef source is zero, but only the bytes no
                            // insert of the chain writes need zeroing.
                            let written = frame
                                .insert_chain(function, inst_id)
                                .map(|inst| {
                                    let NativeInstKind::InsertValue(insert) =
                                        native_inst_set().resolve_inst(function.dfg.inst(inst))
                                    else {
                                        return Err(
                                            "insert chain continues past insert_value".to_string()
                                        );
                                    };
                                    let idx = constant_value_index(
                                        function,
                                        *insert.idx(),
                                        "insert_value",
                                    )?;
                                    let (offset, elem_ty) =
                                        aggregate_elem_offset(&module.ctx, result_ty, idx)?;
                                    Ok((offset as u32, value_storage_size(elem_ty, &module.ctx)?))
                                })
                                .collect::<Result<_, String>>()?;
                            zero_unwritten(address, size, written, target_config, &mut builder);
                        } else {
                            store_indirect(
                                function,
                                source_value,
                                address,
                                size,
                                &value_map,
                                target_config,
                                &mut builder,
                            )?;
                        }
                        address
                    };

                    let idx = constant_value_index(function, *insert.idx(), "insert_value")?;
                    let (offset, elem_ty) = aggregate_elem_offset(&module.ctx, result_ty, idx)?;
                    let value_ty = function.dfg.value_ty(*insert.value());
                    if value_ty != elem_ty {
                        return Err(format!(
                            "insert_value element type mismatch: expected {elem_ty:?}, got {value_ty:?}"
                        ));
                    }

                    if uses_indirect_value_representation(&module.ctx, value_ty) {
                        let field_addr = builder.ins().iadd_imm_s(result_addr, i64::from(offset));
                        store_indirect(
                            function,
                            *insert.value(),
                            field_addr,
                            value_storage_size(value_ty, &module.ctx)?,
                            &value_map,
                            target_config,
                            &mut builder,
                        )?;
                    } else {
                        store_value(
                            function,
                            *insert.value(),
                            result_addr,
                            offset,
                            &value_map,
                            &mut builder,
                        )?;
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
                    let store_ty = *mstore.ty();
                    if frame.forwards(*mstore.value()) {
                        let src =
                            resolve_value(function, *mstore.value(), &value_map, &mut builder)?;
                        move_bytes(
                            src,
                            addr,
                            value_storage_size(store_ty, &module.ctx)?,
                            &mut builder,
                        );
                    } else if uses_indirect_value_representation(&module.ctx, store_ty) {
                        store_indirect(
                            function,
                            *mstore.value(),
                            addr,
                            value_storage_size(store_ty, &module.ctx)?,
                            &value_map,
                            target_config,
                            &mut builder,
                        )?;
                    } else {
                        store_value(function, *mstore.value(), addr, 0, &value_map, &mut builder)?;
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
                        if frame.forwards(result) {
                            value_map.insert(result, addr);
                        } else if uses_indirect_value_representation(&module.ctx, result_ty) {
                            let result_addr = frame.address(result, &mut builder)?;
                            copy_bytes(
                                addr,
                                result_addr,
                                value_storage_size(result_ty, &module.ctx)?,
                                target_config,
                                &mut builder,
                            );
                            value_map.insert(result, result_addr);
                        } else {
                            load_value(
                                result,
                                result_ty,
                                addr,
                                0,
                                &mut value_map,
                                pointer_type,
                                &mut builder,
                            )?;
                        }
                    }
                }
                NativeInstKind::ObjStore(obj_store) => {
                    let dest =
                        resolve_value(function, *obj_store.object(), &value_map, &mut builder)?;
                    let val_ty = function.dfg.value_ty(*obj_store.value());
                    if frame.forwards(*obj_store.value()) {
                        let src =
                            resolve_value(function, *obj_store.value(), &value_map, &mut builder)?;
                        move_bytes(
                            src,
                            dest,
                            value_storage_size(val_ty, &module.ctx)?,
                            &mut builder,
                        );
                    } else if uses_indirect_value_representation(&module.ctx, val_ty) {
                        store_indirect(
                            function,
                            *obj_store.value(),
                            dest,
                            value_storage_size(val_ty, &module.ctx)?,
                            &value_map,
                            target_config,
                            &mut builder,
                        )?;
                    } else {
                        store_value(
                            function,
                            *obj_store.value(),
                            dest,
                            0,
                            &value_map,
                            &mut builder,
                        )?;
                    }
                }
                NativeInstKind::ObjAlloc(obj_alloc) => {
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        let slot = builder.create_sized_stack_slot(stack_slot_data(
                            *obj_alloc.ty(),
                            &module.ctx,
                        )?);
                        value_map.insert(result, builder.ins().stack_addr(pointer_type, slot, 0));
                    }
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
                            load_value(
                                result,
                                result_ty,
                                addr,
                                0,
                                &mut value_map,
                                pointer_type,
                                &mut builder,
                            )?;
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
                NativeInstKind::ObjMaterializeStack(materialize) => {
                    let value =
                        resolve_value(function, *materialize.object(), &value_map, &mut builder)?;
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, value);
                    }
                }
                NativeInstKind::MemAllocDynamic(allocate) => {
                    let size = if function.dfg.value_ty(*allocate.size()) == Type::I256 {
                        let [low, high, upper, top] =
                            resolve_i256(function, *allocate.size(), &value_map, &mut builder)?;
                        let high = builder.ins().bor(high, upper);
                        let high = builder.ins().bor(high, top);
                        builder.ins().trapnz(high, TrapCode::user(2).unwrap());
                        low
                    } else {
                        let size =
                            resolve_value(function, *allocate.size(), &value_map, &mut builder)?;
                        if builder.func.dfg.value_type(size).bits() > pointer_type.bits() {
                            let high = builder
                                .ins()
                                .ushr_imm_u(size, i64::from(pointer_type.bits()));
                            let overflow = builder.ins().icmp_imm_u(IntCC::NotEqual, high, 0);
                            builder.ins().trapnz(overflow, TrapCode::user(2).unwrap());
                        }
                        resize_int_value(size, pointer_type, false, &mut builder)
                    };
                    let address = heap_allocate(module, size, clif_module, &mut builder)?;
                    if let Some(result) = function.dfg.inst_result(inst_id) {
                        value_map.insert(result, address);
                    }
                }
            }
            // Canonicalize every producer, including loads, casts, and call
            // results. Phi inputs are already canonical on their incoming edges.
            for &result in function.dfg.inst_results(inst_id) {
                let ty = function.dfg.value_ty(result);
                if ty == Type::I1 {
                    let value = normalize_scalar(value_map[&result], ty, &mut builder);
                    value_map.insert(result, value);
                }
            }
        }
    }

    builder.seal_all_blocks();
    builder.finalize(clif_module.target_config());

    if module.ctx.triple == TargetTriple::SP1 {
        // SP1 objects are statically linked within PC-relative relocation range.
        // Far RV64 references embed address literals in executable text, which
        // SP1 would decode as instructions. Include frontend-created libcalls
        // and imported globals, not just explicit Sonatina call instructions.
        for data in ctx.func.dfg.ext_funcs.values_mut() {
            data.colocated = true;
        }
        for data in ctx.func.global_values.values_mut() {
            if let clif::GlobalValueData::Symbol { colocated, .. } = data {
                *colocated = true;
            }
        }
    }

    if std::env::var("DUMP_CLIF").is_ok() {
        let name = module.ctx.func_sig(func_ref, |sig| sig.name().to_string());
        eprintln!("[cranelift] CLIF IR for {name}:\n{}", ctx.func.display());
    }

    Ok(ctx)
}

fn heap_allocate(
    module: &Module,
    size: clif::Value,
    clif_module: &mut impl ClifModule,
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    if module.ctx.triple == TargetTriple::SP1 {
        return Err("host heap allocation is unavailable on SP1".into());
    }
    if module.funcs().iter().any(|&func| {
        module.ctx.func_sig(func, |sig| {
            sig.name() == "malloc" && !sig.linkage().is_external()
        })
    }) {
        return Err("native heap allocation requires the host malloc symbol".into());
    }
    let pointer_type = clif_module.target_config().pointer_type();
    let mut signature = clif_module.make_signature();
    signature.params.push(clif::AbiParam::new(pointer_type));
    signature.returns.push(clif::AbiParam::new(pointer_type));
    let allocator = clif_module
        .declare_function("malloc", Linkage::Import, &signature)
        .map_err(|error| format!("failed to declare native allocator: {error}"))?;
    let allocator = clif_module.declare_func_in_func(allocator, builder.func);
    // Give even zero-sized allocations an address and trap on allocation failure.
    let empty = builder.ins().icmp_imm_u(IntCC::Equal, size, 0);
    let one = builder.ins().iconst(pointer_type, 1);
    let size = builder.ins().select(empty, one, size);
    let call = builder.ins().call(allocator, &[size]);
    let address = builder.inst_results(call)[0];
    builder.ins().trapz(address, TrapCode::user(2).unwrap());
    Ok(address)
}

/// Translates a division or remainder. Cranelift divides only up to 64
/// bits; wider operands use the module's divider.
#[allow(clippy::too_many_arguments)]
fn translate_div_rem(
    kind: DivRemKind,
    lhs: ValueId,
    rhs: ValueId,
    inst_id: InstId,
    function: &Function,
    value_map: &mut ValueMap,
    divider: &mut Divider,
    clif_module: &mut impl ClifModule,
    builder: &mut FunctionBuilder,
) -> Result<(), String> {
    let result = function
        .dfg
        .inst_result(inst_id)
        .ok_or("division has no result")?;
    match function.dfg.value_ty(lhs) {
        Type::I256 => {
            let lhs = resolve_i256(function, lhs, value_map, builder)?;
            let rhs = resolve_i256(function, rhs, value_map, builder)?;
            let call = divider.call(clif_module, builder, Numerator::Word)?;
            value_map.insert_limbs(result, div_rem(kind, lhs, rhs, call, builder));
        }
        Type::I128 => {
            let lhs = resolve_value(function, lhs, value_map, builder)?;
            let rhs = resolve_value(function, rhs, value_map, builder)?;
            let call = divider.call(clif_module, builder, Numerator::Word)?;
            value_map.insert(result, div_rem_i128(kind, lhs, rhs, call, builder));
        }
        ty => {
            let lhs = resolve_value(function, lhs, value_map, builder)?;
            let rhs = resolve_value(function, rhs, value_map, builder)?;
            value_map.insert(result, emit_scalar_div_rem(lhs, rhs, ty, kind, builder));
        }
    }
    Ok(())
}

type ModularOp = fn(Limbs, Limbs, Limbs, DividerCall, &mut FunctionBuilder) -> Limbs;

/// Translates `evm_add_mod` or `evm_mul_mod`. Narrower operands are
/// zero-extended to i256, and the result, below the modulus, truncated.
#[allow(clippy::too_many_arguments)]
fn translate_modular(
    op: ModularOp,
    operands: [ValueId; 3],
    inst_id: InstId,
    function: &Function,
    value_map: &mut ValueMap,
    divider: &mut Divider,
    clif_module: &mut impl ClifModule,
    builder: &mut FunctionBuilder,
) -> Result<(), String> {
    let result = function
        .dfg
        .inst_result(inst_id)
        .ok_or("modular arithmetic has no result")?;
    let ty = function.dfg.value_ty(operands[0]);
    let operand = |value, builder: &mut FunctionBuilder| {
        if ty == Type::I256 {
            resolve_i256(function, value, value_map, builder)
        } else {
            resolve_value(function, value, value_map, builder)
                .map(|value| extend_to_limbs(value, ty, false, builder))
        }
    };
    let [lhs, rhs, modulus] = operands;
    let lhs = operand(lhs, builder)?;
    let rhs = operand(rhs, builder)?;
    let modulus = operand(modulus, builder)?;
    let call = divider.call(clif_module, builder, Numerator::Double)?;
    let limbs = op(lhs, rhs, modulus, call, builder);
    if ty == Type::I256 {
        value_map.insert_limbs(result, limbs);
    } else {
        let clif_ty = sonatina_scalar_type_to_clif_or_err(ty)?;
        value_map.insert(result, truncate_limbs(limbs, clif_ty, builder));
    }
    Ok(())
}

/// Extends `from` to `to`, which may be i256.
#[allow(clippy::too_many_arguments)]
fn translate_extend(
    from: ValueId,
    to: Type,
    signed: bool,
    inst_id: InstId,
    function: &Function,
    value_map: &mut ValueMap,
    pointer_type: clif::Type,
    builder: &mut FunctionBuilder,
) -> Result<(), String> {
    let result = function
        .dfg
        .inst_result(inst_id)
        .ok_or("extension has no result")?;
    let from_ty = function.dfg.value_ty(from);
    let value = resolve_value(function, from, value_map, builder)?;
    if to == Type::I256 {
        value_map.insert_limbs(result, extend_to_limbs(value, from_ty, signed, builder));
    } else {
        let to_ty = sonatina_type_to_clif_or_err(to, pointer_type)?;
        let extended = if from_ty == Type::I1 {
            bool_to_int_value(value, to_ty, signed, builder)
        } else {
            resize_int_value(value, to_ty, signed, builder)
        };
        value_map.insert(result, extended);
    }
    Ok(())
}

fn resolve_scalar_value(
    module: &Module,
    function: &Function,
    value_id: ValueId,
    value_map: &ValueMap,
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
    value_map: &ValueMap,
    pointer_type: clif::Type,
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    let val = if function.dfg.value_ty(value_id) == Type::I256 {
        resolve_i256(function, value_id, value_map, builder)?[0]
    } else {
        resolve_value(function, value_id, value_map, builder)?
    };
    Ok(resize_int_value(val, pointer_type, false, builder))
}

#[allow(clippy::too_many_arguments)]
fn translate_icmp(
    cc: IntCC,
    lhs: ValueId,
    rhs: ValueId,
    inst_id: InstId,
    module: &Module,
    function: &Function,
    value_map: &mut ValueMap,
    pointer_type: clif::Type,
    builder: &mut FunctionBuilder,
) -> Result<(), String> {
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
        lhs_val = signed_scalar(lhs_val, function.dfg.value_ty(lhs), builder);
        rhs_val = signed_scalar(rhs_val, function.dfg.value_ty(rhs), builder);
    }
    let result_val = builder.ins().icmp(cc, lhs_val, rhs_val);
    if let Some(result) = function.dfg.inst_result(inst_id) {
        value_map.insert(result, result_val);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use sonatina_ir::inst::{arith::Shl, downcast};

    use super::shift_count_in_range;

    #[test]
    fn masked_and_scaled_counts_stay_below_the_width() {
        let source = r#"target = "x86_64-unknown-native"
func public %f(v0.i64, v1.i64, v2.i32) -> i64 {
block0:
    v3.i64 = and v1 63.i64;
    v4.i64 = shl v3 v0;
    v5.i64 = and v1 7.i64;
    v6.i64 = shl 3.i64 v5;
    v7.i64 = shl v6 v4;
    v8.i64 = shl v1 v7;
    v9.i64 = and v1 64.i64;
    v10.i64 = shl v9 v8;
    v11.i32 = and v2 31.i32;
    v12.i32 = shl v11 v2;
    v13.i64 = zext v12 i64;
    v14.i64 = add v10 v13;
    return v14;
}
"#;
        let module = sonatina_parser::parse_module(source).unwrap().module;
        let func = module.funcs()[0];
        module.func_store.view(func, |function| {
            let mut known_bits = None;
            let in_range: Vec<_> = function
                .layout
                .iter_block()
                .flat_map(|block| function.layout.iter_inst(block))
                .filter_map(|inst| {
                    downcast::<&Shl>(function.inst_set(), function.dfg.inst(inst))
                        .filter(|shl| function.dfg.value_imm(*shl.bits()).is_none())
                        .map(|shl| {
                            shift_count_in_range(
                                function,
                                *shl.bits(),
                                *shl.value(),
                                &mut known_bits,
                            )
                        })
                })
                .collect();
            // `& 63`, `(& 7) << 3` and `& 31` fit; an unmasked count and
            // `& 64`, which may equal the width, do not.
            assert_eq!(in_range, [true, true, false, false, true]);
        });
    }
}
