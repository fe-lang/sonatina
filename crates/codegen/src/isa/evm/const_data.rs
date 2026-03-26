use rustc_hash::FxHashMap;
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    Function, GlobalVariableRef, I256, Immediate, InstId, Linkage, Module, Type, Value, ValueId,
    global_variable::{GlobalVariableData, GvInitializer},
    inst::{arith, cast, data, downcast, evm},
    types::CompoundType,
};

#[derive(Debug, Clone)]
enum ConstPathStep {
    Field(usize),
    IndexConst(usize),
    IndexValue(ValueId),
}

#[derive(Debug, Clone)]
struct ConstPath {
    global: GlobalVariableRef,
    ty: Type,
    steps: Vec<ConstPathStep>,
}

#[derive(Default)]
pub(crate) struct ConstDataLower {
    word_blobs: FxHashMap<GlobalVariableRef, GlobalVariableRef>,
}

impl ConstDataLower {
    pub(crate) fn run(&mut self, module: &Module) -> bool {
        let mut changed = false;
        for func_ref in module.funcs() {
            changed |= module
                .func_store
                .modify(func_ref, |func| self.rewrite_function(module, func));
        }
        changed
    }

    fn rewrite_function(&mut self, module: &Module, func: &mut Function) -> bool {
        let mut changed = false;
        let blocks: Vec<_> = func.layout.iter_block().collect();
        for block in blocks {
            let insts: Vec<_> = func.layout.iter_inst(block).collect();
            for inst in insts {
                if !func.layout.is_inst_inserted(inst) {
                    continue;
                }
                changed |= self.rewrite_inst(module, func, inst);
            }
        }

        if changed {
            func.rebuild_users();
        }
        changed |= cleanup_dead_const_refs(func);
        if changed {
            func.rebuild_users();
        }
        assert_no_const_ops(func);
        changed
    }

    fn rewrite_inst(&mut self, module: &Module, func: &mut Function, inst: InstId) -> bool {
        if let Some(load) =
            downcast::<&data::ConstLoad>(func.inst_set(), func.dfg.inst(inst)).cloned()
        {
            return self.rewrite_const_load(module, func, inst, *load.object());
        }
        if let Some(init) =
            downcast::<&data::ObjInitConst>(func.inst_set(), func.dfg.inst(inst)).cloned()
        {
            return self.rewrite_obj_init_const(module, func, inst, *init.object(), *init.value());
        }
        false
    }

    fn rewrite_const_load(
        &mut self,
        module: &Module,
        func: &mut Function,
        inst: InstId,
        object: ValueId,
    ) -> bool {
        let path = resolve_const_path(func, object)
            .unwrap_or_else(|| panic!("unsupported const.load source at inst {}", inst.as_u32()));
        let result_ty = func
            .dfg
            .inst_result(inst)
            .map(|result| func.dfg.value_ty(result))
            .expect("const.load must have a result");
        if let Some(imm) = eval_const_path_immediate(module, &path) {
            let replacement = func.dfg.make_imm_value(imm);
            replace_with_alias(func, inst, replacement);
            return true;
        }

        let (const_offset_bytes, dynamic_terms) = scalar_const_path_offset_bytes(module, &path)
            .unwrap_or_else(|| {
                panic!(
                    "unsupported dynamic const.load path for global {}",
                    path.global.as_u32()
                )
            });
        let blob = self.word_blob_global(module, path.global);
        let scratch = insert_before_one(
            func,
            inst,
            data::Alloca::new_unchecked(func.inst_set(), Type::I256),
            Type::I256.to_ptr(func.ctx()),
        );
        let mut code_offset = insert_before_one(
            func,
            inst,
            data::SymAddr::new_unchecked(func.inst_set(), data::SymbolRef::Global(blob)),
            func.ctx().type_layout.pointer_repl(),
        );
        if const_offset_bytes != 0 {
            let const_offset = imm_i256(func, const_offset_bytes);
            code_offset = add_i256(func, inst, code_offset, const_offset);
        }
        for (value, stride_bytes) in dynamic_terms {
            let term = zext_to_i256(func, inst, value);
            let term = if stride_bytes == 1 {
                term
            } else {
                let stride = imm_i256(func, stride_bytes);
                mul_i256(func, inst, term, stride)
            };
            code_offset = add_i256(func, inst, code_offset, term);
        }
        let copy_len = imm_i256(func, 32);
        insert_before_no_result(
            func,
            inst,
            evm::EvmCodeCopy::new_unchecked(func.inst_set(), scratch, code_offset, copy_len),
        );
        let replacement = insert_before_one(
            func,
            inst,
            data::Mload::new_unchecked(func.inst_set(), scratch, result_ty),
            result_ty,
        );
        replace_with_alias(func, inst, replacement);
        true
    }

    fn rewrite_obj_init_const(
        &mut self,
        module: &Module,
        func: &mut Function,
        inst: InstId,
        object: ValueId,
        value: ValueId,
    ) -> bool {
        let path = resolve_const_path(func, value).unwrap_or_else(|| {
            panic!(
                "unsupported obj.init.const source at inst {}",
                inst.as_u32()
            )
        });
        let (ty, init) = eval_const_path_subtree(module, &path).unwrap_or_else(|| {
            panic!(
                "obj.init.const currently requires a statically-known const path (global {})",
                path.global.as_u32()
            )
        });
        emit_obj_init(func, inst, object, ty, &init);
        remove_inst(func, inst);
        true
    }

    fn word_blob_global(
        &mut self,
        module: &Module,
        source: GlobalVariableRef,
    ) -> GlobalVariableRef {
        if let Some(&blob) = self.word_blobs.get(&source) {
            return blob;
        }

        let (source_symbol, ty, init) = module.ctx.with_gv_store(|store| {
            let data = store.gv_data(source);
            (
                data.symbol.clone(),
                data.ty,
                data.initializer
                    .clone()
                    .expect("const global must have initializer"),
            )
        });
        let mut bytes = Vec::new();
        encode_const_words(module, ty, &init, &mut bytes).unwrap_or_else(|| {
            panic!(
                "unsupported const-word encoding for global {}",
                source.as_u32()
            )
        });
        let blob_ty = module
            .ctx
            .with_ty_store_mut(|store| store.make_array(Type::I8, bytes.len()));
        let blob_init = GvInitializer::make_array(
            bytes
                .into_iter()
                .map(|byte| GvInitializer::make_imm(byte as i8))
                .collect(),
        );
        let symbol = format!("__sonatina_const_words_{source_symbol}_{}", source.as_u32());
        let blob = module.ctx.with_gv_store_mut(|store| {
            store.lookup_gv(&symbol).unwrap_or_else(|| {
                store.make_gv(GlobalVariableData::constant(
                    symbol,
                    blob_ty,
                    Linkage::Private,
                    blob_init,
                ))
            })
        });
        self.word_blobs.insert(source, blob);
        blob
    }
}

fn resolve_const_path(func: &Function, value: ValueId) -> Option<ConstPath> {
    let inst = func.dfg.value_inst(value)?;
    if let Some(const_ref) = downcast::<&data::ConstRef>(func.inst_set(), func.dfg.inst(inst)) {
        let global = const_ref.global().gv();
        return Some(ConstPath {
            global,
            ty: func.ctx().with_gv_store(|store| store.ty(global)),
            steps: Vec::new(),
        });
    }
    if let Some(proj) = downcast::<&data::ConstProj>(func.inst_set(), func.dfg.inst(inst)) {
        let (&base, rest) = proj.values().split_first()?;
        let mut path = resolve_const_path(func, base)?;
        let mut current_ty = path.ty;
        for &idx_value in rest {
            let (next_ty, step) = const_child_path_step(func, current_ty, idx_value)?;
            current_ty = next_ty;
            path.steps.push(step);
        }
        path.ty = current_ty;
        return Some(path);
    }
    if let Some(index) = downcast::<&data::ConstIndex>(func.inst_set(), func.dfg.inst(inst)) {
        let mut path = resolve_const_path(func, *index.object())?;
        let (next_ty, step) = const_child_path_step(func, path.ty, *index.index())?;
        path.ty = next_ty;
        path.steps.push(step);
        return Some(path);
    }
    None
}

fn const_child_path_step(
    func: &Function,
    current_ty: Type,
    idx_value: ValueId,
) -> Option<(Type, ConstPathStep)> {
    let idx_imm = func
        .dfg
        .value_imm(idx_value)
        .filter(|imm| !imm.is_negative())
        .map(Immediate::as_usize);
    match current_ty.resolve_compound(func.ctx())? {
        CompoundType::Array { elem, len } => {
            let step = match idx_imm {
                Some(idx) if idx < len => ConstPathStep::IndexConst(idx),
                Some(_) => return None,
                None => ConstPathStep::IndexValue(idx_value),
            };
            Some((elem, step))
        }
        CompoundType::Struct(s) => {
            if s.packed {
                return None;
            }
            let idx = idx_imm?;
            Some((*s.fields.get(idx)?, ConstPathStep::Field(idx)))
        }
        CompoundType::Ptr(_)
        | CompoundType::ObjRef(_)
        | CompoundType::ConstRef(_)
        | CompoundType::Enum(_)
        | CompoundType::Func { .. } => None,
    }
}

fn eval_const_path_immediate(module: &Module, path: &ConstPath) -> Option<Immediate> {
    let (ty, init) = eval_const_path_subtree(module, path)?;
    match init {
        GvInitializer::Immediate(imm) if imm.ty() == ty => Some(imm),
        _ => None,
    }
}

fn eval_const_path_subtree(module: &Module, path: &ConstPath) -> Option<(Type, GvInitializer)> {
    module.ctx.with_gv_store(|store| {
        let ty = store.ty(path.global);
        let init = store.init_data(path.global)?;
        eval_initializer_subtree(&module.ctx, ty, init, &path.steps)
    })
}

fn eval_initializer_subtree(
    module: &sonatina_ir::module::ModuleCtx,
    ty: Type,
    init: &GvInitializer,
    steps: &[ConstPathStep],
) -> Option<(Type, GvInitializer)> {
    let Some((step, rest)) = steps.split_first() else {
        return Some((ty, init.clone()));
    };
    match (ty.resolve_compound(module)?, init, step) {
        (
            CompoundType::Array { elem, len },
            GvInitializer::Array(items),
            ConstPathStep::IndexConst(idx),
        ) => {
            (*idx < len).then_some(())?;
            eval_initializer_subtree(module, elem, items.get(*idx)?, rest)
        }
        (CompoundType::Struct(s), GvInitializer::Struct(fields), ConstPathStep::Field(idx)) => {
            if s.packed {
                return None;
            }
            eval_initializer_subtree(module, *s.fields.get(*idx)?, fields.get(*idx)?, rest)
        }
        _ => None,
    }
}

fn scalar_const_path_offset_bytes(
    module: &Module,
    path: &ConstPath,
) -> Option<(u32, Vec<(ValueId, u32)>)> {
    let mut current_ty = module.ctx.with_gv_store(|store| store.ty(path.global));
    let mut const_offset = 0u32;
    let mut dynamic_terms = Vec::new();
    for step in &path.steps {
        match (current_ty.resolve_compound(&module.ctx)?, step) {
            (CompoundType::Array { elem, len }, ConstPathStep::IndexConst(idx)) => {
                if *idx >= len {
                    return None;
                }
                let stride = const_leaf_count(&module.ctx, elem)?.checked_mul(32)?;
                const_offset =
                    const_offset.checked_add(u32::try_from(*idx).ok()?.checked_mul(stride)?)?;
                current_ty = elem;
            }
            (CompoundType::Array { elem, .. }, ConstPathStep::IndexValue(value)) => {
                let stride = const_leaf_count(&module.ctx, elem)?.checked_mul(32)?;
                dynamic_terms.push((*value, stride));
                current_ty = elem;
            }
            (CompoundType::Struct(s), ConstPathStep::Field(idx)) => {
                if s.packed {
                    return None;
                }
                let field_ty = *s.fields.get(*idx)?;
                for &prev in s.fields.iter().take(*idx) {
                    const_offset = const_offset
                        .checked_add(const_leaf_count(&module.ctx, prev)?.checked_mul(32)?)?;
                }
                current_ty = field_ty;
            }
            _ => return None,
        }
    }
    current_ty
        .is_integral()
        .then_some((const_offset, dynamic_terms))
}

fn const_leaf_count(module: &sonatina_ir::module::ModuleCtx, ty: Type) -> Option<u32> {
    if ty.is_integral() {
        return Some(1);
    }
    match ty.resolve_compound(module)? {
        CompoundType::Array { elem, len } => {
            const_leaf_count(module, elem)?.checked_mul(u32::try_from(len).ok()?)
        }
        CompoundType::Struct(s) => {
            if s.packed {
                return None;
            }
            s.fields.into_iter().try_fold(0u32, |count, field| {
                count.checked_add(const_leaf_count(module, field)?)
            })
        }
        CompoundType::Ptr(_)
        | CompoundType::ObjRef(_)
        | CompoundType::ConstRef(_)
        | CompoundType::Enum(_)
        | CompoundType::Func { .. } => None,
    }
}

fn encode_const_words(
    module: &Module,
    ty: Type,
    init: &GvInitializer,
    out: &mut Vec<u8>,
) -> Option<()> {
    if ty.is_integral() {
        let GvInitializer::Immediate(imm) = init else {
            return None;
        };
        if imm.ty() != ty {
            return None;
        }
        out.extend_from_slice(&imm.as_i256().to_u256().to_big_endian());
        return Some(());
    }

    match (ty.resolve_compound(&module.ctx)?, init) {
        (CompoundType::Array { elem, len }, GvInitializer::Array(items)) => {
            if items.len() != len {
                return None;
            }
            for item in items {
                encode_const_words(module, elem, item, out)?;
            }
            Some(())
        }
        (CompoundType::Struct(s), GvInitializer::Struct(fields)) => {
            if s.packed || fields.len() != s.fields.len() {
                return None;
            }
            for (field_ty, field) in s.fields.into_iter().zip(fields) {
                encode_const_words(module, field_ty, field, out)?;
            }
            Some(())
        }
        _ => None,
    }
}

fn emit_obj_init(
    func: &mut Function,
    before: InstId,
    object: ValueId,
    ty: Type,
    init: &GvInitializer,
) {
    if ty.is_integral() {
        let GvInitializer::Immediate(imm) = init else {
            panic!("integral obj.init.const source must be immediate");
        };
        let value = func.dfg.make_imm_value(*imm);
        insert_before_no_result(
            func,
            before,
            data::ObjStore::new_unchecked(func.inst_set(), object, value),
        );
        return;
    }

    match (ty.resolve_compound(func.ctx()), init) {
        (Some(CompoundType::Array { elem, len }), GvInitializer::Array(items)) => {
            assert_eq!(items.len(), len, "array initializer length mismatch");
            for (idx, item) in items.iter().enumerate() {
                let index = func
                    .dfg
                    .make_imm_value(Immediate::I64(i64::try_from(idx).expect("index overflow")));
                let slot = insert_before_one(
                    func,
                    before,
                    data::ObjIndex::new_unchecked(func.inst_set(), object, index),
                    elem.to_obj_ref(func.ctx()),
                );
                emit_obj_init(func, before, slot, elem, item);
            }
        }
        (Some(CompoundType::Struct(s)), GvInitializer::Struct(fields)) => {
            assert!(
                !s.packed,
                "packed structs are unsupported in obj.init.const"
            );
            assert_eq!(
                fields.len(),
                s.fields.len(),
                "struct initializer length mismatch"
            );
            for (idx, (field_ty, field)) in s.fields.iter().copied().zip(fields.iter()).enumerate()
            {
                let index = func
                    .dfg
                    .make_imm_value(Immediate::I64(i64::try_from(idx).expect("index overflow")));
                let slot = insert_before_one(
                    func,
                    before,
                    data::ObjProj::new_unchecked(func.inst_set(), smallvec![object, index]),
                    field_ty.to_obj_ref(func.ctx()),
                );
                emit_obj_init(func, before, slot, field_ty, field);
            }
        }
        _ => panic!("unsupported obj.init.const type {ty:?}"),
    }
}

fn cleanup_dead_const_refs(func: &mut Function) -> bool {
    let mut changed = false;
    loop {
        let mut removed_any = false;
        let blocks: Vec<_> = func.layout.iter_block().collect();
        for block in blocks {
            let insts: Vec<_> = func.layout.iter_inst(block).collect();
            for inst in insts {
                if !func.layout.is_inst_inserted(inst) {
                    continue;
                }
                let is_const_ref =
                    downcast::<&data::ConstRef>(func.inst_set(), func.dfg.inst(inst)).is_some()
                        || downcast::<&data::ConstProj>(func.inst_set(), func.dfg.inst(inst))
                            .is_some()
                        || downcast::<&data::ConstIndex>(func.inst_set(), func.dfg.inst(inst))
                            .is_some();
                if !is_const_ref {
                    continue;
                }
                let Some(result) = func.dfg.inst_result(inst) else {
                    continue;
                };
                if func.dfg.users_num(result) != 0 {
                    continue;
                }
                remove_inst(func, inst);
                removed_any = true;
                changed = true;
            }
        }
        if !removed_any {
            return changed;
        }
    }
}

fn assert_no_const_ops(func: &Function) {
    for block in func.layout.iter_block() {
        for inst in func.layout.iter_inst(block) {
            if downcast::<&data::ConstRef>(func.inst_set(), func.dfg.inst(inst)).is_some()
                || downcast::<&data::ConstProj>(func.inst_set(), func.dfg.inst(inst)).is_some()
                || downcast::<&data::ConstIndex>(func.inst_set(), func.dfg.inst(inst)).is_some()
                || downcast::<&data::ConstLoad>(func.inst_set(), func.dfg.inst(inst)).is_some()
                || downcast::<&data::ObjInitConst>(func.inst_set(), func.dfg.inst(inst)).is_some()
            {
                panic!(
                    "const-data lowering invariant violated: high-level const instruction remained in function"
                );
            }
        }
    }
}

fn insert_before_results<I: sonatina_ir::Inst>(
    func: &mut Function,
    before: InstId,
    data: I,
    result_tys: &[Type],
) -> SmallVec<[ValueId; 2]> {
    let inst = func.dfg.make_inst(data);
    func.layout.insert_inst_before(inst, before);
    result_tys
        .iter()
        .enumerate()
        .map(|(idx, &ty)| {
            let value = func.dfg.make_value(Value::Inst {
                inst,
                result_idx: idx.try_into().expect("too many results"),
                ty,
            });
            func.dfg.append_result(inst, value);
            value
        })
        .collect()
}

fn insert_before_one<I: sonatina_ir::Inst>(
    func: &mut Function,
    before: InstId,
    data: I,
    result_ty: Type,
) -> ValueId {
    insert_before_results(func, before, data, &[result_ty])[0]
}

fn insert_before_no_result<I: sonatina_ir::Inst>(func: &mut Function, before: InstId, data: I) {
    let inst = func.dfg.make_inst(data);
    func.layout.insert_inst_before(inst, before);
}

fn remove_inst(func: &mut Function, inst: InstId) {
    func.layout.remove_inst(inst);
    func.erase_inst(inst);
}

fn replace_with_alias(func: &mut Function, inst: InstId, replacement: ValueId) {
    let result = func
        .dfg
        .inst_result(inst)
        .expect("instruction must have a result");
    func.dfg.change_to_alias(result, replacement);
    remove_inst(func, inst);
}

fn imm_i256(func: &mut Function, value: u32) -> ValueId {
    func.dfg
        .make_imm_value(Immediate::I256(I256::from(u64::from(value))))
}

fn zext_to_i256(func: &mut Function, before: InstId, value: ValueId) -> ValueId {
    if func.dfg.value_ty(value) == Type::I256 {
        value
    } else {
        insert_before_one(
            func,
            before,
            cast::Zext::new_unchecked(func.inst_set(), value, Type::I256),
            Type::I256,
        )
    }
}

fn add_i256(func: &mut Function, before: InstId, lhs: ValueId, rhs: ValueId) -> ValueId {
    insert_before_one(
        func,
        before,
        arith::Add::new_unchecked(func.inst_set(), lhs, rhs),
        Type::I256,
    )
}

fn mul_i256(func: &mut Function, before: InstId, lhs: ValueId, rhs: ValueId) -> ValueId {
    insert_before_one(
        func,
        before,
        arith::Mul::new_unchecked(func.inst_set(), lhs, rhs),
        Type::I256,
    )
}

#[cfg(test)]
mod tests {
    use super::ConstDataLower;
    use crate::{
        isa::evm::EvmBackend,
        object::{CompileOptions, compile_all_objects},
    };
    use sonatina_ir::{
        ir_writer::{FuncWriter, ModuleWriter},
        isa::evm::Evm,
        module::FuncRef,
    };
    use sonatina_parser::parse_module;
    use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

    fn parse(src: &str) -> sonatina_parser::ParsedModule {
        parse_module(src).unwrap_or_else(|errs| panic!("parse failed: {errs:?}"))
    }

    fn find_func_ref(parsed: &sonatina_parser::ParsedModule, name: &str) -> FuncRef {
        parsed
            .module
            .funcs()
            .into_iter()
            .find(|&func_ref| {
                parsed
                    .module
                    .ctx
                    .func_sig(func_ref, |sig| sig.name() == name)
            })
            .unwrap_or_else(|| panic!("function `{name}` should exist"))
    }

    fn test_backend() -> EvmBackend {
        let triple = TargetTriple::new(
            Architecture::Evm,
            Vendor::Ethereum,
            OperatingSystem::Evm(EvmVersion::Osaka),
        );
        EvmBackend::new(Evm::new(triple))
    }

    #[test]
    fn const_load_static_index_folds_to_immediate() {
        let parsed = parse(
            r#"
target = "evm-ethereum-osaka"

global private const [i256; 4] $arr = [1, 2, 3, 4];

func private %entry() -> i256 {
    block0:
        v0.constref<[i256; 4]> = const.ref $arr;
        v1.constref<i256> = const.index v0 2.i8;
        v2.i256 = const.load v1;
        return v2;
}
"#,
        );

        ConstDataLower::default().run(&parsed.module);

        let entry = find_func_ref(&parsed, "entry");
        let dumped = parsed
            .module
            .func_store
            .view(entry, |func| FuncWriter::new(entry, func).dump_string());
        assert!(dumped.contains("return 3.i256;"));
        assert!(!dumped.contains("const."));
    }

    #[test]
    fn const_load_dynamic_index_lowers_to_codecopy() {
        let parsed = parse(
            r#"
target = "evm-ethereum-osaka"

global private const [i256; 4] $arr = [1, 2, 3, 4];

func private %entry(v0.i256) -> i256 {
    block0:
        v1.constref<[i256; 4]> = const.ref $arr;
        v2.constref<i256> = const.index v1 v0;
        v3.i256 = const.load v2;
        return v3;
}
"#,
        );

        ConstDataLower::default().run(&parsed.module);

        let mut writer = ModuleWriter::with_debug_provider(&parsed.module, &parsed.debug);
        let dumped = writer.dump_string();
        assert!(dumped.contains("__sonatina_const_words_arr_"));
        assert!(dumped.contains("evm_code_copy"));
        assert!(dumped.contains("mload"));
        assert!(!dumped.contains("const."));
    }

    #[test]
    fn obj_init_const_lowers_to_obj_stores() {
        let parsed = parse(
            r#"
target = "evm-ethereum-osaka"

global private const [i256; 2] $arr = [11, 22];

func private %entry() -> i256 {
    block0:
        v0.objref<[i256; 2]> = obj.alloc [i256; 2];
        v1.constref<[i256; 2]> = const.ref $arr;
        obj.init.const v0 v1;
        v2.objref<i256> = obj.index v0 1.i8;
        v3.i256 = obj.load v2;
        return v3;
}
"#,
        );

        ConstDataLower::default().run(&parsed.module);

        let entry = find_func_ref(&parsed, "entry");
        let dumped = parsed
            .module
            .func_store
            .view(entry, |func| FuncWriter::new(entry, func).dump_string());
        assert!(!dumped.contains("obj.init.const"));
        assert!(dumped.contains("obj.store"));
        assert!(!dumped.contains("const."));
    }

    #[test]
    fn dynamic_const_load_object_compile_keeps_synthesized_blob_data_reachable() {
        let parsed = parse(
            r#"
target = "evm-ethereum-osaka"

global private const [i256; 4] $arr = [1, 2, 3, 4];

func private %entry(v0.i256) -> i256 {
    block0:
        v1.constref<[i256; 4]> = const.ref $arr;
        v2.constref<i256> = const.index v1 v0;
        v3.i256 = const.load v2;
        return v3;
}

object @Contract {
  section runtime { entry %entry; data $arr; }
}
"#,
        );

        let opts = CompileOptions::default();
        compile_all_objects(&parsed.module, &test_backend(), &opts)
            .expect("object compilation should include backend-synthesized const blobs");
    }
}
