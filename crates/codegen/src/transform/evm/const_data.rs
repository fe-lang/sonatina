use rustc_hash::FxHashMap;
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    Function, GlobalVariableRef, I256, Immediate, InstId, Linkage, Module, Type, Value, ValueId,
    global_variable::{GlobalVariableData, GlobalVariableStore, GvInitializer},
    inst::{arith, cast, data, downcast, evm},
    module::ModuleCtx,
    types::{CompoundType, CompoundTypeRef, StructData},
    visitor::VisitorMut,
};

use crate::{
    optim::const_eval::{
        ConstPath, ConstPathAnalysis, ConstPathStep, analyze_const_paths,
        collect_constref_value_tys, const_path_steps, eval_const_path_immediate,
        eval_const_path_subtree,
    },
    transform::aggregate::shape,
};

type ConstOffsetTerms = Vec<(ValueId, u32)>;
type ConstOffsetPlan = (Type, u32, ConstOffsetTerms);

#[derive(Debug, Clone)]
struct LoweredConstValue {
    addr: ValueId,
    ty: Type,
    path: Option<ConstPath>,
}

struct ConstRewriteCtx<'a> {
    constref_value_tys: &'a FxHashMap<ValueId, Type>,
    const_paths: &'a ConstPathAnalysis,
    lowered_values: &'a mut FxHashMap<ValueId, LoweredConstValue>,
}

impl ConstRewriteCtx<'_> {
    fn resolve(&self, value: ValueId) -> Option<LoweredConstValue> {
        self.lowered_values.get(&value).cloned().or_else(|| {
            self.constref_value_tys
                .get(&value)
                .copied()
                .map(|ty| LoweredConstValue {
                    addr: value,
                    ty,
                    path: self.const_paths.path(value).cloned(),
                })
        })
    }

    fn insert(&mut self, value: ValueId, lowered: LoweredConstValue) {
        self.lowered_values.insert(value, lowered);
    }

    fn remove(&mut self, value: ValueId) {
        self.lowered_values.remove(&value);
    }
}

#[derive(Default)]
struct ConstRefTypeLowerer {
    compound_map: FxHashMap<CompoundTypeRef, Type>,
}

impl ConstRefTypeLowerer {
    fn rewrite_type(&mut self, ctx: &ModuleCtx, ty: Type) -> Type {
        match ty {
            Type::Compound(compound) => self.rewrite_compound(ctx, compound),
            _ => ty,
        }
    }

    fn rewrite_compound(&mut self, ctx: &ModuleCtx, compound: CompoundTypeRef) -> Type {
        if let Some(&mapped) = self.compound_map.get(&compound) {
            return mapped;
        }

        let current = ctx.with_ty_store(|store| store.resolve_compound(compound).clone());
        self.compound_map.insert(compound, Type::Compound(compound));

        let mapped = match current {
            CompoundType::Array { elem, len } => {
                let elem = self.rewrite_type(ctx, elem);
                ctx.with_ty_store_mut(|store| store.make_array(elem, len))
            }
            CompoundType::Ptr(elem) => {
                let elem = self.rewrite_type(ctx, elem);
                ctx.with_ty_store_mut(|store| store.make_ptr(elem))
            }
            CompoundType::ObjRef(elem) => {
                let elem = self.rewrite_type(ctx, elem);
                ctx.with_ty_store_mut(|store| store.make_obj_ref(elem))
            }
            CompoundType::ConstRef(_) => ctx.type_layout.pointer_repl(),
            CompoundType::Enum(data) => {
                let new_variants: Vec<_> = data
                    .variants
                    .iter()
                    .map(|variant| sonatina_ir::types::VariantData {
                        name: variant.name.clone(),
                        explicit_discriminant: variant.explicit_discriminant,
                        fields: variant
                            .fields
                            .iter()
                            .map(|&field| self.rewrite_type(ctx, field))
                            .collect(),
                    })
                    .collect();
                if new_variants != data.variants {
                    ctx.with_ty_store_mut(|store| {
                        store.update_enum_variants(&data.name, &new_variants, data.repr)
                    });
                }
                Type::Compound(compound)
            }
            CompoundType::Func { args, ret_tys } => {
                let args: Vec<_> = args
                    .iter()
                    .map(|&arg| self.rewrite_type(ctx, arg))
                    .collect();
                let ret_tys: Vec<_> = ret_tys
                    .iter()
                    .map(|&ret| self.rewrite_type(ctx, ret))
                    .collect();
                ctx.with_ty_store_mut(|store| store.make_func(&args, &ret_tys))
            }
            CompoundType::Struct(StructData { name, fields, .. }) => {
                let fields: Vec<_> = fields
                    .iter()
                    .map(|&field| self.rewrite_type(ctx, field))
                    .collect();
                ctx.with_ty_store_mut(|store| store.update_struct_fields(&name, &fields));
                Type::Compound(compound)
            }
        };
        self.compound_map.insert(compound, mapped);
        mapped
    }
}

#[derive(Default)]
pub(crate) struct ConstDataLower {
    word_blobs: FxHashMap<GlobalVariableRef, GlobalVariableRef>,
}

impl ConstDataLower {
    pub(crate) fn run(&mut self, module: &Module) -> bool {
        let mut types = ConstRefTypeLowerer::default();
        let mut changed = rewrite_module_types(module, &mut types);
        for func_ref in module.funcs() {
            changed |= module.func_store.modify(func_ref, |func| {
                self.rewrite_function(module, func, &mut types)
            });
        }
        changed
    }

    fn rewrite_function(
        &mut self,
        module: &Module,
        func: &mut Function,
        types: &mut ConstRefTypeLowerer,
    ) -> bool {
        let constref_value_tys = collect_constref_value_tys(func);
        let const_paths = analyze_const_paths(func, &constref_value_tys);
        let mut changed = rewrite_function_types(func, types);
        let mut lowered_values = FxHashMap::default();
        let mut rewrite_ctx = ConstRewriteCtx {
            constref_value_tys: &constref_value_tys,
            const_paths: &const_paths,
            lowered_values: &mut lowered_values,
        };
        let blocks: Vec<_> = func.layout.iter_block().collect();
        for block in blocks {
            let insts: Vec<_> = func.layout.iter_inst(block).collect();
            for inst in insts {
                if !func.layout.is_inst_inserted(inst) {
                    continue;
                }
                changed |= self.rewrite_inst(module, func, inst, &mut rewrite_ctx);
            }
        }

        if changed {
            func.rebuild_users();
        }
        assert_no_const_ops(func);
        changed
    }

    fn rewrite_inst(
        &mut self,
        module: &Module,
        func: &mut Function,
        inst: InstId,
        rewrite_ctx: &mut ConstRewriteCtx<'_>,
    ) -> bool {
        if let Some(const_ref) =
            downcast::<&data::ConstRef>(func.inst_set(), func.dfg.inst(inst)).cloned()
        {
            return self.rewrite_const_ref(
                module,
                func,
                inst,
                const_ref.global().gv(),
                rewrite_ctx,
            );
        }
        if let Some(proj) =
            downcast::<&data::ConstProj>(func.inst_set(), func.dfg.inst(inst)).cloned()
        {
            return self.rewrite_const_proj(func, inst, &proj, rewrite_ctx);
        }
        if let Some(index) =
            downcast::<&data::ConstIndex>(func.inst_set(), func.dfg.inst(inst)).cloned()
        {
            return self.rewrite_const_index(
                func,
                inst,
                *index.object(),
                *index.index(),
                rewrite_ctx,
            );
        }
        if let Some(load) =
            downcast::<&data::ConstLoad>(func.inst_set(), func.dfg.inst(inst)).cloned()
        {
            return self.rewrite_const_load(module, func, inst, *load.object(), rewrite_ctx);
        }
        if let Some(init) =
            downcast::<&data::ObjInitConst>(func.inst_set(), func.dfg.inst(inst)).cloned()
        {
            return self.rewrite_obj_init_const(module, func, inst, init, rewrite_ctx);
        }
        false
    }

    fn rewrite_const_ref(
        &mut self,
        module: &Module,
        func: &mut Function,
        inst: InstId,
        global: GlobalVariableRef,
        rewrite_ctx: &mut ConstRewriteCtx<'_>,
    ) -> bool {
        let blob = self.word_blob_global(module, global);
        let replacement = insert_before_one(
            func,
            inst,
            data::SymAddr::new_unchecked(func.inst_set(), data::SymbolRef::Global(blob)),
            func.ctx().type_layout.pointer_repl(),
        );
        let result = func
            .dfg
            .inst_result(inst)
            .expect("const.ref must have a result");
        let ty = module.ctx.with_gv_store(|store| store.ty(global));
        rewrite_ctx.insert(
            replacement,
            LoweredConstValue {
                addr: replacement,
                ty,
                path: Some(ConstPath {
                    global,
                    ty,
                    steps: Vec::new(),
                }),
            },
        );
        replace_with_alias(func, inst, replacement);
        rewrite_ctx.remove(result);
        true
    }

    fn rewrite_const_proj(
        &mut self,
        func: &mut Function,
        inst: InstId,
        proj: &data::ConstProj,
        rewrite_ctx: &mut ConstRewriteCtx<'_>,
    ) -> bool {
        let Some((&base, rest)) = proj.values().split_first() else {
            panic!("const.proj requires a base operand");
        };
        self.rewrite_const_subref(func, inst, base, rest, rewrite_ctx)
    }

    fn rewrite_const_index(
        &mut self,
        func: &mut Function,
        inst: InstId,
        object: ValueId,
        index: ValueId,
        rewrite_ctx: &mut ConstRewriteCtx<'_>,
    ) -> bool {
        self.rewrite_const_subref(func, inst, object, &[index], rewrite_ctx)
    }

    fn rewrite_const_subref(
        &mut self,
        func: &mut Function,
        inst: InstId,
        base: ValueId,
        indices: &[ValueId],
        rewrite_ctx: &mut ConstRewriteCtx<'_>,
    ) -> bool {
        let base = rewrite_ctx.resolve(base).unwrap_or_else(|| {
            panic!(
                "unsupported const subreference source at inst {}",
                inst.as_u32()
            )
        });
        let (ty, steps) = const_path_steps(func, base.ty, indices).unwrap_or_else(|| {
            panic!(
                "unsupported const projection/index at inst {} (base_ty: {:?}, indices: {:?})",
                inst.as_u32(),
                base.ty,
                indices
                    .iter()
                    .map(|&index| func.dfg.value(index).clone())
                    .collect::<Vec<_>>(),
            )
        });
        let (_, const_offset_bytes, dynamic_terms) =
            const_steps_offset_bytes(func.ctx(), base.ty, &steps).unwrap_or_else(|| {
                panic!(
                    "unsupported const projection/index offset computation at inst {}",
                    inst.as_u32()
                )
            });
        let replacement = const_addr_with_offset(
            func,
            inst,
            base.addr,
            const_offset_bytes,
            dynamic_terms,
            true,
        );
        rewrite_ctx.insert(
            replacement,
            LoweredConstValue {
                addr: replacement,
                ty,
                path: base.path.map(|mut path| {
                    path.ty = ty;
                    path.steps.extend(steps);
                    path
                }),
            },
        );
        replace_with_alias(func, inst, replacement);
        true
    }

    fn rewrite_const_load(
        &mut self,
        module: &Module,
        func: &mut Function,
        inst: InstId,
        object: ValueId,
        rewrite_ctx: &mut ConstRewriteCtx<'_>,
    ) -> bool {
        let source = rewrite_ctx
            .resolve(object)
            .unwrap_or_else(|| panic!("unsupported const.load source at inst {}", inst.as_u32()));
        let result_ty = func
            .dfg
            .inst_result(inst)
            .map(|result| func.dfg.value_ty(result))
            .expect("const.load must have a result");
        if let Some(path) = source.path.as_ref()
            && let Some(imm) =
                eval_const_path_immediate(&module.ctx, path, |value| func.dfg.value_imm(value))
        {
            let replacement = func.dfg.make_imm_value(imm);
            replace_with_alias(func, inst, replacement);
            return true;
        }

        let replacement = emit_const_load_from_addr(func, inst, source.addr, result_ty, None);
        replace_with_alias(func, inst, replacement);
        true
    }

    fn rewrite_obj_init_const(
        &mut self,
        module: &Module,
        func: &mut Function,
        inst: InstId,
        init: data::ObjInitConst,
        rewrite_ctx: &mut ConstRewriteCtx<'_>,
    ) -> bool {
        let source = rewrite_ctx.resolve(*init.value()).unwrap_or_else(|| {
            panic!(
                "unsupported obj.init.const source at inst {}",
                inst.as_u32()
            )
        });
        if !source.ty.is_integral()
            && let Some(copy_len_bytes) = word_blob_copy_len_bytes(func.ctx(), source.ty)
        {
            emit_obj_init_from_codecopy(
                func,
                inst,
                *init.object(),
                source.ty,
                source.addr,
                copy_len_bytes,
            );
        } else if let Some(path) = source.path.as_ref()
            && let Some((ty, subtree_init)) =
                eval_const_path_subtree(&module.ctx, path, |value| func.dfg.value_imm(value))
        {
            emit_obj_init(func, inst, *init.object(), ty, &subtree_init);
        } else {
            emit_obj_init_from_addr(func, inst, *init.object(), source.ty, source.addr);
        }
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
        let symbol_base = format!("__sonatina_const_words_{source_symbol}_{}", source.as_u32());
        let blob = module.ctx.with_gv_store_mut(|store| {
            let symbol = fresh_global_symbol(store, &symbol_base);
            store.make_gv(GlobalVariableData::constant(
                symbol,
                blob_ty,
                Linkage::Private,
                blob_init,
            ))
        });
        self.word_blobs.insert(source, blob);
        blob
    }
}

fn fresh_global_symbol(store: &GlobalVariableStore, base: &str) -> String {
    if store.lookup_gv(base).is_none() {
        return base.to_string();
    }

    let mut suffix = 1u32;
    loop {
        let symbol = format!("{base}_{suffix}");
        if store.lookup_gv(&symbol).is_none() {
            return symbol;
        }
        suffix += 1;
    }
}

fn rewrite_module_types(module: &Module, types: &mut ConstRefTypeLowerer) -> bool {
    let mut changed = false;

    let funcs: Vec<_> = module
        .ctx
        .declared_funcs
        .iter()
        .map(|entry| *entry.key())
        .collect();
    for func in funcs {
        let Some(sig) = module.ctx.get_sig(func) else {
            continue;
        };
        let args: Vec<_> = sig
            .args()
            .iter()
            .map(|&arg| types.rewrite_type(&module.ctx, arg))
            .collect();
        let ret_tys: Vec<_> = sig
            .ret_tys()
            .iter()
            .map(|&ret| types.rewrite_type(&module.ctx, ret))
            .collect();
        if args.as_slice() == sig.args() && ret_tys.as_slice() == sig.ret_tys() {
            continue;
        }
        module
            .ctx
            .declared_funcs
            .get_mut(&func)
            .expect("missing function signature")
            .clone_from(&sonatina_ir::Signature::new(
                sig.name(),
                sig.linkage(),
                &args,
                &ret_tys,
            ));
        changed = true;
    }

    let globals: Vec<_> = module
        .ctx
        .with_gv_store(|store| store.all_gv_refs().collect());
    module.ctx.with_gv_store_mut(|store| {
        for gv in globals {
            let Some(gv_data) = store.get(gv).cloned() else {
                continue;
            };
            let new_ty = types.rewrite_type(&module.ctx, gv_data.ty);
            if new_ty != gv_data.ty {
                store.update_ty(gv, new_ty);
                changed = true;
            }
        }
    });

    changed
}

fn rewrite_function_types(func: &mut Function, types: &mut ConstRefTypeLowerer) -> bool {
    let mut changed = false;
    for value in func.dfg.value_ids().collect::<Vec<_>>() {
        let old_ty = func.dfg.value_ty(value);
        let new_ty = types.rewrite_type(func.ctx(), old_ty);
        if new_ty == old_ty {
            continue;
        }
        func.dfg.values[value] = match func.dfg.value(value).clone() {
            Value::Immediate { imm, .. } => Value::Immediate { imm, ty: new_ty },
            Value::Inst {
                inst, result_idx, ..
            } => Value::Inst {
                inst,
                result_idx,
                ty: new_ty,
            },
            Value::Arg { idx, .. } => Value::Arg { idx, ty: new_ty },
            Value::Global { gv, .. } => Value::Global { gv, ty: new_ty },
            Value::Undef { .. } => Value::Undef { ty: new_ty },
        };
        changed = true;
    }

    struct TypeVisitor<'a> {
        ctx: ModuleCtx,
        types: &'a mut ConstRefTypeLowerer,
        changed: bool,
    }

    impl VisitorMut for TypeVisitor<'_> {
        fn visit_ty(&mut self, item: &mut Type) {
            let new_ty = self.types.rewrite_type(&self.ctx, *item);
            self.changed |= new_ty != *item;
            *item = new_ty;
        }
    }

    let mut visitor = TypeVisitor {
        ctx: func.ctx().clone(),
        types,
        changed: false,
    };
    let blocks: Vec<_> = func.layout.iter_block().collect();
    for block in blocks {
        let insts: Vec<_> = func.layout.iter_inst(block).collect();
        for inst in insts {
            if func.layout.is_inst_inserted(inst) {
                func.dfg.inst_mut(inst).accept_mut(&mut visitor);
            }
        }
    }

    changed || visitor.changed
}

fn const_steps_offset_bytes(
    module: &ModuleCtx,
    base_ty: Type,
    steps: &[ConstPathStep],
) -> Option<ConstOffsetPlan> {
    let mut current_ty = base_ty;
    let mut const_offset = 0u32;
    let mut dynamic_terms = Vec::new();
    for step in steps {
        match (current_ty.resolve_compound(module)?, step) {
            (CompoundType::Array { elem, len }, ConstPathStep::IndexConst(idx)) => {
                if *idx >= len {
                    return None;
                }
                let stride = const_leaf_count(module, elem)?.checked_mul(32)?;
                const_offset =
                    const_offset.checked_add(u32::try_from(*idx).ok()?.checked_mul(stride)?)?;
                current_ty = elem;
            }
            (CompoundType::Array { elem, .. }, ConstPathStep::IndexValue(value)) => {
                let stride = const_leaf_count(module, elem)?.checked_mul(32)?;
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
                        .checked_add(const_leaf_count(module, prev)?.checked_mul(32)?)?;
                }
                current_ty = field_ty;
            }
            _ => return None,
        }
    }
    Some((current_ty, const_offset, dynamic_terms))
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
        out.extend_from_slice(&imm.zext(Type::I256).as_i256().to_u256().to_big_endian());
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

// EVM readonly const refs currently use word blobs: one 32-byte slot per scalar leaf.
// Bulk-copying into an object is only valid when the runtime object layout is exactly the
// same contiguous leaf layout, with no extra padding between recursively flattened fields.
fn word_blob_copy_len_bytes(module: &ModuleCtx, ty: Type) -> Option<u32> {
    if ty.is_integral() {
        return (module.size_of(ty).ok()? == 32).then_some(32);
    }

    match ty.resolve_compound(module)? {
        CompoundType::Array { elem, len } => {
            let elem_size = word_blob_copy_len_bytes(module, elem)?;
            let runtime_elem_size = shape::runtime_size_bytes(module, elem)?;
            let runtime_size = shape::runtime_size_bytes(module, ty)?;
            let total_size = elem_size.checked_mul(u32::try_from(len).ok()?)?;
            (runtime_elem_size == elem_size && runtime_size == total_size).then_some(total_size)
        }
        CompoundType::Struct(s) => {
            if s.packed {
                return None;
            }

            let mut total_size = 0u32;
            for (idx, field_ty) in s.fields.iter().copied().enumerate() {
                let (field_offset, _) =
                    shape::struct_field_offset_bytes(&s.fields, s.packed, idx, module)?;
                if field_offset != total_size {
                    return None;
                }
                total_size = total_size.checked_add(word_blob_copy_len_bytes(module, field_ty)?)?;
            }

            (shape::runtime_size_bytes(module, ty)? == total_size).then_some(total_size)
        }
        CompoundType::Ptr(_)
        | CompoundType::ObjRef(_)
        | CompoundType::ConstRef(_)
        | CompoundType::Enum(_)
        | CompoundType::Func { .. } => None,
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

fn emit_obj_init_from_codecopy(
    func: &mut Function,
    before: InstId,
    object: ValueId,
    ty: Type,
    addr: ValueId,
    copy_len_bytes: u32,
) {
    let dst = insert_before_one(
        func,
        before,
        data::ObjMaterializeStack::new_unchecked(func.inst_set(), object),
        ty.to_ptr(func.ctx()),
    );
    let copy_len = imm_i256(func, copy_len_bytes);
    insert_before_no_result(
        func,
        before,
        evm::EvmCodeCopy::new_unchecked(func.inst_set(), dst, addr, copy_len),
    );
}

fn emit_obj_init_from_addr(
    func: &mut Function,
    before: InstId,
    object: ValueId,
    ty: Type,
    addr: ValueId,
) {
    let scratch = insert_before_one(
        func,
        before,
        data::Alloca::new_unchecked(func.inst_set(), Type::I256),
        Type::I256.to_ptr(func.ctx()),
    );
    emit_obj_init_from_addr_with_scratch(func, before, object, ty, addr, scratch);
}

fn emit_obj_init_from_addr_with_scratch(
    func: &mut Function,
    before: InstId,
    object: ValueId,
    ty: Type,
    addr: ValueId,
    scratch: ValueId,
) {
    if ty.is_integral() {
        let value = emit_const_load_from_addr(func, before, addr, ty, Some(scratch));
        insert_before_no_result(
            func,
            before,
            data::ObjStore::new_unchecked(func.inst_set(), object, value),
        );
        return;
    }

    match ty.resolve_compound(func.ctx()) {
        Some(CompoundType::Array { elem, len }) => {
            let stride = const_leaf_count(func.ctx(), elem)
                .and_then(|count| count.checked_mul(32))
                .unwrap_or_else(|| {
                    panic!("unsupported obj.init.const array element type {elem:?}")
                });
            for idx in 0..len {
                let index = func
                    .dfg
                    .make_imm_value(Immediate::I64(i64::try_from(idx).expect("index overflow")));
                let slot = insert_before_one(
                    func,
                    before,
                    data::ObjIndex::new_unchecked(func.inst_set(), object, index),
                    elem.to_obj_ref(func.ctx()),
                );
                let child_addr = const_addr_with_offset(
                    func,
                    before,
                    addr,
                    u32::try_from(idx)
                        .expect("index overflow")
                        .checked_mul(stride)
                        .expect("const array offset overflow"),
                    Vec::new(),
                    false,
                );
                emit_obj_init_from_addr_with_scratch(func, before, slot, elem, child_addr, scratch);
            }
        }
        Some(CompoundType::Struct(s)) => {
            assert!(
                !s.packed,
                "packed structs are unsupported in obj.init.const"
            );
            let mut field_offset = 0u32;
            for (idx, field_ty) in s.fields.iter().copied().enumerate() {
                let index = func
                    .dfg
                    .make_imm_value(Immediate::I64(i64::try_from(idx).expect("index overflow")));
                let slot = insert_before_one(
                    func,
                    before,
                    data::ObjProj::new_unchecked(func.inst_set(), smallvec![object, index]),
                    field_ty.to_obj_ref(func.ctx()),
                );
                let child_addr =
                    const_addr_with_offset(func, before, addr, field_offset, Vec::new(), false);
                emit_obj_init_from_addr_with_scratch(
                    func, before, slot, field_ty, child_addr, scratch,
                );
                field_offset = field_offset
                    .checked_add(
                        const_leaf_count(func.ctx(), field_ty)
                            .and_then(|count| count.checked_mul(32))
                            .unwrap_or_else(|| {
                                panic!("unsupported obj.init.const struct field type {field_ty:?}")
                            }),
                    )
                    .expect("const struct field offset overflow");
            }
        }
        _ => panic!("unsupported obj.init.const type {ty:?}"),
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

fn const_addr_with_offset(
    func: &mut Function,
    before: InstId,
    base_addr: ValueId,
    const_offset_bytes: u32,
    dynamic_terms: Vec<(ValueId, u32)>,
    fresh_if_identity: bool,
) -> ValueId {
    if const_offset_bytes == 0 && dynamic_terms.is_empty() && fresh_if_identity {
        let zero = imm_i256(func, 0);
        return add_i256(func, before, base_addr, zero);
    }

    let mut addr = base_addr;
    if const_offset_bytes != 0 {
        let const_offset = imm_i256(func, const_offset_bytes);
        addr = add_i256(func, before, addr, const_offset);
    }
    for (value, stride_bytes) in dynamic_terms {
        let mut term = zext_to_i256(func, before, value);
        if stride_bytes != 1 {
            let stride = imm_i256(func, stride_bytes);
            term = mul_i256(func, before, term, stride);
        }
        addr = add_i256(func, before, addr, term);
    }
    addr
}

fn emit_const_load_from_addr(
    func: &mut Function,
    before: InstId,
    addr: ValueId,
    result_ty: Type,
    scratch: Option<ValueId>,
) -> ValueId {
    let scratch = scratch.unwrap_or_else(|| {
        insert_before_one(
            func,
            before,
            data::Alloca::new_unchecked(func.inst_set(), Type::I256),
            Type::I256.to_ptr(func.ctx()),
        )
    });
    let copy_len = imm_i256(func, 32);
    insert_before_no_result(
        func,
        before,
        evm::EvmCodeCopy::new_unchecked(func.inst_set(), scratch, addr, copy_len),
    );
    insert_before_one(
        func,
        before,
        data::Mload::new_unchecked(func.inst_set(), scratch, result_ty),
        result_ty,
    )
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
        global_variable::GvInitializer,
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

    fn global_symbols_with_prefix(
        parsed: &sonatina_parser::ParsedModule,
        prefix: &str,
    ) -> Vec<String> {
        let mut symbols = parsed.module.ctx.with_gv_store(|store| {
            store
                .all_gv_data()
                .map(|data| data.symbol.clone())
                .filter(|symbol| symbol.starts_with(prefix))
                .collect::<Vec<_>>()
        });
        symbols.sort();
        symbols
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
    fn const_load_huge_immediate_index_lowers_to_codecopy() {
        let parsed = parse(
            r#"
target = "evm-ethereum-osaka"

global private const [i256; 4] $arr = [1, 2, 3, 4];

func private %entry() -> i256 {
    block0:
        v0.constref<[i256; 4]> = const.ref $arr;
        v1.constref<i256> = const.index v0 1606938044258990275541962092341162602522202993782792835301376.i256;
        v2.i256 = const.load v1;
        return v2;
}
"#,
        );

        ConstDataLower::default().run(&parsed.module);

        let mut writer = ModuleWriter::with_debug_provider(&parsed.module, &parsed.debug);
        let dumped = writer.dump_string();
        assert!(dumped.contains("evm_code_copy"));
        assert!(dumped.contains("mload"));
        assert!(!dumped.contains("return 1.i256;"));
        assert!(!dumped.contains("return 2.i256;"));
        assert!(!dumped.contains("return 3.i256;"));
        assert!(!dumped.contains("return 4.i256;"));
        assert!(!dumped.contains("const."));
    }

    #[test]
    fn const_load_phi_same_path_folds_to_immediate_despite_layout_order() {
        let parsed = parse(
            r#"
target = "evm-ethereum-osaka"

global private const [i256; 4] $arr = [1, 2, 3, 4];

func private %entry() -> i256 {
    block0:
        br 1.i1 block1 block2;

    block3:
        v4.constref<i256> = phi (v1 block1) (v3 block2);
        v5.i256 = const.load v4;
        return v5;

    block1:
        v0.constref<[i256; 4]> = const.ref $arr;
        v1.constref<i256> = const.index v0 2.i8;
        jump block3;

    block2:
        v2.constref<[i256; 4]> = const.ref $arr;
        v3.constref<i256> = const.index v2 2.i8;
        jump block3;
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
    fn dynamic_const_load_collision_uses_fresh_blob_symbol() {
        let parsed = parse(
            r#"
target = "evm-ethereum-osaka"

global private const [i256; 4] $arr = [1, 2, 3, 4];
global private const [i8; 1] $__sonatina_const_words_arr_0 = [99];

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

        let base_symbol = parsed.module.ctx.with_gv_store(|store| {
            let source = store.lookup_gv("arr").expect("arr global should exist");
            format!("__sonatina_const_words_arr_{}", source.as_u32())
        });
        assert_eq!(
            global_symbols_with_prefix(&parsed, &base_symbol),
            vec![base_symbol.clone(), format!("{base_symbol}_1")]
        );

        let mut writer = ModuleWriter::with_debug_provider(&parsed.module, &parsed.debug);
        let dumped = writer.dump_string();
        assert!(dumped.contains("evm_code_copy"));
        assert!(dumped.contains("mload"));
        assert!(!dumped.contains("const."));
    }

    #[test]
    fn obj_init_const_aggregate_lowers_to_bulk_codecopy() {
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
        assert!(dumped.contains("obj.materialize.stack"));
        assert!(dumped.contains("evm_code_copy"));
        assert!(!dumped.contains("obj.store"));
        assert!(!dumped.contains("const."));
    }

    #[test]
    fn obj_init_const_bulk_codecopy_zero_extends_negative_narrow_words() {
        let parsed = parse(
            r#"
target = "evm-ethereum-osaka"

global private const [i8; 1] $arr = [-1];

func private %entry() -> i256 {
    block0:
        v0.objref<[i8; 1]> = obj.alloc [i8; 1];
        v1.constref<[i8; 1]> = const.ref $arr;
        obj.init.const v0 v1;
        return 0.i256;
}
"#,
        );

        ConstDataLower::default().run(&parsed.module);

        let entry = find_func_ref(&parsed, "entry");
        let dumped = parsed
            .module
            .func_store
            .view(entry, |func| FuncWriter::new(entry, func).dump_string());
        assert!(dumped.contains("evm_code_copy"));
        assert!(!dumped.contains("obj.store"));

        let blob = parsed.module.ctx.with_gv_store(|store| {
            let source = store.lookup_gv("arr").expect("arr global should exist");
            let symbol = format!("__sonatina_const_words_arr_{}", source.as_u32());
            store
                .lookup_gv(&symbol)
                .expect("synthesized blob should exist")
        });
        let blob_bytes = parsed.module.ctx.with_gv_store(|store| {
            let init = store
                .gv_data(blob)
                .initializer
                .clone()
                .expect("blob should have initializer");
            let GvInitializer::Array(bytes) = init else {
                panic!("blob initializer should be a byte array");
            };
            bytes
                .into_iter()
                .map(|byte| {
                    let GvInitializer::Immediate(imm) = byte else {
                        panic!("blob bytes must be immediates");
                    };
                    imm.as_i256().to_u256().low_u32() as u8
                })
                .collect::<Vec<_>>()
        });

        assert_eq!(blob_bytes.len(), 32);
        assert!(blob_bytes[..31].iter().all(|&byte| byte == 0));
        assert_eq!(blob_bytes[31], 0xff);
    }

    #[test]
    fn obj_init_const_scalar_phi_same_path_uses_immediate_store_despite_layout_order() {
        let parsed = parse(
            r#"
target = "evm-ethereum-osaka"

global private const i256 $value = 11;

func private %entry() -> i256 {
    block0:
        br 1.i1 block1 block2;

    block3:
        v2.objref<i256> = obj.alloc i256;
        v3.constref<i256> = phi (v0 block1) (v1 block2);
        obj.init.const v2 v3;
        v4.i256 = obj.load v2;
        return v4;

    block1:
        v0.constref<i256> = const.ref $value;
        jump block3;

    block2:
        v1.constref<i256> = const.ref $value;
        jump block3;
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
        assert!(!dumped.contains("obj.materialize.stack"));
        assert!(!dumped.contains("evm_code_copy"));
        assert!(!dumped.contains("mload"));
        assert!(!dumped.contains("const."));
    }

    #[test]
    fn obj_init_const_scalar_lowers_to_obj_store() {
        let parsed = parse(
            r#"
target = "evm-ethereum-osaka"

global private const i256 $value = 11;

func private %entry() -> i256 {
    block0:
        v0.objref<i256> = obj.alloc i256;
        v1.constref<i256> = const.ref $value;
        obj.init.const v0 v1;
        v2.i256 = obj.load v0;
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
        assert!(!dumped.contains("obj.init.const"));
        assert!(dumped.contains("obj.store"));
        assert!(!dumped.contains("obj.materialize.stack"));
        assert!(!dumped.contains("evm_code_copy"));
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

    #[test]
    fn dynamic_const_load_object_compile_succeeds_with_colliding_blob_symbol() {
        let parsed = parse(
            r#"
target = "evm-ethereum-osaka"

global private const [i256; 4] $arr = [1, 2, 3, 4];
global private const [i8; 1] $__sonatina_const_words_arr_0 = [99];

func private %entry(v0.i256) -> i256 {
    block0:
        v1.constref<[i256; 4]> = const.ref $arr;
        v2.constref<i256> = const.index v1 v0;
        v3.i256 = const.load v2;
        return v3;
}

object @Contract {
  section runtime {
    entry %entry;
    data $arr;
    data $__sonatina_const_words_arr_0;
  }
}
"#,
        );

        let opts = CompileOptions::default();
        compile_all_objects(&parsed.module, &test_backend(), &opts)
            .expect("object compilation should succeed with colliding synthesized blob symbols");
    }

    #[test]
    fn constref_helper_calls_lower_before_object_compile() {
        let parsed = parse(
            r#"
target = "evm-ethereum-osaka"

global private const [i256; 5] $arr = [10, 20, 30, 40, 50];

func private %get(v0.constref<[i256; 5]>, v1.i256) -> i256 {
    block0:
        v2.constref<i256> = const.index v0 v1;
        v3.i256 = const.load v2;
        return v3;
}

func private %entry() {
    block0:
        v0.constref<[i256; 5]> = const.ref $arr;
        jump block1;

    block1:
        v1.i256 = phi (0.i256 block0) (v6 block3);
        v2.i256 = phi (0.i256 block0) (v7 block3);
        v3.i1 = lt v2 5.i256;
        br v3 block2 block4;

    block2:
        v5.i256 = call %get v0 v2;
        v6.i256 = add v1 v5;
        jump block3;

    block3:
        v7.i256 = add v2 1.i256;
        jump block1;

    block4:
        v8.i1 = eq v1 150.i256;
        br v8 block5 block6;

    block5:
        evm_stop;

    block6:
        evm_revert 0.i256 0.i256;
}

object @Contract {
  section runtime { entry %entry; data $arr; }
}
"#,
        );

        let opts = CompileOptions::default();
        compile_all_objects(&parsed.module, &test_backend(), &opts)
            .expect("constref helper calls should lower before object compile");
    }

    #[test]
    fn looped_dynamic_const_load_lowers_before_object_compile() {
        let parsed = parse(
            r#"
target = "evm-ethereum-osaka"

global private const [i256; 5] $arr = [10, 20, 30, 40, 50];

func private %entry() {
    block0:
        v0.constref<[i256; 5]> = const.ref $arr;
        jump block3;

    block3:
        v3.i256 = phi (0.i256 block0) (v12 block5);
        v5.i256 = phi (0.i256 block0) (v15 block5);
        v7.i1 = lt v5 5.i256;
        br v7 block4 block6;

    block4:
        v10.constref<i256> = const.index v0 v5;
        v11.i256 = const.load v10;
        (v12.i256, v13.i1) = uaddo v3 v11;
        br v13 block7 block5;

    block5:
        v15.i256 = add v5 1.i256;
        jump block3;

    block6:
        v9.i1 = eq v3 150.i256;
        br v9 block8 block10;

    block10:
        evm_revert 0.i256 0.i256;

    block8:
        evm_stop;

    block7:
        evm_revert 0.i256 0.i256;
}

object @Contract {
  section runtime { entry %entry; data $arr; }
}
"#,
        );

        let opts = CompileOptions::default();
        compile_all_objects(&parsed.module, &test_backend(), &opts)
            .expect("looped dynamic const loads should lower before object compile");
    }
}
