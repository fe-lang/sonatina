use rustc_hash::FxHashMap;
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    Function, GlobalVariableRef, I256, Immediate, InstId, Linkage, Module, Type, U256, Value,
    ValueId,
    global_variable::{GlobalVariableData, GlobalVariableStore, GvInitializer},
    inst::{arith, cast, cmp, data, downcast, evm, logic},
    module::ModuleCtx,
    types::{CompoundType, CompoundTypeRef, StructData},
    visitor::VisitorMut,
};

use super::scalar_words::evm_scalar_word_bytes;
pub(crate) const CONST_WORD_POOL_PREFIX: &str = "__sonatina_const_words_";

use crate::{
    optim::const_eval::{
        ConstPath, ConstPathAnalysis, ConstPathStep, analyze_const_paths,
        collect_constref_value_tys, const_path_steps, eval_const_path_domain_immediate,
        eval_const_path_dynamic_domain_immediates, eval_const_path_subtree,
    },
    transform::aggregate::shape,
};

type ConstOffsetTerms = Vec<(ValueId, u32)>;
type ConstOffsetPlan = (Type, u32, ConstOffsetTerms);
type SparseExceptions = Vec<(usize, Immediate)>;

struct ConstRewriteInfo<'a> {
    constref_value_tys: &'a FxHashMap<ValueId, Type>,
    const_paths: &'a ConstPathAnalysis,
}

#[derive(Clone, Copy)]
struct ObjInitConstSubtree<'a> {
    source: GlobalVariableRef,
    ty: Type,
    init: &'a GvInitializer,
}

impl<'a> ObjInitConstSubtree<'a> {
    fn child(self, ty: Type, init: &'a GvInitializer) -> Self {
        Self {
            source: self.source,
            ty,
            init,
        }
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
    word_blobs_by_bytes: FxHashMap<Vec<u8>, GlobalVariableRef>,
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
        let info = ConstRewriteInfo {
            constref_value_tys: &constref_value_tys,
            const_paths: &const_paths,
        };
        let blocks: Vec<_> = func.layout.iter_block().collect();
        for block in blocks {
            let insts: Vec<_> = func.layout.iter_inst(block).collect();
            for inst in insts {
                if !func.layout.is_inst_inserted(inst) {
                    continue;
                }
                changed |= self.rewrite_inst(module, func, inst, &info);
            }
        }

        if changed {
            func.rebuild_users();
        }
        changed |= self.cleanup_const_carriers(module, func, &info);
        assert_no_const_ops(func);
        changed
    }

    fn rewrite_inst(
        &mut self,
        module: &Module,
        func: &mut Function,
        inst: InstId,
        info: &ConstRewriteInfo<'_>,
    ) -> bool {
        if let Some(load) =
            downcast::<&data::ConstLoad>(func.inst_set(), func.dfg.inst(inst)).cloned()
        {
            return self.rewrite_const_load(module, func, inst, *load.object(), info.const_paths);
        }
        if let Some(init) =
            downcast::<&data::ObjInitConst>(func.inst_set(), func.dfg.inst(inst)).cloned()
        {
            return self.rewrite_obj_init_const(module, func, inst, init, info);
        }
        false
    }

    fn cleanup_const_carriers(
        &mut self,
        module: &Module,
        func: &mut Function,
        info: &ConstRewriteInfo<'_>,
    ) -> bool {
        let mut changed = false;
        loop {
            func.rebuild_users();
            let mut local_changed = false;
            for inst in inserted_insts(func).into_iter().rev() {
                if self.remove_dead_const_carrier(func, inst, info.constref_value_tys) {
                    local_changed = true;
                }
            }
            changed |= local_changed;
            if !local_changed {
                break;
            }
        }

        loop {
            func.rebuild_users();
            let mut local_changed = false;
            for inst in inserted_insts(func).into_iter().rev() {
                if self.remove_dead_const_carrier(func, inst, info.constref_value_tys)
                    || self.rewrite_live_const_carrier(module, func, inst, info)
                {
                    local_changed = true;
                }
            }
            changed |= local_changed;
            if !local_changed {
                break;
            }
        }

        changed
    }

    fn remove_dead_const_carrier(
        &mut self,
        func: &mut Function,
        inst: InstId,
        constref_value_tys: &FxHashMap<ValueId, Type>,
    ) -> bool {
        if !is_constref_carrier(func, inst, constref_value_tys) {
            return false;
        }
        let result = func
            .dfg
            .inst_result(inst)
            .expect("constref carrier must have one result");
        if func.dfg.users_num(result) != 0 {
            return false;
        }
        remove_inst(func, inst);
        true
    }

    fn rewrite_live_const_carrier(
        &mut self,
        module: &Module,
        func: &mut Function,
        inst: InstId,
        info: &ConstRewriteInfo<'_>,
    ) -> bool {
        if let Some(const_ref) =
            downcast::<&data::ConstRef>(func.inst_set(), func.dfg.inst(inst)).cloned()
        {
            let global = const_ref.global().gv();
            let ty = module.ctx.with_gv_store(|store| store.ty(global));
            let path = ConstPath {
                global,
                ty,
                steps: Vec::new(),
            };
            let replacement = self.materialize_const_path_addr(module, func, inst, &path);
            replace_with_alias(func, inst, replacement);
            return true;
        }
        if let Some(proj) =
            downcast::<&data::ConstProj>(func.inst_set(), func.dfg.inst(inst)).cloned()
        {
            let Some((&base, rest)) = proj.values().split_first() else {
                panic!("const.proj requires a base operand");
            };
            return self.rewrite_live_const_subref(module, func, inst, base, rest, info);
        }
        if let Some(index) =
            downcast::<&data::ConstIndex>(func.inst_set(), func.dfg.inst(inst)).cloned()
        {
            return self.rewrite_live_const_subref(
                module,
                func,
                inst,
                *index.object(),
                &[*index.index()],
                info,
            );
        }
        false
    }

    fn rewrite_live_const_subref(
        &mut self,
        module: &Module,
        func: &mut Function,
        inst: InstId,
        base: ValueId,
        indices: &[ValueId],
        info: &ConstRewriteInfo<'_>,
    ) -> bool {
        let result = func
            .dfg
            .inst_result(inst)
            .expect("const subreference must have a result");
        if let Some(path) = info.const_paths.path(result) {
            let replacement = self.materialize_const_path_addr(module, func, inst, path);
            replace_with_alias(func, inst, replacement);
            return true;
        }

        let base_ty = info
            .constref_value_tys
            .get(&base)
            .copied()
            .unwrap_or_else(|| {
                panic!(
                    "unsupported const subreference source at inst {}",
                    inst.as_u32()
                )
            });
        let (ty, steps) = const_path_steps(func, base_ty, indices).unwrap_or_else(|| {
            panic!(
                "unsupported const projection/index at inst {} (base_ty: {:?}, indices: {:?})",
                inst.as_u32(),
                base_ty,
                indices
                    .iter()
                    .map(|&index| func.dfg.value(index).clone())
                    .collect::<Vec<_>>(),
            )
        });
        let (_, const_offset_bytes, dynamic_terms) =
            const_steps_offset_bytes(func.ctx(), base_ty, &steps).unwrap_or_else(|| {
                panic!(
                    "unsupported const projection/index offset computation at inst {}",
                    inst.as_u32()
                )
            });
        let replacement =
            const_addr_with_offset(func, inst, base, const_offset_bytes, dynamic_terms, true);
        debug_assert_eq!(ty, info.constref_value_tys[&result]);
        replace_with_alias(func, inst, replacement);
        true
    }

    fn rewrite_const_load(
        &mut self,
        module: &Module,
        func: &mut Function,
        inst: InstId,
        object: ValueId,
        const_paths: &ConstPathAnalysis,
    ) -> bool {
        let result_ty = func
            .dfg
            .inst_result(inst)
            .map(|result| func.dfg.value_ty(result))
            .expect("const.load must have a result");
        let addr = if let Some(path) = const_paths.path(object) {
            if let Some(imm) = eval_const_path_domain_immediate(&module.ctx, path, |value| {
                func.dfg.value_imm(value)
            }) {
                let replacement = func.dfg.make_imm_value(imm);
                replace_with_alias(func, inst, replacement);
                return true;
            }

            if let Some(replacement) =
                self.rewrite_dynamic_domain_load(module, func, inst, path, result_ty)
            {
                replace_with_alias(func, inst, replacement);
                return true;
            }

            self.materialize_const_path_addr(module, func, inst, path)
        } else {
            object
        };

        let replacement = emit_const_load_from_addr(func, inst, addr, result_ty, None);
        replace_with_alias(func, inst, replacement);
        true
    }

    fn rewrite_obj_init_const(
        &mut self,
        module: &Module,
        func: &mut Function,
        inst: InstId,
        init: data::ObjInitConst,
        info: &ConstRewriteInfo<'_>,
    ) -> bool {
        let value = *init.value();
        let source_ty = info
            .constref_value_tys
            .get(&value)
            .copied()
            .unwrap_or_else(|| {
                panic!(
                    "unsupported obj.init.const source at inst {}",
                    inst.as_u32()
                )
            });
        if let Some(path) = info.const_paths.path(value) {
            if let Some((ty, subtree_init)) =
                eval_const_path_subtree(&module.ctx, path, |value| func.dfg.value_imm(value))
            {
                debug_assert_eq!(ty, path.ty);
                self.emit_known_obj_init(module, func, inst, *init.object(), path, &subtree_init);
            } else {
                let addr = self.materialize_const_path_addr(module, func, inst, path);
                if !path.ty.is_integral()
                    && let Some(copy_len_bytes) = word_blob_copy_len_bytes(func.ctx(), path.ty)
                {
                    emit_obj_init_from_codecopy(
                        func,
                        inst,
                        *init.object(),
                        path.ty,
                        addr,
                        copy_len_bytes,
                    );
                } else {
                    emit_obj_init_from_addr(func, inst, *init.object(), path.ty, addr);
                }
            }
        } else if !source_ty.is_integral()
            && let Some(copy_len_bytes) = word_blob_copy_len_bytes(func.ctx(), source_ty)
        {
            emit_obj_init_from_codecopy(
                func,
                inst,
                *init.object(),
                source_ty,
                value,
                copy_len_bytes,
            );
        } else {
            emit_obj_init_from_addr(func, inst, *init.object(), source_ty, value);
        }
        remove_inst(func, inst);
        true
    }

    fn emit_known_obj_init(
        &mut self,
        module: &Module,
        func: &mut Function,
        before: InstId,
        object: ValueId,
        path: &ConstPath,
        init: &GvInitializer,
    ) {
        self.emit_known_obj_init_for_ty(
            module,
            func,
            before,
            object,
            ObjInitConstSubtree {
                source: path.global,
                ty: path.ty,
                init,
            },
        );
    }

    fn emit_known_obj_init_for_ty(
        &mut self,
        module: &Module,
        func: &mut Function,
        before: InstId,
        object: ValueId,
        subtree: ObjInitConstSubtree<'_>,
    ) {
        let ty = subtree.ty;
        let init = subtree.init;
        if ty.is_integral() || should_inline_obj_init(func.ctx(), ty) {
            emit_obj_init(func, before, object, ty, init);
            return;
        }

        if initializer_all_zero(&module.ctx, ty, init) {
            emit_obj_zero_fill(func, before, object, ty);
            return;
        }

        if let Some(splat) = initializer_scalar_splat(&module.ctx, ty, init)
            && emit_obj_splat_fill(func, before, object, ty, splat)
        {
            return;
        }

        if should_split_obj_init(&module.ctx, ty, init)
            && self.emit_split_obj_init(module, func, before, object, subtree)
        {
            return;
        }

        let Some(bytes) = encode_runtime_object_const_bytes(&module.ctx, ty, init) else {
            panic!("unsupported runtime-object encoding for obj.init.const type {ty:?}");
        };
        let blob = self.bytes_blob_global(module, subtree.source, bytes);
        let addr = insert_before_one(
            func,
            before,
            data::SymAddr::new_unchecked(func.inst_set(), data::SymbolRef::Global(blob)),
            func.ctx().type_layout.pointer_repl(),
        );
        let copy_len_bytes = shape::runtime_size_bytes(func.ctx(), ty)
            .expect("runtime-object encoding requires a concrete runtime size");
        emit_obj_init_from_codecopy(func, before, object, ty, addr, copy_len_bytes);
    }

    fn emit_split_obj_init(
        &mut self,
        module: &Module,
        func: &mut Function,
        before: InstId,
        object: ValueId,
        subtree: ObjInitConstSubtree<'_>,
    ) -> bool {
        let ty = subtree.ty;
        let init = subtree.init;
        match (ty.resolve_compound(&module.ctx), init) {
            (Some(CompoundType::Array { elem, len }), GvInitializer::Array(items)) => {
                if items.len() != len || len > MAX_SPLIT_OBJ_INIT_ARRAY_LEN {
                    return false;
                }
                for (idx, item) in items.iter().enumerate() {
                    let index = func.dfg.make_imm_value(Immediate::I64(
                        i64::try_from(idx).expect("index overflow"),
                    ));
                    let slot = insert_before_one(
                        func,
                        before,
                        data::ObjIndex::new_unchecked(func.inst_set(), object, index),
                        elem.to_obj_ref(func.ctx()),
                    );
                    self.emit_known_obj_init_for_ty(
                        module,
                        func,
                        before,
                        slot,
                        subtree.child(elem, item),
                    );
                }
                true
            }
            (Some(CompoundType::Struct(s)), GvInitializer::Struct(fields)) => {
                if s.packed || fields.len() != s.fields.len() {
                    return false;
                }
                for (idx, (field_ty, field)) in
                    s.fields.iter().copied().zip(fields.iter()).enumerate()
                {
                    let index = func.dfg.make_imm_value(Immediate::I64(
                        i64::try_from(idx).expect("index overflow"),
                    ));
                    let slot = insert_before_one(
                        func,
                        before,
                        data::ObjProj::new_unchecked(func.inst_set(), smallvec![object, index]),
                        field_ty.to_obj_ref(func.ctx()),
                    );
                    self.emit_known_obj_init_for_ty(
                        module,
                        func,
                        before,
                        slot,
                        subtree.child(field_ty, field),
                    );
                }
                true
            }
            _ => false,
        }
    }

    fn materialize_const_path_addr(
        &mut self,
        module: &Module,
        func: &mut Function,
        before: InstId,
        path: &ConstPath,
    ) -> ValueId {
        let blob = self.word_blob_global(module, path.global);
        let base_addr = insert_before_one(
            func,
            before,
            data::SymAddr::new_unchecked(func.inst_set(), data::SymbolRef::Global(blob)),
            func.ctx().type_layout.pointer_repl(),
        );
        let root_ty = module.ctx.with_gv_store(|store| store.ty(path.global));
        let (ty, const_offset_bytes, dynamic_terms) =
            const_steps_offset_bytes(func.ctx(), root_ty, &path.steps).unwrap_or_else(|| {
                panic!(
                    "unsupported const path address computation for global {}",
                    path.global.as_u32()
                )
            });
        debug_assert_eq!(ty, path.ty);
        const_addr_with_offset(
            func,
            before,
            base_addr,
            const_offset_bytes,
            dynamic_terms,
            false,
        )
    }

    fn rewrite_dynamic_domain_load(
        &mut self,
        module: &Module,
        func: &mut Function,
        before: InstId,
        path: &ConstPath,
        result_ty: Type,
    ) -> Option<ValueId> {
        let (index, values) =
            eval_const_path_dynamic_domain_immediates(&module.ctx, path, |value| {
                func.dfg.value_imm(value)
            })?;
        if !result_ty.is_integral() || values.iter().any(|imm| imm.ty() != result_ty) {
            return None;
        }

        if let Some(replacement) =
            emit_dynamic_values_lookup(func, before, index, result_ty, &values, true)
        {
            return Some(replacement);
        }

        let addr = self.materialize_dynamic_values_addr(
            module,
            func,
            before,
            path.global,
            index,
            &values,
        )?;
        Some(emit_const_load_from_addr(
            func, before, addr, result_ty, None,
        ))
    }

    fn materialize_dynamic_values_addr(
        &mut self,
        module: &Module,
        func: &mut Function,
        before: InstId,
        source: GlobalVariableRef,
        index: ValueId,
        values: &[Immediate],
    ) -> Option<ValueId> {
        let mut bytes = Vec::with_capacity(values.len().checked_mul(32)?);
        for &value in values {
            bytes.extend_from_slice(&evm_scalar_word_bytes(value)?);
        }
        let blob = self.bytes_blob_global(module, source, bytes);
        let base_addr = insert_before_one(
            func,
            before,
            data::SymAddr::new_unchecked(func.inst_set(), data::SymbolRef::Global(blob)),
            func.ctx().type_layout.pointer_repl(),
        );
        Some(const_addr_with_offset(
            func,
            before,
            base_addr,
            0,
            vec![(index, 32)],
            false,
        ))
    }

    fn word_blob_global(
        &mut self,
        module: &Module,
        source: GlobalVariableRef,
    ) -> GlobalVariableRef {
        if let Some(&blob) = self.word_blobs.get(&source) {
            return blob;
        }

        let (ty, init) = module.ctx.with_gv_store(|store| {
            let data = store.gv_data(source);
            (
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
        let blob = self.bytes_blob_global(module, source, bytes);
        self.word_blobs.insert(source, blob);
        blob
    }

    fn bytes_blob_global(
        &mut self,
        module: &Module,
        source: GlobalVariableRef,
        bytes: Vec<u8>,
    ) -> GlobalVariableRef {
        if crate::object::data::encode_gv_initializer_to_bytes(&module.ctx, source)
            .is_ok_and(|native| native == bytes)
        {
            return source;
        }

        if let Some(&blob) = self.word_blobs_by_bytes.get(&bytes) {
            return blob;
        }

        let source_symbol = module
            .ctx
            .with_gv_store(|store| store.gv_data(source).symbol.clone());
        let blob_ty = module
            .ctx
            .with_ty_store_mut(|store| store.make_array(Type::I8, bytes.len()));
        let blob_init = GvInitializer::make_array(
            bytes
                .iter()
                .copied()
                .map(|byte| GvInitializer::make_imm(byte as i8))
                .collect(),
        );
        let symbol_base = format!(
            "{CONST_WORD_POOL_PREFIX}{source_symbol}_{}",
            source.as_u32()
        );
        let blob = module.ctx.with_gv_store_mut(|store| {
            let symbol = fresh_global_symbol(store, &symbol_base);
            store.make_gv(GlobalVariableData::constant(
                symbol,
                blob_ty,
                Linkage::Private,
                blob_init,
            ))
        });
        self.word_blobs_by_bytes.insert(bytes, blob);
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

fn inserted_insts(func: &Function) -> Vec<InstId> {
    func.layout
        .iter_block()
        .flat_map(|block| func.layout.iter_inst(block))
        .collect()
}

fn is_constref_carrier(
    func: &Function,
    inst: InstId,
    constref_value_tys: &FxHashMap<ValueId, Type>,
) -> bool {
    let Some([result]) = func.dfg.try_inst_results(inst) else {
        return false;
    };
    let result = *result;
    if !constref_value_tys.contains_key(&result) {
        return false;
    }

    let inst_data = func.dfg.inst(inst);
    downcast::<&data::ConstRef>(func.inst_set(), inst_data).is_some()
        || downcast::<&data::ConstProj>(func.inst_set(), inst_data).is_some()
        || downcast::<&data::ConstIndex>(func.inst_set(), inst_data).is_some()
        || func.dfg.cast_phi(inst).is_some()
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
        out.extend_from_slice(&evm_scalar_word_bytes(*imm)?);
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

fn encode_runtime_object_const_bytes(
    module: &ModuleCtx,
    ty: Type,
    init: &GvInitializer,
) -> Option<Vec<u8>> {
    if ty.is_integral() {
        let GvInitializer::Immediate(imm) = init else {
            return None;
        };
        if imm.ty() != ty {
            return None;
        }
        return Some(evm_scalar_word_bytes(*imm)?.to_vec());
    }

    match (ty.resolve_compound(module)?, init) {
        (CompoundType::Array { elem, len }, GvInitializer::Array(items)) => {
            if items.len() != len {
                return None;
            }
            let mut bytes = Vec::with_capacity(shape::runtime_size_bytes(module, ty)? as usize);
            for item in items {
                bytes.extend(encode_runtime_object_const_bytes(module, elem, item)?);
            }
            Some(bytes)
        }
        (CompoundType::Struct(s), GvInitializer::Struct(fields)) => {
            if s.packed || fields.len() != s.fields.len() {
                return None;
            }
            let mut bytes = vec![0; shape::runtime_size_bytes(module, ty)? as usize];
            for (idx, (field_ty, field)) in s.fields.iter().copied().zip(fields).enumerate() {
                let (offset, _) =
                    shape::struct_field_offset_bytes(&s.fields, s.packed, idx, module)?;
                let field_bytes = encode_runtime_object_const_bytes(module, field_ty, field)?;
                let offset = offset as usize;
                bytes
                    .get_mut(offset..offset + field_bytes.len())?
                    .copy_from_slice(&field_bytes);
            }
            Some(bytes)
        }
        _ => None,
    }
}

fn initializer_all_zero(module: &ModuleCtx, ty: Type, init: &GvInitializer) -> bool {
    if ty.is_integral() {
        return matches!(init, GvInitializer::Immediate(imm) if imm.ty() == ty && imm.is_zero());
    }

    match (ty.resolve_compound(module), init) {
        (Some(CompoundType::Array { elem, len }), GvInitializer::Array(items)) => {
            items.len() == len
                && items
                    .iter()
                    .all(|item| initializer_all_zero(module, elem, item))
        }
        (Some(CompoundType::Struct(s)), GvInitializer::Struct(fields)) => {
            !s.packed
                && fields.len() == s.fields.len()
                && s.fields
                    .iter()
                    .copied()
                    .zip(fields)
                    .all(|(field_ty, field)| initializer_all_zero(module, field_ty, field))
        }
        _ => false,
    }
}

fn initializer_scalar_splat(
    module: &ModuleCtx,
    ty: Type,
    init: &GvInitializer,
) -> Option<Immediate> {
    let mut splat = None;
    record_initializer_splat(module, ty, init, &mut splat)?;
    splat
}

fn record_initializer_splat(
    module: &ModuleCtx,
    ty: Type,
    init: &GvInitializer,
    splat: &mut Option<Immediate>,
) -> Option<()> {
    if ty.is_integral() {
        let GvInitializer::Immediate(imm) = init else {
            return None;
        };
        if imm.ty() != ty || splat.as_ref().is_some_and(|&existing| existing != *imm) {
            return None;
        }
        *splat = Some(*imm);
        return Some(());
    }

    match (ty.resolve_compound(module)?, init) {
        (CompoundType::Array { elem, len }, GvInitializer::Array(items)) => {
            if items.len() != len {
                return None;
            }
            for item in items {
                record_initializer_splat(module, elem, item, splat)?;
            }
            Some(())
        }
        (CompoundType::Struct(s), GvInitializer::Struct(fields)) => {
            if s.packed || fields.len() != s.fields.len() {
                return None;
            }
            for (field_ty, field) in s.fields.iter().copied().zip(fields) {
                record_initializer_splat(module, field_ty, field, splat)?;
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

fn should_inline_obj_init(module: &ModuleCtx, ty: Type) -> bool {
    const MAX_INLINE_LEAVES: u32 = 4;
    const_leaf_count(module, ty).is_some_and(|leaves| leaves <= MAX_INLINE_LEAVES)
}

const MAX_SPLIT_OBJ_INIT_ARRAY_LEN: usize = 8;

fn should_split_obj_init(module: &ModuleCtx, ty: Type, init: &GvInitializer) -> bool {
    let Some(children) = obj_init_children(module, ty, init) else {
        return false;
    };

    let mut has_inline_child = false;
    let mut has_large_child = false;
    for (child_ty, child_init) in children {
        has_inline_child |= child_ty.is_integral() || should_inline_obj_init(module, child_ty);
        has_large_child |= !child_ty.is_integral() && !should_inline_obj_init(module, child_ty);
        if obj_init_child_avoids_blob(module, child_ty, child_init)
            || should_split_obj_init(module, child_ty, child_init)
        {
            return true;
        }
    }

    has_inline_child && has_large_child
}

fn obj_init_child_avoids_blob(module: &ModuleCtx, ty: Type, init: &GvInitializer) -> bool {
    !ty.is_integral()
        && !should_inline_obj_init(module, ty)
        && (initializer_all_zero(module, ty, init)
            || initializer_scalar_splat(module, ty, init)
                .is_some_and(|_| word_blob_copy_len_bytes(module, ty).is_some_and(|len| len > 32)))
}

fn obj_init_children<'a>(
    module: &ModuleCtx,
    ty: Type,
    init: &'a GvInitializer,
) -> Option<Vec<(Type, &'a GvInitializer)>> {
    match (ty.resolve_compound(module)?, init) {
        (CompoundType::Array { elem, len }, GvInitializer::Array(items)) => (items.len() == len
            && len <= MAX_SPLIT_OBJ_INIT_ARRAY_LEN)
            .then(|| items.iter().map(|item| (elem, item)).collect()),
        (CompoundType::Struct(s), GvInitializer::Struct(fields)) => {
            if s.packed || fields.len() != s.fields.len() {
                return None;
            }
            Some(s.fields.iter().copied().zip(fields.iter()).collect())
        }
        _ => None,
    }
}

fn emit_dynamic_values_lookup(
    func: &mut Function,
    before: InstId,
    index: ValueId,
    result_ty: Type,
    values: &[Immediate],
    allow_periodic: bool,
) -> Option<ValueId> {
    emit_packed_bool_lookup(func, before, index, values)
        .or_else(|| emit_packed_byte_lookup(func, before, index, values))
        .or_else(|| emit_affine_lookup(func, before, index, result_ty, values))
        .or_else(|| emit_power_of_two_lookup(func, before, index, result_ty, values))
        .or_else(|| emit_packed_subword_lookup(func, before, index, result_ty, values))
        .or_else(|| {
            allow_periodic
                .then(|| emit_periodic_lookup(func, before, index, result_ty, values))
                .flatten()
        })
        .or_else(|| emit_sparse_lookup(func, before, index, result_ty, values))
}

fn emit_packed_bool_lookup(
    func: &mut Function,
    before: InstId,
    index: ValueId,
    values: &[Immediate],
) -> Option<ValueId> {
    if values.len() > 256 || !values.iter().all(|imm| matches!(imm, Immediate::I1(_))) {
        return None;
    }

    let mut bits = U256::zero();
    for (idx, imm) in values.iter().enumerate() {
        if matches!(imm, Immediate::I1(true)) {
            bits |= U256::one() << idx;
        }
    }

    let index = zext_to_i256(func, before, index);
    let bitset = imm_i256_u256(func, bits);
    let shifted = shr_i256(func, before, bitset, index);
    let one = imm_i256(func, 1);
    let masked = and_i256(func, before, shifted, one);
    let zero = imm_i256(func, 0);
    Some(insert_before_one(
        func,
        before,
        cmp::Ne::new_unchecked(func.inst_set(), masked, zero),
        Type::I1,
    ))
}

fn emit_packed_byte_lookup(
    func: &mut Function,
    before: InstId,
    index: ValueId,
    values: &[Immediate],
) -> Option<ValueId> {
    if values.len() > 32 || !values.iter().all(|imm| imm.ty() == Type::I8) {
        return None;
    }

    let mut packed = U256::zero();
    for &imm in values {
        packed = (packed << 8) | unsigned_immediate(imm)?;
    }

    let index = zext_to_i256(func, before, index);
    let pos = match 32u32.checked_sub(u32::try_from(values.len()).ok()?)? {
        0 => index,
        offset => {
            let offset = imm_i256(func, offset);
            add_i256(func, before, index, offset)
        }
    };
    let table = imm_i256_u256(func, packed);
    let byte = insert_before_one(
        func,
        before,
        evm::EvmByte::new_unchecked(func.inst_set(), pos, table),
        Type::I256,
    );
    Some(trunc_i256_to(func, before, byte, Type::I8))
}

fn emit_affine_lookup(
    func: &mut Function,
    before: InstId,
    index: ValueId,
    result_ty: Type,
    values: &[Immediate],
) -> Option<ValueId> {
    let (base, stride) = affine_sequence(values)?;
    let mut value = zext_to_i256(func, before, index);
    if !stride.is_one() {
        let stride = imm_i256_from_immediate(func, stride);
        value = mul_i256(func, before, value, stride);
    }
    if !base.is_zero() {
        let base = imm_i256_from_immediate(func, base);
        value = add_i256(func, before, base, value);
    }
    Some(trunc_i256_to(func, before, value, result_ty))
}

fn affine_sequence(values: &[Immediate]) -> Option<(Immediate, Immediate)> {
    if values.len() < 2 || values[0].ty() == Type::I1 {
        return None;
    }

    let base = values[0];
    let stride = values[1] - base;
    if stride.is_zero() {
        return None;
    }

    values
        .iter()
        .copied()
        .enumerate()
        .all(|(idx, value)| {
            let idx = Immediate::from_i256(I256::from_usize(idx), base.ty());
            value == base + stride * idx
        })
        .then_some((base, stride))
}

fn emit_power_of_two_lookup(
    func: &mut Function,
    before: InstId,
    index: ValueId,
    result_ty: Type,
    values: &[Immediate],
) -> Option<ValueId> {
    if result_ty != Type::I256 {
        return None;
    }

    let (base_exp, stride) = power_of_two_exponents(values)?;
    let mut shift = zext_to_i256(func, before, index);
    if stride != 1 {
        let stride = imm_i256(func, stride);
        shift = mul_i256(func, before, shift, stride);
    }
    if base_exp != 0 {
        let base_exp = imm_i256(func, base_exp);
        shift = add_i256(func, before, base_exp, shift);
    }
    let one = imm_i256(func, 1);
    Some(shl_i256(func, before, one, shift))
}

fn power_of_two_exponents(values: &[Immediate]) -> Option<(u32, u32)> {
    let mut exponents = values.iter().copied().map(power_of_two_exponent);
    let base = exponents.next()??;
    let next = exponents.next()??;
    let stride = next.checked_sub(base)?;
    if stride == 0 {
        return None;
    }
    exponents
        .enumerate()
        .all(|(idx, exp)| {
            let idx = u32::try_from(idx + 2).ok();
            idx.and_then(|idx| base.checked_add(stride.checked_mul(idx)?)) == exp
        })
        .then_some((base, stride))
}

fn power_of_two_exponent(value: Immediate) -> Option<u32> {
    let value = value.zext(Type::I256).as_i256().to_u256();
    if value.is_zero() || value & (value - U256::one()) != U256::zero() {
        return None;
    }
    (0..256u32).find(|&bit| value == U256::one() << bit as usize)
}

fn emit_packed_subword_lookup(
    func: &mut Function,
    before: InstId,
    index: ValueId,
    result_ty: Type,
    values: &[Immediate],
) -> Option<ValueId> {
    let width = packed_subword_width(result_ty)?;
    if values.is_empty() || values.len() > 256 / width {
        return None;
    }

    let mut packed = U256::zero();
    for &imm in values {
        packed = (packed << width) | unsigned_immediate_bits(imm, width)?;
    }

    let mut shift = zext_to_i256(func, before, index);
    if width != 1 {
        let width = imm_i256(func, u32::try_from(width).ok()?);
        shift = mul_i256(func, before, shift, width);
    }
    let base_shift = imm_i256(func, u32::try_from((values.len() - 1) * width).ok()?);
    let shift = sub_i256(func, before, base_shift, shift);
    let table = imm_i256_u256(func, packed);
    let shifted = shr_i256(func, before, table, shift);
    Some(trunc_i256_to(func, before, shifted, result_ty))
}

fn packed_subword_width(ty: Type) -> Option<usize> {
    match ty {
        Type::I16 => Some(16),
        Type::I32 => Some(32),
        Type::I64 => Some(64),
        _ => None,
    }
}

fn emit_periodic_lookup(
    func: &mut Function,
    before: InstId,
    index: ValueId,
    result_ty: Type,
    values: &[Immediate],
) -> Option<ValueId> {
    let period = periodic_len(values)?;
    let index = zext_to_i256(func, before, index);
    let index = if period.is_power_of_two() {
        let mask = imm_i256_usize(func, period - 1)?;
        and_i256(func, before, index, mask)
    } else {
        let modulus = imm_i256_usize(func, period)?;
        umod_i256(func, before, index, modulus)
    };
    emit_dynamic_values_lookup(func, before, index, result_ty, &values[..period], false)
}

fn periodic_len(values: &[Immediate]) -> Option<usize> {
    (2..values.len())
        .filter(|period| values.len().is_multiple_of(*period))
        .find(|&period| {
            values
                .iter()
                .enumerate()
                .all(|(idx, value)| *value == values[idx % period])
        })
}

fn emit_sparse_lookup(
    func: &mut Function,
    before: InstId,
    index: ValueId,
    result_ty: Type,
    values: &[Immediate],
) -> Option<ValueId> {
    if result_ty == Type::I1 {
        return None;
    }

    let (default, default_count, exceptions) = sparse_exceptions(values)?;
    if exceptions.len() > 4 || default_count == 1 && values.len() > 4 {
        return None;
    }

    let index = zext_to_i256(func, before, index);
    let mut value = (!default.is_zero()).then(|| func.dfg.make_imm_value(default));
    for (exception_idx, exception) in exceptions {
        let exception_idx = imm_i256_usize(func, exception_idx)?;
        let is_exception = insert_before_one(
            func,
            before,
            cmp::Eq::new_unchecked(func.inst_set(), index, exception_idx),
            Type::I1,
        );
        let selector = zext_to_ty(func, before, is_exception, result_ty);
        let delta = func.dfg.make_imm_value(exception - default);
        let selected_delta = insert_before_one(
            func,
            before,
            arith::Mul::new_unchecked(func.inst_set(), selector, delta),
            result_ty,
        );
        value = Some(if let Some(value) = value {
            insert_before_one(
                func,
                before,
                arith::Add::new_unchecked(func.inst_set(), value, selected_delta),
                result_ty,
            )
        } else {
            selected_delta
        });
    }
    Some(value.unwrap_or_else(|| func.dfg.make_imm_value(default)))
}

fn sparse_exceptions(values: &[Immediate]) -> Option<(Immediate, usize, SparseExceptions)> {
    let mut counts = FxHashMap::default();
    let mut order = Vec::new();
    for &value in values {
        if !counts.contains_key(&value) {
            order.push(value);
        }
        *counts.entry(value).or_insert(0usize) += 1;
    }

    let mut candidates = order.into_iter();
    let mut default = candidates.next()?;
    let mut default_count = counts[&default];
    for candidate in candidates {
        let count = counts[&candidate];
        if count > default_count {
            default = candidate;
            default_count = count;
        }
    }

    let exceptions = values
        .iter()
        .copied()
        .enumerate()
        .filter(|(_, value)| *value != default)
        .collect();
    Some((default, default_count, exceptions))
}

fn unsigned_immediate(imm: Immediate) -> Option<U256> {
    unsigned_immediate_bits(imm, 8)
}

fn unsigned_immediate_bits(imm: Immediate, bits: usize) -> Option<U256> {
    let value = imm.zext(Type::I256).as_i256().to_u256();
    let max = (U256::one() << bits) - U256::one();
    (value <= max).then_some(value)
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

fn emit_obj_zero_fill(func: &mut Function, before: InstId, object: ValueId, ty: Type) {
    let len = shape::runtime_size_bytes(func.ctx(), ty)
        .expect("zero obj.init.const requires a concrete runtime size");
    if len == 0 {
        return;
    }

    let dst = insert_before_one(
        func,
        before,
        data::ObjMaterializeStack::new_unchecked(func.inst_set(), object),
        ty.to_ptr(func.ctx()),
    );
    let code_size = insert_before_one(
        func,
        before,
        evm::EvmCodeSize::new_unchecked(func.inst_set()),
        Type::I256,
    );
    let len = imm_i256(func, len);
    insert_before_no_result(
        func,
        before,
        evm::EvmCodeCopy::new_unchecked(func.inst_set(), dst, code_size, len),
    );
}

fn emit_obj_splat_fill(
    func: &mut Function,
    before: InstId,
    object: ValueId,
    ty: Type,
    value: Immediate,
) -> bool {
    let Some(total_len) = word_blob_copy_len_bytes(func.ctx(), ty) else {
        return false;
    };
    if total_len <= 32 {
        return false;
    }

    let dst = insert_before_one(
        func,
        before,
        data::ObjMaterializeStack::new_unchecked(func.inst_set(), object),
        ty.to_ptr(func.ctx()),
    );
    let word_ptr_ty = Type::I256.to_ptr(func.ctx());
    let dst = insert_before_one(
        func,
        before,
        cast::Bitcast::new_unchecked(func.inst_set(), dst, word_ptr_ty),
        word_ptr_ty,
    );
    let value_id = func.dfg.make_imm_value(value);
    insert_before_no_result(
        func,
        before,
        data::Mstore::new_unchecked(func.inst_set(), dst, value_id, value.ty()),
    );

    let mut filled = 32u32;
    while filled < total_len {
        let chunk = filled.min(total_len - filled);
        let dest = gep_word_offset(func, before, dst, filled / 32);
        let copy_len = imm_i256(func, chunk);
        insert_before_no_result(
            func,
            before,
            evm::EvmMcopy::new_unchecked(func.inst_set(), dest, dst, copy_len),
        );
        filled += chunk;
    }
    true
}

fn gep_word_offset(
    func: &mut Function,
    before: InstId,
    base: ValueId,
    word_offset: u32,
) -> ValueId {
    if word_offset == 0 {
        return base;
    }
    let index = imm_i256(func, word_offset);
    insert_before_one(
        func,
        before,
        data::Gep::new_unchecked(func.inst_set(), smallvec![base, index]),
        Type::I256.to_ptr(func.ctx()),
    )
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

fn imm_i256_usize(func: &mut Function, value: usize) -> Option<ValueId> {
    Some(imm_i256_u256(func, U256::from(u64::try_from(value).ok()?)))
}

fn imm_i256_u256(func: &mut Function, value: U256) -> ValueId {
    func.dfg.make_imm_value(Immediate::I256(I256::from(value)))
}

fn imm_i256_from_immediate(func: &mut Function, value: Immediate) -> ValueId {
    func.dfg.make_imm_value(Immediate::I256(value.as_i256()))
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

fn zext_to_ty(func: &mut Function, before: InstId, value: ValueId, ty: Type) -> ValueId {
    if func.dfg.value_ty(value) == ty {
        value
    } else {
        insert_before_one(
            func,
            before,
            cast::Zext::new_unchecked(func.inst_set(), value, ty),
            ty,
        )
    }
}

fn trunc_i256_to(func: &mut Function, before: InstId, value: ValueId, ty: Type) -> ValueId {
    if ty == Type::I256 {
        value
    } else {
        insert_before_one(
            func,
            before,
            cast::Trunc::new_unchecked(func.inst_set(), value, ty),
            ty,
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

fn sub_i256(func: &mut Function, before: InstId, lhs: ValueId, rhs: ValueId) -> ValueId {
    insert_before_one(
        func,
        before,
        arith::Sub::new_unchecked(func.inst_set(), lhs, rhs),
        Type::I256,
    )
}

fn shl_i256(func: &mut Function, before: InstId, value: ValueId, bits: ValueId) -> ValueId {
    insert_before_one(
        func,
        before,
        arith::Shl::new_unchecked(func.inst_set(), bits, value),
        Type::I256,
    )
}

fn umod_i256(func: &mut Function, before: InstId, lhs: ValueId, rhs: ValueId) -> ValueId {
    insert_before_one(
        func,
        before,
        evm::EvmUmod::new_unchecked(func.inst_set(), lhs, rhs),
        Type::I256,
    )
}

fn shr_i256(func: &mut Function, before: InstId, value: ValueId, bits: ValueId) -> ValueId {
    insert_before_one(
        func,
        before,
        arith::Shr::new_unchecked(func.inst_set(), bits, value),
        Type::I256,
    )
}

fn and_i256(func: &mut Function, before: InstId, lhs: ValueId, rhs: ValueId) -> ValueId {
    insert_before_one(
        func,
        before,
        logic::And::new_unchecked(func.inst_set(), lhs, rhs),
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
        object::{CompileOptions, SymbolId, compile_all_objects},
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

    fn lowered_blob_bytes(parsed: &sonatina_parser::ParsedModule, source_symbol: &str) -> Vec<u8> {
        let blob = parsed.module.ctx.with_gv_store(|store| {
            let source = store
                .lookup_gv(source_symbol)
                .unwrap_or_else(|| panic!("{source_symbol} global should exist"));
            let symbol = format!(
                "{}{source_symbol}_{}",
                super::CONST_WORD_POOL_PREFIX,
                source.as_u32()
            );
            store
                .lookup_gv(&symbol)
                .expect("synthesized blob should exist")
        });
        parsed.module.ctx.with_gv_store(|store| {
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
                .collect()
        })
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

global private const [i256; 5] $arr = [1, 3, 7, 15, 31];

func private %entry(v0.i256) -> i256 {
    block0:
        v1.constref<[i256; 5]> = const.ref $arr;
        v2.constref<i256> = const.index v1 v0;
        v3.i256 = const.load v2;
        return v3;
}
"#,
        );

        ConstDataLower::default().run(&parsed.module);

        let mut writer = ModuleWriter::with_debug_provider(&parsed.module, &parsed.debug);
        let dumped = writer.dump_string();
        assert!(dumped.contains("sym_addr $arr"));
        assert!(!dumped.contains("__sonatina_const_words_arr_"));
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

global private const [i64; 5] $arr = [1, 3, 7, 15, 31];
global private const [i8; 1] $__sonatina_const_words_arr_0 = [99];

func private %entry(v0.i256) -> i64 {
    block0:
        v1.constref<[i64; 5]> = const.ref $arr;
        v2.constref<i64> = const.index v1 v0;
        v3.i64 = const.load v2;
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
    fn dynamic_const_load_affine_i256_lowers_to_expression() {
        let parsed = parse(
            r#"
target = "evm-ethereum-osaka"

global private const [i256; 4] $arr = [10, 12, 14, 16];

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

        let entry = find_func_ref(&parsed, "entry");
        let dumped = parsed
            .module
            .func_store
            .view(entry, |func| FuncWriter::new(entry, func).dump_string());
        assert!(dumped.contains("mul"));
        assert!(dumped.contains("add"));
        assert!(!dumped.contains("evm_code_copy"));
        assert!(!dumped.contains("__sonatina_const_words"));
        assert!(!dumped.contains("const."));
    }

    #[test]
    fn dynamic_const_load_power_of_two_i256_lowers_to_shift() {
        let parsed = parse(
            r#"
target = "evm-ethereum-osaka"

global private const [i256; 4] $arr = [1, 2, 4, 8];

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

        let entry = find_func_ref(&parsed, "entry");
        let dumped = parsed
            .module
            .func_store
            .view(entry, |func| FuncWriter::new(entry, func).dump_string());
        assert!(dumped.contains("shl"));
        assert!(!dumped.contains("evm_code_copy"));
        assert!(!dumped.contains("__sonatina_const_words"));
        assert!(!dumped.contains("const."));
    }

    #[test]
    fn dynamic_const_load_periodic_i256_lowers_to_mod_expression() {
        let parsed = parse(
            r#"
target = "evm-ethereum-osaka"

global private const [i256; 6] $arr = [5, 13, 9, 5, 13, 9];

func private %entry(v0.i256) -> i256 {
    block0:
        v1.constref<[i256; 6]> = const.ref $arr;
        v2.constref<i256> = const.index v1 v0;
        v3.i256 = const.load v2;
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
        assert!(dumped.contains("evm_umod"));
        assert!(dumped.contains("eq"));
        assert!(!dumped.contains("evm_code_copy"));
        assert!(!dumped.contains("__sonatina_const_words"));
        assert!(!dumped.contains("const."));
    }

    #[test]
    fn dynamic_const_load_small_i8_lowers_to_packed_byte() {
        let parsed = parse(
            r#"
target = "evm-ethereum-osaka"

global private const [i8; 4] $arr = [10, 20, 30, 40];

func private %entry(v0.i256) -> i8 {
    block0:
        v1.constref<[i8; 4]> = const.ref $arr;
        v2.constref<i8> = const.index v1 v0;
        v3.i8 = const.load v2;
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
        assert!(dumped.contains("evm_byte"));
        assert!(!dumped.contains("evm_code_copy"));
        assert!(!dumped.contains("__sonatina_const_words"));
        assert!(!dumped.contains("const."));
    }

    #[test]
    fn dynamic_const_load_small_i16_lowers_to_packed_subword() {
        let parsed = parse(
            r#"
target = "evm-ethereum-osaka"

global private const [i16; 4] $arr = [100, 200, 400, 800];

func private %entry(v0.i256) -> i16 {
    block0:
        v1.constref<[i16; 4]> = const.ref $arr;
        v2.constref<i16> = const.index v1 v0;
        v3.i16 = const.load v2;
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
        assert!(dumped.contains("shr"));
        assert!(dumped.contains("trunc"));
        assert!(!dumped.contains("evm_code_copy"));
        assert!(!dumped.contains("__sonatina_const_words"));
        assert!(!dumped.contains("const."));
    }

    #[test]
    fn dynamic_const_load_small_i64_lowers_to_packed_subword() {
        let parsed = parse(
            r#"
target = "evm-ethereum-osaka"

global private const [i64; 4] $arr = [11, 99, 42, 77];

func private %entry(v0.i256) -> i64 {
    block0:
        v1.constref<[i64; 4]> = const.ref $arr;
        v2.constref<i64> = const.index v1 v0;
        v3.i64 = const.load v2;
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
        assert!(dumped.contains("shr"));
        assert!(dumped.contains("trunc"));
        assert!(!dumped.contains("evm_code_copy"));
        assert!(!dumped.contains("__sonatina_const_words"));
        assert!(!dumped.contains("const."));
    }

    #[test]
    fn dynamic_const_load_small_i1_lowers_to_bitset() {
        let parsed = parse(
            r#"
target = "evm-ethereum-osaka"

global private const [i1; 4] $arr = [0, 1, 0, 1];

func private %entry(v0.i256) -> i1 {
    block0:
        v1.constref<[i1; 4]> = const.ref $arr;
        v2.constref<i1> = const.index v1 v0;
        v3.i1 = const.load v2;
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
        assert!(dumped.contains("shr"));
        assert!(dumped.contains("and"));
        assert!(!dumped.contains("evm_code_copy"));
        assert!(!dumped.contains("__sonatina_const_words"));
        assert!(!dumped.contains("const."));
    }

    #[test]
    fn dynamic_const_load_small_i256_lowers_to_inline_selectors() {
        let parsed = parse(
            r#"
target = "evm-ethereum-osaka"

global private const [i256; 3] $arr = [5, 13, 9];

func private %entry(v0.i256) -> i256 {
    block0:
        v1.constref<[i256; 3]> = const.ref $arr;
        v2.constref<i256> = const.index v1 v0;
        v3.i256 = const.load v2;
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
        assert!(dumped.contains("eq"));
        assert!(dumped.contains("mul"));
        assert!(!dumped.contains("evm_umod"));
        assert!(!dumped.contains("evm_code_copy"));
        assert!(!dumped.contains("__sonatina_const_words"));
        assert!(!dumped.contains("const."));
    }

    #[test]
    fn dynamic_const_load_single_sparse_exception_lowers_to_expression() {
        let parsed = parse(
            r#"
target = "evm-ethereum-osaka"

global private const [i256; 4] $arr = [0, 0, 99, 0];

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

        let entry = find_func_ref(&parsed, "entry");
        let dumped = parsed
            .module
            .func_store
            .view(entry, |func| FuncWriter::new(entry, func).dump_string());
        assert!(dumped.contains("eq"));
        assert!(dumped.contains("mul"));
        assert!(!dumped.contains("evm_code_copy"));
        assert!(!dumped.contains("__sonatina_const_words"));
        assert!(!dumped.contains("const."));
    }

    #[test]
    fn dynamic_const_load_exact_synthesized_word_blobs_are_deduped() {
        let parsed = parse(
            r#"
target = "evm-ethereum-osaka"

global private const [i64; 5] $a = [1, 3, 7, 15, 31];
global private const [i64; 5] $b = [1, 3, 7, 15, 31];

func private %entry(v0.i256) -> i64 {
    block0:
        v1.constref<[i64; 5]> = const.ref $a;
        v2.constref<i64> = const.index v1 v0;
        v3.i64 = const.load v2;
        v4.constref<[i64; 5]> = const.ref $b;
        v5.constref<i64> = const.index v4 v0;
        v6.i64 = const.load v5;
        v7.i64 = add v3 v6;
        return v7;
}
"#,
        );

        ConstDataLower::default().run(&parsed.module);

        let symbols = global_symbols_with_prefix(&parsed, "__sonatina_const_words_");
        assert_eq!(symbols.len(), 1, "{symbols:?}");
    }

    #[test]
    fn obj_init_const_small_aggregate_lowers_to_stores() {
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
        assert!(!dumped.contains("obj.materialize.stack"));
        assert!(!dumped.contains("evm_code_copy"));
        assert!(!dumped.contains("__sonatina_const_words"));
        assert!(!dumped.contains("const."));
    }

    #[test]
    fn obj_init_const_small_narrow_aggregate_lowers_to_store() {
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
        assert!(dumped.contains("obj.store"));
        assert!(!dumped.contains("evm_code_copy"));
        assert!(!dumped.contains("__sonatina_const_words"));
        assert!(!dumped.contains("const."));
    }

    #[test]
    fn obj_init_const_bulk_codecopy_zero_extends_nested_narrow_words() {
        let parsed = parse(
            r#"
target = "evm-ethereum-osaka"

type @inner = { i1, [i16; 2] };
type @outer = { @inner, [i1; 2] };

global private const @outer $value = {{1, [-2, 3]}, [0, 1]};

func private %entry() -> i256 {
    block0:
        v0.objref<@outer> = obj.alloc @outer;
        v1.constref<@outer> = const.ref $value;
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

        let blob_bytes = lowered_blob_bytes(&parsed, "value");
        assert_eq!(blob_bytes.len(), 32 * 5);

        let words: Vec<_> = blob_bytes.chunks_exact(32).collect();
        assert!(words[0][..31].iter().all(|&byte| byte == 0));
        assert_eq!(words[0][31], 1);

        assert!(words[1][..30].iter().all(|&byte| byte == 0));
        assert_eq!(&words[1][30..], &[0xff, 0xfe]);

        assert!(words[2][..30].iter().all(|&byte| byte == 0));
        assert_eq!(&words[2][30..], &[0x00, 0x03]);

        assert!(words[3][..31].iter().all(|&byte| byte == 0));
        assert_eq!(words[3][31], 0);

        assert!(words[4][..31].iter().all(|&byte| byte == 0));
        assert_eq!(words[4][31], 1);
    }

    #[test]
    fn obj_init_const_zero_aggregate_lowers_to_zero_fill_without_blob() {
        let parsed = parse(
            r#"
target = "evm-ethereum-osaka"

global private const [i256; 5] $value = [0, 0, 0, 0, 0];

func private %entry() -> i256 {
    block0:
        v0.objref<[i256; 5]> = obj.alloc [i256; 5];
        v1.constref<[i256; 5]> = const.ref $value;
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
        assert!(dumped.contains("evm_code_size"));
        assert!(dumped.contains("evm_code_copy"));
        assert!(!dumped.contains("obj.store"));
        assert!(!dumped.contains("__sonatina_const_words"));
        assert_eq!(
            global_symbols_with_prefix(&parsed, "__sonatina_const_words_").len(),
            0
        );
    }

    #[test]
    fn obj_init_const_splat_aggregate_lowers_to_mcopy_fill_without_blob() {
        let parsed = parse(
            r#"
target = "evm-ethereum-osaka"

global private const [i256; 5] $value = [7, 7, 7, 7, 7];

func private %entry() -> i256 {
    block0:
        v0.objref<[i256; 5]> = obj.alloc [i256; 5];
        v1.constref<[i256; 5]> = const.ref $value;
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
        assert!(dumped.contains("mstore"));
        assert!(dumped.contains("evm_mcopy"));
        assert!(!dumped.contains("evm_code_copy"));
        assert!(!dumped.contains("obj.store"));
        assert!(!dumped.contains("__sonatina_const_words"));
        assert_eq!(
            global_symbols_with_prefix(&parsed, "__sonatina_const_words_").len(),
            0
        );
    }

    #[test]
    fn obj_init_const_mixed_aggregate_lowers_to_split_strategies() {
        let parsed = parse(
            r#"
target = "evm-ethereum-osaka"

type @mixed = { i256, [i256; 5], [i256; 5] };

global private const @mixed $value = {1, [0, 0, 0, 0, 0], [10, 20, 30, 40, 50]};

func private %entry() -> i256 {
    block0:
        v0.objref<@mixed> = obj.alloc @mixed;
        v1.constref<@mixed> = const.ref $value;
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
        assert!(dumped.contains("obj.store"));
        assert!(dumped.contains("evm_code_size"));
        assert_eq!(dumped.matches("evm_code_copy").count(), 2);
        assert_eq!(
            global_symbols_with_prefix(&parsed, "__sonatina_const_words_").len(),
            1
        );
        assert!(!dumped.contains("obj.init.const"));
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

global private const [i64; 5] $arr = [1, 3, 7, 15, 31];

func private %entry(v0.i256) -> i64 {
    block0:
        v1.constref<[i64; 5]> = const.ref $arr;
        v2.constref<i64> = const.index v1 v0;
        v3.i64 = const.load v2;
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
    fn word_compatible_dynamic_const_load_reuses_explicit_data_symbol() {
        let parsed = parse(
            r#"
target = "evm-ethereum-osaka"

global private const [i256; 5] $arr = [1, 3, 7, 15, 31];

func private %entry(v0.i256) -> i256 {
    block0:
        v1.constref<[i256; 5]> = const.ref $arr;
        v2.constref<i256> = const.index v1 v0;
        v3.i256 = const.load v2;
        return v3;
}

object @Contract {
  section runtime { entry %entry; data $arr; }
}
"#,
        );

        let arr = parsed
            .module
            .ctx
            .with_gv_store(|store| store.lookup_gv("arr").expect("arr global should exist"));
        let opts = CompileOptions {
            emit_symtab: true,
            ..Default::default()
        };
        let artifacts = compile_all_objects(&parsed.module, &test_backend(), &opts)
            .expect("object compilation should reuse compatible explicit data");
        let runtime = artifacts[0]
            .sections
            .values()
            .next()
            .expect("runtime section should exist");
        let arr_def = runtime
            .symtab
            .get(&SymbolId::Global(arr))
            .expect("arr symbol should be present");
        assert_eq!(arr_def.size, 160);
        assert_eq!(runtime.bytes.len(), 177);
    }

    #[test]
    fn dynamic_const_load_object_compile_succeeds_with_colliding_blob_symbol() {
        let parsed = parse(
            r#"
target = "evm-ethereum-osaka"

global private const [i64; 5] $arr = [1, 3, 7, 15, 31];
global private const [i8; 1] $__sonatina_const_words_arr_0 = [99];

func private %entry(v0.i256) -> i64 {
    block0:
        v1.constref<[i64; 5]> = const.ref $arr;
        v2.constref<i64> = const.index v1 v0;
        v3.i64 = const.load v2;
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
