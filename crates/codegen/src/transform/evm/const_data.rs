use rustc_hash::FxHashMap;
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    Function, GlobalVariableRef, I256, Immediate, InstId, Linkage, Module, Type, U256, Value,
    ValueId,
    effects::{OtherEffects, classify_inst_effects},
    global_variable::{GlobalVariableData, GlobalVariableStore, GvInitializer},
    inst::{arith, cast, data, downcast, evm, logic},
    module::ModuleCtx,
    object::Directive,
    types::{CompoundType, CompoundTypeRef},
};

use super::scalar_words::evm_scalar_word_bytes;

mod encoding;
mod lookup;
mod object_init;

pub(crate) const CONST_WORD_POOL_PREFIX: &str = "__sonatina_const_words_";

use crate::{
    optim::const_eval::{
        ConstPath, ConstPathAnalysis, ConstPathStep, analyze_const_paths,
        collect_constref_value_tys, const_path_steps, eval_const_path_domain_immediate,
        eval_const_path_dynamic_domain_immediates, eval_const_path_subtree,
    },
    transform::aggregate::shape,
    type_rewrite::{TypeRewrite, rewrite_compound_type_default, rewrite_function_type_uses},
};

type ConstOffsetTerms = Vec<(ValueId, u32)>;
type ConstOffsetPlan = (Type, u32, ConstOffsetTerms);
const MIN_ROW_COPY_WORDS: usize = 3;

use encoding::{
    MAX_SPLIT_OBJ_INIT_ARRAY_LEN, const_leaf_count, encode_const_words,
    encode_runtime_object_const_bytes, initializer_all_zero, initializer_scalar_splat,
    should_inline_obj_init, should_split_obj_init, word_blob_copy_len_bytes,
};
use lookup::{can_emit_dynamic_values_lookup, emit_dynamic_values_lookup};
use object_init::{
    emit_obj_init, emit_obj_init_from_addr, emit_obj_init_from_codecopy, emit_obj_splat_fill,
    emit_obj_zero_fill, gep_word_offset,
};

struct ConstRewriteInfo<'a> {
    constref_value_tys: &'a FxHashMap<ValueId, Type>,
    const_paths: &'a ConstPathAnalysis,
}

#[derive(Clone, PartialEq, Eq)]
enum ConstLoadRowBase {
    WordBlob(GlobalVariableRef),
    DynamicValues {
        source: GlobalVariableRef,
        values: Vec<Immediate>,
    },
}

#[derive(Clone, PartialEq, Eq)]
struct ConstLoadRowKey {
    base: ConstLoadRowBase,
    dynamic_terms: ConstOffsetTerms,
}

#[derive(Clone)]
struct ConstLoadRowCandidate {
    inst: InstId,
    order: usize,
    result_ty: Type,
    key: ConstLoadRowKey,
    word_offset: u32,
}

struct ConstLoadRowGroup {
    key: ConstLoadRowKey,
    candidates: Vec<ConstLoadRowCandidate>,
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

impl TypeRewrite for ConstRefTypeLowerer {
    fn compound_map(&mut self) -> &mut FxHashMap<CompoundTypeRef, Type> {
        &mut self.compound_map
    }

    fn rewrite_compound_type(
        &mut self,
        ctx: &ModuleCtx,
        compound: CompoundTypeRef,
        current: CompoundType,
    ) -> Type {
        match current {
            CompoundType::ConstRef(_) => ctx.type_layout.pointer_repl(),
            _ => rewrite_compound_type_default(self, ctx, compound, current),
        }
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
        changed |= self.rewrite_const_load_rows(module, func, &info);
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

    fn rewrite_const_load_rows(
        &mut self,
        module: &Module,
        func: &mut Function,
        info: &ConstRewriteInfo<'_>,
    ) -> bool {
        let mut changed = false;
        let blocks: Vec<_> = func.layout.iter_block().collect();
        for block in blocks {
            let insts: Vec<_> = func.layout.iter_inst(block).collect();
            let mut segment = Vec::new();
            for inst in insts {
                if !func.layout.is_inst_inserted(inst) {
                    continue;
                }
                if let Some(candidate) =
                    const_load_row_candidate(module, func, inst, segment.len(), info)
                {
                    segment.push(candidate);
                } else if const_load_row_barrier(func, inst) {
                    changed |= self.rewrite_const_load_row_segment(module, func, &mut segment);
                }
            }
            changed |= self.rewrite_const_load_row_segment(module, func, &mut segment);
        }
        changed
    }

    fn rewrite_const_load_row_segment(
        &mut self,
        module: &Module,
        func: &mut Function,
        segment: &mut Vec<ConstLoadRowCandidate>,
    ) -> bool {
        let mut groups = Vec::<ConstLoadRowGroup>::new();
        for candidate in segment.drain(..) {
            if let Some(group) = groups.iter_mut().find(|group| group.key == candidate.key) {
                group.candidates.push(candidate);
            } else {
                groups.push(ConstLoadRowGroup {
                    key: candidate.key.clone(),
                    candidates: vec![candidate],
                });
            }
        }

        let mut changed = false;
        for group in groups {
            changed |= self.rewrite_const_load_row_group(module, func, group);
        }
        changed
    }

    fn rewrite_const_load_row_group(
        &mut self,
        module: &Module,
        func: &mut Function,
        mut group: ConstLoadRowGroup,
    ) -> bool {
        group
            .candidates
            .sort_unstable_by_key(|candidate| candidate.word_offset);

        let mut changed = false;
        let mut run = Vec::new();
        let mut last_offset: Option<u32> = None;
        let mut unique_offsets = 0usize;
        let key = group.key;
        for candidate in group.candidates {
            match last_offset {
                Some(offset)
                    if offset
                        .checked_add(1)
                        .is_some_and(|next_offset| candidate.word_offset > next_offset) =>
                {
                    changed |=
                        self.rewrite_const_load_row_run(module, func, &key, &run, unique_offsets);
                    run.clear();
                    unique_offsets = 1;
                }
                Some(offset) if candidate.word_offset == offset => {}
                Some(_) | None => unique_offsets += 1,
            }
            last_offset = Some(candidate.word_offset);
            run.push(candidate);
        }
        changed |= self.rewrite_const_load_row_run(module, func, &key, &run, unique_offsets);
        changed
    }

    fn rewrite_const_load_row_run(
        &mut self,
        module: &Module,
        func: &mut Function,
        key: &ConstLoadRowKey,
        candidates: &[ConstLoadRowCandidate],
        unique_offsets: usize,
    ) -> bool {
        if unique_offsets < MIN_ROW_COPY_WORDS {
            return false;
        }

        let min_word = candidates
            .iter()
            .map(|candidate| candidate.word_offset)
            .min()
            .expect("row run must be non-empty");
        let max_word = candidates
            .iter()
            .map(|candidate| candidate.word_offset)
            .max()
            .expect("row run must be non-empty");
        let row_words = max_word
            .checked_sub(min_word)
            .and_then(|span| span.checked_add(1))
            .expect("row word span overflow");
        let before = candidates
            .iter()
            .min_by_key(|candidate| candidate.order)
            .expect("row run must be non-empty")
            .inst;
        let row_ptr = self.emit_const_load_row_copy(module, func, before, key, min_word, row_words);
        for candidate in candidates {
            let ptr = gep_word_offset(
                func,
                candidate.inst,
                row_ptr,
                candidate.word_offset - min_word,
            );
            let replacement = insert_before_one(
                func,
                candidate.inst,
                data::Mload::new_unchecked(func.inst_set(), ptr, candidate.result_ty),
                candidate.result_ty,
            );
            replace_with_alias(func, candidate.inst, replacement);
        }
        true
    }

    fn emit_const_load_row_copy(
        &mut self,
        module: &Module,
        func: &mut Function,
        before: InstId,
        key: &ConstLoadRowKey,
        min_word: u32,
        row_words: u32,
    ) -> ValueId {
        let base_addr = self.materialize_const_load_row_base_addr(module, func, before, &key.base);
        let row_addr = const_addr_with_offset(
            func,
            before,
            base_addr,
            min_word.checked_mul(32).expect("row byte offset overflow"),
            key.dynamic_terms.clone(),
            false,
        );
        let row_ty = func.ctx().with_ty_store_mut(|store| {
            store.make_array(
                Type::I256,
                usize::try_from(row_words).expect("row word count overflow"),
            )
        });
        let row_alloc = insert_before_one(
            func,
            before,
            data::Alloca::new_unchecked(func.inst_set(), row_ty),
            row_ty.to_ptr(func.ctx()),
        );
        let row_ptr_ty = Type::I256.to_ptr(func.ctx());
        let row_ptr = insert_before_one(
            func,
            before,
            cast::Bitcast::new_unchecked(func.inst_set(), row_alloc, row_ptr_ty),
            row_ptr_ty,
        );
        let copy_len = imm_i256(
            func,
            row_words.checked_mul(32).expect("row copy length overflow"),
        );
        insert_before_no_result(
            func,
            before,
            evm::EvmCodeCopy::new_unchecked(func.inst_set(), row_ptr, row_addr, copy_len),
        );
        row_ptr
    }

    fn materialize_const_load_row_base_addr(
        &mut self,
        module: &Module,
        func: &mut Function,
        before: InstId,
        base: &ConstLoadRowBase,
    ) -> ValueId {
        let blob = match base {
            ConstLoadRowBase::WordBlob(source) => self.word_blob_global(module, *source),
            ConstLoadRowBase::DynamicValues { source, values } => {
                let mut bytes = Vec::with_capacity(
                    values
                        .len()
                        .checked_mul(32)
                        .expect("dynamic const table size overflow"),
                );
                for &value in values {
                    bytes.extend_from_slice(
                        &evm_scalar_word_bytes(value)
                            .expect("row candidate must have encodable scalar values"),
                    );
                }
                self.bytes_blob_global(module, *source, bytes)
            }
        };
        insert_before_one(
            func,
            before,
            data::SymAddr::new_unchecked(func.inst_set(), data::SymbolRef::Global(blob)),
            func.ctx().type_layout.pointer_repl(),
        )
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
            && global_is_explicit_object_data(module, source)
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

fn global_is_explicit_object_data(module: &Module, gv: GlobalVariableRef) -> bool {
    module.objects.values().any(|object| {
        object.sections.iter().any(|section| {
            section
                .directives
                .iter()
                .any(|directive| matches!(directive, Directive::Data(data) if *data == gv))
        })
    })
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
    rewrite_function_type_uses(func, types, |_, _, _| None)
}

fn inserted_insts(func: &Function) -> Vec<InstId> {
    func.layout
        .iter_block()
        .flat_map(|block| func.layout.iter_inst(block))
        .collect()
}

fn const_load_row_candidate(
    module: &Module,
    func: &Function,
    inst: InstId,
    order: usize,
    info: &ConstRewriteInfo<'_>,
) -> Option<ConstLoadRowCandidate> {
    let load = downcast::<&data::ConstLoad>(func.inst_set(), func.dfg.inst(inst)).cloned()?;
    let result_ty = func
        .dfg
        .inst_result(inst)
        .map(|result| func.dfg.value_ty(result))?;
    if !result_ty.is_integral() {
        return None;
    }

    let path = info.const_paths.path(*load.object())?;
    if eval_const_path_domain_immediate(&module.ctx, path, |value| func.dfg.value_imm(value))
        .is_some()
    {
        return None;
    }
    if let Some((index, values)) =
        eval_const_path_dynamic_domain_immediates(&module.ctx, path, |value| {
            func.dfg.value_imm(value)
        })
    {
        if values.iter().any(|imm| imm.ty() != result_ty)
            || can_emit_dynamic_values_lookup(result_ty, &values, true)
            || values
                .iter()
                .any(|&value| evm_scalar_word_bytes(value).is_none())
        {
            return None;
        }
        let (word_offset, dynamic_terms) =
            normalize_const_load_row_offset(func, 0, vec![(index, 32)])?;
        return Some(ConstLoadRowCandidate {
            inst,
            order,
            result_ty,
            key: ConstLoadRowKey {
                base: ConstLoadRowBase::DynamicValues {
                    source: path.global,
                    values,
                },
                dynamic_terms,
            },
            word_offset,
        });
    }

    let root_ty = module.ctx.with_gv_store(|store| store.ty(path.global));
    let (ty, const_offset_bytes, dynamic_terms) =
        const_steps_offset_bytes(func.ctx(), root_ty, &path.steps)?;
    if ty != result_ty {
        return None;
    }
    let (word_offset, dynamic_terms) =
        normalize_const_load_row_offset(func, const_offset_bytes, dynamic_terms)?;
    Some(ConstLoadRowCandidate {
        inst,
        order,
        result_ty,
        key: ConstLoadRowKey {
            base: ConstLoadRowBase::WordBlob(path.global),
            dynamic_terms,
        },
        word_offset,
    })
}

fn const_load_row_barrier(func: &Function, inst: InstId) -> bool {
    let effects = classify_inst_effects(&func.dfg, inst);
    !effects.accesses.is_empty()
        || effects
            .other
            .intersects(OtherEffects::OBSERVE | OtherEffects::MUTATE | OtherEffects::CONTROL)
}

fn normalize_const_load_row_offset(
    func: &Function,
    const_offset_bytes: u32,
    dynamic_terms: ConstOffsetTerms,
) -> Option<(u32, ConstOffsetTerms)> {
    let mut const_offset = i64::from(const_offset_bytes);
    let mut normalized_terms = Vec::with_capacity(dynamic_terms.len());
    for (value, stride_bytes) in dynamic_terms {
        if stride_bytes % 32 != 0 {
            return None;
        }
        let (base, value_offset) = normalize_index_value_offset(func, value)?;
        const_offset =
            const_offset.checked_add(value_offset.checked_mul(i64::from(stride_bytes))?)?;
        normalized_terms.push((base, stride_bytes));
    }
    if const_offset < 0 || const_offset % 32 != 0 {
        return None;
    }

    normalized_terms.sort_unstable_by_key(|(value, stride)| (value.0, *stride));
    let mut combined: ConstOffsetTerms = Vec::with_capacity(normalized_terms.len());
    for (value, stride) in normalized_terms {
        if let Some((last_value, last_stride)) = combined.last_mut()
            && *last_value == value
        {
            *last_stride = last_stride.checked_add(stride)?;
            continue;
        }
        combined.push((value, stride));
    }

    Some((u32::try_from(const_offset / 32).ok()?, combined))
}

fn normalize_index_value_offset(func: &Function, mut value: ValueId) -> Option<(ValueId, i64)> {
    let mut offset = 0i64;
    loop {
        if func.dfg.value_ty(value) != Type::I256 {
            return Some((value, offset));
        }
        let Some((inst, 0)) = func.dfg.value_inst_result(value) else {
            return Some((value, offset));
        };

        let inst_data = func.dfg.inst(inst);
        if let Some(add) = downcast::<&arith::Add>(func.inst_set(), inst_data) {
            if let Some(rhs_offset) = additive_index_offset(func, *add.rhs())
                && func.dfg.value_ty(*add.lhs()) == Type::I256
            {
                value = *add.lhs();
                offset = offset.checked_add(rhs_offset)?;
                continue;
            }
            if let Some(lhs_offset) = additive_index_offset(func, *add.lhs())
                && func.dfg.value_ty(*add.rhs()) == Type::I256
            {
                value = *add.rhs();
                offset = offset.checked_add(lhs_offset)?;
                continue;
            }
        }

        if let Some(sub) = downcast::<&arith::Sub>(func.inst_set(), inst_data)
            && let Some(rhs_offset) = additive_index_offset(func, *sub.rhs())
            && func.dfg.value_ty(*sub.lhs()) == Type::I256
        {
            value = *sub.lhs();
            offset = offset.checked_sub(rhs_offset)?;
            continue;
        }

        return Some((value, offset));
    }
}

fn additive_index_offset(func: &Function, value: ValueId) -> Option<i64> {
    let imm = func.dfg.value_imm(value)?;
    let value = imm.as_i256();
    if value < I256::from(i64::MIN) || value > I256::from(i64::MAX) {
        return None;
    }
    Some(value.trunc_to_i64())
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

pub(super) fn insert_before_one<I: sonatina_ir::Inst>(
    func: &mut Function,
    before: InstId,
    data: I,
    result_ty: Type,
) -> ValueId {
    insert_before_results(func, before, data, &[result_ty])[0]
}

pub(super) fn insert_before_no_result<I: sonatina_ir::Inst>(
    func: &mut Function,
    before: InstId,
    data: I,
) {
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

pub(super) fn imm_i256(func: &mut Function, value: u32) -> ValueId {
    func.dfg
        .make_imm_value(Immediate::I256(I256::from(u64::from(value))))
}

pub(super) fn imm_i256_usize(func: &mut Function, value: usize) -> Option<ValueId> {
    Some(imm_i256_u256(func, U256::from(u64::try_from(value).ok()?)))
}

pub(super) fn imm_i256_u256(func: &mut Function, value: U256) -> ValueId {
    func.dfg.make_imm_value(Immediate::I256(I256::from(value)))
}

pub(super) fn imm_i256_from_immediate(func: &mut Function, value: Immediate) -> ValueId {
    func.dfg.make_imm_value(Immediate::I256(value.as_i256()))
}

pub(super) fn const_addr_with_offset(
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

pub(super) fn emit_const_load_from_addr(
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

pub(super) fn zext_to_i256(func: &mut Function, before: InstId, value: ValueId) -> ValueId {
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

pub(super) fn zext_to_ty(func: &mut Function, before: InstId, value: ValueId, ty: Type) -> ValueId {
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

pub(super) fn trunc_i256_to(
    func: &mut Function,
    before: InstId,
    value: ValueId,
    ty: Type,
) -> ValueId {
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

pub(super) fn add_i256(func: &mut Function, before: InstId, lhs: ValueId, rhs: ValueId) -> ValueId {
    insert_before_one(
        func,
        before,
        arith::Add::new_unchecked(func.inst_set(), lhs, rhs),
        Type::I256,
    )
}

pub(super) fn sub_i256(func: &mut Function, before: InstId, lhs: ValueId, rhs: ValueId) -> ValueId {
    insert_before_one(
        func,
        before,
        arith::Sub::new_unchecked(func.inst_set(), lhs, rhs),
        Type::I256,
    )
}

pub(super) fn shl_i256(
    func: &mut Function,
    before: InstId,
    value: ValueId,
    bits: ValueId,
) -> ValueId {
    insert_before_one(
        func,
        before,
        arith::Shl::new_unchecked(func.inst_set(), bits, value),
        Type::I256,
    )
}

pub(super) fn umod_i256(
    func: &mut Function,
    before: InstId,
    lhs: ValueId,
    rhs: ValueId,
) -> ValueId {
    insert_before_one(
        func,
        before,
        evm::EvmUmod::new_unchecked(func.inst_set(), lhs, rhs),
        Type::I256,
    )
}

pub(super) fn shr_i256(
    func: &mut Function,
    before: InstId,
    value: ValueId,
    bits: ValueId,
) -> ValueId {
    insert_before_one(
        func,
        before,
        arith::Shr::new_unchecked(func.inst_set(), bits, value),
        Type::I256,
    )
}

pub(super) fn and_i256(func: &mut Function, before: InstId, lhs: ValueId, rhs: ValueId) -> ValueId {
    insert_before_one(
        func,
        before,
        logic::And::new_unchecked(func.inst_set(), lhs, rhs),
        Type::I256,
    )
}

pub(super) fn mul_i256(func: &mut Function, before: InstId, lhs: ValueId, rhs: ValueId) -> ValueId {
    insert_before_one(
        func,
        before,
        arith::Mul::new_unchecked(func.inst_set(), lhs, rhs),
        Type::I256,
    )
}

#[cfg(test)]
mod tests;
