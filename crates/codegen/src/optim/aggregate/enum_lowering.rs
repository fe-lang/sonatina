use rustc_hash::FxHashMap;
use smallvec::smallvec;
use sonatina_ir::{
    Function, I256, Immediate, Module, Type, Value, ValueId,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{cmp, data, downcast},
    module::ModuleCtx,
    types::{CompoundType, CompoundTypeRef, EnumData, EnumVariantRef},
    visitor::VisitorMut,
};

#[derive(Clone)]
struct EnumLayoutInfo {
    lowered_cmpd: CompoundTypeRef,
    tag_ty: Type,
    variant_field_starts: Vec<u32>,
    lowered_variant_field_tys: Vec<Vec<Type>>,
}

impl EnumLayoutInfo {
    fn lowered_ty(&self) -> Type {
        Type::Compound(self.lowered_cmpd)
    }

    fn tag_imm(&self, variant: EnumVariantRef) -> Immediate {
        Immediate::from_i256(I256::from(u64::from(variant.index())), self.tag_ty)
    }

    fn payload_slot(&self, variant: EnumVariantRef, field_idx: usize) -> u32 {
        self.variant_field_starts[usize::try_from(variant.index()).expect("variant index overflow")]
            + u32::try_from(field_idx).expect("field index overflow")
    }

    fn payload_tys(&self, variant: EnumVariantRef) -> &[Type] {
        &self.lowered_variant_field_tys
            [usize::try_from(variant.index()).expect("variant index overflow")]
    }
}

#[derive(Default)]
struct EnumTypeLowerer {
    changed: bool,
    compound_map: FxHashMap<CompoundTypeRef, CompoundTypeRef>,
    layouts: FxHashMap<CompoundTypeRef, EnumLayoutInfo>,
}

impl EnumTypeLowerer {
    fn rewrite_type(&mut self, ctx: &ModuleCtx, ty: Type) -> Type {
        match ty {
            Type::EnumTag(enum_ty) => self.layout(ctx, enum_ty).tag_ty,
            Type::Compound(compound) => Type::Compound(self.rewrite_compound(ctx, compound)),
            _ => ty,
        }
    }

    fn layout(&mut self, ctx: &ModuleCtx, enum_ty: CompoundTypeRef) -> EnumLayoutInfo {
        if let Some(layout) = self.layouts.get(&enum_ty) {
            return layout.clone();
        }

        let data = ctx
            .with_ty_store(|store| store.enum_data(enum_ty).cloned())
            .expect("layout requested for non-enum type");
        let tag_ty = choose_tag_ty(data.variants.len());
        let lowered_name = format!("__enum_lowered_{}_{}", data.name, enum_ty.as_u32());
        let lowered_cmpd = ctx.with_ty_store_mut(|store| {
            if let Some(existing) = store.lookup_struct(&lowered_name) {
                existing
            } else {
                let Type::Compound(cmpd) = store.make_struct(&lowered_name, &[], false) else {
                    unreachable!();
                };
                cmpd
            }
        });

        self.compound_map.insert(enum_ty, lowered_cmpd);

        let mut struct_fields = vec![tag_ty];
        let mut variant_field_starts = Vec::with_capacity(data.variants.len());
        let mut lowered_variant_field_tys = Vec::with_capacity(data.variants.len());
        let mut next_slot = 1u32;
        for variant in &data.variants {
            variant_field_starts.push(next_slot);
            let lowered_fields: Vec<_> = variant
                .fields
                .iter()
                .map(|&field| self.rewrite_type(ctx, field))
                .collect();
            next_slot += u32::try_from(lowered_fields.len()).expect("too many enum payload fields");
            struct_fields.extend(lowered_fields.iter().copied());
            lowered_variant_field_tys.push(lowered_fields);
        }

        ctx.with_ty_store_mut(|store| store.update_struct_fields(&lowered_name, &struct_fields));

        let layout = EnumLayoutInfo {
            lowered_cmpd,
            tag_ty,
            variant_field_starts,
            lowered_variant_field_tys,
        };
        self.layouts.insert(enum_ty, layout.clone());
        self.changed = true;
        layout
    }

    fn rewrite_compound(&mut self, ctx: &ModuleCtx, compound: CompoundTypeRef) -> CompoundTypeRef {
        if let Some(&mapped) = self.compound_map.get(&compound) {
            return mapped;
        }

        let current = ctx.with_ty_store(|store| store.resolve_compound(compound).clone());
        self.compound_map.insert(compound, compound);

        let mapped = match current {
            CompoundType::Enum(EnumData { .. }) => self.layout(ctx, compound).lowered_cmpd,
            CompoundType::Array { elem, len } => {
                let elem = self.rewrite_type(ctx, elem);
                ctx.with_ty_store_mut(|store| {
                    let Type::Compound(mapped) = store.make_array(elem, len) else {
                        unreachable!();
                    };
                    mapped
                })
            }
            CompoundType::Ptr(elem) => {
                let elem = self.rewrite_type(ctx, elem);
                ctx.with_ty_store_mut(|store| {
                    let Type::Compound(mapped) = store.make_ptr(elem) else {
                        unreachable!();
                    };
                    mapped
                })
            }
            CompoundType::ObjRef(elem) => {
                let elem = self.rewrite_type(ctx, elem);
                ctx.with_ty_store_mut(|store| {
                    let Type::Compound(mapped) = store.make_obj_ref(elem) else {
                        unreachable!();
                    };
                    mapped
                })
            }
            CompoundType::Func { args, ret_tys } => {
                let args: Vec<_> = args
                    .iter()
                    .map(|&arg| self.rewrite_type(ctx, arg))
                    .collect();
                let ret_tys: Vec<_> = ret_tys
                    .iter()
                    .map(|&ret_ty| self.rewrite_type(ctx, ret_ty))
                    .collect();
                ctx.with_ty_store_mut(|store| {
                    let Type::Compound(mapped) = store.make_func(&args, &ret_tys) else {
                        unreachable!();
                    };
                    mapped
                })
            }
            CompoundType::Struct(data) => {
                let new_fields: Vec<_> = data
                    .fields
                    .iter()
                    .map(|&field| self.rewrite_type(ctx, field))
                    .collect();
                if new_fields != data.fields {
                    ctx.with_ty_store_mut(|store| {
                        store.update_struct_fields(&data.name, &new_fields)
                    });
                    self.changed = true;
                }
                compound
            }
        };

        if mapped != compound {
            self.changed = true;
        }
        self.compound_map.insert(compound, mapped);
        mapped
    }
}

#[derive(Default)]
pub struct EnumLowerToProduct;

impl EnumLowerToProduct {
    pub fn run(&mut self, module: &Module) -> bool {
        let mut lowerer = EnumTypeLowerer::default();
        let mut changed = rewrite_declared_signatures(module, &mut lowerer);
        changed |= rewrite_global_types(module, &mut lowerer);

        for func_ref in module.funcs() {
            changed |= module.func_store.modify(func_ref, |function| {
                rewrite_function_enum_insts(function, &mut lowerer);
                rewrite_function_types(function, &mut lowerer)
            });
        }

        changed || lowerer.changed
    }
}

fn rewrite_declared_signatures(module: &Module, lowerer: &mut EnumTypeLowerer) -> bool {
    let funcs: Vec<_> = module
        .ctx
        .declared_funcs
        .iter()
        .map(|entry| *entry.key())
        .collect();
    let mut changed = false;

    for func in funcs {
        let Some(sig) = module.ctx.get_sig(func) else {
            continue;
        };
        let new_args: Vec<_> = sig
            .args()
            .iter()
            .map(|&arg| lowerer.rewrite_type(&module.ctx, arg))
            .collect();
        let new_rets: Vec<_> = sig
            .ret_tys()
            .iter()
            .map(|&ret| lowerer.rewrite_type(&module.ctx, ret))
            .collect();
        if new_args == sig.args() && new_rets == sig.ret_tys() {
            continue;
        }

        module
            .ctx
            .declared_funcs
            .get_mut(&func)
            .expect("declared signature must exist")
            .clone_from(&sonatina_ir::Signature::new(
                sig.name(),
                sig.linkage(),
                &new_args,
                &new_rets,
            ));
        changed = true;
    }

    changed
}

fn rewrite_global_types(module: &Module, lowerer: &mut EnumTypeLowerer) -> bool {
    let globals: Vec<_> = module
        .ctx
        .with_gv_store(|store| store.all_gv_refs().collect());
    let mut changed = false;

    module.ctx.with_gv_store_mut(|store| {
        for gv in globals {
            let Some(gv_data) = store.get(gv).cloned() else {
                continue;
            };
            let new_ty = lowerer.rewrite_type(&module.ctx, gv_data.ty);
            if new_ty != gv_data.ty {
                store.update_ty(gv, new_ty);
                changed = true;
            }
        }
    });

    changed
}

fn rewrite_function_enum_insts(function: &mut Function, lowerer: &mut EnumTypeLowerer) -> bool {
    let mut changed = false;

    let blocks: Vec<_> = function.layout.iter_block().collect();
    for block in blocks {
        let insts: Vec<_> = function.layout.iter_inst(block).collect();
        for inst in insts {
            if !function.layout.is_inst_inserted(inst) {
                continue;
            }
            changed |= rewrite_inst(function, inst, lowerer);
        }
    }

    changed
}

fn rewrite_inst(
    function: &mut Function,
    inst: sonatina_ir::InstId,
    lowerer: &mut EnumTypeLowerer,
) -> bool {
    if let Some(enum_make) =
        downcast::<&data::EnumMake>(function.inst_set(), function.dfg.inst(inst)).cloned()
    {
        let layout = lowerer.layout(function.ctx(), enum_make.variant().enum_ty());
        let aggregate = lower_enum_make(function, inst, &layout, &enum_make);
        alias_and_remove_inst(function, inst, Some(aggregate));
        return true;
    }

    if let Some(enum_tag) =
        downcast::<&data::EnumTag>(function.inst_set(), function.dfg.inst(inst)).cloned()
    {
        let result = function
            .dfg
            .inst_result(inst)
            .expect("enum.tag must have a result before lowering");
        let Type::EnumTag(enum_ty) = function.dfg.value_ty(result) else {
            panic!("enum.tag result must use enumtag type before lowering");
        };
        let layout = lowerer.layout(function.ctx(), enum_ty);
        let tag = insert_extract_value_before(function, inst, *enum_tag.value(), 0, layout.tag_ty);
        alias_and_remove_inst(function, inst, Some(tag));
        return true;
    }

    if let Some(enum_is_variant) =
        downcast::<&data::EnumIsVariant>(function.inst_set(), function.dfg.inst(inst)).cloned()
    {
        let layout = lowerer.layout(function.ctx(), enum_is_variant.variant().enum_ty());
        let tag =
            insert_extract_value_before(function, inst, *enum_is_variant.value(), 0, layout.tag_ty);
        let tag_const = function
            .dfg
            .make_imm_value(layout.tag_imm(*enum_is_variant.variant()));
        let eq = insert_result_inst(
            function,
            inst,
            Box::new(cmp::Eq::new_unchecked(function.inst_set(), tag, tag_const)),
            Type::I1,
        );
        alias_and_remove_inst(function, inst, Some(eq));
        return true;
    }

    if downcast::<&data::EnumAssertVariant>(function.inst_set(), function.dfg.inst(inst)).is_some()
    {
        alias_and_remove_inst(function, inst, None);
        return true;
    }

    if let Some(enum_assert_ref) =
        downcast::<&data::EnumAssertVariantRef>(function.inst_set(), function.dfg.inst(inst))
    {
        alias_and_remove_inst(function, inst, Some(*enum_assert_ref.object()));
        return true;
    }

    if let Some(enum_extract) =
        downcast::<&data::EnumExtract>(function.inst_set(), function.dfg.inst(inst)).cloned()
    {
        let layout = lowerer.layout(function.ctx(), enum_extract.variant().enum_ty());
        let field_idx = function
            .dfg
            .value_imm(*enum_extract.field())
            .expect("enum.extract field index must be immediate")
            .as_usize();
        let result_ty = layout.payload_tys(*enum_extract.variant())[field_idx];
        let slot = layout.payload_slot(*enum_extract.variant(), field_idx);
        let value =
            insert_extract_value_before(function, inst, *enum_extract.value(), slot, result_ty);
        alias_and_remove_inst(function, inst, Some(value));
        return true;
    }

    if let Some(enum_set_tag) =
        downcast::<&data::EnumSetTag>(function.inst_set(), function.dfg.inst(inst)).cloned()
    {
        let layout = lowerer.layout(function.ctx(), enum_set_tag.variant().enum_ty());
        let tag_slot =
            insert_obj_proj_before(function, inst, *enum_set_tag.object(), 0, layout.tag_ty);
        let tag_value = function
            .dfg
            .make_imm_value(layout.tag_imm(*enum_set_tag.variant()));
        insert_no_result_inst(
            function,
            inst,
            Box::new(data::ObjStore::new_unchecked(
                function.inst_set(),
                tag_slot,
                tag_value,
            )),
        );
        alias_and_remove_inst(function, inst, None);
        return true;
    }

    if let Some(enum_write) =
        downcast::<&data::EnumWriteVariant>(function.inst_set(), function.dfg.inst(inst)).cloned()
    {
        let layout = lowerer.layout(function.ctx(), enum_write.variant().enum_ty());
        for (field_idx, &value) in enum_write.values().iter().enumerate() {
            let field_ty = layout.payload_tys(*enum_write.variant())[field_idx];
            let slot = layout.payload_slot(*enum_write.variant(), field_idx);
            let field_obj =
                insert_obj_proj_before(function, inst, *enum_write.object(), slot, field_ty);
            insert_no_result_inst(
                function,
                inst,
                Box::new(data::ObjStore::new_unchecked(
                    function.inst_set(),
                    field_obj,
                    value,
                )),
            );
        }

        let tag_slot =
            insert_obj_proj_before(function, inst, *enum_write.object(), 0, layout.tag_ty);
        let tag_value = function
            .dfg
            .make_imm_value(layout.tag_imm(*enum_write.variant()));
        insert_no_result_inst(
            function,
            inst,
            Box::new(data::ObjStore::new_unchecked(
                function.inst_set(),
                tag_slot,
                tag_value,
            )),
        );
        alias_and_remove_inst(function, inst, None);
        return true;
    }

    if let Some(enum_get_tag) =
        downcast::<&data::EnumGetTag>(function.inst_set(), function.dfg.inst(inst)).cloned()
    {
        let result = function
            .dfg
            .inst_result(inst)
            .expect("enum.get_tag must have a result before lowering");
        let Type::EnumTag(enum_ty) = function.dfg.value_ty(result) else {
            panic!("enum.get_tag result must use enumtag type before lowering");
        };
        let layout = lowerer.layout(function.ctx(), enum_ty);
        let tag_slot =
            insert_obj_proj_before(function, inst, *enum_get_tag.object(), 0, layout.tag_ty);
        let tag = insert_result_inst(
            function,
            inst,
            Box::new(data::ObjLoad::new_unchecked(function.inst_set(), tag_slot)),
            layout.tag_ty,
        );
        alias_and_remove_inst(function, inst, Some(tag));
        return true;
    }

    if let Some(enum_proj) =
        downcast::<&data::EnumProj>(function.inst_set(), function.dfg.inst(inst)).cloned()
    {
        let layout = lowerer.layout(function.ctx(), enum_proj.variant().enum_ty());
        let field_idx = function
            .dfg
            .value_imm(*enum_proj.field())
            .expect("enum.proj field index must be immediate")
            .as_usize();
        let field_ty = layout.payload_tys(*enum_proj.variant())[field_idx];
        let slot = layout.payload_slot(*enum_proj.variant(), field_idx);
        let field = insert_obj_proj_before(function, inst, *enum_proj.object(), slot, field_ty);
        alias_and_remove_inst(function, inst, Some(field));
        return true;
    }

    false
}

fn rewrite_function_types(function: &mut Function, lowerer: &mut EnumTypeLowerer) -> bool {
    let mut changed = false;
    let value_ids: Vec<_> = function.dfg.value_ids().collect();
    for value_id in value_ids {
        let old_ty = function.dfg.value_ty(value_id);
        let new_ty = lowerer.rewrite_type(function.ctx(), old_ty);
        if new_ty == old_ty {
            continue;
        }

        function.dfg.values[value_id] = match function.dfg.value(value_id).clone() {
            Value::Immediate { imm, .. } => Value::Immediate {
                imm: if imm.ty() == new_ty {
                    imm
                } else {
                    Immediate::from_i256(imm.as_i256(), new_ty)
                },
                ty: new_ty,
            },
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
        lowerer: &'a mut EnumTypeLowerer,
        changed: bool,
    }

    impl VisitorMut for TypeVisitor<'_> {
        fn visit_ty(&mut self, item: &mut Type) {
            let new_ty = self.lowerer.rewrite_type(&self.ctx, *item);
            self.changed |= new_ty != *item;
            *item = new_ty;
        }
    }

    let mut visitor = TypeVisitor {
        ctx: function.ctx().clone(),
        lowerer,
        changed: false,
    };
    let blocks: Vec<_> = function.layout.iter_block().collect();
    for block in blocks {
        let insts: Vec<_> = function.layout.iter_inst(block).collect();
        for inst in insts {
            if function.layout.is_inst_inserted(inst) {
                function.dfg.inst_mut(inst).accept_mut(&mut visitor);
            }
        }
    }

    changed || visitor.changed
}

fn lower_enum_make(
    function: &mut Function,
    inst: sonatina_ir::InstId,
    layout: &EnumLayoutInfo,
    enum_make: &data::EnumMake,
) -> ValueId {
    let mut aggregate = function.dfg.make_undef_value(layout.lowered_ty());
    let tag = function
        .dfg
        .make_imm_value(layout.tag_imm(*enum_make.variant()));
    aggregate = insert_insert_value_before(function, inst, aggregate, 0, tag, layout.lowered_ty());
    for (field_idx, &value) in enum_make.values().iter().enumerate() {
        let slot = layout.payload_slot(*enum_make.variant(), field_idx);
        aggregate =
            insert_insert_value_before(function, inst, aggregate, slot, value, layout.lowered_ty());
    }
    aggregate
}

fn choose_tag_ty(variant_count: usize) -> Type {
    if variant_count <= 2 {
        Type::I1
    } else if u8::try_from(variant_count).is_ok() {
        Type::I8
    } else if u16::try_from(variant_count).is_ok() {
        Type::I16
    } else if u32::try_from(variant_count).is_ok() {
        Type::I32
    } else if u64::try_from(variant_count).is_ok() {
        Type::I64
    } else {
        Type::I256
    }
}

fn insert_insert_value_before(
    function: &mut Function,
    inst: sonatina_ir::InstId,
    dest: ValueId,
    idx: u32,
    value: ValueId,
    ty: Type,
) -> ValueId {
    let idx_value = function.dfg.make_imm_value(i64::from(idx));
    insert_result_inst(
        function,
        inst,
        Box::new(data::InsertValue::new_unchecked(
            function.inst_set(),
            dest,
            idx_value,
            value,
        )),
        ty,
    )
}

fn insert_extract_value_before(
    function: &mut Function,
    inst: sonatina_ir::InstId,
    dest: ValueId,
    idx: u32,
    ty: Type,
) -> ValueId {
    let idx_value = function.dfg.make_imm_value(i64::from(idx));
    insert_result_inst(
        function,
        inst,
        Box::new(data::ExtractValue::new_unchecked(
            function.inst_set(),
            dest,
            idx_value,
        )),
        ty,
    )
}

fn insert_obj_proj_before(
    function: &mut Function,
    inst: sonatina_ir::InstId,
    object: ValueId,
    idx: u32,
    field_ty: Type,
) -> ValueId {
    let idx_value = function.dfg.make_imm_value(i64::from(idx));
    let result_ty = function
        .ctx()
        .with_ty_store_mut(|store| store.make_obj_ref(field_ty));
    insert_result_inst(
        function,
        inst,
        Box::new(data::ObjProj::new_unchecked(
            function.inst_set(),
            smallvec![object, idx_value],
        )),
        result_ty,
    )
}

fn insert_result_inst(
    function: &mut Function,
    before: sonatina_ir::InstId,
    data: Box<dyn sonatina_ir::Inst>,
    ty: Type,
) -> ValueId {
    let mut cursor = InstInserter::at_location(inst_insert_loc(function, before));
    let inst = cursor.insert_inst_data_dyn(function, data);
    let value = cursor.make_result(function, inst, ty);
    cursor.attach_result(function, inst, value);
    value
}

fn insert_no_result_inst(
    function: &mut Function,
    before: sonatina_ir::InstId,
    data: Box<dyn sonatina_ir::Inst>,
) {
    let mut cursor = InstInserter::at_location(inst_insert_loc(function, before));
    let _ = cursor.insert_inst_data_dyn(function, data);
}

fn inst_insert_loc(function: &Function, inst: sonatina_ir::InstId) -> CursorLocation {
    function.layout.prev_inst_of(inst).map_or(
        CursorLocation::BlockTop(function.layout.inst_block(inst)),
        CursorLocation::At,
    )
}

fn alias_and_remove_inst(
    function: &mut Function,
    inst: sonatina_ir::InstId,
    replacement: Option<ValueId>,
) {
    if let Some(result) = function.dfg.inst_result(inst)
        && let Some(replacement) = replacement
    {
        function.dfg.change_to_alias(result, replacement);
    }
    function.layout.remove_inst(inst);
    function.erase_inst(inst);
}
