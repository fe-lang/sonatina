use rustc_hash::FxHashMap;
use sonatina_ir::{
    Function, Type, ValueId,
    module::ModuleCtx,
    types::{CompoundType, CompoundTypeRef, StructData},
    visitor::VisitorMut,
};

pub(crate) trait TypeRewrite {
    fn compound_map(&mut self) -> &mut FxHashMap<CompoundTypeRef, Type>;

    fn rewrite_leaf_type(&mut self, _ctx: &ModuleCtx, ty: Type) -> Type {
        ty
    }

    fn rewrite_compound_type(
        &mut self,
        ctx: &ModuleCtx,
        compound: CompoundTypeRef,
        current: CompoundType,
    ) -> Type
    where
        Self: Sized,
    {
        rewrite_compound_type_default(self, ctx, compound, current)
    }

    fn note_compound_remap(&mut self, _compound: CompoundTypeRef, _mapped: Type) {}

    fn note_named_compound_update(&mut self, _compound: CompoundTypeRef) {}

    fn rewrite_type(&mut self, ctx: &ModuleCtx, ty: Type) -> Type
    where
        Self: Sized,
    {
        match self.rewrite_leaf_type(ctx, ty) {
            Type::Compound(compound) => self.rewrite_compound(ctx, compound),
            ty => ty,
        }
    }

    fn rewrite_compound(&mut self, ctx: &ModuleCtx, compound: CompoundTypeRef) -> Type
    where
        Self: Sized,
    {
        if let Some(mapped) = self.compound_map().get(&compound).copied() {
            return mapped;
        }

        self.compound_map()
            .insert(compound, Type::Compound(compound));
        let current = ctx.with_ty_store(|store| store.resolve_compound(compound).clone());
        let mapped = self.rewrite_compound_type(ctx, compound, current);
        self.compound_map().insert(compound, mapped);
        if mapped != Type::Compound(compound) {
            self.note_compound_remap(compound, mapped);
        }
        mapped
    }
}

pub(crate) fn rewrite_compound_type_default<R: TypeRewrite>(
    rewriter: &mut R,
    ctx: &ModuleCtx,
    compound: CompoundTypeRef,
    current: CompoundType,
) -> Type {
    match current {
        CompoundType::Array { elem, len } => {
            let elem = rewriter.rewrite_type(ctx, elem);
            ctx.with_ty_store_mut(|store| store.make_array(elem, len))
        }
        CompoundType::Ptr(elem) => {
            let elem = rewriter.rewrite_type(ctx, elem);
            ctx.with_ty_store_mut(|store| store.make_ptr(elem))
        }
        CompoundType::ObjRef(elem) => {
            let elem = rewriter.rewrite_type(ctx, elem);
            ctx.with_ty_store_mut(|store| store.make_obj_ref(elem))
        }
        CompoundType::ConstRef(elem) => {
            let elem = rewriter.rewrite_type(ctx, elem);
            ctx.with_ty_store_mut(|store| store.make_const_ref(elem))
        }
        CompoundType::Enum(data) => {
            let variants: Vec<_> = data
                .variants
                .iter()
                .map(|variant| sonatina_ir::types::VariantData {
                    name: variant.name.clone(),
                    explicit_discriminant: variant.explicit_discriminant,
                    fields: variant
                        .fields
                        .iter()
                        .map(|&field| rewriter.rewrite_type(ctx, field))
                        .collect(),
                })
                .collect();
            if variants != data.variants {
                ctx.with_ty_store_mut(|store| {
                    store.update_enum_variants(&data.name, &variants, data.repr)
                });
                rewriter.note_named_compound_update(compound);
            }
            Type::Compound(compound)
        }
        CompoundType::Func { args, ret_tys } => {
            let args: Vec<_> = args
                .iter()
                .map(|&arg| rewriter.rewrite_type(ctx, arg))
                .collect();
            let ret_tys: Vec<_> = ret_tys
                .iter()
                .map(|&ret| rewriter.rewrite_type(ctx, ret))
                .collect();
            ctx.with_ty_store_mut(|store| store.make_func(&args, &ret_tys))
        }
        CompoundType::Struct(StructData { name, fields, .. }) => {
            let new_fields: Vec<_> = fields
                .iter()
                .map(|&field| rewriter.rewrite_type(ctx, field))
                .collect();
            if new_fields != fields {
                ctx.with_ty_store_mut(|store| store.update_struct_fields(&name, &new_fields));
                rewriter.note_named_compound_update(compound);
            }
            Type::Compound(compound)
        }
    }
}

pub(crate) fn rewrite_function_type_uses<R, F>(
    func: &mut Function,
    rewriter: &mut R,
    mut value_ty_override: F,
) -> bool
where
    R: TypeRewrite,
    F: FnMut(&Function, ValueId, Type) -> Option<Type>,
{
    let mut changed = false;
    for value in func.dfg.value_ids().collect::<Vec<_>>() {
        let old_ty = func.dfg.value_ty(value);
        let new_ty = value_ty_override(func, value, old_ty)
            .unwrap_or_else(|| rewriter.rewrite_type(func.ctx(), old_ty));
        if new_ty != old_ty {
            func.dfg.retype_value(value, new_ty);
            changed = true;
        }
    }

    struct TypeVisitor<'a, R> {
        ctx: ModuleCtx,
        rewriter: &'a mut R,
        changed: bool,
    }

    impl<R: TypeRewrite> VisitorMut for TypeVisitor<'_, R> {
        fn visit_ty(&mut self, item: &mut Type) {
            let new_ty = self.rewriter.rewrite_type(&self.ctx, *item);
            self.changed |= new_ty != *item;
            *item = new_ty;
        }
    }

    let mut visitor = TypeVisitor {
        ctx: func.ctx().clone(),
        rewriter,
        changed: false,
    };
    for block in func.layout.iter_block().collect::<Vec<_>>() {
        for inst in func.layout.iter_inst(block).collect::<Vec<_>>() {
            if func.layout.is_inst_inserted(inst) {
                func.dfg.inst_mut(inst).accept_mut(&mut visitor);
            }
        }
    }

    changed || visitor.changed
}
