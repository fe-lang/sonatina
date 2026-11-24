use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    Type,
    module::ModuleCtx,
    types::{CompoundType, CompoundTypeRef},
};

pub(super) fn iter_nested_types(cmpd: &CompoundType) -> Vec<Type> {
    match cmpd {
        CompoundType::Array { elem, .. } => vec![*elem],
        CompoundType::Ptr(elem) => vec![*elem],
        CompoundType::ObjRef(elem) => vec![*elem],
        CompoundType::ConstRef(elem) => vec![*elem],
        CompoundType::Struct(data) => data.fields.clone(),
        CompoundType::Enum(data) => data
            .variants
            .iter()
            .flat_map(|variant| variant.fields.iter().copied())
            .collect(),
        CompoundType::Func { args, ret_tys } => {
            let mut nested = args.to_vec();
            nested.extend(ret_tys.iter().copied());
            nested
        }
    }
}

pub(super) fn is_type_valid(ctx: &ModuleCtx, ty: Type) -> bool {
    let root = match ty {
        Type::Compound(root) => root,
        Type::EnumTag(root) => {
            return ctx.with_ty_store(|store| {
                store
                    .get_compound(root)
                    .is_some_and(|cmpd| matches!(cmpd, CompoundType::Enum(_)))
            });
        }
        _ => return true,
    };

    let mut reachable = FxHashSet::default();
    let mut stack = vec![root];
    let mut by_value_edges: FxHashMap<CompoundTypeRef, Vec<CompoundTypeRef>> = FxHashMap::default();

    while let Some(cmpd_ref) = stack.pop() {
        if !reachable.insert(cmpd_ref) {
            continue;
        }

        let Some(cmpd) = ctx.with_ty_store(|store| store.get_compound(cmpd_ref).cloned()) else {
            return false;
        };

        let mut push_nested = |nested: Type, by_value: bool| {
            let Type::Compound(nested_ref) = nested else {
                return;
            };
            stack.push(nested_ref);
            if by_value {
                by_value_edges.entry(cmpd_ref).or_default().push(nested_ref);
            }
        };

        match cmpd {
            CompoundType::Array { elem, .. } => push_nested(elem, true),
            CompoundType::Ptr(elem) => push_nested(elem, false),
            CompoundType::ObjRef(elem) => push_nested(elem, false),
            CompoundType::ConstRef(elem) => push_nested(elem, false),
            CompoundType::Struct(data) => {
                for field in data.fields {
                    push_nested(field, true);
                }
            }
            CompoundType::Enum(data) => {
                for field in data
                    .variants
                    .into_iter()
                    .flat_map(|variant| variant.fields.into_iter())
                {
                    push_nested(field, true);
                }
            }
            CompoundType::Func { args, ret_tys } => {
                for arg in args {
                    push_nested(arg, true);
                }
                for ret_ty in ret_tys {
                    push_nested(ret_ty, true);
                }
            }
        }
    }

    #[derive(Clone, Copy)]
    enum VisitState {
        Visiting,
        Done,
    }

    let mut states: FxHashMap<CompoundTypeRef, VisitState> = FxHashMap::default();
    for start in reachable.iter().copied() {
        if states.contains_key(&start) {
            continue;
        }

        states.insert(start, VisitState::Visiting);
        let mut dfs_stack = vec![(start, 0usize)];
        while let Some((node, next_index)) = dfs_stack.last_mut() {
            let successors = by_value_edges.get(node).map(Vec::as_slice).unwrap_or(&[]);
            if *next_index >= successors.len() {
                states.insert(*node, VisitState::Done);
                dfs_stack.pop();
                continue;
            }

            let successor = successors[*next_index];
            *next_index += 1;

            match states.get(&successor) {
                Some(VisitState::Visiting) => return false,
                Some(VisitState::Done) => {}
                None => {
                    states.insert(successor, VisitState::Visiting);
                    dfs_stack.push((successor, 0));
                }
            }
        }
    }

    true
}

/// Whether `ty` has at least one runtime value (IR contract V4):
/// 0-variant enums, enums whose variants are all uninhabited, enum tags of
/// uninhabited enums, and structs or non-empty arrays containing an
/// uninhabited type have no runtime values. Pointers and references remain
/// inhabited regardless of their pointee type.
pub(super) fn is_type_inhabited(ctx: &ModuleCtx, ty: Type) -> bool {
    fn inner(
        ctx: &ModuleCtx,
        ty: Type,
        visiting: &mut FxHashSet<CompoundTypeRef>,
        memo: &mut FxHashMap<CompoundTypeRef, bool>,
    ) -> bool {
        let compound = match ty {
            Type::Compound(compound) | Type::EnumTag(compound) => compound,
            _ => return true,
        };
        if let Some(&cached) = memo.get(&compound) {
            return cached;
        }
        if !visiting.insert(compound) {
            // Recursive by-value cycles are rejected separately by `is_type_valid`.
            return true;
        }
        let Some(data) = ctx.with_ty_store(|store| store.get_compound(compound).cloned()) else {
            visiting.remove(&compound);
            return true;
        };
        let inhabited = match data {
            CompoundType::Array { elem, len } => len == 0 || inner(ctx, elem, visiting, memo),
            CompoundType::Struct(data) => {
                data.fields.iter().all(|&f| inner(ctx, f, visiting, memo))
            }
            CompoundType::Enum(data) => data
                .variants
                .iter()
                .any(|v| v.fields.iter().all(|&f| inner(ctx, f, visiting, memo))),
            CompoundType::Ptr(_)
            | CompoundType::ObjRef(_)
            | CompoundType::ConstRef(_)
            | CompoundType::Func { .. } => true,
        };
        visiting.remove(&compound);
        memo.insert(compound, inhabited);
        inhabited
    }

    inner(
        ctx,
        ty,
        &mut FxHashSet::default(),
        &mut FxHashMap::default(),
    )
}

pub(super) fn is_pointer_ty(ctx: &ModuleCtx, ty: Type) -> bool {
    let Type::Compound(cmpd_ref) = ty else {
        return false;
    };

    ctx.with_ty_store(|store| {
        store
            .get_compound(cmpd_ref)
            .is_some_and(|cmpd| matches!(cmpd, CompoundType::Ptr(_)))
    })
}

pub(super) fn is_obj_ref_ty(ctx: &ModuleCtx, ty: Type) -> bool {
    let Type::Compound(cmpd_ref) = ty else {
        return false;
    };

    ctx.with_ty_store(|store| {
        store
            .get_compound(cmpd_ref)
            .is_some_and(|cmpd| matches!(cmpd, CompoundType::ObjRef(_)))
    })
}

pub(super) fn is_const_ref_ty(ctx: &ModuleCtx, ty: Type) -> bool {
    let Type::Compound(cmpd_ref) = ty else {
        return false;
    };

    ctx.with_ty_store(|store| {
        store
            .get_compound(cmpd_ref)
            .is_some_and(|cmpd| matches!(cmpd, CompoundType::ConstRef(_)))
    })
}

pub(super) fn is_integral_or_pointer(ctx: &ModuleCtx, ty: Type) -> bool {
    ty.is_integral() || is_pointer_ty(ctx, ty)
}

/// Whether `ty` can pass to a C variadic function, as a fixed or an extra
/// argument: each takes one integer register or stack slot.
pub(super) fn is_variadic_arg_ty(ctx: &ModuleCtx, ty: Type) -> bool {
    matches!(ty, Type::I32 | Type::I64) || is_pointer_ty(ctx, ty)
}
