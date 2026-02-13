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
        CompoundType::Struct(data) => data.fields.clone(),
        CompoundType::Func { args, ret_ty } => {
            let mut nested = args.to_vec();
            nested.push(*ret_ty);
            nested
        }
    }
}

pub(super) fn is_type_valid(ctx: &ModuleCtx, ty: Type) -> bool {
    let Type::Compound(root) = ty else {
        return true;
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
            CompoundType::Struct(data) => {
                for field in data.fields {
                    push_nested(field, true);
                }
            }
            CompoundType::Func { args, ret_ty } => {
                for arg in args {
                    push_nested(arg, true);
                }
                push_nested(ret_ty, true);
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

pub(super) fn is_integral_or_pointer(ctx: &ModuleCtx, ty: Type) -> bool {
    ty.is_integral() || is_pointer_ty(ctx, ty)
}
