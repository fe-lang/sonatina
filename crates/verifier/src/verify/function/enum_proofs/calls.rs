//! Typed capabilities available at an opaque call boundary. A callee can form
//! subobject references even when the caller has never named those projections.
use std::collections::BTreeSet;

use rustc_hash::FxHashMap;

use sonatina_ir::{Type, module::ModuleCtx, types::CompoundType};

use super::{
    objects::State,
    value_state::ValueState,
    views::{Index, References, Root, Step},
};

pub(super) struct CallEffects {
    // Keyed by pointee type, with arrays represented by a single index summary.
    candidates: FxHashMap<Type, References>,
    unresolved: bool,
}

impl CallEffects {
    pub fn new(ctx: &ModuleCtx, state: &State, args: impl Iterator<Item = ValueState>) -> Self {
        let mut effects = Self {
            candidates: FxHashMap::default(),
            unresolved: false,
        };
        for arg in args {
            effects.unresolved |= arg.captured(ctx).unknown;
        }
        for value in state.values.values() {
            effects.contents(ctx, value, &state.exposed);
        }
        for (&root, value) in &state.objects {
            if root.externally_accessible(&state.exposed) {
                effects.unresolved |= value.captured(ctx).unknown;
                effects.subobjects(ctx, value.ty, &References::root(root));
                effects.contents(ctx, value, &state.exposed);
            }
        }
        for fact in state.views.values() {
            let mut refs = fact.references.clone();
            refs.views
                .retain(|view| view.place.root.externally_accessible(&state.exposed));
            // An unrelated unresolved SSA value is not itself a call input.
            // Unknown published inputs/contents are tracked separately above.
            if !refs.views.is_empty() {
                effects.subobjects(ctx, fact.value.ty, &refs);
                effects.unresolved |= fact.value.captured(ctx).unknown;
                effects.contents(ctx, &fact.value, &state.exposed);
            }
        }
        effects
    }

    fn contents(&mut self, ctx: &ModuleCtx, value: &ValueState, exposed: &BTreeSet<Root>) {
        if let Some(CompoundType::ObjRef(elem)) = value.ty.resolve_compound(ctx) {
            let mut refs = value.references.clone();
            refs.views
                .retain(|view| view.place.root.externally_accessible(exposed));
            if !refs.views.is_empty() {
                self.subobjects(ctx, elem, &refs);
            }
        }
        for child in value.children.values() {
            self.contents(ctx, child, exposed);
        }
    }

    fn subobjects(&mut self, ctx: &ModuleCtx, ty: Type, refs: &References) {
        self.candidates
            .entry(ty)
            .and_modify(|old| old.join_with(refs))
            .or_insert_with(|| refs.clone());
        match ty.resolve_compound(ctx) {
            Some(CompoundType::Struct(record)) => {
                for (i, &ty) in record.fields.iter().enumerate() {
                    self.subobjects(ctx, ty, &refs.project(Step::Index(Index::Constant(i))));
                }
            }
            Some(CompoundType::Array { elem, len }) if len != 0 => {
                self.subobjects(ctx, elem, &refs.project(Step::Index(Index::Unknown)));
            }
            Some(CompoundType::Enum(enumeration)) => {
                for (v, variant) in enumeration.variants.iter().enumerate() {
                    for (i, &ty) in variant.fields.iter().enumerate() {
                        self.subobjects(ctx, ty, &refs.project(Step::Payload(v as u32, i)));
                    }
                }
            }
            _ => {}
        }
    }

    pub fn value(&self, ctx: &ModuleCtx, root: Root, ty: Type) -> ValueState {
        opaque(ctx, root, ty, Some(self))
    }
}

pub(super) fn opaque(
    ctx: &ModuleCtx,
    root: Root,
    ty: Type,
    call: Option<&CallEffects>,
) -> ValueState {
    let mut value = ValueState::new(
        ty,
        call.is_some() || !matches!(ty.resolve_compound(ctx), Some(CompoundType::Enum(_))),
    );
    match ty.resolve_compound(ctx) {
        Some(CompoundType::ObjRef(elem)) => {
            let mut refs = References::root(root);
            refs.unknown = call.is_none_or(|call| call.unresolved);
            if let Some(candidates) = call.and_then(|call| call.candidates.get(&elem)) {
                refs = refs.join(candidates);
            }
            value.references = refs;
        }
        Some(CompoundType::Struct(record)) => {
            for (i, &ty) in record.fields.iter().enumerate() {
                value
                    .children
                    .insert(Step::Index(Index::Constant(i)), opaque(ctx, root, ty, call));
            }
        }
        Some(CompoundType::Array { elem, len }) if len != 0 => {
            value
                .children
                .insert(Step::Index(Index::Unknown), opaque(ctx, root, elem, call));
        }
        Some(CompoundType::Enum(enumeration)) => {
            for (v, variant) in enumeration.variants.iter().enumerate() {
                for (i, &ty) in variant.fields.iter().enumerate() {
                    value
                        .children
                        .insert(Step::Payload(v as u32, i), opaque(ctx, root, ty, call));
                }
            }
        }
        _ => {}
    }
    value
}
