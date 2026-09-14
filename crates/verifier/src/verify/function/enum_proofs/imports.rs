//! Typed references recoverable from externally accessible memory. Calls and raw
//! loads share this vocabulary; only calls import initialized enum values.
use std::collections::BTreeSet;

use rustc_hash::FxHashMap;

use sonatina_ir::{Type, module::ModuleCtx, types::CompoundType};

use super::{
    objects::State,
    value_state::ValueState,
    views::{Index, References, Root, Step},
};

pub(super) struct ImportSources {
    // Keyed by pointee type, with arrays represented by a single index summary.
    candidates: FxHashMap<Type, References>,
    unresolved: bool,
}

impl ImportSources {
    pub fn new(ctx: &ModuleCtx, state: &State, args: impl Iterator<Item = ValueState>) -> Self {
        let mut sources = Self {
            candidates: FxHashMap::default(),
            unresolved: false,
        };
        for arg in args {
            sources.unresolved |= arg.captured(ctx).unknown;
        }
        for value in state.values.values() {
            sources.contents(ctx, value, &state.exposed);
        }
        for (&root, value) in &state.objects {
            if root.externally_accessible(&state.exposed) {
                sources.unresolved |= value.captured(ctx).unknown;
                sources.subobjects(ctx, value.ty, &References::root(root));
                sources.contents(ctx, value, &state.exposed);
            }
        }
        for fact in state.views.values() {
            let mut refs = fact.references.clone();
            refs.views
                .retain(|view| view.place.root.externally_accessible(&state.exposed));
            // An unrelated unresolved SSA value is not itself a call input.
            // Unknown published inputs/contents are tracked separately above.
            if !refs.views.is_empty() {
                sources.subobjects(ctx, fact.value.ty, &refs);
                sources.unresolved |= fact.value.captured(ctx).unknown;
                sources.contents(ctx, &fact.value, &state.exposed);
            }
        }
        sources
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
}

#[derive(Clone, Copy)]
pub(super) enum Source<'a> {
    Call(&'a ImportSources),
    RawLoad(&'a ImportSources),
    Unsupported,
}

impl Source<'_> {
    pub fn value(self, ctx: &ModuleCtx, root: Root, ty: Type) -> ValueState {
        let mut value = ValueState::new(
            ty,
            matches!(self, Self::Call(_))
                || !matches!(ty.resolve_compound(ctx), Some(CompoundType::Enum(_))),
        );
        match ty.resolve_compound(ctx) {
            Some(CompoundType::ObjRef(elem)) => {
                value.references = match self {
                    Self::Call(sources) | Self::RawLoad(sources) => {
                        let mut refs = References::root(root);
                        refs.unknown = sources.unresolved;
                        if let Some(candidates) = sources.candidates.get(&elem) {
                            refs.join_with(candidates);
                        }
                        refs
                    }
                    // Missing local provenance cannot masquerade as an external
                    // allocation or infect unrelated imports before publication.
                    Self::Unsupported => References::unknown(),
                };
            }
            Some(CompoundType::Struct(record)) => {
                for (i, &ty) in record.fields.iter().enumerate() {
                    value
                        .children
                        .insert(Step::Index(Index::Constant(i)), self.value(ctx, root, ty));
                }
            }
            Some(CompoundType::Array { elem, len }) if len != 0 => {
                value
                    .children
                    .insert(Step::Index(Index::Unknown), self.value(ctx, root, elem));
            }
            Some(CompoundType::Enum(enumeration)) => {
                for (v, variant) in enumeration.variants.iter().enumerate() {
                    for (i, &ty) in variant.fields.iter().enumerate() {
                        value
                            .children
                            .insert(Step::Payload(v as u32, i), self.value(ctx, root, ty));
                    }
                }
            }
            _ => {}
        }
        value
    }
}
