use std::collections::{BTreeMap, BTreeSet};

use sonatina_ir::{Type, ValueId, module::ModuleCtx, types::CompoundType};

use super::views::{Index, References, Step};

/// A whole-subtree certificate plus sparse typed overrides. References carry
/// locations/guards; they never recursively contain their mutable pointee state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ValueState {
    pub ty: Type,
    pub complete: bool,
    pub tag_initialized: bool,
    pub tags: Option<BTreeSet<u32>>,
    pub children: BTreeMap<Step, Self>,
    pub references: References,
}

impl ValueState {
    pub fn new(ty: Type, complete: bool) -> Self {
        Self {
            ty,
            complete,
            tag_initialized: complete,
            tags: None,
            children: BTreeMap::new(),
            references: if complete {
                References::unknown()
            } else {
                References::default()
            },
        }
    }

    pub fn reference(ty: Type, references: References) -> Self {
        Self {
            references,
            ..Self::new(ty, true)
        }
    }

    pub fn child_ty(&self, ctx: &ModuleCtx, step: Step) -> Type {
        match (self.ty.resolve_compound(ctx), step) {
            (Some(CompoundType::Struct(record)), Step::Index(Index::Constant(index))) => {
                record.fields[index]
            }
            (Some(CompoundType::Array { elem, .. }), Step::Index(_)) => elem,
            (Some(CompoundType::Enum(enumeration)), Step::Payload(variant, index)) => {
                enumeration.variants[variant as usize].fields[index]
            }
            _ => unreachable!("validated typed path"),
        }
    }

    fn array_default(&self, ctx: &ModuleCtx) -> Self {
        self.children
            .get(&Step::Index(Index::Unknown))
            .cloned()
            .unwrap_or_else(|| {
                Self::new(
                    self.child_ty(ctx, Step::Index(Index::Unknown)),
                    self.complete,
                )
            })
    }

    pub fn child(&self, ctx: &ModuleCtx, step: Step) -> Self {
        if matches!(
            self.ty.resolve_compound(ctx),
            Some(CompoundType::Array { .. })
        ) {
            if step != Step::Index(Index::Unknown)
                && let Some(child) = self.children.get(&step)
            {
                return child.clone();
            }
            let default = self.array_default(ctx);
            if matches!(step, Step::Index(Index::Constant(_))) {
                return default;
            }
            // Symbolic entries are guarantees about selected views, not write
            // footprints. The default summary and constant cells describe the
            // physical array; treating another symbol's failed query as a write
            // would make joins depend on when that query was materialized.
            return self
                .children
                .iter()
                .filter(|(step, _)| matches!(step, Step::Index(Index::Constant(_))))
                .fold(default, |value, (_, child)| value.join(ctx, child));
        }
        self.children
            .get(&step)
            .cloned()
            .unwrap_or_else(|| Self::new(self.child_ty(ctx, step), self.complete))
    }

    pub fn at(&self, ctx: &ModuleCtx, path: &[Step]) -> Self {
        path.iter()
            .fold(self.clone(), |node, &step| node.child(ctx, step))
    }

    pub fn update(
        &mut self,
        ctx: &ModuleCtx,
        path: &[Step],
        strong: bool,
        write: &impl Fn(&mut Self),
    ) {
        let Some((&step, rest)) = path.split_first() else {
            if strong {
                write(self);
            } else {
                let mut after = self.clone();
                write(&mut after);
                *self = self.join(ctx, &after);
            }
            return;
        };
        let mut child = self.child(ctx, step);
        child.update(ctx, rest, strong, write);
        if matches!(
            self.ty.resolve_compound(ctx),
            Some(CompoundType::Array { .. })
        ) {
            if !matches!(step, Step::Index(Index::Constant(_))) {
                let mut default = self.array_default(ctx);
                default.update(ctx, rest, false, write);
                self.children.insert(Step::Index(Index::Unknown), default);
            }
            for (&other, node) in &mut self.children {
                if other != step && other != Step::Index(Index::Unknown) && !step.disjoint(other) {
                    node.update(ctx, rest, false, write);
                }
            }
            if step != Step::Index(Index::Unknown) {
                self.children.insert(step, child);
            }
            return;
        }
        // Symbolic indices can alias other indices. Update overlapping children
        // weakly, while the exact symbolic view receives the strong postcondition.
        for (&other, node) in &mut self.children {
            if other != step && !step.disjoint(other) {
                if matches!((other, step), (Step::Payload(a, _), Step::Payload(b, _)) if a != b) {
                    node.clear_readability();
                } else {
                    node.update(ctx, rest, false, write);
                }
            }
        }
        self.children.insert(step, child);
    }

    pub fn possible(&self, variant: u32) -> bool {
        self.tags
            .as_ref()
            .is_none_or(|tags| tags.contains(&variant))
    }

    pub fn active(&self, variant: u32) -> bool {
        self.tag_initialized
            && self
                .tags
                .as_ref()
                .is_some_and(|tags| tags.len() == 1 && tags.contains(&variant))
    }

    pub fn refine(&mut self, variant: u32) {
        self.tags = Some(BTreeSet::from([variant]));
        self.tag_initialized = true;
    }

    pub fn set_tag(&mut self, ctx: &ModuleCtx, variant: u32) {
        if !self.active(variant) {
            let Some(CompoundType::Enum(enumeration)) = self.ty.resolve_compound(ctx) else {
                unreachable!("validated enum type");
            };
            for (index, &ty) in enumeration.variants[variant as usize]
                .fields
                .iter()
                .enumerate()
            {
                let step = Step::Payload(variant, index);
                let mut child = self.child(ctx, step);
                child.clear_readability();
                debug_assert_eq!(child.ty, ty);
                self.children.insert(step, child);
            }
        }
        self.refine(variant);
    }

    pub fn assert_variant(&mut self, ctx: &ModuleCtx, variant: u32) {
        self.refine(variant);
        let Some(CompoundType::Enum(enumeration)) = self.ty.resolve_compound(ctx) else {
            unreachable!("validated enum type");
        };
        for (index, &ty) in enumeration.variants[variant as usize]
            .fields
            .iter()
            .enumerate()
        {
            let step = Step::Payload(variant, index);
            let mut certified = Self::new(ty, true);
            // An assumption establishes readability, not a new reference value.
            let old = self.child(ctx, step);
            certified.copy_references(ctx, &old);
            self.children.insert(step, certified);
        }
    }

    pub fn readable(&self, ctx: &ModuleCtx) -> bool {
        match self.ty.resolve_compound(ctx) {
            Some(CompoundType::Struct(record)) => record.fields.iter().enumerate().all(|(i, _)| {
                self.child(ctx, Step::Index(Index::Constant(i)))
                    .readable(ctx)
            }),
            Some(CompoundType::Array { len, .. }) => {
                let cells: Vec<_> = self
                    .children
                    .iter()
                    .filter(|(step, _)| matches!(step, Step::Index(Index::Constant(i)) if *i < len))
                    .map(|(_, value)| value)
                    .collect();
                (cells.len() == len || self.array_default(ctx).readable(ctx))
                    && cells.iter().all(|value| value.readable(ctx))
            }
            Some(CompoundType::Enum(enumeration)) => {
                self.tag_initialized
                    && enumeration.variants.iter().enumerate().all(|(v, variant)| {
                        !self.possible(v as u32)
                            || variant.fields.iter().enumerate().all(|(i, _)| {
                                self.child(ctx, Step::Payload(v as u32, i)).readable(ctx)
                            })
                    })
            }
            _ => self.complete,
        }
    }

    pub fn join(&self, ctx: &ModuleCtx, other: &Self) -> Self {
        debug_assert_eq!(self.ty, other.ty);
        let mut result = Self::new(self.ty, self.complete && other.complete);
        result.tag_initialized = self.tag_initialized && other.tag_initialized;
        result.tags = match (&self.tags, &other.tags) {
            (Some(a), Some(b)) => Some(a.union(b).copied().collect()),
            _ => None,
        };
        result.references = self.references.join(&other.references);
        let mut keys: BTreeSet<_> = self
            .children
            .keys()
            .chain(other.children.keys())
            .copied()
            .collect();
        if let Some(CompoundType::Enum(enumeration)) = self.ty.resolve_compound(ctx) {
            keys.extend(
                enumeration
                    .variants
                    .iter()
                    .enumerate()
                    .flat_map(|(v, variant)| {
                        variant
                            .fields
                            .iter()
                            .enumerate()
                            .map(move |(i, _)| Step::Payload(v as u32, i))
                    }),
            );
        }
        for step in keys {
            let (a, b) = if step == Step::Index(Index::Unknown) {
                (self.array_default(ctx), other.array_default(ctx))
            } else {
                (self.child(ctx, step), other.child(ctx, step))
            };
            let mut child = match step {
                Step::Payload(v, _) if !self.possible(v) && other.possible(v) => b.clone(),
                Step::Payload(v, _) if self.possible(v) && !other.possible(v) => a.clone(),
                _ => a.join(ctx, &b),
            };
            child.merge_references(ctx, &a);
            child.merge_references(ctx, &b);
            // Keep the finite union of queried cells, selected-view guarantees
            // and physical default summaries distinct through the join.
            result.children.insert(step, child);
        }
        result
    }

    fn clear_readability(&mut self) {
        self.complete = false;
        self.tag_initialized = false;
        self.tags = None;
        for child in self.children.values_mut() {
            child.clear_readability();
        }
    }

    pub fn forget(&mut self, ctx: &ModuleCtx) {
        self.complete = false;
        self.tag_initialized = false;
        self.tags = None;
        if self.ty.is_obj_ref(ctx) {
            self.references.unknown = true;
            self.references.cache = None;
            self.references.anchors.clear();
        }
        for child in self.children.values_mut() {
            child.forget(ctx);
        }
    }

    pub fn copy_references(&mut self, ctx: &ModuleCtx, source: &Self) {
        if self.ty.is_obj_ref(ctx) {
            self.references = source.references.clone();
        }
        // A sparse source summary replaces reference provenance in existing
        // concrete/symbolic cells too; stale overrides must not shadow it.
        let keys: BTreeSet<_> = self
            .children
            .keys()
            .chain(source.children.keys())
            .copied()
            .collect();
        for step in keys {
            let (mut target, child) = if step == Step::Index(Index::Unknown) {
                (self.array_default(ctx), source.array_default(ctx))
            } else {
                (self.child(ctx, step), source.child(ctx, step))
            };
            target.copy_references(ctx, &child);
            self.children.insert(step, target);
        }
    }

    pub fn visit_references(&mut self, ctx: &ModuleCtx, f: &mut impl FnMut(&mut References)) {
        if self.ty.is_obj_ref(ctx) {
            f(&mut self.references);
        }
        for child in self.children.values_mut() {
            child.visit_references(ctx, f);
        }
    }

    // Conditional readability cannot discard references in physically retained
    // inactive payload cells. Reference alternatives always join by union.
    fn merge_references(&mut self, ctx: &ModuleCtx, source: &Self) {
        if self.ty.is_obj_ref(ctx) {
            self.references = self.references.join(&source.references);
        }
        for (&step, child) in &source.children {
            let mut target = self.child(ctx, step);
            target.merge_references(ctx, child);
            self.children.insert(step, target);
        }
    }

    pub fn forget_index(&mut self, ctx: &ModuleCtx, id: ValueId) {
        if let Some(old) = self.children.remove(&Step::Index(Index::Symbol(id))) {
            let step = Step::Index(Index::Unknown);
            let summary = self.array_default(ctx).join(ctx, &old);
            self.children.insert(step, summary);
        }
        for child in self.children.values_mut() {
            child.forget_index(ctx, id);
        }
    }

    pub fn captured(&self, ctx: &ModuleCtx) -> References {
        let mut references = References::default();
        match self.ty.resolve_compound(ctx) {
            Some(CompoundType::ObjRef(_)) => {
                references = self.references.clone();
                references.unknown |= self.complete && references.views.is_empty();
            }
            Some(CompoundType::Struct(record)) => {
                for (i, _) in record.fields.iter().enumerate() {
                    references = references.join(
                        &self
                            .child(ctx, Step::Index(Index::Constant(i)))
                            .captured(ctx),
                    );
                }
            }
            Some(CompoundType::Enum(enumeration)) => {
                for (v, variant) in enumeration.variants.iter().enumerate() {
                    for (i, _) in variant.fields.iter().enumerate() {
                        references = references
                            .join(&self.child(ctx, Step::Payload(v as u32, i)).captured(ctx));
                    }
                }
            }
            Some(CompoundType::Array { len, .. }) => {
                for child in self.children.values() {
                    references = references.join(&child.captured(ctx));
                }
                if self
                    .children
                    .keys()
                    .filter(|step| matches!(step, Step::Index(Index::Constant(i)) if *i < len))
                    .count()
                    < len
                {
                    references = references.join(&self.array_default(ctx).captured(ctx));
                }
            }
            _ => {}
        }
        references
    }
}
