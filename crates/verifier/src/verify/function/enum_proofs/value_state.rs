use std::{
    collections::BTreeSet,
    ops::{Deref, DerefMut},
    sync::Arc,
};

use rpds::RedBlackTreeMapSync;
use sonatina_ir::{Type, ValueId, module::ModuleCtx, types::CompoundType};

use super::views::{Index, References, Step};

/// A whole-subtree certificate plus sparse typed overrides. References carry
/// locations/guards; they never recursively contain their mutable pointee state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ValueState(Arc<ValueStateData>);

// Snapshots share unchanged subtrees. Mutating a node copies only its own facts
// and shares the persistent child map; only affected map paths and value paths
// are copied. Retaining a chain of aggregate inserts must not copy every prefix.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ValueStateData {
    pub ty: Type,
    pub complete: bool,
    pub tag_initialized: bool,
    pub tags: Option<BTreeSet<u32>>,
    pub children: RedBlackTreeMapSync<Step, ValueState>,
    pub references: References,
}

impl Deref for ValueState {
    type Target = ValueStateData;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for ValueState {
    fn deref_mut(&mut self) -> &mut Self::Target {
        Arc::make_mut(&mut self.0)
    }
}

impl ValueState {
    pub fn new(ty: Type, complete: bool) -> Self {
        Self(Arc::new(ValueStateData {
            ty,
            complete,
            tag_initialized: complete,
            tags: None,
            children: RedBlackTreeMapSync::new_sync(),
            references: if complete {
                References::unknown()
            } else {
                References::default()
            },
        }))
    }

    pub fn reference(ty: Type, references: References) -> Self {
        let mut value = Self::new(ty, true);
        value.references = references;
        value
    }

    pub fn insert_child(&mut self, step: Step, child: Self) {
        // Rebuilding an equal entry discards sharing between SSA snapshots.
        // Keep absent keys distinct from explicit default facts.
        if self.children.get(&step) != Some(&child) {
            self.children.insert_mut(step, child);
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
                self.insert_child(Step::Index(Index::Unknown), default);
            }
            self.update_children(|other, node| {
                if other != step && other != Step::Index(Index::Unknown) && !step.disjoint(other) {
                    node.update(ctx, rest, false, write);
                }
            });
            if step != Step::Index(Index::Unknown) {
                self.insert_child(step, child);
            }
            return;
        }
        // Symbolic indices can alias other indices. Update overlapping children
        // weakly, while the exact symbolic view receives the strong postcondition.
        self.update_children(|other, node| {
            if other != step && !step.disjoint(other) {
                if matches!((other, step), (Step::Payload(a, _), Step::Payload(b, _)) if a != b) {
                    node.clear_readability();
                } else {
                    node.update(ctx, rest, false, write);
                }
            }
        });
        self.insert_child(step, child);
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
                self.insert_child(step, child);
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
            self.insert_child(step, certified);
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
        let mut result = self.clone();
        let complete = self.complete && other.complete;
        let tag_initialized = self.tag_initialized && other.tag_initialized;
        let tags = match (&self.tags, &other.tags) {
            (Some(a), Some(b)) => Some(a.union(b).copied().collect()),
            _ => None,
        };
        let references = self.references.join(&other.references);
        if result.complete != complete
            || result.tag_initialized != tag_initialized
            || result.tags != tags
            || result.references != references
        {
            let data = Arc::make_mut(&mut result.0);
            data.complete = complete;
            data.tag_initialized = tag_initialized;
            data.tags = tags;
            data.references = references;
        }
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
            result.insert_child(step, child);
        }
        result
    }

    // Visit without copying shared map entries unless their values change.
    fn update_children(&mut self, mut update: impl FnMut(Step, &mut Self)) {
        let changed: Vec<_> = self
            .children
            .iter()
            .filter_map(|(&step, child)| {
                let mut next = child.clone();
                update(step, &mut next);
                (!Arc::ptr_eq(&child.0, &next.0)).then_some((step, next))
            })
            .collect();
        for (step, child) in changed {
            self.insert_child(step, child);
        }
    }

    fn clear_readability(&mut self) {
        if self.complete || self.tag_initialized || self.tags.is_some() {
            self.complete = false;
            self.tag_initialized = false;
            self.tags = None;
        }
        self.update_children(|_, child| child.clear_readability());
    }

    pub fn forget(&mut self, ctx: &ModuleCtx) {
        let reference = self.ty.is_obj_ref(ctx);
        if self.complete
            || self.tag_initialized
            || self.tags.is_some()
            || reference
                && (!self.references.unknown
                    || self.references.cache.is_some()
                    || !self.references.anchors.is_empty())
        {
            self.complete = false;
            self.tag_initialized = false;
            self.tags = None;
            if reference {
                self.references.unknown = true;
                self.references.cache = None;
                self.references.anchors.clear();
            }
        }
        self.update_children(|_, child| child.forget(ctx));
    }

    pub fn copy_references(&mut self, ctx: &ModuleCtx, source: &Self) {
        if self.ty.is_obj_ref(ctx) && self.references != source.references {
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
            self.insert_child(step, target);
        }
    }

    pub fn visit_references(&mut self, ctx: &ModuleCtx, f: &mut impl FnMut(&mut References)) {
        if self.ty.is_obj_ref(ctx) {
            if let Some(data) = Arc::get_mut(&mut self.0) {
                f(&mut data.references);
            } else {
                let mut references = self.references.clone();
                f(&mut references);
                if references != self.references {
                    self.references = references;
                }
            }
        }
        self.update_children(|_, child| child.visit_references(ctx, f));
    }

    // Conditional readability cannot discard references in physically retained
    // inactive payload cells. Reference alternatives always join by union.
    fn merge_references(&mut self, ctx: &ModuleCtx, source: &Self) {
        if self.ty.is_obj_ref(ctx) {
            let references = self.references.join(&source.references);
            if self.references != references {
                self.references = references;
            }
        }
        for (&step, child) in &source.children {
            let mut target = self.child(ctx, step);
            target.merge_references(ctx, child);
            self.insert_child(step, target);
        }
    }

    pub fn forget_index(&mut self, ctx: &ModuleCtx, id: ValueId) {
        let symbol = Step::Index(Index::Symbol(id));
        if let Some(old) = self.children.get(&symbol) {
            let summary = self.array_default(ctx).join(ctx, old);
            self.children.remove_mut(&symbol);
            self.insert_child(Step::Index(Index::Unknown), summary);
        }
        self.update_children(|_, child| child.forget_index(ctx, id));
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

#[cfg(test)]
mod tests {
    use std::ptr;

    use super::*;
    use crate::verify::function::enum_proofs::views::Root;
    use sonatina_parser::parse_module;

    #[test]
    fn aggregate_insert_snapshots_share_unchanged_map_entries() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"
func private %entry(v0.[i256; 256]) {
block0:
 return;
}
"#,
        )
        .unwrap();
        let ctx = &parsed.module.ctx;
        let ty = ctx.func_sig(parsed.module.funcs()[0], |sig| sig.args()[0]);
        let mut value = ValueState::new(ty, false);
        let mut snapshots = vec![value.clone()];
        // Retain every intermediate aggregate, as the verifier does for SSA
        // insert_value results. Copying each map would retain a quadratic
        // number of entries even if the entries' values shared allocations.
        for index in 0..256 {
            let step = Step::Index(Index::Constant(index));
            value.update(ctx, &[step], true, &|child| {
                *child = ValueState::new(Type::I256, true);
            });
            let previous = snapshots.last().unwrap();
            assert!(!previous.child(ctx, step).readable(ctx));
            assert!(value.child(ctx, step).readable(ctx));
            for (key, child) in &previous.children {
                assert!(ptr::eq(child, value.children.get(key).unwrap()));
            }
            snapshots.push(value.clone());
        }
        assert!(value.readable(ctx));
        assert!(snapshots[..256].iter().all(|value| !value.readable(ctx)));
        for snapshot in &snapshots {
            let joined = snapshot.join(ctx, snapshot);
            assert!(Arc::ptr_eq(&snapshot.0, &joined.0));
            let mut copied = snapshot.clone();
            copied.copy_references(ctx, snapshot);
            assert!(Arc::ptr_eq(&snapshot.0, &copied.0));
        }

        let first = Step::Index(Index::Constant(0));
        value.update(ctx, &[first], true, &|child| child.forget(ctx));
        assert!(!value.readable(ctx));
        assert!(snapshots.last().unwrap().readable(ctx));
        let joined = snapshots.last().unwrap().join(ctx, &value);
        assert!(!joined.readable(ctx));
        for (key, child) in &snapshots.last().unwrap().children {
            if *key != first {
                assert!(ptr::eq(child, value.children.get(key).unwrap()));
                assert!(ptr::eq(child, joined.children.get(key).unwrap()));
            }
        }
    }

    #[test]
    fn snapshots_isolate_nested_writes_and_share_unchanged_subtrees() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"
type @E = enum { #None, #Some(objref<i256>) };
type @Pair = { @E, @E };
func private %entry(v0.@Pair) {
block0:
 return;
}
"#,
        )
        .unwrap();
        let ctx = &parsed.module.ctx;
        let ty = ctx.func_sig(parsed.module.funcs()[0], |sig| sig.args()[0]);
        let left = Step::Index(Index::Constant(0));
        let right = Step::Index(Index::Constant(1));
        let payload = Step::Payload(1, 0);
        let old_refs = References::root(Root::Recent(ValueId::from_u32(10)));
        let new_refs = References::root(Root::Recent(ValueId::from_u32(11)));
        let mut original = ValueState::new(ty, false);
        for step in [left, right] {
            original.update(ctx, &[step], true, &|value| value.refine(1));
            original.update(ctx, &[step, payload], true, &|value| {
                *value = ValueState::reference(value.ty, old_refs.clone());
            });
        }
        let mut unchanged = original.clone();
        unchanged.forget_index(ctx, ValueId::from_u32(12));
        let mut visited = 0;
        unchanged.visit_references(ctx, &mut |refs| {
            visited += 1;
            refs.rewrite(|_| {}, Some(ValueId::from_u32(12)));
        });
        assert_eq!(visited, 2);
        assert!(Arc::ptr_eq(&original.0, &unchanged.0));

        let mut forgotten = original.clone();
        forgotten.forget(ctx);
        assert!(!forgotten.readable(ctx));
        assert!(original.readable(ctx));
        let mut forgotten_again = forgotten.clone();
        forgotten_again.forget(ctx);
        assert!(Arc::ptr_eq(&forgotten.0, &forgotten_again.0));
        assert!(forgotten.at(ctx, &[left, payload]).references.unknown);
        assert_eq!(original.at(ctx, &[left, payload]).references, old_refs);

        let mut cleared = original.clone();
        cleared.clear_readability();
        let mut cleared_again = cleared.clone();
        cleared_again.clear_readability();
        assert!(Arc::ptr_eq(&cleared.0, &cleared_again.0));
        assert!(!cleared.readable(ctx));
        assert_eq!(cleared.at(ctx, &[left, payload]).references, old_refs);

        let mut updated = original.clone();
        assert!(Arc::ptr_eq(&original.0, &updated.0));
        let read = updated.at(ctx, &[left, payload]);
        assert!(Arc::ptr_eq(
            &read.0,
            &original
                .children
                .get(&left)
                .unwrap()
                .children
                .get(&payload)
                .unwrap()
                .0
        ));

        updated.update(ctx, &[left, payload], true, &|value| {
            value.references = new_refs.clone();
        });
        assert_eq!(original.at(ctx, &[left, payload]).references, old_refs);
        assert_eq!(updated.at(ctx, &[left, payload]).references, new_refs);
        assert!(Arc::ptr_eq(
            &original.children.get(&right).unwrap().0,
            &updated.children.get(&right).unwrap().0
        ));
        updated.update(ctx, &[left], true, &|value| value.set_tag(ctx, 0));
        assert!(original.child(ctx, left).active(1));
        assert!(updated.child(ctx, left).active(0));
        assert!(original.readable(ctx));
        assert!(updated.readable(ctx));

        let scalar = ValueState::new(Type::I256, true);
        let mut copy = scalar.clone();
        copy.forget_index(ctx, ValueId::from_u32(10));
        copy.visit_references(ctx, &mut |_| panic!("scalar has no references"));
        assert!(Arc::ptr_eq(&scalar.0, &copy.0));
    }
}
