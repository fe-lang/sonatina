use std::collections::{BTreeMap, BTreeSet};

use sonatina_ir::{Type, Value, ValueId, module::ModuleCtx, types::CompoundType};

use super::{
    super::FunctionVerifier,
    value_state::ValueState,
    views::{Index, Place, References, Relation, Root, Step},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ViewFact {
    pub references: References,
    pub value: ValueState,
    pub guards: bool,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct State {
    pub objects: BTreeMap<Root, ValueState>,
    pub values: BTreeMap<ValueId, ValueState>,
    bound: BTreeSet<ValueId>,
    pub views: BTreeMap<ValueId, ViewFact>,
    pub observations: BTreeMap<ValueId, References>,
    pub value_observations: BTreeMap<ValueId, (ValueId, Option<u32>)>,
    pub exposed: BTreeSet<Root>,
}

impl State {
    pub fn boundary(verifier: &FunctionVerifier<'_>) -> Self {
        let mut state = Self::default();
        for &arg in &verifier.func.arg_values {
            let ty = verifier.func.dfg.value_ty(arg);
            let value = if let Some(elem) = verifier.objref_ty(ty) {
                let root = Root::Incoming(arg);
                state
                    .objects
                    .insert(root, Self::imported(verifier.ctx, arg, elem, false));
                state.exposed.insert(root);
                ValueState::reference(ty, References::root(root))
            } else {
                Self::imported(verifier.ctx, arg, ty, true)
            };
            state.bind(verifier.ctx, arg, value, None);
        }
        let mut pending: Vec<_> = state
            .values
            .values()
            .chain(state.objects.values())
            .flat_map(|value| {
                value
                    .captured(verifier.ctx)
                    .views
                    .into_iter()
                    .map(|view| view.place.root)
            })
            .collect();
        while let Some(root) = pending.pop() {
            if state.objects.contains_key(&root) {
                continue;
            }
            if let Root::IncomingNested(owner, ty) = root {
                let Some(CompoundType::ObjRef(elem)) =
                    Type::Compound(ty).resolve_compound(verifier.ctx)
                else {
                    unreachable!("imported reference type")
                };
                let value = Self::imported(verifier.ctx, owner, elem, false);
                pending.extend(
                    value
                        .captured(verifier.ctx)
                        .views
                        .into_iter()
                        .map(|view| view.place.root),
                );
                state.objects.insert(root, value);
                state.exposed.insert(root);
            }
        }
        state
    }

    // Nested imported references denote preexisting objects. Per-type summary
    // roots avoid unfolding recursive reference types and never permit a heap
    // strong update; a loaded SSA view can still carry its own postcondition.
    fn imported(ctx: &ModuleCtx, owner: ValueId, ty: Type, complete: bool) -> ValueState {
        let mut value = ValueState::new(ty, complete);
        match ty.resolve_compound(ctx) {
            Some(CompoundType::ObjRef(_)) => {
                let Type::Compound(id) = ty else {
                    unreachable!()
                };
                value.references = References::root(Root::IncomingNested(owner, id));
            }
            Some(CompoundType::Struct(record)) => {
                for (i, &ty) in record.fields.iter().enumerate() {
                    value.children.insert(
                        Step::Index(Index::Constant(i)),
                        Self::imported(ctx, owner, ty, complete),
                    );
                }
            }
            Some(CompoundType::Array { elem, len }) if len != 0 => {
                value.children.insert(
                    Step::Index(Index::Unknown),
                    Self::imported(ctx, owner, elem, complete),
                );
            }
            Some(CompoundType::Enum(enumeration)) => {
                for (v, variant) in enumeration.variants.iter().enumerate() {
                    for (i, &ty) in variant.fields.iter().enumerate() {
                        value.children.insert(
                            Step::Payload(v as u32, i),
                            Self::imported(ctx, owner, ty, complete),
                        );
                    }
                }
            }
            _ => {}
        }
        value
    }

    pub fn value(&self, verifier: &FunctionVerifier<'_>, id: ValueId) -> ValueState {
        self.values.get(&id).cloned().unwrap_or_else(|| {
            let complete = matches!(
                verifier.func.dfg.value(id),
                Value::Immediate { .. } | Value::Undef { .. } | Value::Arg { .. }
            );
            ValueState::new(verifier.func.dfg.value_ty(id), complete)
        })
    }

    pub fn reference(&self, verifier: &FunctionVerifier<'_>, id: ValueId) -> References {
        self.value(verifier, id).references
    }

    pub fn contents(&self, ctx: &ModuleCtx, refs: &References, ty: Type) -> ValueState {
        if let Some(fact) = refs.cache.and_then(|id| self.views.get(&id)) {
            return fact.value.clone();
        }
        if let Some(value) = refs.anchors.iter().find_map(|anchor| {
            self.views
                .get(&anchor.value)
                .map(|fact| fact.value.at(ctx, &anchor.path))
        }) {
            return value;
        }
        self.heap_contents(ctx, refs, ty)
    }

    fn heap_contents(&self, ctx: &ModuleCtx, refs: &References, ty: Type) -> ValueState {
        let mut values = refs
            .views
            .iter()
            .map(|view| {
                self.objects.get(&view.place.root).map_or_else(
                    || ValueState::new(ty, false),
                    |root| root.at(ctx, &view.place.path),
                )
            })
            .collect::<Vec<_>>();
        if refs.unknown {
            values.push(ValueState::new(ty, false));
        }
        values
            .into_iter()
            .reduce(|a, b| a.join(ctx, &b))
            .unwrap_or_else(|| ValueState::new(ty, false))
    }

    pub fn guards_hold(&self, ctx: &ModuleCtx, refs: &References) -> bool {
        !refs.unknown
            && refs.views.iter().all(|view| {
                view.guards.iter().all(|guard| {
                    guard
                        .witness
                        .and_then(|id| self.views.get(&id))
                        .is_some_and(|fact| fact.guards)
                        || guard.anchor.as_ref().is_some_and(|anchor| {
                            self.views.get(&anchor.value).is_some_and(|fact| {
                                fact.value.at(ctx, &anchor.path).active(guard.variant)
                            })
                        })
                        || self.objects.get(&guard.place.root).is_some_and(|root| {
                            root.at(ctx, &guard.place.path).active(guard.variant)
                        })
                })
            })
    }

    pub fn fact(&self, ctx: &ModuleCtx, refs: &References, ty: Type) -> ViewFact {
        ViewFact {
            references: refs.clone(),
            value: self.contents(ctx, refs, ty),
            guards: self.guards_hold(ctx, refs),
        }
    }

    pub fn bind(
        &mut self,
        ctx: &ModuleCtx,
        id: ValueId,
        mut value: ValueState,
        fact: Option<ViewFact>,
    ) {
        let mut fact = if let Some(CompoundType::ObjRef(elem)) = value.ty.resolve_compound(ctx) {
            Some(fact.unwrap_or_else(|| self.fact(ctx, &value.references, elem)))
        } else {
            None
        };
        self.prepare_binding(ctx, id);
        value.visit_references(ctx, &mut |refs| refs.rewrite(|_| {}, Some(id)));
        if let Some(fact) = &mut fact {
            fact.value.forget_index(ctx, id);
            fact.value
                .visit_references(ctx, &mut |refs| refs.rewrite(|_| {}, Some(id)));
        }
        self.install(id, value, fact);
    }

    pub fn prepare_binding(&mut self, ctx: &ModuleCtx, id: ValueId) {
        if !self.bound.insert(id) {
            self.forget_binding(ctx, id);
        }
    }

    pub fn install(&mut self, id: ValueId, mut value: ValueState, fact: Option<ViewFact>) {
        if let Some(mut fact) = fact {
            let refs = &mut value.references;
            refs.cache = Some(id);
            if fact.guards {
                refs.views = refs
                    .views
                    .iter()
                    .cloned()
                    .map(|mut view| {
                        view.guards = view
                            .guards
                            .into_iter()
                            .map(|mut guard| {
                                guard.witness = Some(id);
                                guard
                            })
                            .collect();
                        view
                    })
                    .collect();
            }
            fact.references = refs.clone();
            self.views.insert(id, fact);
        }
        self.values.insert(id, value);
    }

    fn forget_binding(&mut self, ctx: &ModuleCtx, id: ValueId) {
        for value in self.objects.values_mut().chain(self.values.values_mut()) {
            value.forget_index(ctx, id);
        }
        for fact in self.views.values_mut() {
            fact.value.forget_index(ctx, id);
        }
        self.views.remove(&id);
        self.observations.remove(&id);
        self.value_observations
            .retain(|&key, (value, _)| key != id && *value != id);
        self.rewrite_references(ctx, &mut |refs| {
            refs.rewrite(
                |place| {
                    for step in &mut place.path {
                        if *step == Step::Index(Index::Symbol(id)) {
                            *step = Step::Index(Index::Unknown);
                        }
                    }
                },
                Some(id),
            );
        });
    }

    fn rewrite_references(&mut self, ctx: &ModuleCtx, f: &mut impl FnMut(&mut References)) {
        for value in self.values.values_mut().chain(self.objects.values_mut()) {
            value.visit_references(ctx, f);
        }
        for fact in self.views.values_mut() {
            f(&mut fact.references);
            fact.value.visit_references(ctx, f);
        }
        for refs in self.observations.values_mut() {
            f(refs);
        }
    }

    pub fn allocate(&mut self, ctx: &ModuleCtx, id: ValueId, ty: Type) -> References {
        let recent = Root::Recent(id);
        let summary = Root::Summary(id);
        if let Some(old) = self.objects.remove(&recent) {
            let old = self
                .objects
                .remove(&summary)
                .map_or(old.clone(), |summary| summary.join(ctx, &old));
            self.objects.insert(summary, old);
            self.rewrite_references(ctx, &mut |refs| {
                refs.rewrite(
                    |place| {
                        if place.root == recent {
                            place.root = summary;
                        }
                    },
                    None,
                )
            });
            if self.exposed.remove(&recent) {
                self.exposed.insert(summary);
            }
        }
        self.objects.insert(recent, ValueState::new(ty, false));
        References::root(recent)
    }

    pub fn join(&self, ctx: &ModuleCtx, other: &Self) -> Self {
        let mut result = Self {
            objects: self.objects.clone(),
            bound: self.bound.union(&other.bound).copied().collect(),
            ..Self::default()
        };
        // Allocation facts are conditional on that allocation existing. Phi
        // substitution occurs first, so branch-local values cannot lose their
        // guarantees merely because the other branch did not allocate them.
        for (&root, value) in &other.objects {
            result
                .objects
                .entry(root)
                .and_modify(|a| *a = a.join(ctx, value))
                .or_insert_with(|| value.clone());
        }
        for (&id, a) in &self.values {
            if let Some(b) = other.values.get(&id) {
                result.values.insert(id, a.join(ctx, b));
            }
        }
        for (&id, a) in &self.views {
            if let Some(b) = other.views.get(&id) {
                result.views.insert(
                    id,
                    ViewFact {
                        references: a.references.join(&b.references),
                        value: a.value.join(ctx, &b.value),
                        guards: a.guards && b.guards,
                    },
                );
            }
        }
        for (&id, refs) in &self.observations {
            if let Some(other) = other.observations.get(&id)
                && (refs == other || refs.same_location(other))
            {
                result.observations.insert(id, refs.join(other));
            }
        }
        for (&id, relation) in &self.value_observations {
            if other.value_observations.get(&id) == Some(relation) {
                result.value_observations.insert(id, *relation);
            }
        }
        result.exposed = self.exposed.union(&other.exposed).copied().collect();
        result.close_exposure(ctx);
        result
    }

    pub fn expose(&mut self, ctx: &ModuleCtx, refs: &References) {
        self.exposed
            .extend(refs.views.iter().map(|view| view.place.root));
        if refs.unknown {
            self.exposed.extend(self.objects.keys());
        }
        self.close_exposure(ctx);
    }

    pub fn close_exposure(&mut self, ctx: &ModuleCtx) {
        let mut pending: Vec<_> = self.exposed.iter().copied().collect();
        let mut seen = BTreeSet::new();
        while let Some(root) = pending.pop() {
            if !seen.insert(root) {
                continue;
            }
            self.exposed.insert(root);
            if let Some(value) = self.objects.get(&root) {
                let captures = value.captured(ctx);
                pending.extend(captures.views.iter().map(|view| view.place.root));
                if captures.unknown {
                    pending.extend(self.objects.keys().filter(|root| !seen.contains(root)));
                }
            }
        }
    }

    pub fn havoc(&mut self, ctx: &ModuleCtx, raw_only: bool) {
        for (&root, value) in &mut self.objects {
            if !raw_only || self.exposed.contains(&root) {
                value.forget(ctx);
            }
        }
        for fact in self.views.values_mut() {
            if fact.references.unknown
                || fact
                    .references
                    .views
                    .iter()
                    .any(|view| !raw_only || self.exposed.contains(&view.place.root))
            {
                fact.value.forget(ctx);
            }
            if fact
                .references
                .views
                .iter()
                .flat_map(|view| &view.guards)
                .any(|guard| !raw_only || self.exposed.contains(&guard.place.root))
            {
                fact.guards = false;
            }
        }
        self.observations.retain(|_, refs| {
            raw_only
                && !refs.unknown
                && refs
                    .views
                    .iter()
                    .all(|view| !self.exposed.contains(&view.place.root))
        });
    }

    pub fn write(
        &mut self,
        ctx: &ModuleCtx,
        target: &References,
        ty: Type,
        assertion: bool,
        write: impl Fn(&mut ValueState),
    ) {
        let mut post = self.contents(ctx, target, ty);
        write(&mut post);
        let targets: BTreeSet<_> = target.views.iter().map(|view| view.place.clone()).collect();
        let exact = !target.unknown && targets.len() == 1 && targets.iter().all(Place::exact);
        for (&root, value) in &mut self.objects {
            if target.unknown {
                if !assertion {
                    value.forget(ctx);
                }
                continue;
            }
            for place in &targets {
                if root == place.root {
                    value.update(ctx, &place.path, exact, &write);
                } else if root.may_alias(place.root) && !assertion {
                    value.forget(ctx);
                }
            }
        }
        let facts = std::mem::take(&mut self.views);
        for (id, mut fact) in facts {
            if let Some((relation, path)) = target.relation(&fact.references) {
                match relation {
                    Relation::Equal => fact.value = post.clone(),
                    Relation::Within => fact.value.update(ctx, &path, true, &write),
                    Relation::Contains => fact.value = post.at(ctx, &path),
                    Relation::Disjoint => {}
                    Relation::Overlap => {
                        if !assertion {
                            fact.value.forget(ctx);
                        }
                    }
                }
            } else if (target.unknown
                || targets.iter().any(|target| {
                    fact.references
                        .views
                        .iter()
                        .any(|view| target.relation(&view.place) != Relation::Disjoint)
                }))
                && (!assertion
                    || exact
                        && fact.references.views.iter().all(|view| {
                            targets.iter().any(|target| {
                                matches!(
                                    target.relation(&view.place),
                                    Relation::Equal | Relation::Contains | Relation::Within
                                )
                            })
                        }))
            {
                fact.value = self.heap_contents(ctx, &fact.references, fact.value.ty);
            }
            if !assertion
                && (target.unknown
                    || targets.iter().any(|target| {
                        fact.references
                            .views
                            .iter()
                            .flat_map(|view| &view.guards)
                            .any(|guard| {
                                matches!(
                                    target.relation(&guard.place),
                                    Relation::Equal | Relation::Contains | Relation::Overlap
                                )
                            })
                    }))
            {
                fact.guards = false;
            }
            self.views.insert(id, fact);
        }
        if !assertion {
            self.observations.retain(|_, refs| {
                !target.unknown
                    && !targets.iter().any(|target| {
                        refs.views.iter().any(|view| {
                            matches!(
                                target.relation(&view.place),
                                Relation::Equal | Relation::Contains | Relation::Overlap
                            )
                        })
                    })
            });
        }
        self.close_exposure(ctx);
    }
}
