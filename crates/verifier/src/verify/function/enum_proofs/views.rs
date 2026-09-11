use std::collections::{BTreeMap, BTreeSet};

use sonatina_ir::{ValueId, types::CompoundTypeRef};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) enum Root {
    Incoming(ValueId),
    IncomingNested(ValueId, CompoundTypeRef),
    Recent(ValueId),
    Summary(ValueId),
    Opaque(ValueId),
    External,
}

impl Root {
    pub fn externally_accessible(self, exposed: &BTreeSet<Self>) -> bool {
        !matches!(self, Self::Recent(_) | Self::Summary(_)) || exposed.contains(&self)
    }

    pub fn single(self) -> bool {
        matches!(self, Self::Incoming(_) | Self::Recent(_))
    }

    pub fn may_alias(self, other: Self) -> bool {
        self == other
            || matches!(
                (self, other),
                (Self::Opaque(_), _)
                    | (_, Self::Opaque(_))
                    | (
                        Self::Incoming(_) | Self::IncomingNested(..),
                        Self::Incoming(_) | Self::IncomingNested(..)
                    )
            )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) enum Index {
    Constant(usize),
    Symbol(ValueId),
    Unknown,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) enum Step {
    Index(Index),
    Payload(u32, usize),
}

impl Step {
    pub fn disjoint(self, other: Self) -> bool {
        matches!((self, other),
            (Self::Index(Index::Constant(a)), Self::Index(Index::Constant(b))) if a != b)
            || matches!((self, other),
                (Self::Payload(a, i), Self::Payload(b, j)) if a == b && i != j)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) struct Place {
    pub root: Root,
    pub path: Vec<Step>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Relation {
    Equal,
    Contains,
    Within,
    Disjoint,
    Overlap,
}

pub(super) fn path_relation(left: &[Step], right: &[Step]) -> Relation {
    for (&a, &b) in left.iter().zip(right) {
        if matches!(a, Step::Index(Index::Unknown)) || matches!(b, Step::Index(Index::Unknown)) {
            return Relation::Overlap;
        }
        if a != b {
            return if a.disjoint(b) {
                Relation::Disjoint
            } else {
                Relation::Overlap
            };
        }
    }
    match left.len().cmp(&right.len()) {
        std::cmp::Ordering::Less => Relation::Contains,
        std::cmp::Ordering::Equal => Relation::Equal,
        std::cmp::Ordering::Greater => Relation::Within,
    }
}

impl Place {
    pub fn relation(&self, other: &Self) -> Relation {
        if self.root == other.root {
            path_relation(&self.path, &other.path)
        } else if self.root.may_alias(other.root) {
            Relation::Overlap
        } else {
            Relation::Disjoint
        }
    }

    pub fn exact(&self) -> bool {
        self.root.single()
            && self
                .path
                .iter()
                .all(|step| !matches!(step, Step::Index(Index::Unknown)))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) struct Guard {
    pub place: Place,
    pub variant: u32,
    // A phi's edge-substituted guarantee can prove a guard even when merging
    // the candidate allocation facts alone loses the necessary correlation.
    pub witness: Option<ValueId>,
    pub anchor: Option<Anchor>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) struct View {
    pub place: Place,
    pub guards: BTreeSet<Guard>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) struct Anchor {
    pub value: ValueId,
    pub path: Vec<Step>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct References {
    pub views: BTreeSet<View>,
    pub unknown: bool,
    pub anchors: BTreeSet<Anchor>,
    pub cache: Option<ValueId>,
}

impl References {
    pub fn externally_accessible(&self, exposed: &BTreeSet<Root>) -> bool {
        self.unknown
            || self
                .views
                .iter()
                .any(|view| view.place.root.externally_accessible(exposed))
    }

    pub fn root(root: Root) -> Self {
        Self {
            views: BTreeSet::from([View {
                place: Place { root, path: vec![] },
                guards: BTreeSet::new(),
            }]),
            ..Self::default()
        }
    }

    pub fn unknown() -> Self {
        Self {
            unknown: true,
            ..Self::default()
        }
    }

    pub fn join(&self, other: &Self) -> Self {
        let mut result = self.clone();
        result.join_with(other);
        result
    }

    pub fn join_with(&mut self, other: &Self) {
        self.views.extend(other.views.iter().cloned());
        self.unknown |= other.unknown;
        self.anchors.retain(|anchor| other.anchors.contains(anchor));
        if self.cache != other.cache {
            self.cache = None;
        }
    }

    pub fn relation(&self, other: &Self) -> Option<(Relation, Vec<Step>)> {
        let own = self.cache.map(|value| Anchor {
            value,
            path: vec![],
        });
        let theirs = other.cache.map(|value| Anchor {
            value,
            path: vec![],
        });
        let mut overlap = None;
        for a in self.anchors.iter().chain(own.as_ref()) {
            for b in other
                .anchors
                .iter()
                .chain(theirs.as_ref())
                .filter(|b| b.value == a.value)
            {
                let relation = path_relation(&a.path, &b.path);
                if relation == Relation::Overlap {
                    overlap = Some((relation, vec![]));
                    continue;
                }
                let path = match relation {
                    Relation::Within => a.path[b.path.len()..].to_vec(),
                    Relation::Contains => b.path[a.path.len()..].to_vec(),
                    _ => vec![],
                };
                return Some((relation, path));
            }
        }
        overlap
    }

    pub fn same_location(&self, other: &Self) -> bool {
        !self.unknown
            && !other.unknown
            && (self
                .relation(other)
                .is_some_and(|(relation, _)| relation == Relation::Equal)
                || self.views.len() == 1
                    && other.views.len() == 1
                    && self
                        .views
                        .first()
                        .zip(other.views.first())
                        .is_some_and(|(a, b)| a.place.exact() && a.place == b.place))
    }

    pub fn project(&self, step: Step) -> Self {
        let mut result = self.clone();
        result.cache = None;
        result.views = self
            .views
            .iter()
            .map(|view| {
                let mut view = view.clone();
                if let Step::Payload(variant, _) = step {
                    view.guards.insert(Guard {
                        place: view.place.clone(),
                        variant,
                        witness: None,
                        anchor: self.cache.map(|value| Anchor {
                            value,
                            path: vec![],
                        }),
                    });
                }
                view.place.path.push(step);
                view
            })
            .collect();
        if let Some(value) = self.cache {
            result.anchors.insert(Anchor {
                value,
                path: vec![],
            });
        }
        result.anchors = result
            .anchors
            .into_iter()
            .map(|mut anchor| {
                anchor.path.push(step);
                anchor
            })
            .collect();
        result
    }

    /// Substitute correlated phi endpoints before their predecessor states
    /// merge. All old names are removed before any new name is installed.
    pub fn substitute(
        &mut self,
        ids: &BTreeSet<ValueId>,
        aliases: &[(ValueId, Self)],
        named: &BTreeMap<ValueId, Self>,
    ) {
        let replacements = |reference: &Self| {
            aliases
                .iter()
                .filter_map(|(value, incoming)| {
                    reference
                        .relation(incoming)
                        .filter(|(relation, _)| {
                            matches!(relation, Relation::Equal | Relation::Within)
                        })
                        .map(|(_, path)| Anchor {
                            value: *value,
                            path,
                        })
                })
                .collect::<BTreeSet<_>>()
        };
        let added = replacements(self);
        self.views = self.views.iter().cloned().map(|mut view| {
            for step in &mut view.place.path {
                if matches!(*step, Step::Index(Index::Symbol(id)) if ids.contains(&id)) { *step = Step::Index(Index::Unknown); }
            }
            view.guards = view.guards.into_iter().map(|mut guard| {
                for step in &mut guard.place.path {
                    if matches!(*step, Step::Index(Index::Symbol(id)) if ids.contains(&id)) { *step = Step::Index(Index::Unknown); }
                }
                if guard.witness.is_some_and(|id| ids.contains(&id)) { guard.witness = None; }
                guard.anchor = guard.anchor.and_then(|anchor| {
                    let replacement = named.get(&anchor.value).and_then(|source| {
                        let source = anchor.path.iter().fold(source.clone(), |refs, &step| refs.project(step));
                        replacements(&source).into_iter().next()
                    });
                    replacement.or_else(|| (!ids.contains(&anchor.value) && !anchor.path.iter().any(|step| matches!(*step, Step::Index(Index::Symbol(id)) if ids.contains(&id)))).then_some(anchor))
                });
                guard
            }).collect();
            view
        }).collect();
        if self.cache.is_some_and(|id| ids.contains(&id)) {
            self.cache = None;
        }
        self.anchors.retain(|anchor| {
            !ids.contains(&anchor.value)
                && !anchor.path.iter().any(
                    |step| matches!(*step, Step::Index(Index::Symbol(id)) if ids.contains(&id)),
                )
        });
        self.anchors.extend(added);
    }

    pub fn rewrite(&mut self, mut place: impl FnMut(&mut Place), kill: Option<ValueId>) {
        let mut rewrite = |target: &mut Place| {
            place(target);
            for step in &mut target.path {
                if matches!(*step, Step::Index(Index::Symbol(id)) if Some(id) == kill) {
                    *step = Step::Index(Index::Unknown);
                }
            }
        };
        self.views = self
            .views
            .iter()
            .map(|view| {
                let mut view = view.clone();
                rewrite(&mut view.place);
                view.guards = view
                    .guards
                    .into_iter()
                    .map(|mut guard| {
                        rewrite(&mut guard.place);
                        if let Some(anchor) = &mut guard.anchor {
                            for step in &mut anchor.path {
                                if matches!(*step, Step::Index(Index::Symbol(id)) if Some(id) == kill) { *step = Step::Index(Index::Unknown); }
                            }
                        }
                        if guard.anchor.as_ref().is_some_and(|a| Some(a.value) == kill) { guard.anchor = None; }
                        if kill.is_some() && guard.witness == kill {
                            guard.witness = None;
                        }
                        guard
                    })
                    .collect();
                view
            })
            .collect();
        if kill.is_some() && self.cache == kill {
            self.cache = None;
        }
        self.anchors.retain(|anchor| {
            Some(anchor.value) != kill
                && !anchor
                    .path
                    .iter()
                    .any(|step| matches!(*step, Step::Index(Index::Symbol(id)) if Some(id) == kill))
        });
    }
}
