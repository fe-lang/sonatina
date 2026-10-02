//! Conservative write candidates. Facts remain in State; this index only skips
//! facts whose anchors, physical locations and guard locations are disjoint.
use std::{
    collections::{BTreeMap, BTreeSet},
    ops::Bound::{Excluded, Unbounded},
};

use sonatina_ir::ValueId;

use super::views::{Index, References, Root, Step};

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Paths {
    values: BTreeSet<ValueId>,
    children: BTreeMap<Step, Self>,
}

impl Paths {
    fn update(&mut self, path: &[Step], id: ValueId, insert: bool) {
        if let Some((step, rest)) = path.split_first() {
            if insert {
                self.children
                    .entry(*step)
                    .or_default()
                    .update(rest, id, true);
            } else if let Some(child) = self.children.get_mut(step) {
                child.update(rest, id, false);
                if child.values.is_empty() && child.children.is_empty() {
                    self.children.remove(step);
                }
            }
        } else if insert {
            self.values.insert(id);
        } else {
            self.values.remove(&id);
        }
    }

    fn all(&self, found: &mut BTreeSet<ValueId>) {
        found.extend(&self.values);
        for child in self.children.values() {
            child.all(found);
        }
    }

    fn overlapping(&self, path: &[Step], found: &mut BTreeSet<ValueId>) {
        let Some((step, rest)) = path.split_first() else {
            self.all(found);
            return;
        };
        found.extend(&self.values);
        match step {
            Step::Index(Index::Constant(_)) => {
                if let Some(child) = self.children.get(step) {
                    child.overlapping(rest, found);
                }
                // Every other constant is disjoint. Symbols, unknown indices
                // and payload steps can overlap at this first differing step.
                for (_, child) in self.children.range((
                    Excluded(Step::Index(Index::Constant(usize::MAX))),
                    Unbounded,
                )) {
                    child.all(found);
                }
            }
            Step::Payload(variant, _) => {
                if let Some(child) = self.children.get(step) {
                    child.overlapping(rest, found);
                }
                // Other fields of this variant are disjoint; other variants
                // and index steps overlap, regardless of the remaining path.
                for (_, child) in self.children.range(..Step::Payload(*variant, 0)).chain(
                    self.children
                        .range((Excluded(Step::Payload(*variant, usize::MAX)), Unbounded)),
                ) {
                    child.all(found);
                }
            }
            Step::Index(Index::Symbol(_) | Index::Unknown) => self.all(found),
        }
    }
}

fn update_paths<K: Copy + Ord>(
    paths: &mut BTreeMap<K, Paths>,
    key: K,
    path: &[Step],
    id: ValueId,
    insert: bool,
) {
    if insert {
        paths.entry(key).or_default().update(path, id, true);
    } else if let Some(tree) = paths.get_mut(&key) {
        tree.update(path, id, false);
        if tree.values.is_empty() && tree.children.is_empty() {
            paths.remove(&key);
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct ViewIndex {
    places: BTreeMap<Root, Paths>,
    anchors: BTreeMap<ValueId, Paths>,
}

impl ViewIndex {
    pub fn update(&mut self, id: ValueId, refs: &References, insert: bool) {
        for view in &refs.views {
            for place in std::iter::once(&view.place).chain(view.guards.iter().map(|g| &g.place)) {
                update_paths(&mut self.places, place.root, &place.path, id, insert);
            }
        }
        for (value, path) in refs
            .anchors
            .iter()
            .map(|anchor| (anchor.value, anchor.path.as_slice()))
            .chain(refs.cache.map(|value| (value, &[][..])))
        {
            update_paths(&mut self.anchors, value, path, id, insert);
        }
    }

    pub fn candidates(&self, target: &References) -> BTreeSet<ValueId> {
        debug_assert!(!target.unknown);
        let mut found = BTreeSet::new();
        for view in &target.views {
            for (&root, paths) in &self.places {
                if root == view.place.root {
                    paths.overlapping(&view.place.path, &mut found);
                } else if root.may_alias(view.place.root) {
                    paths.all(&mut found);
                }
            }
        }
        for (value, path) in target
            .anchors
            .iter()
            .map(|anchor| (anchor.value, anchor.path.as_slice()))
            .chain(target.cache.map(|value| (value, &[][..])))
        {
            if let Some(paths) = self.anchors.get(&value) {
                paths.overlapping(path, &mut found);
            }
        }
        found
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::verify::function::enum_proofs::views::{
        Anchor, Guard, Place, Relation, View, path_relation,
    };

    #[test]
    fn path_candidates_cover_all_overlaps_and_skip_disjoint_array_cells() {
        let steps = [
            Step::Index(Index::Constant(0)),
            Step::Index(Index::Constant(1)),
            Step::Index(Index::Constant(usize::MAX)),
            Step::Index(Index::Symbol(ValueId::from_u32(10))),
            Step::Index(Index::Symbol(ValueId::from_u32(11))),
            Step::Index(Index::Unknown),
            Step::Payload(0, 0),
            Step::Payload(0, 1),
            Step::Payload(u32::MAX, usize::MAX),
        ];
        let mut paths = vec![vec![]];
        for _ in 0..3 {
            let next: Vec<_> = paths
                .iter()
                .filter(|path| path.len() == paths.last().unwrap().len())
                .flat_map(|path| {
                    steps.map(|step| {
                        let mut next = path.clone();
                        next.push(step);
                        next
                    })
                })
                .collect();
            paths.extend(next);
        }
        let mut index = Paths::default();
        for (id, path) in paths.iter().enumerate() {
            index.update(path, ValueId::from_u32(id as u32), true);
        }
        for target in &paths {
            let mut found = BTreeSet::new();
            index.overlapping(target, &mut found);
            for (id, path) in paths.iter().enumerate() {
                assert!(
                    path_relation(target, path) == Relation::Disjoint
                        || found.contains(&ValueId::from_u32(id as u32)),
                    "missed {target:?} against {path:?}"
                );
            }
        }
        let mut array = Paths::default();
        for id in 0..4096 {
            array.update(
                &[Step::Index(Index::Constant(id))],
                ValueId::from_u32(id as u32),
                true,
            );
        }
        let mut found = BTreeSet::new();
        array.overlapping(&[Step::Index(Index::Constant(123))], &mut found);
        assert_eq!(found, BTreeSet::from([ValueId::from_u32(123)]));
        for (id, path) in paths.iter().enumerate() {
            index.update(path, ValueId::from_u32(id as u32), false);
        }
        assert_eq!(index, Paths::default());
    }

    #[test]
    fn candidates_include_alias_roots_guards_and_correlated_anchors() {
        let id = ValueId::from_u32(1);
        let local = Root::Recent(id);
        let mut refs = References::root(local);
        refs.cache = Some(id);
        refs.anchors.insert(Anchor {
            value: id,
            path: vec![],
        });
        refs.views.insert(View {
            place: Place {
                root: Root::Incoming(id),
                path: vec![],
            },
            guards: BTreeSet::from([Guard {
                place: Place {
                    root: Root::Summary(id),
                    path: vec![],
                },
                variant: 0,
                witness: None,
                anchor: None,
            }]),
        });
        let mut index = ViewIndex::default();
        index.update(id, &refs, true);
        for root in [
            local,
            Root::Incoming(ValueId::from_u32(2)),
            Root::Summary(id),
        ] {
            assert_eq!(
                index.candidates(&References::root(root)),
                BTreeSet::from([id])
            );
        }
        let mut disjoint = References::root(Root::Recent(ValueId::from_u32(2)));
        assert!(index.candidates(&disjoint).is_empty());
        disjoint.anchors.insert(Anchor {
            value: id,
            path: vec![],
        });
        assert_eq!(index.candidates(&disjoint), BTreeSet::from([id]));
        index.update(id, &refs, false);
        assert_eq!(index, ViewIndex::default());
    }
}
