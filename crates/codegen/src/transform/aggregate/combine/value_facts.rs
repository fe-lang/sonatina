use cranelift_entity::SecondaryMap;
use rustc_hash::FxHashMap;
use sonatina_ir::{Function, ValueId, inst::data};

use super::{inst_const_index, is_explicit_undef, shape};
use shape::FieldPath;

#[derive(Default)]
pub(super) struct AggregateValueFacts {
    pub(super) reconstructed: SecondaryMap<ValueId, Option<ValueId>>,
}

#[derive(Clone, Copy)]
struct Insert {
    base: ValueId,
    value: ValueId,
    index: Option<u32>,
    field_count: usize,
    source: Option<ValueId>,
}

#[derive(Clone, Copy)]
enum Visit {
    Enter(ValueId),
    Exit(ValueId),
}

/// The fields the inserts on the current path assigned, each with the
/// aggregate its value was extracted from, if any.
#[derive(Default)]
struct Assignments {
    fields: FxHashMap<u32, Option<ValueId>>,
    sources: FxHashMap<ValueId, usize>,
    sourced: usize,
}

impl Assignments {
    fn replace(&mut self, index: u32, field: Option<Option<ValueId>>) -> Option<Option<ValueId>> {
        let previous = self.fields.remove(&index);
        if let Some(Some(source)) = previous {
            self.sourced -= 1;
            let count = self.sources.get_mut(&source).unwrap();
            *count -= 1;
            if *count == 0 {
                self.sources.remove(&source);
            }
        }
        if let Some(source) = field {
            if let Some(source) = source {
                self.sourced += 1;
                *self.sources.entry(source).or_default() += 1;
            }
            self.fields.insert(index, source);
        }
        previous
    }
}

impl AggregateValueFacts {
    pub(super) fn compute(func: &Function) -> Self {
        let aggregates: Vec<_> = func
            .dfg
            .value_ids()
            .filter(|&value| shape::is_supported_aggregate_ty(func.ctx(), func.dfg.value_ty(value)))
            .collect();
        let mut facts = Self::default();
        let mut inserts = SecondaryMap::<ValueId, Option<Insert>>::default();
        let mut children = SecondaryMap::<ValueId, Vec<ValueId>>::default();
        for &value in &aggregates {
            if let Some(inst) = func.dfg.value_inst(value)
                && let Some(insert) = func.dfg.downcast::<&data::InsertValue>(inst)
            {
                let ty = func.dfg.value_ty(value);
                let index = inst_const_index(func, *insert.idx());
                inserts[value] = Some(Insert {
                    base: *insert.dest(),
                    value: *insert.value(),
                    index,
                    field_count: shape::aggregate_child_count(func.ctx(), ty).unwrap_or(0),
                    source: None,
                });
                children[*insert.dest()].push(value);
            }
        }

        // Inserts have one destination parent. Phi and other definitions terminate
        // a tree, so an iterative DFS can share one map and roll back at each fork.
        let mut visits = Vec::new();
        let mut pending = Vec::new();
        for &value in &aggregates {
            if let Some(insert) = inserts[value]
                && inserts[insert.base].is_none()
            {
                pending.push(Visit::Enter(value));
                while let Some(visit) = pending.pop() {
                    visits.push(visit);
                    if let Visit::Enter(value) = visit {
                        pending.push(Visit::Exit(value));
                        pending.extend(children[value].iter().rev().copied().map(Visit::Enter));
                    }
                }
            }
        }

        // Compute coverage once, including dynamic-index barriers, before
        // asking about nested reconstructions.
        let mut complete = SecondaryMap::<ValueId, bool>::default();
        let mut counts = FxHashMap::<u32, usize>::default();
        let mut invalid = 0usize;
        for visit in &visits {
            let (Visit::Enter(value) | Visit::Exit(value)) = *visit;
            let insert = inserts[value].unwrap();
            let valid = insert
                .index
                .is_some_and(|index| (index as usize) < insert.field_count);
            match visit {
                Visit::Enter(_) => {
                    invalid += usize::from(!valid);
                    if let Some(index) = insert.index {
                        *counts.entry(index).or_default() += 1;
                    }
                    complete[value] = invalid == 0 && counts.len() == insert.field_count;
                }
                Visit::Exit(_) => {
                    invalid -= usize::from(!valid);
                    if let Some(index) = insert.index {
                        let count = counts.get_mut(&index).unwrap();
                        *count -= 1;
                        if *count == 0 {
                            counts.remove(&index);
                        }
                    }
                }
            }
        }

        let mut sources = ReconstructionSources {
            func,
            complete: &complete,
            memo: FxHashMap::default(),
        };
        for &value in &aggregates {
            if let Some(insert) = inserts[value].as_mut()
                && let Some(index) = insert.index
            {
                let mut path = FieldPath::from_slice(&[index]);
                insert.source = sources.resolve(insert.value, &mut path).filter(|&source| {
                    !is_explicit_undef(func, source)
                        && func.dfg.value_ty(source) == func.dfg.value_ty(value)
                });
            }
        }

        let mut assignments = Assignments::default();
        let mut undo = Vec::new();
        for visit in &visits {
            let (Visit::Enter(value) | Visit::Exit(value)) = *visit;
            let insert = inserts[value].unwrap();
            match visit {
                Visit::Enter(_) => {
                    if let Some(index) = insert.index {
                        undo.push(assignments.replace(index, Some(insert.source)));
                    }
                    facts.reconstructed[value] = (complete[value]
                        && assignments.sourced == insert.field_count
                        && assignments.sources.len() == 1)
                        .then(|| *assignments.sources.keys().next().unwrap());
                }
                Visit::Exit(_) => {
                    if let Some(index) = insert.index {
                        assignments.replace(index, undo.pop().unwrap());
                    }
                }
            }
        }
        facts
    }
}

struct ReconstructionSources<'a> {
    func: &'a Function,
    complete: &'a SecondaryMap<ValueId, bool>,
    memo: FxHashMap<(ValueId, FieldPath), Option<ValueId>>,
}

impl ReconstructionSources<'_> {
    fn resolve(&mut self, value: ValueId, path: &mut FieldPath) -> Option<ValueId> {
        let key = (value, path.clone());
        if let Some(&source) = self.memo.get(&key) {
            return source;
        }
        self.memo.insert(key.clone(), None);
        if let Some(source) = extract_chain_source(self.func, value, path) {
            self.memo.insert(key, Some(source));
            return Some(source);
        }
        if !self.complete[value] {
            return None;
        }

        // The last inserted field must itself come from this path. Reject a
        // mismatching path before walking a potentially large nested aggregate.
        let inst = self.func.dfg.value_inst(value)?;
        let insert = self.func.dfg.downcast::<&data::InsertValue>(inst)?;
        let index = inst_const_index(self.func, *insert.idx())?;
        let field = *insert.value();
        path.push(index);
        let source = self.resolve(field, path);
        path.pop();
        let source = source?;

        let mut assignments = FxHashMap::default();
        let mut current = value;
        while let Some(inst) = self.func.dfg.value_inst(current) {
            let Some(insert) = self.func.dfg.downcast::<&data::InsertValue>(inst) else {
                break;
            };
            let index = inst_const_index(self.func, *insert.idx())?;
            assignments.entry(index).or_insert(*insert.value());
            current = *insert.dest();
        }
        for (index, field) in assignments {
            path.push(index);
            let field_source = self.resolve(field, path);
            path.pop();
            let field_source = field_source?;
            if source != field_source {
                return None;
            }
        }
        self.memo.insert(key, Some(source));
        Some(source)
    }
}

fn extract_chain_source(func: &Function, mut value: ValueId, path: &[u32]) -> Option<ValueId> {
    for &index in path.iter().rev() {
        let inst = func.dfg.value_inst(value)?;
        let extract = func.dfg.downcast::<&data::ExtractValue>(inst)?;
        if inst_const_index(func, *extract.idx()) != Some(index) {
            return None;
        }
        value = *extract.dest();
    }
    Some(value)
}

#[cfg(test)]
mod tests;
