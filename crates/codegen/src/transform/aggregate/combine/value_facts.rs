use cranelift_entity::SecondaryMap;
use rustc_hash::FxHashMap;
use sonatina_ir::{
    Function, ValueId,
    inst::{cast, control_flow, data, downcast},
};

use super::{inst_const_index, is_explicit_undef, shape};
use shape::FieldPath;

#[derive(Default)]
pub(super) struct AggregateValueFacts {
    pub(super) definitely_non_undef: SecondaryMap<ValueId, bool>,
    pub(super) reconstructed: SecondaryMap<ValueId, Option<ValueId>>,
}

#[derive(Clone, Copy)]
struct Insert {
    base: ValueId,
    value: ValueId,
    index: Option<u32>,
    field_count: usize,
    field_matches: bool,
    source: Option<ValueId>,
}

#[derive(Clone, Copy)]
enum Visit {
    Enter(ValueId),
    Exit(ValueId),
}

#[derive(Clone, Copy)]
struct Field {
    defined: bool,
    source: Option<ValueId>,
}

#[derive(Default)]
struct Assignments {
    fields: FxHashMap<u32, Field>,
    defined: usize,
    sources: FxHashMap<ValueId, usize>,
    sourced: usize,
}

impl Assignments {
    fn replace(&mut self, index: u32, field: Option<Field>) -> Option<Field> {
        let previous = self.fields.remove(&index);
        if let Some(previous) = previous {
            self.defined -= usize::from(previous.defined);
            if let Some(source) = previous.source {
                self.sourced -= 1;
                let count = self.sources.get_mut(&source).unwrap();
                *count -= 1;
                if *count == 0 {
                    self.sources.remove(&source);
                }
            }
        }
        if let Some(field) = field {
            self.defined += usize::from(field.defined);
            if let Some(source) = field.source {
                self.sourced += 1;
                *self.sources.entry(source).or_default() += 1;
            }
            self.fields.insert(index, field);
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
            facts.definitely_non_undef[value] = !is_explicit_undef(func, value);
            if let Some(inst) = func.dfg.value_inst(value)
                && let Some(insert) =
                    downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(inst))
            {
                let ty = func.dfg.value_ty(value);
                let index = inst_const_index(func, *insert.idx());
                inserts[value] = Some(Insert {
                    base: *insert.dest(),
                    value: *insert.value(),
                    index,
                    field_count: shape::aggregate_child_count(func.ctx(), ty).unwrap_or(0),
                    field_matches: index
                        .and_then(|index| shape::aggregate_child_ty(func.ctx(), ty, index))
                        == Some(func.dfg.value_ty(*insert.value())),
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

        // Coverage does not depend on definedness. Compute it once, including
        // dynamic-index barriers, before asking about nested reconstructions.
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
        loop {
            let mut changed = false;
            for &value in &aggregates {
                if inserts[value].is_none() {
                    let next = non_insert_is_defined(func, value, &facts.definitely_non_undef);
                    changed |= facts.definitely_non_undef[value] != next;
                    facts.definitely_non_undef[value] = next;
                }
            }
            for visit in &visits {
                let (Visit::Enter(value) | Visit::Exit(value)) = *visit;
                let insert = inserts[value].unwrap();
                match visit {
                    Visit::Enter(_) => {
                        if let Some(index) = insert.index {
                            let field = Field {
                                defined: insert.field_matches
                                    && value_is_defined(
                                        func,
                                        insert.value,
                                        &facts.definitely_non_undef,
                                    ),
                                source: insert.source,
                            };
                            undo.push(assignments.replace(index, Some(field)));
                        }
                        let next = facts.definitely_non_undef[insert.base]
                            || complete[value] && assignments.defined == insert.field_count;
                        changed |= facts.definitely_non_undef[value] != next;
                        facts.definitely_non_undef[value] = next;
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
            if !changed {
                return facts;
            }
        }
    }
}

fn value_is_defined(
    func: &Function,
    value: ValueId,
    defined: &SecondaryMap<ValueId, bool>,
) -> bool {
    if shape::is_supported_aggregate_ty(func.ctx(), func.dfg.value_ty(value)) {
        defined[value]
    } else {
        !is_explicit_undef(func, value)
    }
}

fn non_insert_is_defined(
    func: &Function,
    value: ValueId,
    defined: &SecondaryMap<ValueId, bool>,
) -> bool {
    if is_explicit_undef(func, value) {
        return false;
    }
    let Some(inst) = func.dfg.value_inst(value) else {
        return true;
    };
    let data = func.dfg.inst(inst);
    if let Some(phi) = downcast::<&control_flow::Phi>(func.inst_set(), data) {
        return phi.args().iter().any(|&(arg, _)| arg != value)
            && phi.args().iter().all(|&(arg, _)| {
                func.dfg.value_ty(arg) == func.dfg.value_ty(value)
                    && value_is_defined(func, arg, defined)
            });
    }
    if let Some(extract) = downcast::<&data::ExtractValue>(func.inst_set(), data) {
        return value_is_defined(func, *extract.dest(), defined);
    }
    if let Some(bitcast) = downcast::<&cast::Bitcast>(func.inst_set(), data) {
        return value_is_defined(func, *bitcast.from(), defined);
    }
    false
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
        let insert =
            downcast::<&data::InsertValue>(self.func.inst_set(), self.func.dfg.inst(inst))?;
        let index = inst_const_index(self.func, *insert.idx())?;
        let field = *insert.value();
        path.push(index);
        let source = self.resolve(field, path);
        path.pop();
        let source = source?;

        let mut assignments = FxHashMap::default();
        let mut current = value;
        while let Some(inst) = self.func.dfg.value_inst(current) {
            let Some(insert) =
                downcast::<&data::InsertValue>(self.func.inst_set(), self.func.dfg.inst(inst))
            else {
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
        let extract = downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(inst))?;
        if inst_const_index(func, *extract.idx()) != Some(index) {
            return None;
        }
        value = *extract.dest();
    }
    Some(value)
}

#[cfg(test)]
mod tests;
