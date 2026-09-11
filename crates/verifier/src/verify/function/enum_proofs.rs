//! Forward enum verification over guarded references, value snapshots, mutable
//! objects, and exposure. Local typing and SSA availability are prerequisites.
use std::collections::{BTreeMap, BTreeSet, VecDeque};

use sonatina_ir::{
    BlockId, Type,
    inst::{control_flow, data, downcast},
    types::CompoundType,
};

use super::FunctionVerifier;
use crate::diagnostic::{Diagnostic, DiagnosticCode};
use objects::State;
use value_state::ValueState;
use views::{Anchor, References};

mod objects;
#[cfg(test)]
mod tests;
mod transfer;
mod value_state;
mod views;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Proof {
    NoLocalEnumObligation,
    Proven,
    Unproved(&'static str),
}

fn read(
    state: &State,
    verifier: &FunctionVerifier<'_>,
    refs: &References,
    ty: Type,
    tag_only: bool,
) -> Proof {
    if refs.unknown || refs.views.is_empty() {
        Proof::Unproved("unknown local reference provenance")
    } else if refs.views.iter().all(|view| view.guards.is_empty()) {
        Proof::NoLocalEnumObligation
    } else if !state.guards_hold(verifier.ctx, refs) {
        Proof::Unproved("an ancestor enum variant is not proven active")
    } else {
        let initialized = |value: &ValueState| {
            if tag_only {
                value.tag_initialized
            } else {
                value.readable(verifier.ctx)
            }
        };
        let value = state.contents(verifier.ctx, refs, ty);
        let mut guarded = refs.clone();
        guarded.views.retain(|view| !view.guards.is_empty());
        guarded.cache = None;
        // An imported, unguarded alternative has no local payload obligation.
        // The symbolic view can prove all alternatives at once; otherwise only
        // the guarded candidates demand a subtree proof.
        if initialized(&value) || initialized(&state.contents(verifier.ctx, &guarded, ty)) {
            Proof::Proven
        } else {
            Proof::Unproved("the demanded enum payload subtree is not proven initialized")
        }
    }
}

pub(super) fn verify(verifier: &mut FunctionVerifier<'_>) {
    // Enum projection is the only source of a local ancestor obligation.
    // Imported references have no hidden guard under the interface contract.
    if !verifier.block_to_insts.values().flatten().any(|&id| {
        let inst = verifier.func.dfg.inst(id);
        downcast::<&data::EnumProj>(verifier.ctx.inst_set, inst).is_some()
            || downcast::<&data::EnumExtract>(verifier.ctx.inst_set, inst).is_some()
            || downcast::<&data::EnumGetTag>(verifier.ctx.inst_set, inst).is_some()
    }) {
        return;
    }
    let entries = solve(verifier);
    for block in verifier.block_order.clone() {
        let Some(mut state) = entries.get(&block).cloned() else {
            continue;
        };
        for inst in verifier.block_to_insts[&block].clone() {
            if let Proof::Unproved(reason) = transfer::instruction(verifier, &mut state, inst) {
                verifier.emit(Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    reason,
                    verifier.inst_location(inst),
                ));
            }
        }
    }
}

fn solve(verifier: &FunctionVerifier<'_>) -> BTreeMap<BlockId, State> {
    let cfg = &verifier.analysis_cfg;
    let mut entries = BTreeMap::new();
    let mut pending = VecDeque::new();
    let mut queued = BTreeSet::new();
    for &block in &cfg.blocks {
        if cfg.entries.contains(&block) {
            let mut boundary = State::boundary(verifier);
            // A virtual entry has no predecessor from which a phi can import
            // facts. This is reachable unknown state, distinct from NoFlow.
            phis(verifier, &mut boundary, None, block);
            entries.insert(block, boundary);
            pending.push_back(block);
            queued.insert(block);
        }
    }
    while let Some(block) = pending.pop_front() {
        queued.remove(&block);
        let mut state = entries[&block].clone();
        for &inst in &verifier.block_to_insts[&block] {
            transfer::instruction(verifier, &mut state, inst);
        }
        for &succ in cfg.succs.get(&block).into_iter().flatten() {
            let Some(mut edge) = edge(verifier, &state, block, succ) else {
                continue;
            };
            phis(verifier, &mut edge, Some(block), succ);
            let next = entries
                .get(&succ)
                .map_or_else(|| edge.clone(), |old| old.join(verifier.ctx, &edge));
            if entries.get(&succ) != Some(&next) {
                entries.insert(succ, next);
                if queued.insert(succ) {
                    pending.push_back(succ);
                }
            }
        }
    }
    entries
}

fn phis(verifier: &FunctionVerifier<'_>, state: &mut State, pred: Option<BlockId>, block: BlockId) {
    let ctx = verifier.ctx;
    let mut incoming = vec![];
    for &inst in &verifier.block_to_insts[&block] {
        let Some(phi) = downcast::<&control_flow::Phi>(ctx.inst_set, verifier.func.dfg.inst(inst))
        else {
            continue;
        };
        let id = verifier.func.dfg.inst_results(inst)[0];
        let ty = verifier.func.dfg.value_ty(id);
        let source =
            pred.and_then(|pred| phi.args().iter().find(|(_, b)| *b == pred).map(|(v, _)| *v));
        let value = source.map_or_else(|| ValueState::new(ty, false), |v| state.value(verifier, v));
        let fact = verifier
            .objref_ty(ty)
            .map(|elem| state.fact(ctx, &value.references, elem));
        incoming.push((id, source, value, fact));
    }
    let mut observations = vec![];
    let mut value_observations = vec![];
    for &(id, source, _, _) in &incoming {
        if let Some(refs) = source.and_then(|v| state.observations.get(&v)) {
            let mapped = incoming
                .iter()
                .find(|(_, _, _, fact)| {
                    fact.as_ref()
                        .is_some_and(|fact| refs.same_location(&fact.references))
                })
                .map(|(id, ..)| *id);
            observations.push((id, refs.clone(), mapped));
        }
        if let Some(&(value, predicate)) = source.and_then(|v| state.value_observations.get(&v)) {
            let mapped = incoming
                .iter()
                .find(|(_, source, ..)| *source == Some(value))
                .map(|(id, ..)| *id);
            if mapped.is_some() || incoming.iter().all(|(id, ..)| *id != value) {
                value_observations.push((id, (mapped.unwrap_or(value), predicate)));
            }
        }
    }
    // Read and substitute every operand against the predecessor's names, then
    // retire all old bindings before installing any of the new phi bindings.
    let ids: BTreeSet<_> = incoming.iter().map(|(id, ..)| *id).collect();
    let aliases: Vec<_> = incoming
        .iter()
        .filter_map(|(id, _, _, fact)| fact.as_ref().map(|fact| (*id, fact.references.clone())))
        .collect();
    let named = state
        .views
        .iter()
        .map(|(&id, fact)| (id, fact.references.clone()))
        .collect();
    for (_, _, value, fact) in &mut incoming {
        for &old in &ids {
            value.forget_index(ctx, old);
        }
        value.visit_references(ctx, &mut |refs| refs.substitute(&ids, &aliases, &named));
        if let Some(fact) = fact {
            for &old in &ids {
                fact.value.forget_index(ctx, old);
            }
            fact.value
                .visit_references(ctx, &mut |refs| refs.substitute(&ids, &aliases, &named));
        }
    }
    for (_, refs, _) in &mut observations {
        refs.substitute(&ids, &aliases, &named);
    }
    for &id in &ids {
        state.prepare_binding(ctx, id);
    }
    for (id, _, mut value, fact) in incoming {
        if fact.is_some() {
            value.references.anchors.insert(Anchor {
                value: id,
                path: vec![],
            });
        }
        state.install(id, value, fact);
    }
    for (id, mut refs, mapped) in observations {
        if let Some(mapped) = mapped {
            refs = state.values[&mapped].references.clone();
        }
        state.observations.insert(id, refs);
    }
    state.value_observations.extend(value_observations);
}

fn edge(
    verifier: &FunctionVerifier<'_>,
    state: &State,
    pred: BlockId,
    succ: BlockId,
) -> Option<State> {
    let mut next = state.clone();
    let inst = verifier
        .func
        .dfg
        .inst(verifier.func.layout.last_inst_of(pred)?);
    let table = downcast::<&control_flow::BrTable>(verifier.ctx.inst_set, inst);
    let branch = downcast::<&control_flow::Br>(verifier.ctx.inst_set, inst);
    let scrutinee = table
        .map(|b| *b.scrutinee())
        .or_else(|| branch.map(|b| *b.cond()));
    let Some(scrutinee) = scrutinee else {
        return Some(next);
    };
    let refs = state.observations.get(&scrutinee);
    let immutable = state.value_observations.get(&scrutinee);
    let value = if let Some(refs) = refs {
        let Type::EnumTag(ty) = verifier.func.dfg.value_ty(scrutinee) else {
            unreachable!("object tag observation")
        };
        state.contents(verifier.ctx, refs, Type::Compound(ty))
    } else if let Some(&(value, _)) = immutable {
        state.value(verifier, value)
    } else {
        return Some(next);
    };
    let Some(CompoundType::Enum(enumeration)) = value.ty.resolve_compound(verifier.ctx) else {
        unreachable!("enum observation")
    };
    let tags: BTreeSet<_> = enumeration
        .variants
        .iter()
        .enumerate()
        .filter_map(|(index, _)| {
            let case_index = immutable
                .and_then(|(_, predicate)| *predicate)
                .map_or(index, |variant| usize::from(index as u32 == variant));
            let reaches = if let Some(table) = table {
                let mut explicit = false;
                let mut reaches = false;
                for &(case, dest) in table.table() {
                    if verifier
                        .value_imm(case)
                        .and_then(|n| n.to_nonnegative_usize())
                        == Some(case_index)
                    {
                        explicit = true;
                        reaches |= dest == succ;
                    }
                }
                reaches || !explicit && *table.default() == Some(succ)
            } else if let Some(branch) = branch
                && let Some(&(_, Some(variant))) = immutable
            {
                (index as u32 == variant && *branch.nz_dest() == succ)
                    || (index as u32 != variant && *branch.z_dest() == succ)
            } else {
                true
            };
            (reaches && value.possible(index as u32)).then_some(index as u32)
        })
        .collect();
    if tags.is_empty() {
        return None;
    }
    let refine = |value: &mut ValueState| {
        value.tags = Some(tags.clone());
        value.tag_initialized = true;
    };
    if let Some(refs) = refs {
        next.write(verifier.ctx, refs, value.ty, true, refine);
    } else if let Some(&(id, _)) = immutable {
        let mut value = value;
        refine(&mut value);
        next.values.insert(id, value);
    }
    Some(next)
}
