//! Enum proofs are must facts; raw exposure is a separate may fact.
//!
//! Typed places determine overlap. Typed mutations determine initialization
//! and tag changes. Both load proofs and saved-tag freshness consume those
//! same effects. Exposure joins by union; proofs join by intersection. All
//! flows use the verifier's shared CFG domain, including virtual dead entries.
use super::FunctionVerifier;
use objects::{Effect, Mutation, Objects, Place, Relation};
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    BlockId, InstId, Type, ValueId,
    inst::{control_flow, data, downcast},
    types::{CompoundType, CompoundTypeRef, EnumVariantRef},
};
use std::collections::VecDeque;
mod objects;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(super) struct EnumFieldLoadProof {
    active_variant: bool,
    field_initialized: bool,
}
impl EnumFieldLoadProof {
    const PROVEN: Self = Self {
        active_variant: true,
        field_initialized: true,
    };
    pub(super) fn is_proven(self) -> bool {
        self.active_variant && self.field_initialized
    }
    fn intersect(self, other: Self) -> Self {
        Self {
            active_variant: self.active_variant && other.active_variant,
            field_initialized: self.field_initialized && other.field_initialized,
        }
    }
}
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Field {
    variant: EnumVariantRef,
    index: usize,
}

pub(super) fn compute(verifier: &FunctionVerifier<'_>) -> FxHashMap<InstId, EnumFieldLoadProof> {
    let mut objects = Objects::new(verifier);
    let mut results = FxHashMap::default();
    let mut requests: FxHashMap<Place, FxHashMap<Field, FxHashSet<InstId>>> = FxHashMap::default();
    for &inst in verifier.block_to_insts.values().flatten() {
        let Some(load) = verifier
            .func
            .dfg
            .get_inst(inst)
            .and_then(|i| downcast::<&data::ObjLoad>(verifier.ctx.inst_set, i))
        else {
            continue;
        };
        if verifier
            .value_ty(*load.object())
            .and_then(|ty| verifier.objref_ty(ty))
            .is_none()
        {
            continue;
        }
        let Some(proj) = verifier
            .func
            .dfg
            .value_inst(*load.object())
            .and_then(|i| verifier.func.dfg.get_inst(i))
            .and_then(|i| downcast::<&data::EnumProj>(verifier.ctx.inst_set, i))
        else {
            continue;
        };
        results.insert(inst, EnumFieldLoadProof::default());
        if let Some(index) = verifier
            .value_imm(*proj.field())
            .and_then(|i| i.to_nonnegative_usize())
        {
            requests
                .entry(objects.place(*proj.object()))
                .or_default()
                .entry(Field {
                    variant: *proj.variant(),
                    index,
                })
                .or_default()
                .insert(inst);
        }
    }
    if requests.is_empty() {
        return results;
    }
    let effects: FxHashMap<_, _> = verifier
        .block_to_insts
        .values()
        .flatten()
        .map(|&id| (id, objects.effect(id)))
        .collect();
    let mut branches: FxHashMap<Place, Vec<_>> = FxHashMap::default();
    for (&pred, successors) in &verifier.analysis_cfg.succs {
        let Some(branch) = verifier
            .func
            .layout
            .last_inst_of(pred)
            .and_then(|i| verifier.func.dfg.get_inst(i))
            .and_then(|i| downcast::<&control_flow::BrTable>(verifier.ctx.inst_set, i))
        else {
            continue;
        };
        let Some(tag) = enum_get_tag_of_value(verifier, *branch.scrutinee()) else {
            continue;
        };
        let Some(observation) = verifier.func.dfg.value_inst(*branch.scrutinee()) else {
            continue;
        };
        let object = objects.place(*tag.object());
        if !requests.contains_key(&object) {
            continue;
        }
        for &succ in successors {
            if let Some((_, variant)) = br_table_edge_variant(verifier, branch, succ) {
                branches.entry(object.clone()).or_default().push((
                    pred,
                    succ,
                    variant,
                    observation,
                ));
            }
        }
    }
    for (object, fields) in requests {
        let entries = solve(
            verifier,
            false,
            !object.is_local(),
            |a, b| a || b,
            |_, _, x| x,
            |id, x| effects[&id].exposure_after(&object, x),
        );
        let mut exposed = FxHashSet::default();
        for (&block, &entry) in &entries {
            let mut state = entry;
            for &inst in verifier.block_to_insts.get(&block).into_iter().flatten() {
                if state {
                    exposed.insert(inst);
                }
                state = effects[&inst].exposure_after(&object, state);
            }
        }
        let mut edges: FxHashMap<EnumVariantRef, FxHashSet<_>> = FxHashMap::default();
        for &(pred, succ, variant, observation) in branches.get(&object).into_iter().flatten() {
            if observation_reaches(verifier, &effects, &exposed, &object, observation, pred) {
                edges.entry(variant).or_default().insert((pred, succ));
            }
        }
        for (field, uses) in fields {
            let payload = object.payload(field.variant, field.index);
            let transfer = |id, proof| {
                transfer(
                    &object,
                    &payload,
                    field.variant,
                    proof,
                    &effects[&id],
                    exposed.contains(&id),
                )
            };
            let entries = solve(
                verifier,
                EnumFieldLoadProof::PROVEN,
                EnumFieldLoadProof::default(),
                EnumFieldLoadProof::intersect,
                |pred, block, mut proof| {
                    proof.active_variant |= edges
                        .get(&field.variant)
                        .is_some_and(|e| e.contains(&(pred, block)));
                    proof
                },
                transfer,
            );
            for (block, mut proof) in entries {
                for &inst in verifier.block_to_insts.get(&block).into_iter().flatten() {
                    if uses.contains(&inst) {
                        results.insert(inst, proof);
                    }
                    proof = transfer(inst, proof);
                }
            }
        }
    }
    results
}

fn transfer(
    object: &Place,
    payload: &Place,
    variant: EnumVariantRef,
    mut proof: EnumFieldLoadProof,
    effect: &Effect,
    exposed: bool,
) -> EnumFieldLoadProof {
    match &effect.mutation {
        Mutation::Assert(target, asserted) if target == object => {
            return if *asserted == variant {
                EnumFieldLoadProof::PROVEN
            } else {
                EnumFieldLoadProof::default()
            };
        }
        Mutation::Write {
            target,
            tag,
            complete,
        } => match target.relation(object) {
            Relation::Equal => {
                if *tag != Some(variant) {
                    return EnumFieldLoadProof::default();
                }
                proof.active_variant = true;
                proof.field_initialized |= complete;
                return proof;
            }
            Relation::Within => {
                match target.relation(payload) {
                    Relation::Disjoint => {}
                    Relation::Equal | Relation::Contains => proof.field_initialized = *complete,
                    Relation::Within => proof.field_initialized &= complete,
                    Relation::MayOverlap => proof.field_initialized = false,
                }
                return proof;
            }
            Relation::Disjoint => return proof,
            Relation::Contains | Relation::MayOverlap => return EnumFieldLoadProof::default(),
        },
        _ => {}
    }
    if effect.invalidates_tag(object, exposed) {
        EnumFieldLoadProof::default()
    } else {
        proof
    }
}

// The two finite monotone domains share scheduling and boundary semantics;
// their initial element and join deliberately differ (may versus must).
fn solve<T: Copy + Eq>(
    verifier: &FunctionVerifier<'_>,
    initial: T,
    boundary: T,
    join: impl Fn(T, T) -> T,
    edge: impl Fn(BlockId, BlockId, T) -> T,
    transfer: impl Fn(InstId, T) -> T,
) -> FxHashMap<BlockId, T> {
    let cfg = &verifier.analysis_cfg;
    let mut exits: FxHashMap<_, _> = cfg.blocks.iter().map(|&b| (b, initial)).collect();
    let mut entries = FxHashMap::default();
    let mut pending: VecDeque<_> = cfg.blocks.iter().copied().collect();
    let mut queued: FxHashSet<_> = cfg.blocks.iter().copied().collect();
    while let Some(block) = pending.pop_front() {
        queued.remove(&block);
        // Virtual entries also have real backedges: include them for may facts.
        let incoming = cfg
            .preds
            .get(&block)
            .into_iter()
            .flatten()
            .filter_map(|&p| exits.get(&p).map(|&x| edge(p, block, x)));
        let entry = incoming
            .chain(cfg.entries.contains(&block).then_some(boundary))
            .reduce(&join)
            .unwrap_or(boundary);
        entries.insert(block, entry);
        let exit = verifier
            .block_to_insts
            .get(&block)
            .into_iter()
            .flatten()
            .fold(entry, |x, &id| transfer(id, x));
        if exits.insert(block, exit) != Some(exit) {
            for &succ in cfg.succs.get(&block).into_iter().flatten() {
                if exits.contains_key(&succ) && queued.insert(succ) {
                    pending.push_back(succ);
                }
            }
        }
    }
    entries
}

fn observation_reaches(
    verifier: &FunctionVerifier<'_>,
    effects: &FxHashMap<InstId, Effect>,
    exposed: &FxHashSet<InstId>,
    object: &Place,
    observation: InstId,
    branch: BlockId,
) -> bool {
    let cfg = &verifier.analysis_cfg;
    let mut pending = vec![branch];
    let mut seen = FxHashSet::default();
    while let Some(block) = pending.pop() {
        if !seen.insert(block) {
            continue;
        }
        let Some(insts) = verifier.block_to_insts.get(&block) else {
            return false;
        };
        let mut found = false;
        for &inst in insts.iter().rev() {
            if inst == observation {
                found = true;
                break;
            }
            if effects[&inst].invalidates_tag(object, exposed.contains(&inst)) {
                return false;
            }
        }
        if found {
            continue;
        }
        if cfg.entries.contains(&block) {
            return false;
        }
        let Some(preds) = cfg.preds.get(&block).filter(|p| !p.is_empty()) else {
            return false;
        };
        pending.extend(preds);
    }
    true
}

fn br_table_edge_variant(
    verifier: &FunctionVerifier<'_>,
    br_table: &control_flow::BrTable,
    succ: BlockId,
) -> Option<(ValueId, EnumVariantRef)> {
    let enum_get_tag = enum_get_tag_of_value(verifier, *br_table.scrutinee())?;
    let object = *enum_get_tag.object();
    let Type::EnumTag(enum_ty) = verifier.value_ty(*br_table.scrutinee())? else {
        return None;
    };
    let variant_count = verifier.ctx.with_ty_store(|store| {
        let CompoundType::Enum(enum_data) = store.get_compound(enum_ty)? else {
            return None;
        };
        Some(enum_data.variants.len())
    })?;
    let cases: Vec<_> = br_table
        .table()
        .iter()
        .map(|&(value, dest)| Some((enum_variant_for_tag_value(verifier, enum_ty, value)?, dest)))
        .collect::<Option<_>>()?;

    // A destination can be reached by several explicit cases and by the
    // default. Prove a variant only when all tags reaching it agree, including
    // the complement of the explicit cases when the default reaches it.
    let mut proved_variant = None;
    for idx in 0..variant_count {
        let variant = EnumVariantRef::new(enum_ty, u32::try_from(idx).ok()?);
        let mut explicit = false;
        let mut reaches = false;
        for &(case, dest) in &cases {
            if case == variant {
                explicit = true;
                reaches |= dest == succ;
            }
        }
        reaches |= !explicit && *br_table.default() == Some(succ);
        if reaches {
            if proved_variant.is_some() {
                return None;
            }
            proved_variant = Some(variant);
        }
    }
    Some((object, proved_variant?))
}

fn enum_variant_for_tag_value(
    verifier: &FunctionVerifier<'_>,
    enum_ty: CompoundTypeRef,
    value: ValueId,
) -> Option<EnumVariantRef> {
    let idx = verifier.value_imm(value)?.to_nonnegative_usize()?;
    let variant_count = verifier.ctx.with_ty_store(|store| {
        let CompoundType::Enum(enum_data) = store.get_compound(enum_ty)? else {
            return None;
        };
        Some(enum_data.variants.len())
    })?;
    (idx < variant_count).then_some(EnumVariantRef::new(
        enum_ty,
        u32::try_from(idx).expect("enum variant index overflow"),
    ))
}

fn enum_get_tag_of_value(
    verifier: &FunctionVerifier<'_>,
    value: ValueId,
) -> Option<data::EnumGetTag> {
    verifier.value_ty(value)?;
    let inst = verifier.func.dfg.value_inst(value)?;
    downcast::<&data::EnumGetTag>(verifier.ctx.inst_set, verifier.func.dfg.get_inst(inst)?).cloned()
}
