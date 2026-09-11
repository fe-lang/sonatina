use sonatina_ir::{
    InstId, Type, ValueId,
    effects::{AccessKind, AccessLoc},
    inst::{control_flow, data, downcast},
    types::CompoundType,
};

use super::{
    FunctionVerifier, Proof,
    objects::{State, ViewFact},
    read,
    value_state::ValueState,
    views::{Index, References, Root, Step},
};
use crate::verify::function::refs::collect_inst_refs;

fn index(verifier: &FunctionVerifier<'_>, value: ValueId) -> Step {
    Step::Index(
        verifier
            .value_imm(value)
            .and_then(|n| n.to_nonnegative_usize())
            .map_or(Index::Symbol(value), Index::Constant),
    )
}

fn project(
    verifier: &FunctionVerifier<'_>,
    state: &mut State,
    result: ValueId,
    object: ValueId,
    steps: impl IntoIterator<Item = Step>,
) {
    let mut refs = state.reference(verifier, object);
    let ty = verifier
        .objref_ty(verifier.func.dfg.value_ty(object))
        .expect("validated object reference");
    let mut value = state.contents(verifier.ctx, &refs, ty);
    let mut guards = state.guards_hold(verifier.ctx, &refs);
    for step in steps {
        if let Step::Payload(variant, _) = step {
            guards &= value.active(variant);
        }
        value = value.child(verifier.ctx, step);
        refs = refs.project(step);
    }
    let fact = ViewFact {
        references: refs.clone(),
        value,
        guards,
    };
    state.bind(
        verifier.ctx,
        result,
        ValueState::reference(verifier.func.dfg.value_ty(result), refs),
        Some(fact),
    );
}

pub(super) fn instruction(verifier: &FunctionVerifier<'_>, state: &mut State, id: InstId) -> Proof {
    let ctx = verifier.ctx;
    let inst = verifier.func.dfg.inst(id);
    let is = ctx.inst_set;
    let results = verifier.func.dfg.inst_results(id);
    let result = results.first().copied();
    let mut proof = Proof::NoLocalEnumObligation;
    if downcast::<&control_flow::Phi>(is, inst).is_some() {
        // Phis were simultaneously substituted on the predecessor edge.
    } else if let Some(alloc) = downcast::<&data::ObjAlloc>(is, inst) {
        let result = result.expect("validated allocation result");
        let refs = state.allocate(ctx, result, *alloc.ty());
        state.bind(
            ctx,
            result,
            ValueState::reference(verifier.func.dfg.value_ty(result), refs),
            None,
        );
    } else if let Some(proj) = downcast::<&data::EnumProj>(is, inst) {
        project(
            verifier,
            state,
            result.unwrap(),
            *proj.object(),
            [Step::Payload(
                proj.variant().index(),
                verifier
                    .value_imm(*proj.field())
                    .unwrap()
                    .to_nonnegative_usize()
                    .unwrap(),
            )],
        );
    } else if let Some(proj) = downcast::<&data::ObjProj>(is, inst) {
        project(
            verifier,
            state,
            result.unwrap(),
            proj.values()[0],
            proj.values()[1..].iter().map(|&v| index(verifier, v)),
        );
    } else if let Some(proj) = downcast::<&data::ObjIndex>(is, inst) {
        project(
            verifier,
            state,
            result.unwrap(),
            *proj.object(),
            [index(verifier, *proj.index())],
        );
    } else if let Some(load) = downcast::<&data::ObjLoad>(is, inst) {
        let result = result.unwrap();
        let ty = verifier.func.dfg.value_ty(result);
        let refs = state.reference(verifier, *load.object());
        proof = read(state, verifier, &refs, ty, false);
        let mut value = state.contents(ctx, &refs, ty);
        if !matches!(
            ty.resolve_compound(ctx),
            Some(CompoundType::Struct(_) | CompoundType::Array { .. } | CompoundType::Enum(_))
        ) {
            // Scalar SSA definedness is outside the enum contract. The load's
            // guarded read was checked above; aggregate copies retain their
            // source subtree facts, including unwritten nested enum payloads.
            value.complete = true;
        }
        state.bind(ctx, result, value, None);
    } else if let Some(tag) = downcast::<&data::EnumGetTag>(is, inst) {
        let result = result.unwrap();
        let ty = verifier
            .objref_ty(verifier.func.dfg.value_ty(*tag.object()))
            .unwrap();
        let refs = state.reference(verifier, *tag.object());
        proof = read(state, verifier, &refs, ty, true);
        state.bind(
            ctx,
            result,
            ValueState::new(verifier.func.dfg.value_ty(result), true),
            None,
        );
        state.observations.insert(result, refs);
    } else if let Some(assertion) = downcast::<&data::EnumAssertVariantRef>(is, inst) {
        let refs = state.reference(verifier, *assertion.object());
        let ty = verifier
            .objref_ty(verifier.func.dfg.value_ty(*assertion.object()))
            .unwrap();
        state.write(ctx, &refs, ty, true, |value| {
            value.assert_variant(ctx, assertion.variant().index())
        });
        state.bind(
            ctx,
            result.unwrap(),
            ValueState::reference(verifier.func.dfg.value_ty(result.unwrap()), refs),
            None,
        );
    } else if let Some(store) = downcast::<&data::ObjStore>(is, inst) {
        let refs = state.reference(verifier, *store.object());
        let value = state.value(verifier, *store.value());
        state.write(ctx, &refs, value.ty, false, |target| {
            *target = value.clone()
        });
    } else if let Some(init) = downcast::<&data::ObjInitConst>(is, inst) {
        let refs = state.reference(verifier, *init.object());
        let ty = verifier
            .objref_ty(verifier.func.dfg.value_ty(*init.object()))
            .unwrap();
        state.write(ctx, &refs, ty, false, |target| {
            *target = ValueState::new(ty, true)
        });
    } else if let Some(tag) = downcast::<&data::EnumSetTag>(is, inst) {
        let refs = state.reference(verifier, *tag.object());
        let ty = verifier
            .objref_ty(verifier.func.dfg.value_ty(*tag.object()))
            .unwrap();
        state.write(ctx, &refs, ty, false, |value| {
            value.set_tag(ctx, tag.variant().index())
        });
    } else if let Some(write) = downcast::<&data::EnumWriteVariant>(is, inst) {
        let refs = state.reference(verifier, *write.object());
        let ty = verifier
            .objref_ty(verifier.func.dfg.value_ty(*write.object()))
            .unwrap();
        let fields: Vec<_> = write
            .values()
            .iter()
            .map(|&v| state.value(verifier, v))
            .collect();
        state.write(ctx, &refs, ty, false, |value| {
            value.refine(write.variant().index());
            for (i, field) in fields.iter().enumerate() {
                value.update(
                    ctx,
                    &[Step::Payload(write.variant().index(), i)],
                    true,
                    &|target| *target = field.clone(),
                );
            }
        });
    } else if let Some(make) = downcast::<&data::EnumMake>(is, inst) {
        let mut value = ValueState::new(*make.ty(), false);
        value.refine(make.variant().index());
        for (i, &field) in make.values().iter().enumerate() {
            value.children.insert(
                Step::Payload(make.variant().index(), i),
                state.value(verifier, field),
            );
        }
        state.bind(ctx, result.unwrap(), value, None);
    } else if let Some(extract) = downcast::<&data::EnumExtract>(is, inst) {
        let value = state.value(verifier, *extract.value());
        let field = value.child(
            ctx,
            Step::Payload(
                extract.variant().index(),
                verifier
                    .value_imm(*extract.field())
                    .unwrap()
                    .to_nonnegative_usize()
                    .unwrap(),
            ),
        );
        proof = if !value.active(extract.variant().index()) {
            Proof::Unproved("enum.extract requires a proven active variant at the use site")
        } else if !field.readable(ctx) {
            Proof::Unproved("enum.extract requires an initialized payload subtree")
        } else {
            Proof::Proven
        };
        state.bind(ctx, result.unwrap(), field, None);
    } else if let Some(tag) = downcast::<&data::EnumTag>(is, inst) {
        let result = result.unwrap();
        state.bind(
            ctx,
            result,
            ValueState::new(verifier.func.dfg.value_ty(result), true),
            None,
        );
        state
            .value_observations
            .insert(result, (*tag.value(), None));
    } else if let Some(test) = downcast::<&data::EnumIsVariant>(is, inst) {
        let result = result.unwrap();
        state.bind(
            ctx,
            result,
            ValueState::new(verifier.func.dfg.value_ty(result), true),
            None,
        );
        state
            .value_observations
            .insert(result, (*test.value(), Some(test.variant().index())));
    } else if let Some(assertion) = downcast::<&data::EnumAssertVariant>(is, inst) {
        let mut value = state.value(verifier, *assertion.value());
        value.assert_variant(ctx, assertion.variant().index());
        state.values.insert(*assertion.value(), value);
    } else if let Some(insert) = downcast::<&data::InsertValue>(is, inst) {
        let mut value = state.value(verifier, *insert.dest());
        let field = state.value(verifier, *insert.value());
        value.update(ctx, &[index(verifier, *insert.idx())], true, &|target| {
            *target = field.clone()
        });
        state.bind(ctx, result.unwrap(), value, None);
    } else if let Some(extract) = downcast::<&data::ExtractValue>(is, inst) {
        let value = state
            .value(verifier, *extract.dest())
            .child(ctx, index(verifier, *extract.idx()));
        state.bind(ctx, result.unwrap(), value, None);
    } else if let Some(mat) = downcast::<&data::ObjMaterializeStack>(is, inst) {
        state.expose(ctx, &state.reference(verifier, *mat.object()));
        state.bind(
            ctx,
            result.unwrap(),
            ValueState::new(verifier.func.dfg.value_ty(result.unwrap()), true),
            None,
        );
    } else if let Some(mat) = downcast::<&data::ObjMaterializeHeap>(is, inst) {
        state.expose(ctx, &state.reference(verifier, *mat.object()));
        state.bind(
            ctx,
            result.unwrap(),
            ValueState::new(verifier.func.dfg.value_ty(result.unwrap()), true),
            None,
        );
    } else {
        let call = downcast::<&control_flow::Call>(is, inst).is_some();
        let publish = call
            || downcast::<&control_flow::Return>(is, inst).is_some()
            || inst.declared_effect_hint().has_write_effect();
        if publish {
            for value in collect_inst_refs(inst).values {
                state.expose(ctx, &state.value(verifier, value).captured(ctx));
            }
        }
        let unknown_call_input = call
            && (collect_inst_refs(inst)
                .values
                .iter()
                .any(|&value| state.value(verifier, value).captured(ctx).unknown)
                || state.exposed.iter().any(|root| {
                    state
                        .objects
                        .get(root)
                        .is_some_and(|value| value.captured(ctx).unknown)
                }));
        if call {
            // A call can replace reference cells as well as return references.
            // Their contents are interface imports with retained possible local
            // aliases/guards, not unsupported local producers. Save candidates
            // before invalidating their mutable pointees.
            let objects: Vec<_> = state
                .objects
                .iter()
                .map(|(&root, value)| {
                    (
                        root,
                        opaque(
                            verifier,
                            state,
                            Root::External,
                            value.ty,
                            true,
                            unknown_call_input,
                        ),
                    )
                })
                .collect();
            let views: Vec<_> = state
                .views
                .iter()
                .map(|(&id, fact)| {
                    (
                        id,
                        opaque(
                            verifier,
                            state,
                            Root::External,
                            fact.value.ty,
                            true,
                            unknown_call_input,
                        ),
                    )
                })
                .collect();
            state.havoc(ctx, false);
            for (root, value) in objects {
                state
                    .objects
                    .get_mut(&root)
                    .unwrap()
                    .copy_references(ctx, &value);
            }
            for (id, value) in views {
                state
                    .views
                    .get_mut(&id)
                    .unwrap()
                    .value
                    .copy_references(ctx, &value);
            }
            state.close_exposure(ctx);
        } else if raw_write(verifier, id) {
            state.havoc(ctx, true);
        }
        for &result in results {
            let ty = verifier.func.dfg.value_ty(result);
            // Scalar operations and constant addressing cannot carry objrefs.
            // All other producers use a conservative typed opaque shape. A call
            // is an interface import, but can return a locally guarded alias.
            let value = opaque(
                verifier,
                state,
                Root::Opaque(result),
                ty,
                call,
                unknown_call_input,
            );
            state.bind(ctx, result, value, None);
        }
    }
    proof
}

fn opaque(
    verifier: &FunctionVerifier<'_>,
    state: &State,
    root: Root,
    ty: Type,
    imported: bool,
    unresolved: bool,
) -> ValueState {
    let ctx = verifier.ctx;
    let mut value = ValueState::new(
        ty,
        imported || !matches!(ty.resolve_compound(ctx), Some(CompoundType::Enum(_))),
    );
    match ty.resolve_compound(ctx) {
        Some(CompoundType::ObjRef(_)) => {
            let mut refs = References::root(root);
            refs.unknown = !imported || unresolved;
            for source in state.values.values().chain(state.objects.values()) {
                refs.views.extend(source.references_of_type(ctx, ty).views);
            }
            value.references = refs;
        }
        Some(CompoundType::Struct(record)) => {
            for (i, &ty) in record.fields.iter().enumerate() {
                value.children.insert(
                    Step::Index(Index::Constant(i)),
                    opaque(verifier, state, root, ty, imported, unresolved),
                );
            }
        }
        Some(CompoundType::Array { elem, len }) if len != 0 => {
            value.children.insert(
                Step::Index(Index::Unknown),
                opaque(verifier, state, root, elem, imported, unresolved),
            );
        }
        Some(CompoundType::Enum(enumeration)) => {
            for (v, variant) in enumeration.variants.iter().enumerate() {
                for (i, &ty) in variant.fields.iter().enumerate() {
                    value.children.insert(
                        Step::Payload(v as u32, i),
                        opaque(verifier, state, root, ty, imported, unresolved),
                    );
                }
            }
        }
        _ => {}
    }
    value
}

fn raw_write(verifier: &FunctionVerifier<'_>, id: InstId) -> bool {
    let separate = |addr, bytes| {
        bytes == 0
            || verifier
                .func
                .dfg
                .value_inst(addr)
                .and_then(|id| {
                    downcast::<&data::Alloca>(verifier.ctx.inst_set, verifier.func.dfg.inst(id))
                })
                .and_then(|alloc| verifier.type_size(*alloc.ty()))
                .is_some_and(|size| bytes <= size)
    };
    let inst = verifier.func.dfg.inst(id);
    if let Some(store) = downcast::<&data::Mstore>(verifier.ctx.inst_set, inst) {
        return !verifier
            .type_size(*store.ty())
            .is_some_and(|bytes| separate(*store.addr(), bytes));
    }
    inst.declared_effect_hint().has_write_effect()
        && verifier.func.dfg.effects(id).accesses.iter().any(|access| {
            if access.kind != AccessKind::Write
                || access.space != verifier.ctx.address_spaces().default_space()
            {
                return false;
            }
            let range = match &access.loc {
                AccessLoc::LinearExact { addr, bytes, .. } => Some((*addr, *bytes as usize)),
                AccessLoc::LinearRange { addr, len } => verifier
                    .value_imm(*len)
                    .and_then(|len| len.to_nonnegative_usize())
                    .map(|len| (*addr, len)),
                _ => None,
            };
            !range.is_some_and(|(addr, bytes)| separate(addr, bytes))
        })
}
