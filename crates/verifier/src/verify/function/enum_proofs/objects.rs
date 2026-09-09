//! Typed object places and mutations, independent of optimization assumptions.
use super::super::FunctionVerifier;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    AccessKind, AccessLoc, InstId, Type, ValueId,
    inst::{control_flow, data, downcast},
    types::{CompoundType, EnumVariantRef},
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Step {
    Index(Index),
    Payload(EnumVariantRef, usize),
}
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Index {
    Constant(usize),
    Dynamic(ValueId),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) struct Place {
    root: ValueId,
    path: Vec<Step>,
    local: bool,
}
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Relation {
    Equal,
    Contains,
    Within,
    Disjoint,
    MayOverlap,
}
impl Place {
    pub fn is_local(&self) -> bool {
        self.local
    }
    pub fn payload(&self, variant: EnumVariantRef, index: usize) -> Self {
        let mut place = self.clone();
        place.path.push(Step::Payload(variant, index));
        place
    }
    pub fn relation(&self, other: &Self) -> Relation {
        if self.root != other.root {
            return if self.local && other.local {
                Relation::Disjoint
            } else {
                Relation::MayOverlap
            };
        }
        for (left, right) in self.path.iter().zip(&other.path) {
            if left == right {
                continue;
            }
            return match (left, right) {
                (Step::Index(Index::Constant(a)), Step::Index(Index::Constant(b))) if a != b => {
                    Relation::Disjoint
                }
                (Step::Payload(a, i), Step::Payload(b, j)) if a == b && i != j => {
                    Relation::Disjoint
                }
                _ => Relation::MayOverlap,
            };
        }
        match self.path.len().cmp(&other.path.len()) {
            std::cmp::Ordering::Equal => Relation::Equal,
            std::cmp::Ordering::Less => Relation::Contains,
            std::cmp::Ordering::Greater => Relation::Within,
        }
    }
    pub fn shares_allocation(&self, other: &Self) -> bool {
        self.root == other.root || !(self.local && other.local)
    }
}

#[derive(Clone)]
pub(super) enum Mutation {
    None,
    Allocate(Place),
    Assert(Place, EnumVariantRef),
    Write {
        target: Place,
        tag: Option<EnumVariantRef>,
        complete: bool,
    },
    RawWrite,
    Call,
}
pub(super) struct Effect {
    pub mutation: Mutation,
    pub exposes: Vec<Place>,
}
impl Effect {
    pub fn invalidates_tag(&self, object: &Place, exposed: bool) -> bool {
        match &self.mutation {
            Mutation::Write { target, .. } => matches!(
                target.relation(object),
                Relation::Equal | Relation::Contains | Relation::MayOverlap
            ),
            Mutation::Allocate(target) => target.root == object.root,
            Mutation::RawWrite => exposed,
            Mutation::Call => true,
            Mutation::None | Mutation::Assert(..) => false,
        }
    }
    pub fn exposure_after(&self, object: &Place, exposed: bool) -> bool {
        if let Mutation::Allocate(target) = &self.mutation
            && target.root == object.root
        {
            return false;
        }
        exposed
            || self
                .exposes
                .iter()
                .any(|target| target.shares_allocation(object))
    }
}

pub(super) struct Objects<'a, 'b> {
    verifier: &'a FunctionVerifier<'b>,
    places: FxHashMap<ValueId, Place>,
}
impl<'a, 'b> Objects<'a, 'b> {
    pub fn new(verifier: &'a FunctionVerifier<'b>) -> Self {
        Self {
            verifier,
            places: FxHashMap::default(),
        }
    }
    pub fn place(&mut self, value: ValueId) -> Place {
        if let Some(place) = self.places.get(&value) {
            return place.clone();
        }
        let mut root = value;
        let mut reverse = Vec::new();
        let mut seen = FxHashSet::default();
        let mut local = false;
        while seen.insert(root) && self.verifier.value_ty(root).is_some() {
            let Some(inst) = self
                .verifier
                .func
                .dfg
                .value_inst(root)
                .and_then(|i| self.verifier.func.dfg.get_inst(i))
            else {
                break;
            };
            let is = self.verifier.ctx.inst_set;
            if let Some(assertion) = downcast::<&data::EnumAssertVariantRef>(is, inst) {
                root = *assertion.object();
            } else if let Some(proj) = downcast::<&data::EnumProj>(is, inst) {
                let Some(index) = self
                    .verifier
                    .value_imm(*proj.field())
                    .and_then(|i| i.to_nonnegative_usize())
                else {
                    break;
                };
                reverse.push(Step::Payload(*proj.variant(), index));
                root = *proj.object();
            } else if let Some(proj) = downcast::<&data::ObjProj>(is, inst) {
                let Some((&base, indices)) = proj.values().split_first() else {
                    break;
                };
                reverse.extend(indices.iter().rev().map(|&i| self.index(i)));
                root = base;
            } else if let Some(proj) = downcast::<&data::ObjIndex>(is, inst) {
                reverse.push(self.index(*proj.index()));
                root = *proj.object();
            } else {
                local = downcast::<&data::ObjAlloc>(is, inst).is_some();
                break;
            }
        }
        reverse.reverse();
        let place = Place {
            root,
            path: reverse,
            local,
        };
        self.places.insert(value, place.clone());
        place
    }
    fn index(&self, value: ValueId) -> Step {
        Step::Index(
            self.verifier
                .value_imm(value)
                .and_then(|i| i.to_nonnegative_usize())
                .map_or(Index::Dynamic(value), Index::Constant),
        )
    }
    // Find references carried by SSA aggregates as well as direct objrefs.
    // Unknown loads/arguments remain possible aliases; cycles terminate safely.
    fn references(&mut self, values: &[ValueId]) -> Vec<Place> {
        let mut pending = values.to_vec();
        let mut seen = FxHashSet::default();
        let mut places = Vec::new();
        while let Some(value) = pending.pop() {
            if !seen.insert(value) {
                continue;
            }
            let Some(ty) = self.verifier.value_ty(value) else {
                continue;
            };
            if self.verifier.objref_ty(ty).is_some() {
                places.push(self.place(value));
                continue;
            }
            if !contains_objref(self.verifier, ty) {
                continue;
            }
            let inst = self
                .verifier
                .func
                .dfg
                .value_inst(value)
                .and_then(|i| self.verifier.func.dfg.get_inst(i));
            let is = self.verifier.ctx.inst_set;
            if let Some(insert) = inst.and_then(|i| downcast::<&data::InsertValue>(is, i)) {
                pending.extend([*insert.dest(), *insert.value()]);
            } else if let Some(make) = inst.and_then(|i| downcast::<&data::EnumMake>(is, i)) {
                pending.extend(make.values());
            } else if let Some(phi) = inst.and_then(|i| downcast::<&control_flow::Phi>(is, i)) {
                pending.extend(phi.args().iter().map(|(v, _)| v));
            } else {
                places.push(self.place(value));
            }
        }
        places
    }
    // Raw allocations cannot contain typed objects. Only a bounded write is
    // disjoint: an oversized or unknown-range write may reach another object.
    // Derived/unknown pointers conservatively retain interference.
    fn write_is_separate(&self, addr: ValueId, bytes: usize) -> bool {
        if bytes == 0 {
            return true;
        }
        self.verifier
            .value_ty(addr)
            .and_then(|_| self.verifier.func.dfg.value_inst(addr))
            .and_then(|id| self.verifier.func.dfg.get_inst(id))
            .and_then(|inst| downcast::<&data::Alloca>(self.verifier.ctx.inst_set, inst))
            .and_then(|alloc| self.verifier.type_size(*alloc.ty()))
            .is_some_and(|size| bytes <= size)
    }
    pub fn effect(&mut self, id: InstId) -> Effect {
        let Some(inst) = self.verifier.func.dfg.get_inst(id) else {
            return Effect {
                mutation: Mutation::Call,
                exposes: Vec::new(),
            };
        };
        let is = self.verifier.ctx.inst_set;
        let mut exposes = Vec::new();
        let mutation = if downcast::<&data::ObjAlloc>(is, inst).is_some() {
            self.verifier
                .func
                .dfg
                .inst_results(id)
                .first()
                .copied()
                .map_or(Mutation::None, |v| Mutation::Allocate(self.place(v)))
        } else if let Some(a) = downcast::<&data::EnumAssertVariantRef>(is, inst) {
            Mutation::Assert(self.place(*a.object()), *a.variant())
        } else if let Some(write) = downcast::<&data::EnumWriteVariant>(is, inst) {
            exposes = self.references(write.values());
            Mutation::Write {
                target: self.place(*write.object()),
                tag: Some(*write.variant()),
                complete: true,
            }
        } else if let Some(write) = downcast::<&data::EnumSetTag>(is, inst) {
            let complete = self.verifier.ctx.with_ty_store(|types| {
                let Some(CompoundType::Enum(data)) = types.get_compound(write.variant().enum_ty())
                else {
                    return false;
                };
                data.variants
                    .get(write.variant().index() as usize)
                    .is_some_and(|v| v.fields.is_empty())
            });
            Mutation::Write {
                target: self.place(*write.object()),
                tag: Some(*write.variant()),
                complete,
            }
        } else if let Some(write) = downcast::<&data::ObjStore>(is, inst) {
            exposes = self.references(&[*write.value()]);
            Mutation::Write {
                target: self.place(*write.object()),
                tag: None,
                complete: true,
            }
        } else if let Some(write) = downcast::<&data::ObjInitConst>(is, inst) {
            Mutation::Write {
                target: self.place(*write.object()),
                tag: None,
                complete: true,
            }
        } else if let Some(mat) = downcast::<&data::ObjMaterializeStack>(is, inst) {
            exposes.push(self.place(*mat.object()));
            Mutation::None
        } else if let Some(mat) = downcast::<&data::ObjMaterializeHeap>(is, inst) {
            exposes.push(self.place(*mat.object()));
            Mutation::None
        } else if let Some(call) = downcast::<&control_flow::Call>(is, inst) {
            exposes = self.references(call.args());
            Mutation::Call
        } else if let Some(store) = downcast::<&data::Mstore>(is, inst) {
            // Unlike the effects API, checked layout queries tolerate malformed IR.
            if self
                .verifier
                .type_size(*store.ty())
                .is_some_and(|bytes| self.write_is_separate(*store.addr(), bytes))
            {
                Mutation::None
            } else {
                Mutation::RawWrite
            }
        } else if inst.declared_effect_hint().has_write_effect()
            && self
                .verifier
                .func
                .dfg
                .effects(id)
                .accesses
                .iter()
                .any(|access| {
                    if access.kind != AccessKind::Write
                        || access.space != self.verifier.ctx.address_spaces().default_space()
                    {
                        return false;
                    }
                    let range = match &access.loc {
                        AccessLoc::LinearExact { addr, bytes, .. } => {
                            Some((*addr, *bytes as usize))
                        }
                        AccessLoc::LinearRange { addr, len } => self
                            .verifier
                            .value_imm(*len)
                            .and_then(|len| len.to_nonnegative_usize())
                            .map(|len| (*addr, len)),
                        _ => None,
                    };
                    !range.is_some_and(|(addr, bytes)| self.write_is_separate(addr, bytes))
                })
        {
            Mutation::RawWrite
        } else {
            Mutation::None
        };
        Effect { mutation, exposes }
    }
}

fn contains_objref(verifier: &FunctionVerifier<'_>, ty: Type) -> bool {
    verifier.ctx.with_ty_store(|types| {
        let mut seen = FxHashSet::default();
        let mut pending = vec![ty];
        while let Some(ty) = pending.pop() {
            let Type::Compound(id) = ty else {
                continue;
            };
            if !seen.insert(id) {
                continue;
            }
            match types.get_compound(id) {
                Some(CompoundType::ObjRef(_)) => return true,
                Some(CompoundType::Struct(s)) => pending.extend(&s.fields),
                Some(CompoundType::Enum(e)) => {
                    pending.extend(e.variants.iter().flat_map(|v| &v.fields))
                }
                Some(CompoundType::Array { elem, len }) if *len != 0 => pending.push(*elem),
                _ => {}
            }
        }
        false
    })
}
