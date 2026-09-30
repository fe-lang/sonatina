//! Sparse definedness of typed values and object subtrees. This is stronger than
//! verifier readability: a trusted payload assumption cannot define scalar undef.

use rpds::RedBlackTreeMapSync;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    Function, Type, Value, ValueId,
    effects::AccessKind,
    inst::{control_flow, data, downcast},
    module::ModuleCtx,
    types::{CompoundType, EnumVariantRef},
};

use crate::analysis::definedness::value_may_be_undef;

use super::{
    object_tracking::root_leaf_count_for_ty,
    shape::{self, AggregateLayoutCache, AggregateSlice},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct InitializedValue {
    ty: Type,
    default_defined: bool,
    variant: Option<EnumVariantRef>,
    // Snapshots share unchanged entries; a write copies only its map path.
    // Empty scalar leaves need no allocation.
    children: RedBlackTreeMapSync<u32, Self>,
}

impl InitializedValue {
    pub(crate) fn new(ty: Type, defined: bool) -> Self {
        Self {
            ty,
            default_defined: defined,
            variant: None,
            children: RedBlackTreeMapSync::new_sync(),
        }
    }

    fn child(&self, ctx: &ModuleCtx, index: u32) -> Option<Self> {
        let ty = shape::aggregate_child_ty(ctx, self.ty, index)?;
        Some(
            self.children
                .get(&index)
                .cloned()
                .unwrap_or_else(|| Self::new(ty, self.default_defined)),
        )
    }

    pub(crate) fn defined(&self, ctx: &ModuleCtx) -> bool {
        if let Some(CompoundType::Enum(data)) = self.ty.resolve_compound(ctx) {
            if !self.child(ctx, 0).is_some_and(|tag| tag.defined(ctx)) {
                return false;
            }
            let Some(variant) = self.variant else {
                return self.default_defined
                    && self.children.values().all(|child| child.defined(ctx));
            };
            return data.variants[variant.index() as usize]
                .fields
                .iter()
                .enumerate()
                .all(|(index, _)| {
                    let Some(slice) =
                        shape::enum_variant_field_slice(ctx, self.ty, variant, index as u32)
                    else {
                        return false;
                    };
                    self.at(ctx, slice, &mut AggregateLayoutCache::default())
                        .defined(ctx)
                });
        }
        match shape::aggregate_child_count(ctx, self.ty) {
            Some(count) => {
                (self.default_defined || self.children.size() == count)
                    && self.children.values().all(|child| child.defined(ctx))
            }
            None => self.default_defined,
        }
    }

    pub(crate) fn at(
        &self,
        ctx: &ModuleCtx,
        slice: AggregateSlice,
        cache: &mut AggregateLayoutCache,
    ) -> Self {
        if self.ty == slice.ty
            && slice.first_leaf == 0
            && root_leaf_count_for_ty(cache, ctx, self.ty) == slice.leaf_count
        {
            return self.clone();
        }
        let Some((index, child_slice)) = cache.child_containing_slice(ctx, self.ty, slice) else {
            return Self::new(slice.ty, false);
        };
        if let Some(shape::EnumSlotInfo::VariantField { variant, .. }) =
            shape::enum_slot_info(ctx, self.ty, index)
            && self.variant != Some(variant)
        {
            return Self::new(slice.ty, false);
        }
        self.child(ctx, index).map_or_else(
            || Self::new(slice.ty, false),
            |child| {
                child.at(
                    ctx,
                    AggregateSlice {
                        first_leaf: slice.first_leaf - child_slice.first_leaf,
                        ..slice
                    },
                    cache,
                )
            },
        )
    }

    pub(crate) fn put(
        &mut self,
        ctx: &ModuleCtx,
        slice: AggregateSlice,
        value: Self,
        cache: &mut AggregateLayoutCache,
    ) {
        if self.ty == slice.ty
            && slice.first_leaf == 0
            && root_leaf_count_for_ty(cache, ctx, self.ty) == slice.leaf_count
        {
            *self = value;
            return;
        }
        let Some((index, child_slice)) = cache.child_containing_slice(ctx, self.ty, slice) else {
            *self = Self::new(self.ty, false);
            return;
        };
        if let Some(mut child) = self.child(ctx, index) {
            child.put(
                ctx,
                AggregateSlice {
                    first_leaf: slice.first_leaf - child_slice.first_leaf,
                    ..slice
                },
                value,
                cache,
            );
            self.children.insert_mut(index, child);
        }
    }

    pub(crate) fn forget(
        &mut self,
        ctx: &ModuleCtx,
        slice: AggregateSlice,
        cache: &mut AggregateLayoutCache,
    ) {
        if slice.first_leaf == 0 && root_leaf_count_for_ty(cache, ctx, self.ty) == slice.leaf_count
        {
            *self = Self::new(self.ty, false);
            return;
        }
        let Some((index, child_slice)) = cache.child_containing_slice(ctx, self.ty, slice) else {
            *self = Self::new(self.ty, false);
            return;
        };
        if index == 0 && matches!(self.ty.resolve_compound(ctx), Some(CompoundType::Enum(_))) {
            self.variant = None;
        }
        if let Some(mut child) = self.child(ctx, index) {
            child.forget(
                ctx,
                AggregateSlice {
                    first_leaf: slice.first_leaf - child_slice.first_leaf,
                    ..slice
                },
                cache,
            );
            self.children.insert_mut(index, child);
        }
    }

    pub(crate) fn variant(&self) -> Option<EnumVariantRef> {
        self.variant
    }

    pub(crate) fn assume_variant(&mut self, variant: EnumVariantRef) {
        // A trusted readability assumption supplies no scalar-definedness proof.
        self.variant = Some(variant);
    }

    pub(crate) fn select(&mut self, ctx: &ModuleCtx, variant: EnumVariantRef) {
        self.variant = Some(variant);
        if let Some(ty) = shape::enum_tag_ty(self.ty) {
            self.children.insert_mut(0, Self::new(ty, true));
        }
        debug_assert!(matches!(
            self.ty.resolve_compound(ctx),
            Some(CompoundType::Enum(_))
        ));
    }

    pub(crate) fn join(&self, ctx: &ModuleCtx, other: &Self) -> Self {
        debug_assert_eq!(self.ty, other.ty);
        if self.defined(ctx) && other.defined(ctx) && self.variant != other.variant {
            return Self::new(self.ty, true);
        }
        let mut result = Self::new(self.ty, self.default_defined && other.default_defined);
        result.variant = self
            .variant
            .filter(|variant| Some(*variant) == other.variant);
        for &index in self.children.keys().chain(other.children.keys()) {
            if let Some(a) = self.child(ctx, index)
                && let Some(b) = other.child(ctx, index)
            {
                result.children.insert_mut(index, a.join(ctx, &b));
            }
        }
        result
    }
}

pub(crate) fn value_initialization(
    func: &Function,
    value: ValueId,
    snapshots: &FxHashMap<ValueId, InitializedValue>,
    cache: &mut AggregateLayoutCache,
) -> InitializedValue {
    let mut analysis = ValueInitialization {
        func,
        snapshots,
        layout: cache,
        values: FxHashMap::default(),
        visiting: FxHashSet::default(),
        remaining: 256,
    };
    analysis.value(value)
}

struct ValueInitialization<'a> {
    func: &'a Function,
    snapshots: &'a FxHashMap<ValueId, InitializedValue>,
    layout: &'a mut AggregateLayoutCache,
    values: FxHashMap<ValueId, InitializedValue>,
    visiting: FxHashSet<ValueId>,
    remaining: usize,
}

impl ValueInitialization<'_> {
    fn value(&mut self, value: ValueId) -> InitializedValue {
        if let Some(facts) = self
            .snapshots
            .get(&value)
            .or_else(|| self.values.get(&value))
        {
            return facts.clone();
        }
        let ty = self.func.dfg.value_ty(value);
        if self.remaining == 0 || !self.visiting.insert(value) {
            let unknown = InitializedValue::new(ty, false);
            self.values.insert(value, unknown.clone());
            return unknown;
        }
        self.remaining -= 1;
        let result = self.compute(value);
        self.visiting.remove(&value);
        self.values.insert(value, result.clone());
        result
    }

    fn compute(&mut self, value: ValueId) -> InitializedValue {
        let func = self.func;
        let ty = func.dfg.value_ty(value);
        let Some(inst) = func.dfg.value_inst(value) else {
            return InitializedValue::new(
                ty,
                !matches!(func.dfg.value(value), Value::Undef { .. }),
            );
        };
        let data = func.dfg.inst(inst);
        let is = func.inst_set();
        if let Some(insert) = downcast::<&data::InsertValue>(is, data) {
            let mut base = self.value(*insert.dest());
            if let Some(index) = shape::const_u32(&func.dfg, *insert.idx()) {
                let field = self.value(*insert.value());
                base.children.insert_mut(index, field);
                return base;
            }
        } else if let Some(extract) = downcast::<&data::ExtractValue>(is, data) {
            let base = self.value(*extract.dest());
            if let Some(index) = shape::const_u32(&func.dfg, *extract.idx())
                && let Some(child) = base.child(func.ctx(), index)
            {
                return child;
            }
        } else if let Some(make) = downcast::<&data::EnumMake>(is, data) {
            let mut result = InitializedValue::new(ty, false);
            result.select(func.ctx(), *make.variant());
            for (index, &field) in make.values().iter().enumerate() {
                if let Some(slice) =
                    shape::enum_variant_field_slice(func.ctx(), ty, *make.variant(), index as u32)
                {
                    let field = self.value(field);
                    result.put(func.ctx(), slice, field, self.layout);
                }
            }
            return result;
        } else if let Some(extract) = downcast::<&data::EnumExtract>(is, data) {
            let base = self.value(*extract.value());
            if let Some(index) = shape::const_u32(&func.dfg, *extract.field())
                && let Some(slice) =
                    shape::enum_variant_field_slice(func.ctx(), base.ty, *extract.variant(), index)
            {
                return base.at(func.ctx(), slice, self.layout);
            }
        } else if let Some(tag) = downcast::<&data::EnumTag>(is, data) {
            return self
                .value(*tag.value())
                .child(func.ctx(), 0)
                .unwrap_or_else(|| InitializedValue::new(ty, false));
        } else if let Some(phi) = downcast::<&control_flow::Phi>(is, data) {
            return phi
                .args()
                .iter()
                .map(|&(value, _)| self.value(value))
                .reduce(|a, b| a.join(func.ctx(), &b))
                .unwrap_or_else(|| InitializedValue::new(ty, false));
        } else if downcast::<&control_flow::Call>(is, data).is_none()
            && downcast::<&data::ObjLoad>(is, data).is_none()
            && downcast::<&data::EnumGetTag>(is, data).is_none()
            && !func
                .dfg
                .effects(inst)
                .accesses
                .iter()
                .any(|access| access.kind == AccessKind::Read)
        {
            // Both raw and high-level object reads were excluded above. Only
            // a point-specific snapshot can establish a memory read's definedness.
            for used in data.collect_values() {
                self.value(used);
            }
            let defined = !value_may_be_undef(func, value, &mut FxHashMap::default(), |used| {
                self.snapshots
                    .get(&used)
                    .or_else(|| self.values.get(&used))
                    .map(|facts| !facts.defined(func.ctx()))
            });
            return InitializedValue::new(ty, defined);
        }
        InitializedValue::new(ty, false)
    }
}

#[cfg(test)]
mod tests {
    use std::ptr;

    use super::*;
    use sonatina_parser::parse_module;
    use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

    #[test]
    fn snapshots_share_subtrees_and_isolate_partial_writes() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"
type @Pair = { i256, i256 };
type @Nested = { @Pair, @Pair };
func private %f(v0.@Nested) {
block0:
    return;
}
"#,
        )
        .unwrap();
        let ctx = &parsed.module.ctx;
        let ty = ctx.func_sig(parsed.module.funcs()[0], |sig| sig.args()[0]);
        let mut layout = AggregateLayoutCache::default();
        let mut value = InitializedValue::new(ty, false);
        for path in [[0, 0], [0, 1], [1, 0], [1, 1]] {
            let slice = shape::aggregate_slice_for_path(ctx, ty, &path).unwrap();
            value.put(
                ctx,
                slice,
                InitializedValue::new(slice.ty, true),
                &mut layout,
            );
        }
        assert!(value.defined(ctx));
        let retained = value.clone();
        assert!(value.children.ptr_eq(&retained.children));
        let left = shape::aggregate_slice_for_path(ctx, ty, &[0]).unwrap();
        let projected = value.at(ctx, left, &mut layout);
        assert!(projected.children.ptr_eq(&value.children[&0].children));

        let first = shape::aggregate_slice_for_path(ctx, ty, &[0, 0]).unwrap();
        value.put(
            ctx,
            first,
            InitializedValue::new(first.ty, false),
            &mut layout,
        );
        assert!(!value.defined(ctx));
        assert!(retained.defined(ctx));
        assert!(projected.defined(ctx));
        assert!(ptr::eq(&value.children[&1], &retained.children[&1]));
        assert!(
            value.children[&1]
                .children
                .ptr_eq(&retained.children[&1].children)
        );
        assert!(
            !value.children[&0]
                .children
                .ptr_eq(&retained.children[&0].children)
        );
        let right = shape::aggregate_slice_for_path(ctx, ty, &[1]).unwrap();
        let before_forget = value.clone();
        value.forget(ctx, right, &mut layout);
        assert!(!value.at(ctx, right, &mut layout).defined(ctx));
        assert!(before_forget.at(ctx, right, &mut layout).defined(ctx));
        assert!(retained.defined(ctx));
        assert!(!retained.join(ctx, &value).defined(ctx));
    }

    #[test]
    fn shared_enum_snapshots_preserve_tag_and_payload_definedness() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"
type @E = enum { #None, #Some(i256) };
func private %f(v0.@E) {
block0:
    return;
}
"#,
        )
        .unwrap();
        let ctx = &parsed.module.ctx;
        let ty = ctx.func_sig(parsed.module.funcs()[0], |sig| sig.args()[0]);
        let Type::Compound(enum_ty) = ty else {
            panic!("expected enum");
        };
        let some = EnumVariantRef::new(enum_ty, 1);
        let none = EnumVariantRef::new(enum_ty, 0);
        let payload = shape::enum_variant_field_slice(ctx, ty, some, 0).unwrap();
        let tag = shape::enum_tag_slice(ctx, ty).unwrap();
        let mut layout = AggregateLayoutCache::default();
        let mut value = InitializedValue::new(ty, false);
        value.select(ctx, some);
        assert!(
            !value.defined(ctx),
            "selecting a tag does not define its payload"
        );
        value.put(
            ctx,
            payload,
            InitializedValue::new(payload.ty, true),
            &mut layout,
        );
        assert!(value.defined(ctx));
        let retained = value.clone();
        value.forget(ctx, payload, &mut layout);
        value.assume_variant(some);
        assert!(
            !value.defined(ctx),
            "trusted assumptions cannot define scalar undef"
        );
        assert!(retained.defined(ctx));
        value.select(ctx, none);
        assert!(
            value.defined(ctx),
            "inactive undefined payloads do not count"
        );
        assert_eq!(retained.variant(), Some(some));
        let joined = retained.join(ctx, &value);
        assert!(joined.defined(ctx));
        assert_eq!(joined.variant(), None);
        value.forget(ctx, tag, &mut layout);
        value.assume_variant(none);
        assert!(
            !value.defined(ctx),
            "an assumption cannot define a forgotten tag"
        );
        assert!(retained.defined(ctx));
    }

    #[test]
    fn object_reads_need_point_specific_snapshots() {
        let module = parse_module(
            r#"
target = "evm-ethereum-osaka"
type @E = enum { #Empty, #Value(i256) };
func private %f() {
block0:
    v0.objref<i256> = obj.alloc i256;
    v1.i256 = obj.load v0;
    v2.objref<@E> = obj.alloc @E;
    v3.@E = obj.load v2;
    enum.set_tag v2 #Empty;
    v4.enumtag(@E) = enum.get_tag v2;
    return;
}
"#,
        )
        .unwrap()
        .module;
        let report = verify_module(&module, &VerifierConfig::for_level(VerificationLevel::Full));
        assert!(report.is_ok(), "{report}");
        module.func_store.view(module.funcs()[0], |func| {
            let mut cache = AggregateLayoutCache::default();
            for index in [1, 3, 4] {
                let value = ValueId::from_u32(index);
                assert!(
                    !value_initialization(func, value, &FxHashMap::default(), &mut cache)
                        .defined(func.ctx())
                );
                let snapshots = FxHashMap::from_iter([(
                    value,
                    InitializedValue::new(func.dfg.value_ty(value), true),
                )]);
                assert!(
                    value_initialization(func, value, &snapshots, &mut cache).defined(func.ctx())
                );
            }
        });
    }
}
