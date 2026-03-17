use std::hash::{Hash, Hasher};

use rustc_hash::{FxHashSet, FxHasher};
use sonatina_ir::{
    AccessLoc, AddressSpaceId, Function, GlobalVariableRef, I256, Immediate, InstDowncast, InstId,
    Type, Value, ValueId,
    inst::{
        arith::{Add, Sub},
        cast::{Bitcast, IntToPtr, PtrToInt},
        control_flow::Phi,
        data::{Alloca, Gep},
        equiv::{InstClassKind, InstKeyExt},
        evm::EvmMalloc,
    },
    types::CompoundType,
};

use crate::{isa::evm::STATIC_BASE, optim::aggregate::shape};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ValueKey {
    Imm(Immediate),
    Value(ValueId),
    Expr(Box<KeyExpr>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum KeyExpr {
    Unary {
        opcode: &'static str,
        result_idx: u16,
        ty: Type,
        arg: ValueKey,
    },
    Binary {
        opcode: &'static str,
        result_idx: u16,
        ty: Type,
        lhs: ValueKey,
        rhs: ValueKey,
    },
    Cast {
        opcode: &'static str,
        result_idx: u16,
        ty: Type,
        arg: ValueKey,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BaseObject {
    Alloca(InstId),
    Malloc(InstId),
    Global(GlobalVariableRef),
    Arg(ValueId),
    Absolute(Immediate),
    Unknown(ValueId),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LinearLocKey {
    pub space: AddressSpaceId,
    pub base: BaseObject,
    pub offset: i64,
    pub bytes: u32,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LinearRangeKey {
    pub space: AddressSpaceId,
    pub base: BaseObject,
    pub offset: i64,
    pub bytes: i64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RangeCoverage {
    NoOverlap,
    FullyCovered,
    PartiallyCovered {
        before: Option<LinearRangeKey>,
        after: Option<LinearRangeKey>,
    },
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct KeyedLocKey {
    pub space: AddressSpaceId,
    pub key: ValueKey,
    pub bytes: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TrackedLocKey {
    Linear(LinearLocKey),
    Keyed(KeyedLocKey),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AliasResult {
    NoAlias,
    MayAlias,
    MustAlias,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct CanonicalAddr {
    base: BaseObject,
    offset: i64,
}

pub struct MemoryAccessAnalysis;

impl MemoryAccessAnalysis {
    pub fn new() -> Self {
        Self
    }

    pub fn trackable_exact_loc(
        &self,
        func: &Function,
        access: &sonatina_ir::MemoryAccess,
    ) -> Option<TrackedLocKey> {
        match &access.loc {
            AccessLoc::LinearExact { addr, bytes, ty } => {
                let addr = self.canonical_linear_addr(func, *addr);
                if matches!(addr.base, BaseObject::Unknown(_)) {
                    return None;
                }
                Some(TrackedLocKey::Linear(LinearLocKey {
                    space: access.space,
                    base: addr.base,
                    offset: addr.offset,
                    bytes: *bytes,
                    ty: *ty,
                }))
            }
            AccessLoc::LinearExactImm { addr, bytes, ty } => {
                Some(TrackedLocKey::Linear(LinearLocKey {
                    space: access.space,
                    base: BaseObject::Absolute(*addr),
                    offset: 0,
                    bytes: *bytes,
                    ty: *ty,
                }))
            }
            AccessLoc::KeyedExact { key, bytes } => Some(TrackedLocKey::Keyed(KeyedLocKey {
                space: access.space,
                key: self.trackable_value_key(func, *key)?,
                bytes: *bytes,
            })),
            AccessLoc::LinearRange { .. } | AccessLoc::WholeSpace | AccessLoc::Unknown => None,
        }
    }

    pub fn trackable_linear_range(
        &self,
        func: &Function,
        access: &sonatina_ir::MemoryAccess,
    ) -> Option<LinearRangeKey> {
        let AccessLoc::LinearRange { addr, len } = &access.loc else {
            return None;
        };

        let addr = self.canonical_linear_addr(func, *addr);
        if matches!(addr.base, BaseObject::Unknown(_)) {
            return None;
        }

        let bytes = self.value_const_i64(func, *len)?;
        if bytes < 0 {
            return None;
        }

        Some(LinearRangeKey {
            space: access.space,
            base: addr.base,
            offset: addr.offset,
            bytes,
        })
    }

    pub fn alias(&self, lhs: &TrackedLocKey, rhs: &TrackedLocKey) -> AliasResult {
        match (lhs, rhs) {
            (TrackedLocKey::Linear(lhs), TrackedLocKey::Linear(rhs)) => self.alias_linear(lhs, rhs),
            (TrackedLocKey::Keyed(lhs), TrackedLocKey::Keyed(rhs)) => self.alias_keyed(lhs, rhs),
            (TrackedLocKey::Linear(_), TrackedLocKey::Keyed(_))
            | (TrackedLocKey::Keyed(_), TrackedLocKey::Linear(_)) => AliasResult::NoAlias,
        }
    }

    pub fn range_may_alias_key(&self, range: &LinearRangeKey, key: &TrackedLocKey) -> bool {
        match key {
            TrackedLocKey::Linear(key) => self.range_may_alias_linear(range, key),
            TrackedLocKey::Keyed(_) => false,
        }
    }

    pub fn access_may_alias_key(
        &self,
        func: &Function,
        access: &sonatina_ir::MemoryAccess,
        key: &TrackedLocKey,
    ) -> bool {
        if access.space
            != match key {
                TrackedLocKey::Linear(key) => key.space,
                TrackedLocKey::Keyed(key) => key.space,
            }
        {
            return false;
        }

        match (key, &access.loc) {
            (_, AccessLoc::WholeSpace | AccessLoc::Unknown) => true,
            (TrackedLocKey::Linear(_), AccessLoc::LinearRange { .. }) => self
                .trackable_linear_range(func, access)
                .is_none_or(|range| self.range_may_alias_key(&range, key)),
            (TrackedLocKey::Keyed(_), AccessLoc::LinearRange { .. }) => false,
            (TrackedLocKey::Linear(_), AccessLoc::KeyedExact { .. })
            | (
                TrackedLocKey::Keyed(_),
                AccessLoc::LinearExact { .. } | AccessLoc::LinearExactImm { .. },
            ) => false,
            (
                _,
                AccessLoc::LinearExact { .. }
                | AccessLoc::LinearExactImm { .. }
                | AccessLoc::KeyedExact { .. },
            ) => self
                .trackable_exact_loc(func, access)
                .is_none_or(|other| self.alias(key, &other) != AliasResult::NoAlias),
        }
    }

    fn alias_linear(&self, lhs: &LinearLocKey, rhs: &LinearLocKey) -> AliasResult {
        if lhs.space != rhs.space {
            return AliasResult::NoAlias;
        }

        if let Some(alias) = absolute_linear_alias(lhs, rhs) {
            return alias;
        }

        if reserved_evm_meta_interval(&lhs.base, lhs.offset, i64::from(lhs.bytes))
            .is_some_and(|_| is_allocator_managed_base(&rhs.base))
            || reserved_evm_meta_interval(&rhs.base, rhs.offset, i64::from(rhs.bytes))
                .is_some_and(|_| is_allocator_managed_base(&lhs.base))
        {
            return AliasResult::NoAlias;
        }

        match self.alias_linear_bases(&lhs.base, &rhs.base) {
            AliasResult::MustAlias => self.alias_same_base_linear(lhs, rhs),
            alias => alias,
        }
    }

    fn alias_same_base_linear(&self, lhs: &LinearLocKey, rhs: &LinearLocKey) -> AliasResult {
        let Some(lhs_end) = lhs.offset.checked_add(i64::from(lhs.bytes)) else {
            return AliasResult::MayAlias;
        };
        let Some(rhs_end) = rhs.offset.checked_add(i64::from(rhs.bytes)) else {
            return AliasResult::MayAlias;
        };

        if lhs_end <= rhs.offset || rhs_end <= lhs.offset {
            return AliasResult::NoAlias;
        }

        if lhs.base == rhs.base && lhs.offset == rhs.offset && lhs.bytes == rhs.bytes {
            return AliasResult::MustAlias;
        }

        AliasResult::MayAlias
    }

    fn alias_keyed(&self, lhs: &KeyedLocKey, rhs: &KeyedLocKey) -> AliasResult {
        if lhs.space != rhs.space {
            return AliasResult::NoAlias;
        }

        if lhs.key == rhs.key && lhs.bytes == rhs.bytes {
            return AliasResult::MustAlias;
        }

        match (&lhs.key, &rhs.key) {
            (ValueKey::Imm(lhs), ValueKey::Imm(rhs)) if lhs != rhs => AliasResult::NoAlias,
            _ => AliasResult::MayAlias,
        }
    }

    fn range_may_alias_linear(&self, range: &LinearRangeKey, key: &LinearLocKey) -> bool {
        !matches!(
            self.exact_write_coverage(range, key),
            RangeCoverage::NoOverlap
        )
    }

    pub fn exact_write_coverage(
        &self,
        range: &LinearRangeKey,
        key: &LinearLocKey,
    ) -> RangeCoverage {
        if range.space != key.space || range.bytes == 0 || key.bytes == 0 {
            return RangeCoverage::NoOverlap;
        }

        if let Some(((range_start, range_end), (key_start, key_end))) =
            absolute_byte_range(&range.base, range.offset, range.bytes).zip(absolute_byte_range(
                &key.base,
                key.offset,
                i64::from(key.bytes),
            ))
        {
            return self.coverage_from_intervals(range, range_start, range_end, key_start, key_end);
        }

        if reserved_evm_meta_interval(&range.base, range.offset, range.bytes)
            .is_some_and(|_| is_allocator_managed_base(&key.base))
            || reserved_evm_meta_interval(&key.base, key.offset, i64::from(key.bytes))
                .is_some_and(|_| is_allocator_managed_base(&range.base))
        {
            return RangeCoverage::NoOverlap;
        }

        match self.alias_linear_bases(&range.base, &key.base) {
            AliasResult::NoAlias => RangeCoverage::NoOverlap,
            AliasResult::MayAlias => RangeCoverage::Unknown,
            AliasResult::MustAlias => range
                .offset
                .checked_add(range.bytes)
                .zip(key.offset.checked_add(i64::from(key.bytes)))
                .map_or(RangeCoverage::Unknown, |(range_end, key_end)| {
                    self.coverage_from_intervals(
                        range,
                        range.offset,
                        range_end,
                        key.offset,
                        key_end,
                    )
                }),
        }
    }

    fn coverage_from_intervals(
        &self,
        range: &LinearRangeKey,
        range_start: i64,
        range_end: i64,
        key_start: i64,
        key_end: i64,
    ) -> RangeCoverage {
        if !byte_ranges_overlap(range_start, range_end, key_start, key_end) {
            return RangeCoverage::NoOverlap;
        }

        if key_start <= range_start && range_end <= key_end {
            return RangeCoverage::FullyCovered;
        }

        let before = if range_start < key_start {
            let bytes = match key_start.checked_sub(range_start) {
                Some(bytes) => bytes,
                None => return RangeCoverage::Unknown,
            };
            Some(LinearRangeKey {
                space: range.space,
                base: range.base.clone(),
                offset: range.offset,
                bytes,
            })
        } else {
            None
        };
        let after = if key_end < range_end {
            let delta = match key_end.checked_sub(range_start) {
                Some(delta) => delta,
                None => return RangeCoverage::Unknown,
            };
            let bytes = match range_end.checked_sub(key_end) {
                Some(bytes) => bytes,
                None => return RangeCoverage::Unknown,
            };
            let offset = match range.offset.checked_add(delta) {
                Some(offset) => offset,
                None => return RangeCoverage::Unknown,
            };
            Some(LinearRangeKey {
                space: range.space,
                base: range.base.clone(),
                offset,
                bytes,
            })
        } else {
            None
        };

        RangeCoverage::PartiallyCovered { before, after }
    }

    fn alias_linear_bases(&self, lhs: &BaseObject, rhs: &BaseObject) -> AliasResult {
        match (lhs, rhs) {
            _ if lhs == rhs => AliasResult::MustAlias,
            (BaseObject::Alloca(a), BaseObject::Alloca(b)) if a != b => AliasResult::NoAlias,
            (BaseObject::Alloca(_), BaseObject::Global(_))
            | (BaseObject::Global(_), BaseObject::Alloca(_))
            | (BaseObject::Alloca(_), BaseObject::Arg(_))
            | (BaseObject::Arg(_), BaseObject::Alloca(_))
            | (BaseObject::Alloca(_), BaseObject::Malloc(_))
            | (BaseObject::Malloc(_), BaseObject::Alloca(_))
            | (BaseObject::Global(_), BaseObject::Malloc(_))
            | (BaseObject::Malloc(_), BaseObject::Global(_)) => AliasResult::NoAlias,
            (BaseObject::Global(a), BaseObject::Global(b)) if a != b => AliasResult::NoAlias,
            (BaseObject::Malloc(a), BaseObject::Malloc(b)) if a != b => AliasResult::NoAlias,
            (BaseObject::Unknown(_), _) | (_, BaseObject::Unknown(_)) => AliasResult::MayAlias,
            _ => AliasResult::MayAlias,
        }
    }

    fn canonical_linear_addr(&self, func: &Function, addr: ValueId) -> CanonicalAddr {
        self.canonical_linear_addr_rec(func, addr, &mut FxHashSet::default())
    }

    fn canonical_linear_addr_rec(
        &self,
        func: &Function,
        addr: ValueId,
        visiting: &mut FxHashSet<ValueId>,
    ) -> CanonicalAddr {
        if !visiting.insert(addr) {
            return CanonicalAddr::unknown(addr);
        }

        let canonical = match func.dfg.value(addr) {
            Value::Immediate { imm, .. } => CanonicalAddr {
                base: BaseObject::Absolute(*imm),
                offset: 0,
            },
            Value::Global { gv, .. } => CanonicalAddr {
                base: BaseObject::Global(*gv),
                offset: 0,
            },
            Value::Arg { .. } => CanonicalAddr {
                base: BaseObject::Arg(addr),
                offset: 0,
            },
            Value::Undef { .. } => CanonicalAddr::unknown(addr),
            Value::Inst { inst, .. } => self.canonical_addr_from_inst(func, addr, *inst, visiting),
        };

        visiting.remove(&addr);
        canonical
    }

    fn canonical_addr_from_inst(
        &self,
        func: &Function,
        value: ValueId,
        inst: InstId,
        visiting: &mut FxHashSet<ValueId>,
    ) -> CanonicalAddr {
        let inst_data = func.dfg.inst(inst);
        let is = func.inst_set();

        if <&Alloca as InstDowncast>::downcast(is, inst_data).is_some() {
            return CanonicalAddr {
                base: BaseObject::Alloca(inst),
                offset: 0,
            };
        }

        if <&EvmMalloc as InstDowncast>::downcast(is, inst_data).is_some() {
            return CanonicalAddr {
                base: BaseObject::Malloc(inst),
                offset: 0,
            };
        }

        if let Some(gep) = <&Gep as InstDowncast>::downcast(is, inst_data) {
            let Some((&base, indices)) = gep.values().split_first() else {
                return CanonicalAddr::unknown(value);
            };
            let Some(offset) = self.const_gep_offset(func, base, indices) else {
                return CanonicalAddr::unknown(value);
            };
            let base = self.canonical_linear_addr_rec(func, base, visiting);
            return base
                .with_offset(offset)
                .unwrap_or_else(|| CanonicalAddr::unknown(value));
        }

        if let Some(bitcast) = <&Bitcast as InstDowncast>::downcast(is, inst_data) {
            return self.canonical_linear_addr_rec(func, *bitcast.from(), visiting);
        }

        if let Some(int_to_ptr) = <&IntToPtr as InstDowncast>::downcast(is, inst_data) {
            return self.canonical_linear_addr_rec(func, *int_to_ptr.from(), visiting);
        }

        if let Some(ptr_to_int) = <&PtrToInt as InstDowncast>::downcast(is, inst_data) {
            return self.canonical_linear_addr_rec(func, *ptr_to_int.from(), visiting);
        }

        if let Some(add) = <&Add as InstDowncast>::downcast(is, inst_data) {
            if let Some(offset) = self.value_const_i64(func, *add.rhs()) {
                return self
                    .canonical_linear_addr_rec(func, *add.lhs(), visiting)
                    .with_offset(offset)
                    .unwrap_or_else(|| CanonicalAddr::unknown(value));
            }
            if let Some(offset) = self.value_const_i64(func, *add.lhs()) {
                return self
                    .canonical_linear_addr_rec(func, *add.rhs(), visiting)
                    .with_offset(offset)
                    .unwrap_or_else(|| CanonicalAddr::unknown(value));
            }
            return CanonicalAddr::unknown(value);
        }

        if let Some(sub) = <&Sub as InstDowncast>::downcast(is, inst_data) {
            if let Some(offset) = self.value_const_i64(func, *sub.rhs()) {
                return self
                    .canonical_linear_addr_rec(func, *sub.lhs(), visiting)
                    .with_offset(-offset)
                    .unwrap_or_else(|| CanonicalAddr::unknown(value));
            }
            return CanonicalAddr::unknown(value);
        }

        if let Some(phi) = <&Phi as InstDowncast>::downcast(is, inst_data) {
            let mut args = phi.args().iter().map(|(value, _)| *value);
            let Some(first) = args.next() else {
                return CanonicalAddr::unknown(value);
            };
            let first = self.canonical_linear_addr_rec(func, first, visiting);
            if args.all(|arg| self.canonical_linear_addr_rec(func, arg, visiting) == first) {
                return first;
            }
            return CanonicalAddr::unknown(value);
        }

        CanonicalAddr::unknown(value)
    }

    fn trackable_value_key(&self, func: &Function, value: ValueId) -> Option<ValueKey> {
        self.trackable_value_key_rec(func, value, &mut FxHashSet::default())
    }

    fn trackable_value_key_rec(
        &self,
        func: &Function,
        value: ValueId,
        visiting: &mut FxHashSet<ValueId>,
    ) -> Option<ValueKey> {
        if !visiting.insert(value) {
            return Some(ValueKey::Value(value));
        }

        let key = match func.dfg.value(value) {
            Value::Immediate { imm, .. } => Some(ValueKey::Imm(*imm)),
            Value::Arg { .. } => Some(ValueKey::Value(value)),
            Value::Inst {
                inst,
                result_idx,
                ty,
            } => Some(self.inst_value_key(func, value, *inst, *result_idx, *ty, visiting)),
            Value::Global { .. } | Value::Undef { .. } => None,
        };

        visiting.remove(&value);
        key
    }

    fn inst_value_key(
        &self,
        func: &Function,
        value: ValueId,
        inst: InstId,
        result_idx: u16,
        ty: Type,
        visiting: &mut FxHashSet<ValueId>,
    ) -> ValueKey {
        let result_tys: Vec<_> = func
            .dfg
            .inst_results(inst)
            .iter()
            .map(|&result| func.dfg.value_ty(result))
            .collect();
        let key = func.dfg.inst(inst).owned_key(&result_tys);

        match key.kind() {
            InstClassKind::Unary(_) => {
                let Some(arg) = key
                    .unary_arg()
                    .and_then(|arg| self.trackable_value_key_rec(func, arg, visiting))
                else {
                    return ValueKey::Value(value);
                };
                ValueKey::Expr(Box::new(KeyExpr::Unary {
                    opcode: key.opcode_text(),
                    result_idx,
                    ty,
                    arg,
                }))
            }
            InstClassKind::Binary(_) => {
                let Some((lhs, rhs)) = key.binary_args() else {
                    return ValueKey::Value(value);
                };
                let Some(mut lhs) = self.trackable_value_key_rec(func, lhs, visiting) else {
                    return ValueKey::Value(value);
                };
                let Some(mut rhs) = self.trackable_value_key_rec(func, rhs, visiting) else {
                    return ValueKey::Value(value);
                };
                if key.is_commutative_binary()
                    && value_key_fingerprint(&rhs) < value_key_fingerprint(&lhs)
                {
                    std::mem::swap(&mut lhs, &mut rhs);
                }
                ValueKey::Expr(Box::new(KeyExpr::Binary {
                    opcode: key.opcode_text(),
                    result_idx,
                    ty,
                    lhs,
                    rhs,
                }))
            }
            InstClassKind::Cast(_) => {
                let Some((arg, _)) = key.cast_arg_ty() else {
                    return ValueKey::Value(value);
                };
                let Some(arg) = self.trackable_value_key_rec(func, arg, visiting) else {
                    return ValueKey::Value(value);
                };
                ValueKey::Expr(Box::new(KeyExpr::Cast {
                    opcode: key.opcode_text(),
                    result_idx,
                    ty,
                    arg,
                }))
            }
            InstClassKind::Phi => {
                let Some(phi_args) = key.phi_args() else {
                    return ValueKey::Value(value);
                };
                let mut args = phi_args
                    .iter()
                    .map(|(arg, _)| self.trackable_value_key_rec(func, *arg, visiting));
                let Some(first) = args.next().flatten() else {
                    return ValueKey::Value(value);
                };
                if args.all(|arg| arg.as_ref() == Some(&first)) {
                    first
                } else {
                    ValueKey::Value(value)
                }
            }
            InstClassKind::Opaque => ValueKey::Value(value),
        }
    }

    fn const_gep_offset(&self, func: &Function, base: ValueId, indices: &[ValueId]) -> Option<i64> {
        let mut current_ty = func.dfg.value_ty(base);
        if !current_ty.is_pointer(func.ctx()) {
            return None;
        }

        let mut total = 0i64;
        for &idx_value in indices {
            let idx = self.value_const_i64(func, idx_value)?;
            match current_ty.resolve_compound(func.ctx())? {
                CompoundType::Ptr(elem_ty) => {
                    let elem_size = i64::try_from(func.ctx().size_of_unchecked(elem_ty)).ok()?;
                    total = total.checked_add(elem_size.checked_mul(idx)?)?;
                    current_ty = elem_ty;
                }
                CompoundType::Array { elem, .. } => {
                    let elem_size = i64::try_from(func.ctx().size_of_unchecked(elem)).ok()?;
                    total = total.checked_add(elem_size.checked_mul(idx)?)?;
                    current_ty = elem;
                }
                CompoundType::Struct(s) => {
                    let idx = usize::try_from(idx).ok()?;
                    let (field_offset, field_ty) =
                        shape::struct_field_offset_bytes(&s.fields, s.packed, idx, func.ctx())?;
                    total = total.checked_add(i64::from(field_offset))?;
                    current_ty = field_ty;
                }
                CompoundType::Enum(_) | CompoundType::ObjRef(_) | CompoundType::Func { .. } => {
                    return None;
                }
            }
        }

        Some(total)
    }

    fn value_const_i64(&self, func: &Function, value: ValueId) -> Option<i64> {
        immediate_i64(func.dfg.value_imm(value)?)
    }
}

impl Default for MemoryAccessAnalysis {
    fn default() -> Self {
        Self::new()
    }
}

impl CanonicalAddr {
    fn unknown(value: ValueId) -> Self {
        Self {
            base: BaseObject::Unknown(value),
            offset: 0,
        }
    }

    fn with_offset(mut self, delta: i64) -> Option<Self> {
        self.offset = self.offset.checked_add(delta)?;
        Some(self)
    }
}

fn absolute_byte_range(base: &BaseObject, offset: i64, bytes: i64) -> Option<(i64, i64)> {
    let BaseObject::Absolute(base) = base else {
        return None;
    };

    let start = immediate_i64(*base)?.checked_add(offset)?;
    let end = start.checked_add(bytes)?;
    Some((start, end))
}

fn absolute_linear_alias(lhs: &LinearLocKey, rhs: &LinearLocKey) -> Option<AliasResult> {
    let ((lhs_start, lhs_end), (rhs_start, rhs_end)) =
        absolute_byte_range(&lhs.base, lhs.offset, i64::from(lhs.bytes)).zip(
            absolute_byte_range(&rhs.base, rhs.offset, i64::from(rhs.bytes)),
        )?;

    Some(
        if !byte_ranges_overlap(lhs_start, lhs_end, rhs_start, rhs_end) {
            AliasResult::NoAlias
        } else if lhs_start == rhs_start && lhs_end == rhs_end {
            AliasResult::MustAlias
        } else {
            AliasResult::MayAlias
        },
    )
}

fn reserved_evm_meta_interval(base: &BaseObject, offset: i64, bytes: i64) -> Option<(i64, i64)> {
    let (start, end) = absolute_byte_range(base, offset, bytes)?;
    (end <= i64::from(STATIC_BASE)).then_some((start, end))
}

fn is_allocator_managed_base(base: &BaseObject) -> bool {
    matches!(base, BaseObject::Alloca(_) | BaseObject::Malloc(_))
}

fn byte_ranges_overlap(lhs_start: i64, lhs_end: i64, rhs_start: i64, rhs_end: i64) -> bool {
    lhs_start < rhs_end && rhs_start < lhs_end
}

fn value_key_fingerprint(key: &ValueKey) -> u64 {
    let mut hasher = FxHasher::default();
    key.hash(&mut hasher);
    hasher.finish()
}

fn immediate_i64(imm: Immediate) -> Option<i64> {
    let value = imm.as_i256();
    if value < I256::from(i64::MIN) || value > I256::from(i64::MAX) {
        return None;
    }

    Some(value.trunc_to_i64())
}

#[cfg(test)]
mod tests {
    use super::*;
    use sonatina_ir::{
        AccessKind, AccessLoc, MemoryAccess, Type,
        builder::test_util::*,
        inst::{
            arith::Add,
            control_flow::Return,
            data::{Alloca, Mload},
            evm::{EvmMalloc, EvmSload},
        },
        isa::Isa,
    };

    fn single_key(func: &Function, inst: InstId) -> TrackedLocKey {
        let analysis = MemoryAccessAnalysis::new();
        let effects = func.dfg.effects(inst);
        let access = effects.accesses.first().expect("expected one access");
        analysis
            .trackable_exact_loc(func, access)
            .expect("access should be trackable")
    }

    fn maybe_single_key(func: &Function, inst: InstId) -> Option<TrackedLocKey> {
        let analysis = MemoryAccessAnalysis::new();
        let effects = func.dfg.effects(inst);
        let access = effects.accesses.first().expect("expected one access");
        analysis.trackable_exact_loc(func, access)
    }

    fn range_access(space: AddressSpaceId, addr: ValueId, len: ValueId) -> MemoryAccess {
        MemoryAccess {
            space,
            kind: AccessKind::Read,
            must_happen: false,
            loc: AccessLoc::LinearRange { addr, len },
        }
    }

    fn exact_imm_access(space: AddressSpaceId, addr: Immediate) -> MemoryAccess {
        MemoryAccess {
            space,
            kind: AccessKind::Read,
            must_happen: true,
            loc: AccessLoc::LinearExactImm {
                addr,
                bytes: 32,
                ty: Type::I256,
            },
        }
    }

    #[test]
    fn alias_distinguishes_allocas() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let ptr_ty = builder.ptr_type(Type::I256);
        let addr0 = builder.insert_inst_with(|| Alloca::new(is, Type::I256), ptr_ty);
        let addr1 = builder.insert_inst_with(|| Alloca::new(is, Type::I256), ptr_ty);
        let load0 = builder.insert_inst_with(|| Mload::new(is, addr0, Type::I256), Type::I256);
        let load1 = builder.insert_inst_with(|| Mload::new(is, addr1, Type::I256), Type::I256);
        let _ = (load0, load1);
        builder.insert_inst_no_result_with(|| Return::new_unit(is));
        builder.seal_all();

        let insts: Vec<_> = builder.func.layout.iter_inst(block).collect();
        let key0 = single_key(&builder.func, insts[2]);
        let key1 = single_key(&builder.func, insts[3]);

        assert_eq!(
            MemoryAccessAnalysis::new().alias(&key0, &key1),
            AliasResult::NoAlias
        );
    }

    #[test]
    fn keyed_immediates_must_and_do_not_alias() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let k0 = builder.make_imm_value(1i32);
        let k1 = builder.make_imm_value(2i32);
        let load0 = builder.insert_inst_with(|| EvmSload::new(is, k0), Type::I256);
        let load1 = builder.insert_inst_with(|| EvmSload::new(is, k0), Type::I256);
        let load2 = builder.insert_inst_with(|| EvmSload::new(is, k1), Type::I256);
        let _ = (load0, load1, load2);
        builder.insert_inst_no_result_with(|| Return::new_unit(is));
        builder.seal_all();

        let insts: Vec<_> = builder.func.layout.iter_inst(block).collect();
        let key0 = single_key(&builder.func, insts[0]);
        let key1 = single_key(&builder.func, insts[1]);
        let key2 = single_key(&builder.func, insts[2]);
        let analysis = MemoryAccessAnalysis::new();

        assert_eq!(analysis.alias(&key0, &key1), AliasResult::MustAlias);
        assert_eq!(analysis.alias(&key0, &key2), AliasResult::NoAlias);
    }

    #[test]
    fn pointer_args_stay_may_alias() {
        let mb = test_module_builder();
        let ptr_ty = mb.ptr_type(Type::I256);
        let (evm, mut builder) = test_func_builder(&mb, &[ptr_ty, ptr_ty], Type::Unit);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let arg0 = builder.args()[0];
        let arg1 = builder.args()[1];
        let load0 = builder.insert_inst_with(|| Mload::new(is, arg0, Type::I256), Type::I256);
        let load1 = builder.insert_inst_with(|| Mload::new(is, arg1, Type::I256), Type::I256);
        let _ = (load0, load1);
        builder.insert_inst_no_result_with(|| Return::new_unit(is));
        builder.seal_all();

        let insts: Vec<_> = builder.func.layout.iter_inst(block).collect();
        let key0 = single_key(&builder.func, insts[0]);
        let key1 = single_key(&builder.func, insts[1]);

        assert_eq!(
            MemoryAccessAnalysis::new().alias(&key0, &key1),
            AliasResult::MayAlias
        );
    }

    #[test]
    fn different_spaces_do_not_alias() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let ptr_ty = builder.ptr_type(Type::I256);
        let addr = builder.insert_inst_with(|| Alloca::new(is, Type::I256), ptr_ty);
        let mload = builder.insert_inst_with(|| Mload::new(is, addr, Type::I256), Type::I256);
        let key = builder.make_imm_value(1i32);
        let sload = builder.insert_inst_with(|| EvmSload::new(is, key), Type::I256);
        let _ = (mload, sload);
        builder.insert_inst_no_result_with(|| Return::new_unit(is));
        builder.seal_all();

        let insts: Vec<_> = builder.func.layout.iter_inst(block).collect();
        let memory_key = single_key(&builder.func, insts[1]);
        let storage_key = single_key(&builder.func, insts[2]);

        assert_eq!(
            MemoryAccessAnalysis::new().alias(&memory_key, &storage_key),
            AliasResult::NoAlias
        );
    }

    #[test]
    fn dynamic_linear_address_is_not_trackable() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I256, Type::I256], Type::Unit);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let lhs = builder.args()[0];
        let rhs = builder.args()[1];
        let addr = builder.insert_inst_with(|| Add::new(is, lhs, rhs), Type::I256);
        let load = builder.insert_inst_with(|| Mload::new(is, addr, Type::I256), Type::I256);
        let _ = load;
        builder.insert_inst_no_result_with(|| Return::new_unit(is));
        builder.seal_all();

        let insts: Vec<_> = builder.func.layout.iter_inst(block).collect();
        assert!(maybe_single_key(&builder.func, insts[1]).is_none());
    }

    #[test]
    fn dynamic_keyed_access_reuses_same_ssa_key() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I256, Type::I256], Type::Unit);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let lhs = builder.args()[0];
        let rhs = builder.args()[1];
        let key = builder.insert_inst_with(|| Add::new(is, lhs, rhs), Type::I256);
        let load0 = builder.insert_inst_with(|| EvmSload::new(is, key), Type::I256);
        let load1 = builder.insert_inst_with(|| EvmSload::new(is, key), Type::I256);
        let _ = (load0, load1);
        builder.insert_inst_no_result_with(|| Return::new_unit(is));
        builder.seal_all();

        let insts: Vec<_> = builder.func.layout.iter_inst(block).collect();
        let key0 = single_key(&builder.func, insts[1]);
        let key1 = single_key(&builder.func, insts[2]);
        let analysis = MemoryAccessAnalysis::new();

        assert_eq!(analysis.alias(&key0, &key1), AliasResult::MustAlias);
    }

    #[test]
    fn structurally_equivalent_dynamic_keyed_accesses_must_alias() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I256, Type::I256], Type::Unit);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let lhs = builder.args()[0];
        let rhs = builder.args()[1];
        let key0 = builder.insert_inst_with(|| Add::new(is, lhs, rhs), Type::I256);
        let key1 = builder.insert_inst_with(|| Add::new(is, lhs, rhs), Type::I256);
        let load0 = builder.insert_inst_with(|| EvmSload::new(is, key0), Type::I256);
        let load1 = builder.insert_inst_with(|| EvmSload::new(is, key1), Type::I256);
        let _ = (load0, load1);
        builder.insert_inst_no_result_with(|| Return::new_unit(is));
        builder.seal_all();

        let insts: Vec<_> = builder.func.layout.iter_inst(block).collect();
        let key0 = single_key(&builder.func, insts[2]);
        let key1 = single_key(&builder.func, insts[3]);

        assert_eq!(
            MemoryAccessAnalysis::new().alias(&key0, &key1),
            AliasResult::MustAlias
        );
    }

    #[test]
    fn zero_length_linear_range_does_not_alias_exact_linear_key() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let addr = builder.make_imm_value(I256::from(64));
        let load = builder.insert_inst_with(|| Mload::new(is, addr, Type::I256), Type::I256);
        let _ = load;
        builder.insert_inst_no_result_with(|| Return::new_unit(is));
        builder.seal_all();

        let inst = builder.func.layout.first_inst_of(block).expect("load");
        let key = single_key(&builder.func, inst);
        let zero = builder.make_imm_value(I256::from(0));
        let analysis = MemoryAccessAnalysis::new();
        let range = analysis
            .trackable_linear_range(
                &builder.func,
                &range_access(
                    builder.func.ctx().address_spaces().default_space(),
                    addr,
                    zero,
                ),
            )
            .expect("zero-length range should be trackable");

        assert!(!analysis.range_may_alias_key(&range, &key));
    }

    #[test]
    fn disjoint_absolute_linear_range_does_not_alias_exact_linear_key() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let addr = builder.make_imm_value(I256::from(64));
        let load = builder.insert_inst_with(|| Mload::new(is, addr, Type::I256), Type::I256);
        let _ = load;
        builder.insert_inst_no_result_with(|| Return::new_unit(is));
        builder.seal_all();

        let inst = builder.func.layout.first_inst_of(block).expect("load");
        let key = single_key(&builder.func, inst);
        let range_addr = builder.make_imm_value(I256::from(0));
        let range_len = builder.make_imm_value(I256::from(32));
        let analysis = MemoryAccessAnalysis::new();
        let range = analysis
            .trackable_linear_range(
                &builder.func,
                &range_access(
                    builder.func.ctx().address_spaces().default_space(),
                    range_addr,
                    range_len,
                ),
            )
            .expect("range should be trackable");

        assert!(!analysis.range_may_alias_key(&range, &key));
    }

    #[test]
    fn overlapping_absolute_linear_range_aliases_exact_linear_key() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let addr = builder.make_imm_value(I256::from(64));
        let load = builder.insert_inst_with(|| Mload::new(is, addr, Type::I256), Type::I256);
        let _ = load;
        builder.insert_inst_no_result_with(|| Return::new_unit(is));
        builder.seal_all();

        let inst = builder.func.layout.first_inst_of(block).expect("load");
        let key = single_key(&builder.func, inst);
        let range_len = builder.make_imm_value(I256::from(32));
        let analysis = MemoryAccessAnalysis::new();
        let range = analysis
            .trackable_linear_range(
                &builder.func,
                &range_access(
                    builder.func.ctx().address_spaces().default_space(),
                    addr,
                    range_len,
                ),
            )
            .expect("range should be trackable");

        assert!(analysis.range_may_alias_key(&range, &key));
    }

    #[test]
    fn immediate_exact_linear_access_tracks_as_absolute_key() {
        let mb = test_module_builder();
        let (_evm, builder) = test_func_builder(&mb, &[], Type::Unit);
        let analysis = MemoryAccessAnalysis::new();
        let addr = Immediate::from_i256(I256::from(64), Type::I256);

        let key = analysis
            .trackable_exact_loc(
                &builder.func,
                &exact_imm_access(builder.func.ctx().address_spaces().default_space(), addr),
            )
            .expect("immediate exact access should be trackable");

        assert_eq!(
            key,
            TrackedLocKey::Linear(LinearLocKey {
                space: builder.func.ctx().address_spaces().default_space(),
                base: BaseObject::Absolute(addr),
                offset: 0,
                bytes: 32,
                ty: Type::I256,
            })
        );
    }

    #[test]
    fn reserved_absolute_meta_access_does_not_alias_malloc_key() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let size = builder.make_imm_value(I256::from(32));
        let ptr_ty = builder.ptr_type(Type::I8);
        let addr = builder.insert_inst_with(|| EvmMalloc::new(is, size), ptr_ty);
        let load = builder.insert_inst_with(|| Mload::new(is, addr, Type::I256), Type::I256);
        let _ = load;
        builder.insert_inst_no_result_with(|| Return::new_unit(is));
        builder.seal_all();

        let insts: Vec<_> = builder.func.layout.iter_inst(block).collect();
        let malloc_key = single_key(&builder.func, insts[1]);
        let free_ptr = Immediate::from_i256(I256::from(64), Type::I256);
        let absolute_key = MemoryAccessAnalysis::new()
            .trackable_exact_loc(
                &builder.func,
                &exact_imm_access(
                    builder.func.ctx().address_spaces().default_space(),
                    free_ptr,
                ),
            )
            .expect("free pointer access should be trackable");

        assert_eq!(
            MemoryAccessAnalysis::new().alias(&malloc_key, &absolute_key),
            AliasResult::NoAlias
        );
    }

    #[test]
    fn absolute_access_at_static_base_may_alias_malloc_key() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let size = builder.make_imm_value(I256::from(32));
        let ptr_ty = builder.ptr_type(Type::I8);
        let addr = builder.insert_inst_with(|| EvmMalloc::new(is, size), ptr_ty);
        let load = builder.insert_inst_with(|| Mload::new(is, addr, Type::I256), Type::I256);
        let _ = load;
        builder.insert_inst_no_result_with(|| Return::new_unit(is));
        builder.seal_all();

        let insts: Vec<_> = builder.func.layout.iter_inst(block).collect();
        let malloc_key = single_key(&builder.func, insts[1]);
        let heap_addr = Immediate::from_i256(I256::from(STATIC_BASE), Type::I256);
        let absolute_key = MemoryAccessAnalysis::new()
            .trackable_exact_loc(
                &builder.func,
                &exact_imm_access(
                    builder.func.ctx().address_spaces().default_space(),
                    heap_addr,
                ),
            )
            .expect("heap access should be trackable");

        assert_eq!(
            MemoryAccessAnalysis::new().alias(&malloc_key, &absolute_key),
            AliasResult::MayAlias
        );
    }

    #[test]
    fn exact_write_fully_covers_linear_range() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let addr = builder.make_imm_value(I256::from(64));
        let load = builder.insert_inst_with(|| Mload::new(is, addr, Type::I256), Type::I256);
        let _ = load;
        builder.insert_inst_no_result_with(|| Return::new_unit(is));
        builder.seal_all();

        let inst = builder.func.layout.first_inst_of(block).expect("load");
        let TrackedLocKey::Linear(key) = single_key(&builder.func, inst) else {
            panic!("expected a linear key");
        };
        let range_len = builder.make_imm_value(I256::from(32));
        let analysis = MemoryAccessAnalysis::new();
        let range = analysis
            .trackable_linear_range(
                &builder.func,
                &range_access(
                    builder.func.ctx().address_spaces().default_space(),
                    addr,
                    range_len,
                ),
            )
            .expect("range should be trackable");

        assert_eq!(
            analysis.exact_write_coverage(&range, &key),
            RangeCoverage::FullyCovered
        );
    }

    #[test]
    fn exact_write_partially_covers_linear_range() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let key_addr = builder.make_imm_value(I256::from(80));
        let load = builder.insert_inst_with(|| Mload::new(is, key_addr, Type::I256), Type::I256);
        let _ = load;
        builder.insert_inst_no_result_with(|| Return::new_unit(is));
        builder.seal_all();

        let inst = builder.func.layout.first_inst_of(block).expect("load");
        let TrackedLocKey::Linear(key) = single_key(&builder.func, inst) else {
            panic!("expected a linear key");
        };
        let range_addr = builder.make_imm_value(I256::from(64));
        let range_len = builder.make_imm_value(I256::from(32));
        let analysis = MemoryAccessAnalysis::new();
        let range = analysis
            .trackable_linear_range(
                &builder.func,
                &range_access(
                    builder.func.ctx().address_spaces().default_space(),
                    range_addr,
                    range_len,
                ),
            )
            .expect("range should be trackable");

        assert_eq!(
            analysis.exact_write_coverage(&range, &key),
            RangeCoverage::PartiallyCovered {
                before: Some(LinearRangeKey {
                    space: range.space,
                    base: range.base.clone(),
                    offset: range.offset,
                    bytes: 16,
                }),
                after: None,
            }
        );
    }

    #[test]
    fn exact_write_disjoint_from_linear_range() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let key_addr = builder.make_imm_value(I256::from(96));
        let load = builder.insert_inst_with(|| Mload::new(is, key_addr, Type::I256), Type::I256);
        let _ = load;
        builder.insert_inst_no_result_with(|| Return::new_unit(is));
        builder.seal_all();

        let inst = builder.func.layout.first_inst_of(block).expect("load");
        let TrackedLocKey::Linear(key) = single_key(&builder.func, inst) else {
            panic!("expected a linear key");
        };
        let range_addr = builder.make_imm_value(I256::from(64));
        let range_len = builder.make_imm_value(I256::from(32));
        let analysis = MemoryAccessAnalysis::new();
        let range = analysis
            .trackable_linear_range(
                &builder.func,
                &range_access(
                    builder.func.ctx().address_spaces().default_space(),
                    range_addr,
                    range_len,
                ),
            )
            .expect("range should be trackable");

        assert_eq!(
            analysis.exact_write_coverage(&range, &key),
            RangeCoverage::NoOverlap
        );
    }
}
