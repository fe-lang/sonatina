use rustc_hash::FxHashSet;
use sonatina_ir::{
    AccessLoc, AddressSpaceId, Function, GlobalVariableRef, I256, Immediate, InstDowncast, InstId,
    Type, Value, ValueId,
    inst::{
        arith::{Add, Sub},
        cast::{Bitcast, IntToPtr, PtrToInt},
        control_flow::Phi,
        data::{Alloca, Gep},
        evm::EvmMalloc,
    },
    types::CompoundType,
};

use crate::optim::aggregate::shape;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ValueKey {
    Imm(Immediate),
    Value(ValueId),
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
            | (TrackedLocKey::Keyed(_), AccessLoc::LinearExact { .. }) => false,
            (_, AccessLoc::LinearExact { .. } | AccessLoc::KeyedExact { .. }) => self
                .trackable_exact_loc(func, access)
                .is_none_or(|other| self.alias(key, &other) != AliasResult::NoAlias),
        }
    }

    fn alias_linear(&self, lhs: &LinearLocKey, rhs: &LinearLocKey) -> AliasResult {
        if lhs.space != rhs.space {
            return AliasResult::NoAlias;
        }

        match (&lhs.base, &rhs.base) {
            _ if lhs.base == rhs.base => self.alias_same_base_linear(lhs, rhs),
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
        if range.space != key.space || range.bytes == 0 {
            return false;
        }

        if let (Some((range_start, range_end)), Some((key_start, key_end))) = (
            absolute_byte_range(&range.base, range.offset, range.bytes),
            absolute_byte_range(&key.base, key.offset, i64::from(key.bytes)),
        ) {
            return byte_ranges_overlap(range_start, range_end, key_start, key_end);
        }

        match self.alias_linear_bases(&range.base, &key.base) {
            AliasResult::NoAlias => false,
            AliasResult::MayAlias => true,
            AliasResult::MustAlias => range
                .offset
                .checked_add(range.bytes)
                .zip(key.offset.checked_add(i64::from(key.bytes)))
                .is_none_or(|(range_end, key_end)| {
                    byte_ranges_overlap(range.offset, range_end, key.offset, key_end)
                }),
        }
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
        match func.dfg.value(value) {
            Value::Immediate { imm, .. } => Some(ValueKey::Imm(*imm)),
            Value::Arg { .. } => Some(ValueKey::Value(value)),
            Value::Global { .. } | Value::Inst { .. } | Value::Undef { .. } => None,
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
                CompoundType::Func { .. } => return None,
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

fn byte_ranges_overlap(lhs_start: i64, lhs_end: i64, rhs_start: i64, rhs_end: i64) -> bool {
    lhs_start < rhs_end && rhs_start < lhs_end
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
            evm::EvmSload,
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
    fn dynamic_keyed_access_is_not_trackable() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I256, Type::I256], Type::Unit);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let lhs = builder.args()[0];
        let rhs = builder.args()[1];
        let key = builder.insert_inst_with(|| Add::new(is, lhs, rhs), Type::I256);
        let load = builder.insert_inst_with(|| EvmSload::new(is, key), Type::I256);
        let _ = load;
        builder.insert_inst_no_result_with(|| Return::new_unit(is));
        builder.seal_all();

        let insts: Vec<_> = builder.func.layout.iter_inst(block).collect();
        assert!(maybe_single_key(&builder.func, insts[1]).is_none());
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
}
