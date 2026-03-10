use bitflags::bitflags;
use cranelift_entity::entity_impl;
use smallvec::{SmallVec, smallvec};

use crate::{
    DataFlowGraph, InstDowncast, InstId, Type, ValueId,
    bitset::BitSet,
    inst::{
        SideEffect, control_flow, data,
        evm::{
            EvmAddress, EvmBalance, EvmBaseFee, EvmBlobBaseFee, EvmBlobHash, EvmBlockHash, EvmCall,
            EvmCallCode, EvmCallValue, EvmCalldataCopy, EvmCalldataLoad, EvmCalldataSize,
            EvmCaller, EvmChainId, EvmCodeCopy, EvmCodeSize, EvmCoinBase, EvmCreate, EvmCreate2,
            EvmDelegateCall, EvmExtCodeCopy, EvmExtCodeHash, EvmExtCodeSize, EvmGas, EvmGasLimit,
            EvmGasPrice, EvmInvalid, EvmKeccak256, EvmLog0, EvmLog1, EvmLog2, EvmLog3, EvmLog4,
            EvmMalloc, EvmMcopy, EvmMsize, EvmMstore8, EvmNumber, EvmOrigin, EvmPrevRandao,
            EvmReturn, EvmReturnDataCopy, EvmReturnDataSize, EvmRevert, EvmSelfBalance,
            EvmSelfDestruct, EvmSload, EvmSstore, EvmStaticCall, EvmStop, EvmTimestamp, EvmTload,
            EvmTstore,
        },
    },
    isa::evm::space::{CALLDATA, CODE, MEMORY, RETURNDATA, STORAGE, TRANSIENT},
    module::FuncAttrs,
};

const EVM_WORD_BYTES: u32 = 32;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AddressSpaceId(u32);
entity_impl!(AddressSpaceId);

impl AddressSpaceId {
    pub const fn new(raw: u32) -> Self {
        Self(raw)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AddressSpaceKind {
    Linear,
    Keyed,
    Opaque,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AddressSpaceDesc {
    pub id: AddressSpaceId,
    pub name: &'static str,
    pub kind: AddressSpaceKind,
    pub immutable: bool,
}

pub trait AddressSpaceInfo: Send + Sync {
    fn default_space(&self) -> AddressSpaceId;
    fn desc(&self, id: AddressSpaceId) -> AddressSpaceDesc;
    fn all_spaces(&self) -> &'static [AddressSpaceDesc];
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AccessKind {
    Read,
    Write,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AccessLoc {
    LinearExact { addr: ValueId, bytes: u32, ty: Type },
    LinearRange { addr: ValueId, len: ValueId },
    KeyedExact { key: ValueId, bytes: u32 },
    WholeSpace,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemoryAccess {
    pub space: AddressSpaceId,
    pub kind: AccessKind,
    pub must_happen: bool,
    pub loc: AccessLoc,
}

bitflags! {
    #[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
    pub struct OtherEffects: u8 {
        const OBSERVE = 1 << 0;
        const MUTATE  = 1 << 1;
        const CONTROL = 1 << 2;
        const ALLOC   = 1 << 3;
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct InstEffects {
    pub accesses: SmallVec<[MemoryAccess; 2]>,
    pub other: OtherEffects,
}

impl InstEffects {
    pub fn to_legacy_side_effect(&self) -> SideEffect {
        if self.other.contains(OtherEffects::CONTROL) {
            SideEffect::Control
        } else if self
            .accesses
            .iter()
            .any(|access| access.kind == AccessKind::Write)
            || self
                .other
                .intersects(OtherEffects::MUTATE | OtherEffects::ALLOC)
        {
            SideEffect::Write
        } else if self
            .accesses
            .iter()
            .any(|access| access.kind == AccessKind::Read)
            || self.other.contains(OtherEffects::OBSERVE)
        {
            SideEffect::Read
        } else {
            SideEffect::None
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FuncEffectSummary {
    pub may_read_spaces: BitSet<AddressSpaceId>,
    pub may_write_spaces: BitSet<AddressSpaceId>,
    pub may_read_unknown: bool,
    pub may_write_unknown: bool,
    pub other: OtherEffects,
    pub noreturn: bool,
    pub will_return: bool,
    pub will_terminate: bool,
}

impl FuncEffectSummary {
    pub fn unknown_call() -> Self {
        Self {
            may_read_unknown: true,
            may_write_unknown: true,
            ..Self::default()
        }
    }

    pub fn from_legacy_attrs(attrs: FuncAttrs) -> Self {
        Self {
            may_read_unknown: attrs.contains(FuncAttrs::MEM_READ),
            may_write_unknown: attrs.contains(FuncAttrs::MEM_WRITE),
            noreturn: attrs.contains(FuncAttrs::NORETURN),
            will_return: attrs.contains(FuncAttrs::WILLRETURN),
            will_terminate: attrs.contains(FuncAttrs::WILLTERMINATE),
            ..Self::default()
        }
    }

    pub fn to_legacy_attrs(&self) -> FuncAttrs {
        let mut attrs = FuncAttrs::empty();

        if self.noreturn {
            attrs.insert(FuncAttrs::NORETURN);
        }
        if self.will_return {
            attrs.insert(FuncAttrs::WILLRETURN);
        }
        if self.will_terminate {
            attrs.insert(FuncAttrs::WILLTERMINATE);
        }

        if !self.may_read_spaces.is_empty()
            || self.may_read_unknown
            || self.other.contains(OtherEffects::OBSERVE)
        {
            attrs.insert(FuncAttrs::MEM_READ);
        }

        if !self.may_write_spaces.is_empty()
            || self.may_write_unknown
            || self
                .other
                .intersects(OtherEffects::MUTATE | OtherEffects::ALLOC)
        {
            attrs.insert(FuncAttrs::MEM_WRITE);
        }

        attrs
    }

    pub fn to_legacy_side_effect(&self) -> SideEffect {
        if self.noreturn || !self.will_return {
            SideEffect::Control
        } else if !self.may_write_spaces.is_empty()
            || self.may_write_unknown
            || self
                .other
                .intersects(OtherEffects::MUTATE | OtherEffects::ALLOC)
        {
            SideEffect::Write
        } else if !self.may_read_spaces.is_empty()
            || self.may_read_unknown
            || self.other.contains(OtherEffects::OBSERVE)
        {
            SideEffect::Read
        } else {
            SideEffect::None
        }
    }

    pub fn union_with(&mut self, other: &Self) {
        self.may_read_spaces.union_with(&other.may_read_spaces);
        self.may_write_spaces.union_with(&other.may_write_spaces);
        self.may_read_unknown |= other.may_read_unknown;
        self.may_write_unknown |= other.may_write_unknown;
        self.other |= other.other;
        self.noreturn |= other.noreturn;
        self.will_return |= other.will_return;
        self.will_terminate |= other.will_terminate;
    }

    pub fn summarize_inst_effects(&mut self, effects: &InstEffects) {
        for access in &effects.accesses {
            match access.kind {
                AccessKind::Read => {
                    self.may_read_spaces.insert(access.space);
                }
                AccessKind::Write => {
                    self.may_write_spaces.insert(access.space);
                }
            }
        }
        self.other |= effects.other & !OtherEffects::CONTROL;
    }
}

pub fn classify_inst_effects(dfg: &DataFlowGraph, inst_id: InstId) -> InstEffects {
    let inst = dfg.inst(inst_id);
    let is = dfg.inst_set();
    let spaces = dfg.ctx.address_spaces();

    if let Some(mload) = <&data::Mload as InstDowncast>::downcast(is, inst) {
        let bytes = dfg.ctx.size_of_unchecked(*mload.ty()) as u32;
        return exact_linear(
            spaces.default_space(),
            AccessKind::Read,
            *mload.addr(),
            bytes,
            *mload.ty(),
        );
    }

    if let Some(mstore) = <&data::Mstore as InstDowncast>::downcast(is, inst) {
        let bytes = dfg.ctx.size_of_unchecked(*mstore.ty()) as u32;
        return exact_linear(
            spaces.default_space(),
            AccessKind::Write,
            *mstore.addr(),
            bytes,
            *mstore.ty(),
        );
    }

    if <&data::Alloca as InstDowncast>::downcast(is, inst).is_some() {
        return InstEffects {
            other: OtherEffects::ALLOC,
            ..InstEffects::default()
        };
    }

    if let Some(call) = dfg.call_info(inst_id) {
        return inst_effects_from_func_summary(&dfg.ctx.func_effects(call.callee()), spaces);
    }

    if let Some(mstore8) = <&EvmMstore8 as InstDowncast>::downcast(is, inst) {
        return exact_linear(MEMORY, AccessKind::Write, *mstore8.addr(), 1, Type::I8);
    }

    if let Some(sload) = <&EvmSload as InstDowncast>::downcast(is, inst) {
        return exact_keyed(STORAGE, AccessKind::Read, *sload.key(), EVM_WORD_BYTES);
    }

    if let Some(sstore) = <&EvmSstore as InstDowncast>::downcast(is, inst) {
        return exact_keyed(STORAGE, AccessKind::Write, *sstore.key(), EVM_WORD_BYTES);
    }

    if let Some(tload) = <&EvmTload as InstDowncast>::downcast(is, inst) {
        return exact_keyed(TRANSIENT, AccessKind::Read, *tload.key(), EVM_WORD_BYTES);
    }

    if let Some(tstore) = <&EvmTstore as InstDowncast>::downcast(is, inst) {
        return exact_keyed(TRANSIENT, AccessKind::Write, *tstore.key(), EVM_WORD_BYTES);
    }

    if let Some(calldata_load) = <&EvmCalldataLoad as InstDowncast>::downcast(is, inst) {
        let ty = dfg
            .inst_result(inst_id)
            .map(|value| dfg.value_ty(value))
            .unwrap_or(Type::I256);
        return exact_linear(
            CALLDATA,
            AccessKind::Read,
            *calldata_load.data_offset(),
            EVM_WORD_BYTES,
            ty,
        );
    }

    if let Some(keccak) = <&EvmKeccak256 as InstDowncast>::downcast(is, inst) {
        return range_access(MEMORY, AccessKind::Read, *keccak.addr(), *keccak.len());
    }

    if let Some(copy) = <&EvmCalldataCopy as InstDowncast>::downcast(is, inst) {
        return InstEffects {
            accesses: smallvec![
                range_access_data(CALLDATA, AccessKind::Read, *copy.data_offset(), *copy.len()),
                range_access_data(MEMORY, AccessKind::Write, *copy.dst_addr(), *copy.len()),
            ],
            ..InstEffects::default()
        };
    }

    if let Some(copy) = <&EvmCodeCopy as InstDowncast>::downcast(is, inst) {
        return InstEffects {
            accesses: smallvec![
                range_access_data(CODE, AccessKind::Read, *copy.code_offset(), *copy.len()),
                range_access_data(MEMORY, AccessKind::Write, *copy.dst_addr(), *copy.len()),
            ],
            ..InstEffects::default()
        };
    }

    if let Some(copy) = <&EvmReturnDataCopy as InstDowncast>::downcast(is, inst) {
        return InstEffects {
            accesses: smallvec![
                range_access_data(
                    RETURNDATA,
                    AccessKind::Read,
                    *copy.data_offset(),
                    *copy.len(),
                ),
                range_access_data(MEMORY, AccessKind::Write, *copy.dst_addr(), *copy.len()),
            ],
            ..InstEffects::default()
        };
    }

    if let Some(copy) = <&EvmExtCodeCopy as InstDowncast>::downcast(is, inst) {
        return InstEffects {
            accesses: smallvec![range_access_data(
                MEMORY,
                AccessKind::Write,
                *copy.dst_addr(),
                *copy.len(),
            )],
            other: OtherEffects::OBSERVE,
        };
    }

    if let Some(mcopy) = <&EvmMcopy as InstDowncast>::downcast(is, inst) {
        return InstEffects {
            accesses: smallvec![
                range_access_data(MEMORY, AccessKind::Read, *mcopy.addr(), *mcopy.len()),
                range_access_data(MEMORY, AccessKind::Write, *mcopy.dest(), *mcopy.len()),
            ],
            ..InstEffects::default()
        };
    }

    if let Some(log) = <&EvmLog0 as InstDowncast>::downcast(is, inst) {
        return read_memory_with_other(*log.addr(), *log.len(), OtherEffects::MUTATE);
    }

    if let Some(log) = <&EvmLog1 as InstDowncast>::downcast(is, inst) {
        return read_memory_with_other(*log.addr(), *log.len(), OtherEffects::MUTATE);
    }

    if let Some(log) = <&EvmLog2 as InstDowncast>::downcast(is, inst) {
        return read_memory_with_other(*log.addr(), *log.len(), OtherEffects::MUTATE);
    }

    if let Some(log) = <&EvmLog3 as InstDowncast>::downcast(is, inst) {
        return read_memory_with_other(*log.addr(), *log.len(), OtherEffects::MUTATE);
    }

    if let Some(log) = <&EvmLog4 as InstDowncast>::downcast(is, inst) {
        return read_memory_with_other(*log.addr(), *log.len(), OtherEffects::MUTATE);
    }

    if let Some(ret) = <&EvmReturn as InstDowncast>::downcast(is, inst) {
        return read_memory_with_other(*ret.addr(), *ret.len(), OtherEffects::CONTROL);
    }

    if let Some(revert) = <&EvmRevert as InstDowncast>::downcast(is, inst) {
        return read_memory_with_other(*revert.addr(), *revert.len(), OtherEffects::CONTROL);
    }

    if let Some(create) = <&EvmCreate as InstDowncast>::downcast(is, inst) {
        return read_memory_with_other(*create.addr(), *create.len(), OtherEffects::MUTATE);
    }

    if let Some(create) = <&EvmCreate2 as InstDowncast>::downcast(is, inst) {
        return read_memory_with_other(*create.addr(), *create.len(), OtherEffects::MUTATE);
    }

    if let Some(call) = <&EvmCall as InstDowncast>::downcast(is, inst) {
        return external_call_effects(
            *call.arg_addr(),
            *call.arg_len(),
            *call.ret_addr(),
            *call.ret_offset(),
            true,
        );
    }

    if let Some(call) = <&EvmCallCode as InstDowncast>::downcast(is, inst) {
        return external_call_effects(
            *call.arg_addr(),
            *call.arg_len(),
            *call.ret_addr(),
            *call.ret_offset(),
            true,
        );
    }

    if let Some(call) = <&EvmDelegateCall as InstDowncast>::downcast(is, inst) {
        return external_call_effects(
            *call.arg_addr(),
            *call.arg_len(),
            *call.ret_addr(),
            *call.ret_len(),
            true,
        );
    }

    if let Some(call) = <&EvmStaticCall as InstDowncast>::downcast(is, inst) {
        return external_call_effects(
            *call.arg_addr(),
            *call.arg_len(),
            *call.ret_addr(),
            *call.ret_len(),
            false,
        );
    }

    if <&EvmMalloc as InstDowncast>::downcast(is, inst).is_some() {
        return InstEffects {
            other: OtherEffects::ALLOC,
            ..InstEffects::default()
        };
    }

    if <&EvmStop as InstDowncast>::downcast(is, inst).is_some()
        || <&EvmInvalid as InstDowncast>::downcast(is, inst).is_some()
        || <&control_flow::Unreachable as InstDowncast>::downcast(is, inst).is_some()
        || <&control_flow::Return as InstDowncast>::downcast(is, inst).is_some()
    {
        return InstEffects {
            other: OtherEffects::CONTROL,
            ..InstEffects::default()
        };
    }

    if <&EvmSelfDestruct as InstDowncast>::downcast(is, inst).is_some() {
        return InstEffects {
            other: OtherEffects::MUTATE | OtherEffects::CONTROL,
            ..InstEffects::default()
        };
    }

    if is_observe_only_evm_inst(dfg, inst_id) {
        return InstEffects {
            accesses: msize_barrier_if_needed(dfg, inst_id),
            other: OtherEffects::OBSERVE,
        };
    }

    fallback_from_legacy_side_effect(inst.side_effect(), spaces)
}

fn exact_linear(
    space: AddressSpaceId,
    kind: AccessKind,
    addr: ValueId,
    bytes: u32,
    ty: Type,
) -> InstEffects {
    InstEffects {
        accesses: smallvec![MemoryAccess {
            space,
            kind,
            must_happen: true,
            loc: AccessLoc::LinearExact { addr, bytes, ty },
        }],
        ..InstEffects::default()
    }
}

fn exact_keyed(space: AddressSpaceId, kind: AccessKind, key: ValueId, bytes: u32) -> InstEffects {
    InstEffects {
        accesses: smallvec![MemoryAccess {
            space,
            kind,
            must_happen: true,
            loc: AccessLoc::KeyedExact { key, bytes },
        }],
        ..InstEffects::default()
    }
}

fn range_access(
    space: AddressSpaceId,
    kind: AccessKind,
    addr: ValueId,
    len: ValueId,
) -> InstEffects {
    InstEffects {
        accesses: smallvec![range_access_data(space, kind, addr, len)],
        ..InstEffects::default()
    }
}

fn range_access_data(
    space: AddressSpaceId,
    kind: AccessKind,
    addr: ValueId,
    len: ValueId,
) -> MemoryAccess {
    MemoryAccess {
        space,
        kind,
        must_happen: false,
        loc: AccessLoc::LinearRange { addr, len },
    }
}

fn read_memory_with_other(addr: ValueId, len: ValueId, other: OtherEffects) -> InstEffects {
    InstEffects {
        accesses: smallvec![range_access_data(MEMORY, AccessKind::Read, addr, len)],
        other,
    }
}

fn whole_space(space: AddressSpaceId, kind: AccessKind) -> MemoryAccess {
    MemoryAccess {
        space,
        kind,
        must_happen: false,
        loc: AccessLoc::WholeSpace,
    }
}

fn external_call_effects(
    arg_addr: ValueId,
    arg_len: ValueId,
    ret_addr: ValueId,
    ret_len: ValueId,
    may_write_state: bool,
) -> InstEffects {
    let mut accesses = smallvec![
        range_access_data(MEMORY, AccessKind::Read, arg_addr, arg_len),
        range_access_data(MEMORY, AccessKind::Write, ret_addr, ret_len),
        whole_space(STORAGE, AccessKind::Read),
        whole_space(TRANSIENT, AccessKind::Read),
        whole_space(RETURNDATA, AccessKind::Write),
    ];

    if may_write_state {
        accesses.push(whole_space(STORAGE, AccessKind::Write));
        accesses.push(whole_space(TRANSIENT, AccessKind::Write));
    }

    InstEffects {
        accesses,
        other: if may_write_state {
            OtherEffects::MUTATE
        } else {
            OtherEffects::OBSERVE
        },
    }
}

fn inst_effects_from_func_summary(
    summary: &FuncEffectSummary,
    spaces: &dyn AddressSpaceInfo,
) -> InstEffects {
    let mut effects = InstEffects {
        other: summary.other,
        ..InstEffects::default()
    };

    if summary.noreturn || !summary.will_return {
        effects.other.insert(OtherEffects::CONTROL);
    }

    for space in summary.may_read_spaces.iter() {
        effects.accesses.push(whole_space(space, AccessKind::Read));
    }
    for space in summary.may_write_spaces.iter() {
        effects.accesses.push(whole_space(space, AccessKind::Write));
    }

    if summary.may_read_unknown {
        for desc in spaces.all_spaces() {
            if !summary.may_read_spaces.contains(desc.id) {
                effects
                    .accesses
                    .push(whole_space(desc.id, AccessKind::Read));
            }
        }
    }

    if summary.may_write_unknown {
        for desc in spaces.all_spaces() {
            if !desc.immutable && !summary.may_write_spaces.contains(desc.id) {
                effects
                    .accesses
                    .push(whole_space(desc.id, AccessKind::Write));
            }
        }
    }

    effects
}

fn fallback_from_legacy_side_effect(
    side_effect: SideEffect,
    spaces: &dyn AddressSpaceInfo,
) -> InstEffects {
    match side_effect {
        SideEffect::None => InstEffects::default(),
        SideEffect::Read => InstEffects {
            accesses: spaces
                .all_spaces()
                .iter()
                .map(|desc| whole_space(desc.id, AccessKind::Read))
                .collect(),
            other: OtherEffects::OBSERVE,
        },
        SideEffect::Write => InstEffects {
            accesses: spaces
                .all_spaces()
                .iter()
                .map(|desc| whole_space(desc.id, AccessKind::Read))
                .chain(
                    spaces
                        .all_spaces()
                        .iter()
                        .filter(|desc| !desc.immutable)
                        .map(|desc| whole_space(desc.id, AccessKind::Write)),
                )
                .collect(),
            other: OtherEffects::MUTATE,
        },
        SideEffect::Control => InstEffects {
            other: OtherEffects::CONTROL,
            ..InstEffects::default()
        },
    }
}

fn is_observe_only_evm_inst(dfg: &DataFlowGraph, inst_id: InstId) -> bool {
    let inst = dfg.inst(inst_id);
    let is = dfg.inst_set();

    <&EvmAddress as InstDowncast>::downcast(is, inst).is_some()
        || <&EvmBalance as InstDowncast>::downcast(is, inst).is_some()
        || <&EvmOrigin as InstDowncast>::downcast(is, inst).is_some()
        || <&EvmCaller as InstDowncast>::downcast(is, inst).is_some()
        || <&EvmCallValue as InstDowncast>::downcast(is, inst).is_some()
        || <&EvmCalldataSize as InstDowncast>::downcast(is, inst).is_some()
        || <&EvmCodeSize as InstDowncast>::downcast(is, inst).is_some()
        || <&EvmGasPrice as InstDowncast>::downcast(is, inst).is_some()
        || <&EvmExtCodeSize as InstDowncast>::downcast(is, inst).is_some()
        || <&EvmReturnDataSize as InstDowncast>::downcast(is, inst).is_some()
        || <&EvmExtCodeHash as InstDowncast>::downcast(is, inst).is_some()
        || <&EvmBlockHash as InstDowncast>::downcast(is, inst).is_some()
        || <&EvmCoinBase as InstDowncast>::downcast(is, inst).is_some()
        || <&EvmTimestamp as InstDowncast>::downcast(is, inst).is_some()
        || <&EvmNumber as InstDowncast>::downcast(is, inst).is_some()
        || <&EvmPrevRandao as InstDowncast>::downcast(is, inst).is_some()
        || <&EvmGasLimit as InstDowncast>::downcast(is, inst).is_some()
        || <&EvmChainId as InstDowncast>::downcast(is, inst).is_some()
        || <&EvmSelfBalance as InstDowncast>::downcast(is, inst).is_some()
        || <&EvmBaseFee as InstDowncast>::downcast(is, inst).is_some()
        || <&EvmBlobHash as InstDowncast>::downcast(is, inst).is_some()
        || <&EvmBlobBaseFee as InstDowncast>::downcast(is, inst).is_some()
        || <&EvmGas as InstDowncast>::downcast(is, inst).is_some()
        || <&EvmMsize as InstDowncast>::downcast(is, inst).is_some()
}

fn msize_barrier_if_needed(dfg: &DataFlowGraph, inst_id: InstId) -> SmallVec<[MemoryAccess; 2]> {
    if <&EvmMsize as InstDowncast>::downcast(dfg.inst_set(), dfg.inst(inst_id)).is_none() {
        return SmallVec::new();
    }

    smallvec![whole_space(MEMORY, AccessKind::Read)]
}

#[cfg(test)]
mod tests {
    use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

    use super::*;
    use crate::isa::{Isa, evm::Evm};

    fn evm_spaces() -> &'static dyn AddressSpaceInfo {
        Evm::new(TargetTriple::new(
            Architecture::Evm,
            Vendor::Ethereum,
            OperatingSystem::Evm(EvmVersion::Osaka),
        ))
        .address_spaces()
    }

    #[test]
    fn legacy_write_fallback_reads_all_spaces_and_writes_only_mutable_spaces() {
        let effects = fallback_from_legacy_side_effect(SideEffect::Write, evm_spaces());

        assert!(effects.other.contains(OtherEffects::MUTATE));
        for desc in evm_spaces().all_spaces() {
            assert!(
                effects
                    .accesses
                    .iter()
                    .any(|access| access.space == desc.id && access.kind == AccessKind::Read),
                "missing read fallback for {}",
                desc.name
            );

            assert_eq!(
                effects
                    .accesses
                    .iter()
                    .any(|access| access.space == desc.id && access.kind == AccessKind::Write),
                !desc.immutable,
                "unexpected write fallback for {}",
                desc.name
            );
        }
    }

    #[test]
    fn unknown_write_summaries_skip_immutable_spaces() {
        let mut summary = FuncEffectSummary {
            may_write_unknown: true,
            ..FuncEffectSummary::default()
        };
        summary.may_read_spaces.insert(MEMORY);

        let effects = inst_effects_from_func_summary(&summary, evm_spaces());

        for desc in evm_spaces().all_spaces() {
            let has_write = effects
                .accesses
                .iter()
                .any(|access| access.space == desc.id && access.kind == AccessKind::Write);
            assert_eq!(
                has_write, !desc.immutable,
                "unexpected write summary for {}",
                desc.name
            );
        }
    }
}
