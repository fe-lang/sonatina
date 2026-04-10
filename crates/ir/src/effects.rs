use bitflags::bitflags;
use cranelift_entity::entity_impl;
use smallvec::SmallVec;

use crate::{
    DataFlowGraph, I256, Immediate, InstDowncast, InstId, Type, ValueId,
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
};

const EVM_WORD_BYTES: u32 = 32;
const EVM_FREE_PTR_SLOT: i64 = 0x40;

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
    LinearExact {
        addr: ValueId,
        bytes: u32,
        ty: Type,
    },
    LinearExactImm {
        addr: Immediate,
        bytes: u32,
        ty: Type,
    },
    LinearRange {
        addr: ValueId,
        len: ValueId,
    },
    KeyedExact {
        key: ValueId,
        bytes: u32,
    },
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

bitflags! {
    #[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
    pub struct EffectBits: u8 {
        const MEM_READ  = 1 << 0;
        const MEM_WRITE = 1 << 1;
        const OBSERVE   = 1 << 2;
        const MUTATE    = 1 << 3;
        const CONTROL   = 1 << 4;
        const ALLOC     = 1 << 5;
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct InstEffectSummary {
    bits: EffectBits,
}

impl InstEffectSummary {
    pub fn from_bits(bits: EffectBits) -> Self {
        Self { bits }
    }

    pub fn bits(self) -> EffectBits {
        self.bits
    }

    pub fn has_effect(self) -> bool {
        !self.bits.is_empty()
    }

    pub fn may_read_memory(self) -> bool {
        self.bits.contains(EffectBits::MEM_READ)
    }

    pub fn may_write_memory(self) -> bool {
        self.bits.contains(EffectBits::MEM_WRITE)
    }

    pub fn may_observe_state(self) -> bool {
        self.bits
            .intersects(EffectBits::MEM_READ | EffectBits::OBSERVE)
    }

    pub fn may_mutate_state(self) -> bool {
        self.bits
            .intersects(EffectBits::MEM_WRITE | EffectBits::MUTATE | EffectBits::ALLOC)
    }

    pub fn may_transfer_control(self) -> bool {
        self.bits.contains(EffectBits::CONTROL)
    }

    pub fn may_allocate(self) -> bool {
        self.bits.contains(EffectBits::ALLOC)
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct InstEffects {
    pub accesses: SmallVec<[MemoryAccess; 2]>,
    pub other: OtherEffects,
}

impl InstEffects {
    pub fn summary(&self) -> InstEffectSummary {
        let mut bits = EffectBits::default();
        for access in &self.accesses {
            match access.kind {
                AccessKind::Read => bits.insert(EffectBits::MEM_READ),
                AccessKind::Write => bits.insert(EffectBits::MEM_WRITE),
            }
        }

        if self.other.contains(OtherEffects::OBSERVE) {
            bits.insert(EffectBits::OBSERVE);
        }
        if self.other.contains(OtherEffects::MUTATE) {
            bits.insert(EffectBits::MUTATE);
        }
        if self.other.contains(OtherEffects::CONTROL) {
            bits.insert(EffectBits::CONTROL);
        }
        if self.other.contains(OtherEffects::ALLOC) {
            bits.insert(EffectBits::ALLOC);
        }

        InstEffectSummary::from_bits(bits)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EffectCostClass {
    Pure,
    Observe,
    Mutate,
    Control,
    Return,
}

impl EffectCostClass {
    pub const fn base_cost(self) -> i32 {
        match self {
            Self::Pure => 1,
            Self::Observe => 2,
            Self::Mutate => 3,
            // Keep non-return control flow more expensive than a plain return so
            // inliner profitability matches the pre-refactor side-effect model.
            Self::Control => 2,
            Self::Return => 1,
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
    pub may_commit_visible_writes: bool,
    pub will_return: bool,
    pub will_terminate: bool,
}

impl FuncEffectSummary {
    pub fn unknown_call() -> Self {
        Self {
            may_read_unknown: true,
            may_write_unknown: true,
            may_commit_visible_writes: true,
            ..Self::default()
        }
    }

    pub fn effect_summary(&self) -> InstEffectSummary {
        let mut bits = EffectBits::default();

        if self.may_read_memory() {
            bits.insert(EffectBits::MEM_READ);
        }
        if self.may_write_memory() {
            bits.insert(EffectBits::MEM_WRITE);
        }
        if self.other.contains(OtherEffects::OBSERVE) {
            bits.insert(EffectBits::OBSERVE);
        }
        if self.other.contains(OtherEffects::MUTATE) {
            bits.insert(EffectBits::MUTATE);
        }
        if self.may_transfer_control() {
            bits.insert(EffectBits::CONTROL);
        }
        if self.other.contains(OtherEffects::ALLOC) {
            bits.insert(EffectBits::ALLOC);
        }

        InstEffectSummary::from_bits(bits)
    }

    pub fn always_returns(&self) -> bool {
        self.will_return
    }

    pub fn never_returns(&self) -> bool {
        self.noreturn
    }

    pub fn always_terminates(&self) -> bool {
        self.will_terminate
    }

    pub fn may_return_to_caller(&self) -> bool {
        !self.never_returns()
    }

    pub fn may_read_memory(&self) -> bool {
        !self.may_read_spaces.is_empty() || self.may_read_unknown
    }

    pub fn may_write_memory(&self) -> bool {
        !self.may_write_spaces.is_empty() || self.may_write_unknown
    }

    pub fn may_observe_state(&self) -> bool {
        self.may_read_memory() || self.other.contains(OtherEffects::OBSERVE)
    }

    pub fn may_mutate_state(&self) -> bool {
        self.may_write_memory()
            || self
                .other
                .intersects(OtherEffects::MUTATE | OtherEffects::ALLOC)
    }

    pub fn may_transfer_control(&self) -> bool {
        self.never_returns() || !self.always_returns()
    }

    pub fn can_elide_if_unused_call(&self) -> bool {
        self.always_returns() && !self.may_mutate_state()
    }

    pub fn is_committing_noreturn(&self) -> bool {
        self.never_returns() && self.may_commit_visible_writes
    }

    pub fn union_with(&mut self, other: &Self) {
        self.may_read_spaces.union_with(&other.may_read_spaces);
        self.may_write_spaces.union_with(&other.may_write_spaces);
        self.may_read_unknown |= other.may_read_unknown;
        self.may_write_unknown |= other.may_write_unknown;
        self.other |= other.other;
        self.noreturn |= other.noreturn;
        self.may_commit_visible_writes |= other.may_commit_visible_writes;
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

pub fn summarize_inst_effects(dfg: &DataFlowGraph, inst_id: InstId) -> InstEffectSummary {
    classify_inst_effects_with(dfg, inst_id, SummaryEffectSink::default())
}

pub fn classify_inst_effects(dfg: &DataFlowGraph, inst_id: InstId) -> InstEffects {
    classify_inst_effects_with(dfg, inst_id, DetailedEffectSink::default())
}

trait EffectSink {
    type Output;

    fn read_exact(&mut self, space: AddressSpaceId, addr: ValueId, bytes: u32, ty: Type);
    fn write_exact(&mut self, space: AddressSpaceId, addr: ValueId, bytes: u32, ty: Type);
    fn read_exact_imm(&mut self, space: AddressSpaceId, addr: Immediate, bytes: u32, ty: Type);
    fn write_exact_imm(&mut self, space: AddressSpaceId, addr: Immediate, bytes: u32, ty: Type);
    fn read_keyed(&mut self, space: AddressSpaceId, key: ValueId, bytes: u32);
    fn write_keyed(&mut self, space: AddressSpaceId, key: ValueId, bytes: u32);
    fn read_range(&mut self, space: AddressSpaceId, addr: ValueId, len: ValueId);
    fn write_range(&mut self, space: AddressSpaceId, addr: ValueId, len: ValueId);
    fn read_whole(&mut self, space: AddressSpaceId);
    fn write_whole(&mut self, space: AddressSpaceId);
    fn add_other(&mut self, other: OtherEffects);
    fn finish(self) -> Self::Output;
}

#[derive(Default)]
struct DetailedEffectSink {
    effects: InstEffects,
}

impl DetailedEffectSink {
    fn push_access(&mut self, access: MemoryAccess) {
        self.effects.accesses.push(access);
    }
}

impl EffectSink for DetailedEffectSink {
    type Output = InstEffects;

    fn read_exact(&mut self, space: AddressSpaceId, addr: ValueId, bytes: u32, ty: Type) {
        self.push_access(MemoryAccess {
            space,
            kind: AccessKind::Read,
            must_happen: true,
            loc: AccessLoc::LinearExact { addr, bytes, ty },
        });
    }

    fn write_exact(&mut self, space: AddressSpaceId, addr: ValueId, bytes: u32, ty: Type) {
        self.push_access(MemoryAccess {
            space,
            kind: AccessKind::Write,
            must_happen: true,
            loc: AccessLoc::LinearExact { addr, bytes, ty },
        });
    }

    fn read_exact_imm(&mut self, space: AddressSpaceId, addr: Immediate, bytes: u32, ty: Type) {
        self.push_access(MemoryAccess {
            space,
            kind: AccessKind::Read,
            must_happen: true,
            loc: AccessLoc::LinearExactImm { addr, bytes, ty },
        });
    }

    fn write_exact_imm(&mut self, space: AddressSpaceId, addr: Immediate, bytes: u32, ty: Type) {
        self.push_access(MemoryAccess {
            space,
            kind: AccessKind::Write,
            must_happen: true,
            loc: AccessLoc::LinearExactImm { addr, bytes, ty },
        });
    }

    fn read_keyed(&mut self, space: AddressSpaceId, key: ValueId, bytes: u32) {
        self.push_access(MemoryAccess {
            space,
            kind: AccessKind::Read,
            must_happen: true,
            loc: AccessLoc::KeyedExact { key, bytes },
        });
    }

    fn write_keyed(&mut self, space: AddressSpaceId, key: ValueId, bytes: u32) {
        self.push_access(MemoryAccess {
            space,
            kind: AccessKind::Write,
            must_happen: true,
            loc: AccessLoc::KeyedExact { key, bytes },
        });
    }

    fn read_range(&mut self, space: AddressSpaceId, addr: ValueId, len: ValueId) {
        self.push_access(MemoryAccess {
            space,
            kind: AccessKind::Read,
            must_happen: false,
            loc: AccessLoc::LinearRange { addr, len },
        });
    }

    fn write_range(&mut self, space: AddressSpaceId, addr: ValueId, len: ValueId) {
        self.push_access(MemoryAccess {
            space,
            kind: AccessKind::Write,
            must_happen: false,
            loc: AccessLoc::LinearRange { addr, len },
        });
    }

    fn read_whole(&mut self, space: AddressSpaceId) {
        self.push_access(MemoryAccess {
            space,
            kind: AccessKind::Read,
            must_happen: false,
            loc: AccessLoc::WholeSpace,
        });
    }

    fn write_whole(&mut self, space: AddressSpaceId) {
        self.push_access(MemoryAccess {
            space,
            kind: AccessKind::Write,
            must_happen: false,
            loc: AccessLoc::WholeSpace,
        });
    }

    fn add_other(&mut self, other: OtherEffects) {
        self.effects.other |= other;
    }

    fn finish(self) -> Self::Output {
        self.effects
    }
}

#[derive(Default)]
struct SummaryEffectSink {
    bits: EffectBits,
}

impl SummaryEffectSink {
    fn record_access(&mut self, kind: AccessKind) {
        match kind {
            AccessKind::Read => self.bits.insert(EffectBits::MEM_READ),
            AccessKind::Write => self.bits.insert(EffectBits::MEM_WRITE),
        }
    }
}

impl EffectSink for SummaryEffectSink {
    type Output = InstEffectSummary;

    fn read_exact(&mut self, _: AddressSpaceId, _: ValueId, _: u32, _: Type) {
        self.record_access(AccessKind::Read);
    }

    fn write_exact(&mut self, _: AddressSpaceId, _: ValueId, _: u32, _: Type) {
        self.record_access(AccessKind::Write);
    }

    fn read_exact_imm(&mut self, _: AddressSpaceId, _: Immediate, _: u32, _: Type) {
        self.record_access(AccessKind::Read);
    }

    fn write_exact_imm(&mut self, _: AddressSpaceId, _: Immediate, _: u32, _: Type) {
        self.record_access(AccessKind::Write);
    }

    fn read_keyed(&mut self, _: AddressSpaceId, _: ValueId, _: u32) {
        self.record_access(AccessKind::Read);
    }

    fn write_keyed(&mut self, _: AddressSpaceId, _: ValueId, _: u32) {
        self.record_access(AccessKind::Write);
    }

    fn read_range(&mut self, _: AddressSpaceId, _: ValueId, _: ValueId) {
        self.record_access(AccessKind::Read);
    }

    fn write_range(&mut self, _: AddressSpaceId, _: ValueId, _: ValueId) {
        self.record_access(AccessKind::Write);
    }

    fn read_whole(&mut self, _: AddressSpaceId) {
        self.record_access(AccessKind::Read);
    }

    fn write_whole(&mut self, _: AddressSpaceId) {
        self.record_access(AccessKind::Write);
    }

    fn add_other(&mut self, other: OtherEffects) {
        if other.contains(OtherEffects::OBSERVE) {
            self.bits.insert(EffectBits::OBSERVE);
        }
        if other.contains(OtherEffects::MUTATE) {
            self.bits.insert(EffectBits::MUTATE);
        }
        if other.contains(OtherEffects::CONTROL) {
            self.bits.insert(EffectBits::CONTROL);
        }
        if other.contains(OtherEffects::ALLOC) {
            self.bits.insert(EffectBits::ALLOC);
        }
    }

    fn finish(self) -> Self::Output {
        InstEffectSummary::from_bits(self.bits)
    }
}

fn classify_inst_effects_with<S: EffectSink>(
    dfg: &DataFlowGraph,
    inst_id: InstId,
    mut sink: S,
) -> S::Output {
    let inst = dfg.inst(inst_id);
    let is = dfg.inst_set();
    let spaces = dfg.ctx.address_spaces();

    if let Some(mload) = <&data::Mload as InstDowncast>::downcast(is, inst) {
        let bytes = dfg.ctx.size_of_unchecked(*mload.ty()) as u32;
        sink.read_exact(spaces.default_space(), *mload.addr(), bytes, *mload.ty());
        return sink.finish();
    }

    if let Some(mstore) = <&data::Mstore as InstDowncast>::downcast(is, inst) {
        let bytes = dfg.ctx.size_of_unchecked(*mstore.ty()) as u32;
        sink.write_exact(spaces.default_space(), *mstore.addr(), bytes, *mstore.ty());
        return sink.finish();
    }

    if <&data::Alloca as InstDowncast>::downcast(is, inst).is_some() {
        sink.add_other(OtherEffects::ALLOC);
        return sink.finish();
    }

    if <&data::ObjAlloc as InstDowncast>::downcast(is, inst).is_some() {
        sink.add_other(OtherEffects::ALLOC);
        return sink.finish();
    }

    if <&data::ObjLoad as InstDowncast>::downcast(is, inst).is_some() {
        sink.add_other(OtherEffects::OBSERVE);
        return sink.finish();
    }

    if <&data::ObjStore as InstDowncast>::downcast(is, inst).is_some() {
        sink.add_other(OtherEffects::MUTATE);
        return sink.finish();
    }

    if <&data::EnumGetTag as InstDowncast>::downcast(is, inst).is_some() {
        sink.add_other(OtherEffects::OBSERVE);
        return sink.finish();
    }

    if <&data::EnumAssertVariant as InstDowncast>::downcast(is, inst).is_some() {
        sink.add_other(OtherEffects::OBSERVE | OtherEffects::CONTROL);
        return sink.finish();
    }

    if <&data::EnumAssertVariantRef as InstDowncast>::downcast(is, inst).is_some() {
        sink.add_other(OtherEffects::OBSERVE);
        return sink.finish();
    }

    if <&data::EnumSetTag as InstDowncast>::downcast(is, inst).is_some()
        || <&data::EnumWriteVariant as InstDowncast>::downcast(is, inst).is_some()
    {
        sink.add_other(OtherEffects::MUTATE);
        return sink.finish();
    }

    if let Some(call) = dfg.call_info(inst_id) {
        record_func_summary(&mut sink, &dfg.ctx.func_effects(call.callee()), spaces);
        return sink.finish();
    }

    if let Some(mstore8) = <&EvmMstore8 as InstDowncast>::downcast(is, inst) {
        sink.write_exact(MEMORY, *mstore8.addr(), 1, Type::I8);
        return sink.finish();
    }

    if let Some(sload) = <&EvmSload as InstDowncast>::downcast(is, inst) {
        sink.read_keyed(STORAGE, *sload.key(), EVM_WORD_BYTES);
        return sink.finish();
    }

    if let Some(sstore) = <&EvmSstore as InstDowncast>::downcast(is, inst) {
        sink.write_keyed(STORAGE, *sstore.key(), EVM_WORD_BYTES);
        return sink.finish();
    }

    if let Some(tload) = <&EvmTload as InstDowncast>::downcast(is, inst) {
        sink.read_keyed(TRANSIENT, *tload.key(), EVM_WORD_BYTES);
        return sink.finish();
    }

    if let Some(tstore) = <&EvmTstore as InstDowncast>::downcast(is, inst) {
        sink.write_keyed(TRANSIENT, *tstore.key(), EVM_WORD_BYTES);
        return sink.finish();
    }

    if let Some(calldata_load) = <&EvmCalldataLoad as InstDowncast>::downcast(is, inst) {
        let ty = dfg
            .inst_result(inst_id)
            .map(|value| dfg.value_ty(value))
            .unwrap_or(Type::I256);
        sink.read_exact(CALLDATA, *calldata_load.data_offset(), EVM_WORD_BYTES, ty);
        return sink.finish();
    }

    if let Some(keccak) = <&EvmKeccak256 as InstDowncast>::downcast(is, inst) {
        sink.read_range(MEMORY, *keccak.addr(), *keccak.len());
        return sink.finish();
    }

    if let Some(copy) = <&EvmCalldataCopy as InstDowncast>::downcast(is, inst) {
        sink.read_range(CALLDATA, *copy.data_offset(), *copy.len());
        sink.write_range(MEMORY, *copy.dst_addr(), *copy.len());
        return sink.finish();
    }

    if let Some(copy) = <&EvmCodeCopy as InstDowncast>::downcast(is, inst) {
        sink.read_range(CODE, *copy.code_offset(), *copy.len());
        sink.write_range(MEMORY, *copy.dst_addr(), *copy.len());
        return sink.finish();
    }

    if let Some(copy) = <&EvmReturnDataCopy as InstDowncast>::downcast(is, inst) {
        sink.read_range(RETURNDATA, *copy.data_offset(), *copy.len());
        sink.write_range(MEMORY, *copy.dst_addr(), *copy.len());
        return sink.finish();
    }

    if let Some(copy) = <&EvmExtCodeCopy as InstDowncast>::downcast(is, inst) {
        sink.write_range(MEMORY, *copy.dst_addr(), *copy.len());
        sink.add_other(OtherEffects::OBSERVE);
        return sink.finish();
    }

    if let Some(mcopy) = <&EvmMcopy as InstDowncast>::downcast(is, inst) {
        sink.read_range(MEMORY, *mcopy.addr(), *mcopy.len());
        sink.write_range(MEMORY, *mcopy.dest(), *mcopy.len());
        return sink.finish();
    }

    if let Some(log) = <&EvmLog0 as InstDowncast>::downcast(is, inst) {
        record_read_memory_with_other(&mut sink, *log.addr(), *log.len(), OtherEffects::MUTATE);
        return sink.finish();
    }

    if let Some(log) = <&EvmLog1 as InstDowncast>::downcast(is, inst) {
        record_read_memory_with_other(&mut sink, *log.addr(), *log.len(), OtherEffects::MUTATE);
        return sink.finish();
    }

    if let Some(log) = <&EvmLog2 as InstDowncast>::downcast(is, inst) {
        record_read_memory_with_other(&mut sink, *log.addr(), *log.len(), OtherEffects::MUTATE);
        return sink.finish();
    }

    if let Some(log) = <&EvmLog3 as InstDowncast>::downcast(is, inst) {
        record_read_memory_with_other(&mut sink, *log.addr(), *log.len(), OtherEffects::MUTATE);
        return sink.finish();
    }

    if let Some(log) = <&EvmLog4 as InstDowncast>::downcast(is, inst) {
        record_read_memory_with_other(&mut sink, *log.addr(), *log.len(), OtherEffects::MUTATE);
        return sink.finish();
    }

    if let Some(ret) = <&EvmReturn as InstDowncast>::downcast(is, inst) {
        record_read_memory_with_other(&mut sink, *ret.addr(), *ret.len(), OtherEffects::CONTROL);
        return sink.finish();
    }

    if let Some(revert) = <&EvmRevert as InstDowncast>::downcast(is, inst) {
        record_read_memory_with_other(
            &mut sink,
            *revert.addr(),
            *revert.len(),
            OtherEffects::CONTROL,
        );
        return sink.finish();
    }

    if let Some(create) = <&EvmCreate as InstDowncast>::downcast(is, inst) {
        record_create_effects(&mut sink, *create.addr(), *create.len());
        return sink.finish();
    }

    if let Some(create) = <&EvmCreate2 as InstDowncast>::downcast(is, inst) {
        record_create_effects(&mut sink, *create.addr(), *create.len());
        return sink.finish();
    }

    if let Some(call) = <&EvmCall as InstDowncast>::downcast(is, inst) {
        record_external_call_effects(
            &mut sink,
            *call.arg_addr(),
            *call.arg_len(),
            *call.ret_addr(),
            *call.ret_offset(),
            true,
        );
        return sink.finish();
    }

    if let Some(call) = <&EvmCallCode as InstDowncast>::downcast(is, inst) {
        record_external_call_effects(
            &mut sink,
            *call.arg_addr(),
            *call.arg_len(),
            *call.ret_addr(),
            *call.ret_offset(),
            true,
        );
        return sink.finish();
    }

    if let Some(call) = <&EvmDelegateCall as InstDowncast>::downcast(is, inst) {
        record_external_call_effects(
            &mut sink,
            *call.arg_addr(),
            *call.arg_len(),
            *call.ret_addr(),
            *call.ret_len(),
            true,
        );
        return sink.finish();
    }

    if let Some(call) = <&EvmStaticCall as InstDowncast>::downcast(is, inst) {
        record_external_call_effects(
            &mut sink,
            *call.arg_addr(),
            *call.arg_len(),
            *call.ret_addr(),
            *call.ret_len(),
            false,
        );
        return sink.finish();
    }

    if <&EvmMalloc as InstDowncast>::downcast(is, inst).is_some() {
        record_malloc_effects(&mut sink);
        return sink.finish();
    }

    if <&EvmStop as InstDowncast>::downcast(is, inst).is_some()
        || <&EvmInvalid as InstDowncast>::downcast(is, inst).is_some()
        || <&control_flow::Unreachable as InstDowncast>::downcast(is, inst).is_some()
        || <&control_flow::Return as InstDowncast>::downcast(is, inst).is_some()
    {
        sink.add_other(OtherEffects::CONTROL);
        return sink.finish();
    }

    if <&EvmSelfDestruct as InstDowncast>::downcast(is, inst).is_some() {
        sink.add_other(OtherEffects::MUTATE | OtherEffects::CONTROL);
        return sink.finish();
    }

    if is_observe_only_evm_inst(dfg, inst_id) {
        if <&EvmMsize as InstDowncast>::downcast(is, inst).is_some() {
            sink.read_whole(MEMORY);
        }
        sink.add_other(OtherEffects::OBSERVE);
        return sink.finish();
    }

    record_fallback_from_declared_effect_hint(&mut sink, inst.declared_effect_hint(), spaces);
    sink.finish()
}

fn record_read_memory_with_other<S: EffectSink>(
    sink: &mut S,
    addr: ValueId,
    len: ValueId,
    other: OtherEffects,
) {
    sink.read_range(MEMORY, addr, len);
    sink.add_other(other);
}

fn record_external_call_effects<S: EffectSink>(
    sink: &mut S,
    arg_addr: ValueId,
    arg_len: ValueId,
    ret_addr: ValueId,
    ret_len: ValueId,
    may_write_state: bool,
) {
    sink.read_range(MEMORY, arg_addr, arg_len);
    sink.write_range(MEMORY, ret_addr, ret_len);
    sink.read_whole(STORAGE);
    sink.read_whole(TRANSIENT);
    sink.write_whole(RETURNDATA);

    if may_write_state {
        sink.write_whole(STORAGE);
        sink.write_whole(TRANSIENT);
        sink.add_other(OtherEffects::MUTATE);
    } else {
        sink.add_other(OtherEffects::OBSERVE);
    }
}

fn record_create_effects<S: EffectSink>(sink: &mut S, addr: ValueId, len: ValueId) {
    sink.read_range(MEMORY, addr, len);
    sink.read_whole(STORAGE);
    sink.write_whole(STORAGE);
    sink.read_whole(TRANSIENT);
    sink.write_whole(TRANSIENT);
    sink.write_whole(RETURNDATA);
    sink.add_other(OtherEffects::MUTATE);
}

fn record_malloc_effects<S: EffectSink>(sink: &mut S) {
    let addr = Immediate::from_i256(I256::from(EVM_FREE_PTR_SLOT), Type::I256);
    // Conservatively model every evm_malloc as touching the free-pointer slot,
    // even though transient malloc lowering can avoid memory[0x40].
    sink.read_exact_imm(MEMORY, addr, EVM_WORD_BYTES, Type::I256);
    sink.write_exact_imm(MEMORY, addr, EVM_WORD_BYTES, Type::I256);
    sink.add_other(OtherEffects::ALLOC);
}

#[cfg(test)]
fn inst_effects_from_func_summary(
    summary: &FuncEffectSummary,
    spaces: &dyn AddressSpaceInfo,
) -> InstEffects {
    let mut sink = DetailedEffectSink::default();
    record_func_summary(&mut sink, summary, spaces);
    sink.finish()
}

fn record_func_summary<S: EffectSink>(
    sink: &mut S,
    summary: &FuncEffectSummary,
    spaces: &dyn AddressSpaceInfo,
) {
    sink.add_other(summary.other);

    if summary.noreturn || !summary.will_return {
        sink.add_other(OtherEffects::CONTROL);
    }

    for space in summary.may_read_spaces.iter() {
        sink.read_whole(space);
    }
    for space in summary.may_write_spaces.iter() {
        sink.write_whole(space);
    }

    if summary.may_read_unknown {
        for desc in spaces.all_spaces() {
            if !summary.may_read_spaces.contains(desc.id) {
                sink.read_whole(desc.id);
            }
        }
    }

    if summary.may_write_unknown {
        for desc in spaces.all_spaces() {
            if !desc.immutable && !summary.may_write_spaces.contains(desc.id) {
                sink.write_whole(desc.id);
            }
        }
    }
}

#[cfg(test)]
fn fallback_from_declared_effect_hint(
    side_effect: SideEffect,
    spaces: &dyn AddressSpaceInfo,
) -> InstEffects {
    let mut sink = DetailedEffectSink::default();
    record_fallback_from_declared_effect_hint(&mut sink, side_effect, spaces);
    sink.finish()
}

fn record_fallback_from_declared_effect_hint<S: EffectSink>(
    sink: &mut S,
    side_effect: SideEffect,
    spaces: &dyn AddressSpaceInfo,
) {
    match side_effect {
        SideEffect::None => {}
        SideEffect::Read => {
            for desc in spaces.all_spaces() {
                sink.read_whole(desc.id);
            }
            sink.add_other(OtherEffects::OBSERVE);
        }
        SideEffect::Write => {
            for desc in spaces.all_spaces() {
                sink.read_whole(desc.id);
                if !desc.immutable {
                    sink.write_whole(desc.id);
                }
            }
            sink.add_other(OtherEffects::MUTATE);
        }
        SideEffect::Control => sink.add_other(OtherEffects::CONTROL),
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

#[cfg(test)]
mod tests {
    use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

    use super::*;
    use crate::{
        builder::test_util::*,
        inst::{
            control_flow::Return,
            data::{Alloca, ObjAlloc, ObjLoad, ObjStore},
            evm::{EvmMalloc, EvmSelfDestruct},
        },
        isa::{Isa, evm::Evm},
    };

    fn inst_id_for<T>(func: &crate::Function) -> InstId
    where
        for<'a> &'a T: InstDowncast<'a>,
    {
        let is = func.inst_set();
        func.layout
            .iter_block()
            .flat_map(|block| func.layout.iter_inst(block))
            .find(|&inst| <&T as InstDowncast>::downcast(is, func.dfg.inst(inst)).is_some())
            .expect("instruction should exist")
    }

    fn effects_for_inst<T>(func: &crate::Function) -> InstEffects
    where
        for<'a> &'a T: InstDowncast<'a>,
    {
        let inst = inst_id_for::<T>(func);
        func.dfg.effects(inst)
    }

    fn summary_for_inst<T>(func: &crate::Function) -> InstEffectSummary
    where
        for<'a> &'a T: InstDowncast<'a>,
    {
        let inst = inst_id_for::<T>(func);
        func.dfg.effect_summary(inst)
    }

    fn has_access(effects: &InstEffects, space: AddressSpaceId, kind: AccessKind) -> bool {
        effects
            .accesses
            .iter()
            .any(|access| access.space == space && access.kind == kind)
    }

    fn build_create_func() -> crate::Function {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::I256);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let ptr_ty = builder.ptr_type(Type::I256);
        let addr = builder.insert_inst_with(|| Alloca::new(is, Type::I256), ptr_ty);
        let zero = builder.make_imm_value(0i32);
        let created = builder.insert_inst_with(|| EvmCreate::new(is, zero, addr, zero), Type::I256);
        builder.insert_inst_no_result_with(|| Return::new_single(is, created));
        builder.seal_all();

        builder.func
    }

    fn build_create2_func() -> crate::Function {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::I256);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let ptr_ty = builder.ptr_type(Type::I256);
        let addr = builder.insert_inst_with(|| Alloca::new(is, Type::I256), ptr_ty);
        let zero = builder.make_imm_value(0i32);
        let created =
            builder.insert_inst_with(|| EvmCreate2::new(is, zero, addr, zero, zero), Type::I256);
        builder.insert_inst_no_result_with(|| Return::new_single(is, created));
        builder.seal_all();

        builder.func
    }

    fn build_malloc_func() -> crate::Function {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], mb.ptr_type(Type::I8));
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let size = builder.make_imm_value(Immediate::from_i256(I256::from(32), Type::I256));
        let ptr = builder.insert_inst_with(|| EvmMalloc::new(is, size), mb.ptr_type(Type::I8));
        builder.insert_inst_no_result_with(|| Return::new_single(is, ptr));
        builder.seal_all();

        builder.func
    }

    fn build_object_memory_func() -> crate::Function {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::I256);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let obj =
            builder.insert_inst_with(|| ObjAlloc::new(is, Type::I256), mb.objref_type(Type::I256));
        let one = builder.make_imm_value(1i32);
        builder.insert_inst_no_result_with(|| ObjStore::new(is, obj, one));
        let loaded = builder.insert_inst_with(|| ObjLoad::new(is, obj), Type::I256);
        builder.insert_inst_no_result_with(|| Return::new_single(is, loaded));
        builder.seal_all();

        builder.func
    }

    fn build_self_destruct_func() -> crate::Function {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::I256);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let zero = builder.make_imm_value(0i32);
        builder.insert_inst_no_result_with(|| EvmSelfDestruct::new(is, zero));
        builder.seal_all();

        builder.func
    }

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
        let effects = fallback_from_declared_effect_hint(SideEffect::Write, evm_spaces());

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

    #[test]
    fn evm_create_effects_include_reentrant_state_and_returndata_barriers() {
        let func = build_create_func();
        let effects = effects_for_inst::<EvmCreate>(&func);

        assert!(has_access(&effects, MEMORY, AccessKind::Read));
        assert!(has_access(&effects, STORAGE, AccessKind::Read));
        assert!(has_access(&effects, STORAGE, AccessKind::Write));
        assert!(has_access(&effects, TRANSIENT, AccessKind::Read));
        assert!(has_access(&effects, TRANSIENT, AccessKind::Write));
        assert!(has_access(&effects, RETURNDATA, AccessKind::Write));
        assert!(!has_access(&effects, MEMORY, AccessKind::Write));
        assert_eq!(effects.other, OtherEffects::MUTATE);
    }

    #[test]
    fn evm_create2_effects_include_reentrant_state_and_returndata_barriers() {
        let func = build_create2_func();
        let effects = effects_for_inst::<EvmCreate2>(&func);

        assert!(has_access(&effects, MEMORY, AccessKind::Read));
        assert!(has_access(&effects, STORAGE, AccessKind::Read));
        assert!(has_access(&effects, STORAGE, AccessKind::Write));
        assert!(has_access(&effects, TRANSIENT, AccessKind::Read));
        assert!(has_access(&effects, TRANSIENT, AccessKind::Write));
        assert!(has_access(&effects, RETURNDATA, AccessKind::Write));
        assert!(!has_access(&effects, MEMORY, AccessKind::Write));
        assert_eq!(effects.other, OtherEffects::MUTATE);
    }

    #[test]
    fn evm_malloc_effects_touch_free_ptr_slot_without_whole_space_barriers() {
        let func = build_malloc_func();
        let effects = effects_for_inst::<EvmMalloc>(&func);

        assert_eq!(effects.accesses.len(), 2);
        assert!(effects.other.contains(OtherEffects::ALLOC));
        assert!(
            effects
                .accesses
                .iter()
                .all(|access| !matches!(access.loc, AccessLoc::WholeSpace))
        );

        let free_ptr = Immediate::from_i256(I256::from(EVM_FREE_PTR_SLOT), Type::I256);
        let [read, write] = effects.accesses.as_slice() else {
            panic!("expected exactly one read and one write");
        };

        for (access, kind) in [(read, AccessKind::Read), (write, AccessKind::Write)] {
            assert_eq!(access.space, MEMORY);
            assert_eq!(access.kind, kind);
            assert!(access.must_happen);
            match access.loc {
                AccessLoc::LinearExactImm { addr, bytes, ty } => {
                    assert_eq!(addr, free_ptr);
                    assert_eq!(bytes, EVM_WORD_BYTES);
                    assert_eq!(ty, Type::I256);
                }
                ref other => panic!("expected exact immediate access, got {other:?}"),
            }
        }
    }

    #[test]
    fn obj_alloc_effects_are_tracked_as_alloc() {
        let func = build_object_memory_func();
        let effects = effects_for_inst::<ObjAlloc>(&func);

        assert!(effects.accesses.is_empty());
        assert_eq!(effects.other, OtherEffects::ALLOC);
    }

    #[test]
    fn obj_load_store_effects_do_not_fall_back_to_whole_space_barriers() {
        let func = build_object_memory_func();

        let load_effects = effects_for_inst::<ObjLoad>(&func);
        assert!(load_effects.accesses.is_empty());
        assert_eq!(load_effects.other, OtherEffects::OBSERVE);

        let store_effects = effects_for_inst::<ObjStore>(&func);
        assert!(store_effects.accesses.is_empty());
        assert_eq!(store_effects.other, OtherEffects::MUTATE);
    }

    #[test]
    fn self_destruct_summary_preserves_control_and_mutation_bits() {
        let func = build_self_destruct_func();
        let summary = summary_for_inst::<EvmSelfDestruct>(&func);

        assert_eq!(
            summary,
            effects_for_inst::<EvmSelfDestruct>(&func).summary()
        );
        assert!(summary.may_mutate_state());
        assert!(summary.may_transfer_control());
        assert!(summary.may_write_memory() || summary.may_mutate_state());
    }
}
