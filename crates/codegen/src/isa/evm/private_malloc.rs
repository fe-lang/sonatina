use rustc_hash::FxHashSet;
use sonatina_ir::{
    Function, InstId, InstSetExt, Type, Value, ValueId,
    inst::evm::inst_set::EvmInstKind,
    isa::{Isa, evm::Evm},
    module::ModuleCtx,
};

use super::{memory_plan::WORD_BYTES, prepare::value_imm_u32};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PrivateMallocUseInfo {
    requires_exact_heap_base: bool,
}

pub(crate) struct PrivateMallocUseAnalysis<'a> {
    function: &'a Function,
    module: &'a ModuleCtx,
    isa: &'a Evm,
    pub(crate) malloc: InstId,
    derived_values: FxHashSet<ValueId>,
}

impl<'a> PrivateMallocUseAnalysis<'a> {
    pub(crate) fn new(
        function: &'a Function,
        module: &'a ModuleCtx,
        isa: &'a Evm,
        malloc: InstId,
    ) -> Self {
        let mut analysis = Self {
            function,
            module,
            isa,
            malloc,
            derived_values: function.dfg.inst_results(malloc).iter().copied().collect(),
        };
        analysis.compute_derived_values();
        analysis
    }

    fn analyze_private_address_uses(&self) -> Option<PrivateMallocUseInfo> {
        let mut requires_exact_heap_base = false;
        for block in self.function.layout.iter_block() {
            for inst in self.function.layout.iter_inst(block) {
                if inst != self.malloc && self.inst_uses_derived_value(inst) {
                    requires_exact_heap_base |= self.use_requires_exact_heap_base(inst)?;
                }
            }
        }

        Some(PrivateMallocUseInfo {
            requires_exact_heap_base,
        })
    }

    pub(crate) fn analyze_bounded_private_address_uses(
        &self,
        alloc_size: ValueId,
        exact_heap_base: bool,
    ) -> Option<()> {
        for block in self.function.layout.iter_block() {
            for inst in self.function.layout.iter_inst(block) {
                if inst != self.malloc && self.inst_uses_derived_value(inst) {
                    self.private_use_is_bounded(inst, alloc_size, exact_heap_base)?;
                }
            }
        }

        Some(())
    }

    fn compute_derived_values(&mut self) {
        let mut changed = true;
        while changed {
            changed = false;
            for block in self.function.layout.iter_block() {
                for inst in self.function.layout.iter_inst(block) {
                    if inst != self.malloc && self.inst_uses_derived_value(inst) {
                        changed |= self.add_address_derived_results(inst);
                    }
                }
            }
        }
    }

    fn add_address_derived_results(&mut self, inst: InstId) -> bool {
        match self.resolve(inst) {
            EvmInstKind::Bitcast(_)
            | EvmInstKind::IntToPtr(_)
            | EvmInstKind::PtrToInt(_)
            | EvmInstKind::Gep(_)
            | EvmInstKind::Add(_)
            | EvmInstKind::Sub(_)
            | EvmInstKind::Phi(_) => {
                let mut changed = false;
                for result in self.function.dfg.inst_results(inst) {
                    changed |= self.derived_values.insert(*result);
                }
                changed
            }
            EvmInstKind::Uaddo(_)
            | EvmInstKind::Saddo(_)
            | EvmInstKind::Usubo(_)
            | EvmInstKind::Ssubo(_) => self
                .function
                .dfg
                .inst_results(inst)
                .first()
                .is_some_and(|result| self.derived_values.insert(*result)),
            _ => false,
        }
    }

    fn use_requires_exact_heap_base(&self, inst: InstId) -> Option<bool> {
        if self.inst_derives_address(inst) {
            return self
                .checked_overflow_flag(inst)
                .map_or(Some(false), |flag| {
                    self.checked_overflow_flag_is_private_control(flag)
                });
        }

        match self.resolve(inst) {
            EvmInstKind::Lt(lt) => {
                self.address_overflow_predicate_requires_exact_heap_base(inst, *lt.lhs(), *lt.rhs())
            }
            EvmInstKind::Mstore(mstore) if !self.derived_values.contains(mstore.value()) => {
                Some(false)
            }
            EvmInstKind::EvmMstore(mstore) if !self.derived_values.contains(mstore.value()) => {
                Some(false)
            }
            EvmInstKind::EvmMstore8(mstore) if !self.derived_values.contains(mstore.val()) => {
                Some(false)
            }
            EvmInstKind::EvmReturn(ret) if !self.derived_values.contains(ret.len()) => Some(false),
            EvmInstKind::EvmRevert(revert) if !self.derived_values.contains(revert.len()) => {
                Some(false)
            }
            _ => None,
        }
    }

    fn private_use_is_bounded(
        &self,
        inst: InstId,
        alloc_size: ValueId,
        exact_heap_base: bool,
    ) -> Option<()> {
        if self.inst_derives_address(inst) {
            if let Some(flag) = self.checked_overflow_flag(inst)
                && self.value_is_used(flag)
            {
                return None;
            }
            return Some(());
        }

        match self.resolve(inst) {
            EvmInstKind::Lt(lt)
                if exact_heap_base && self.inst_result_uses_are_private_branches(inst) =>
            {
                self.static_overflow_predicate_is_false(
                    *lt.lhs(),
                    *lt.rhs(),
                    value_imm_u32(self.function, alloc_size)?,
                )
            }
            EvmInstKind::Mload(mload) => {
                self.typed_addr_range_within_alloc(*mload.addr(), *mload.ty(), alloc_size)
            }
            EvmInstKind::Mstore(mstore) if !self.derived_values.contains(mstore.value()) => {
                self.typed_addr_range_within_alloc(*mstore.addr(), *mstore.ty(), alloc_size)
            }
            EvmInstKind::EvmMload(mload) => {
                self.addr_range_within_alloc(*mload.addr(), WORD_BYTES, alloc_size)
            }
            EvmInstKind::EvmMstore(mstore) if !self.derived_values.contains(mstore.value()) => {
                self.addr_range_within_alloc(*mstore.addr(), WORD_BYTES, alloc_size)
            }
            EvmInstKind::EvmMstore8(mstore) if !self.derived_values.contains(mstore.val()) => {
                self.addr_range_within_alloc(*mstore.addr(), 1, alloc_size)
            }
            EvmInstKind::Memzero(memzero) => {
                self.value_addr_range_within_alloc(*memzero.dest(), *memzero.len(), alloc_size)
            }
            EvmInstKind::EvmKeccak256(keccak) => {
                self.value_addr_range_within_alloc(*keccak.addr(), *keccak.len(), alloc_size)
            }
            EvmInstKind::EvmCalldataCopy(copy)
                if self.values_are_not_derived([*copy.data_offset(), *copy.len()]) =>
            {
                self.value_addr_range_within_alloc(*copy.dst_addr(), *copy.len(), alloc_size)
            }
            EvmInstKind::EvmCodeCopy(copy)
                if self.values_are_not_derived([*copy.code_offset(), *copy.len()]) =>
            {
                self.value_addr_range_within_alloc(*copy.dst_addr(), *copy.len(), alloc_size)
            }
            EvmInstKind::EvmReturnDataCopy(copy)
                if self.values_are_not_derived([*copy.data_offset(), *copy.len()]) =>
            {
                self.value_addr_range_within_alloc(*copy.dst_addr(), *copy.len(), alloc_size)
            }
            EvmInstKind::EvmExtCodeCopy(copy)
                if self.values_are_not_derived([
                    *copy.ext_addr(),
                    *copy.code_offset(),
                    *copy.len(),
                ]) =>
            {
                self.value_addr_range_within_alloc(*copy.dst_addr(), *copy.len(), alloc_size)
            }
            EvmInstKind::EvmMcopy(copy) if !self.derived_values.contains(copy.len()) => {
                if self.derived_values.contains(copy.addr())
                    && !self.derived_values.contains(copy.dest())
                    && value_imm_u32(self.function, *copy.len()) != Some(0)
                {
                    return None;
                }
                self.value_addr_range_within_alloc(*copy.dest(), *copy.len(), alloc_size)?;
                self.value_addr_range_within_alloc(*copy.addr(), *copy.len(), alloc_size)
            }
            EvmInstKind::EvmLog0(log) if !self.derived_values.contains(log.len()) => {
                self.value_addr_range_within_alloc(*log.addr(), *log.len(), alloc_size)
            }
            EvmInstKind::EvmLog1(log)
                if self.values_are_not_derived([*log.len(), *log.topic0()]) =>
            {
                self.value_addr_range_within_alloc(*log.addr(), *log.len(), alloc_size)
            }
            EvmInstKind::EvmLog2(log)
                if self.values_are_not_derived([*log.len(), *log.topic0(), *log.topic1()]) =>
            {
                self.value_addr_range_within_alloc(*log.addr(), *log.len(), alloc_size)
            }
            EvmInstKind::EvmLog3(log)
                if self.values_are_not_derived([
                    *log.len(),
                    *log.topic0(),
                    *log.topic1(),
                    *log.topic2(),
                ]) =>
            {
                self.value_addr_range_within_alloc(*log.addr(), *log.len(), alloc_size)
            }
            EvmInstKind::EvmLog4(log)
                if self.values_are_not_derived([
                    *log.len(),
                    *log.topic0(),
                    *log.topic1(),
                    *log.topic2(),
                    *log.topic3(),
                ]) =>
            {
                self.value_addr_range_within_alloc(*log.addr(), *log.len(), alloc_size)
            }
            EvmInstKind::EvmCreate(create)
                if self.values_are_not_derived([*create.val(), *create.len()]) =>
            {
                self.value_addr_range_within_alloc(*create.addr(), *create.len(), alloc_size)
            }
            EvmInstKind::EvmCreate2(create)
                if self.values_are_not_derived([*create.val(), *create.len(), *create.salt()]) =>
            {
                self.value_addr_range_within_alloc(*create.addr(), *create.len(), alloc_size)
            }
            EvmInstKind::EvmCall(call)
                if self.values_are_not_derived([
                    *call.gas(),
                    *call.addr(),
                    *call.val(),
                    *call.arg_len(),
                    *call.ret_len(),
                ]) =>
            {
                self.call_addr_ranges_are_bounded(
                    *call.arg_addr(),
                    *call.arg_len(),
                    *call.ret_addr(),
                    *call.ret_len(),
                    alloc_size,
                )
            }
            EvmInstKind::EvmCallCode(call)
                if self.values_are_not_derived([
                    *call.gas(),
                    *call.addr(),
                    *call.val(),
                    *call.arg_len(),
                    *call.ret_len(),
                ]) =>
            {
                self.call_addr_ranges_are_bounded(
                    *call.arg_addr(),
                    *call.arg_len(),
                    *call.ret_addr(),
                    *call.ret_len(),
                    alloc_size,
                )
            }
            EvmInstKind::EvmDelegateCall(call)
                if self.values_are_not_derived([
                    *call.gas(),
                    *call.ext_addr(),
                    *call.arg_len(),
                    *call.ret_len(),
                ]) =>
            {
                self.call_addr_ranges_are_bounded(
                    *call.arg_addr(),
                    *call.arg_len(),
                    *call.ret_addr(),
                    *call.ret_len(),
                    alloc_size,
                )
            }
            EvmInstKind::EvmStaticCall(call)
                if self.values_are_not_derived([
                    *call.gas(),
                    *call.ext_addr(),
                    *call.arg_len(),
                    *call.ret_len(),
                ]) =>
            {
                self.call_addr_ranges_are_bounded(
                    *call.arg_addr(),
                    *call.arg_len(),
                    *call.ret_addr(),
                    *call.ret_len(),
                    alloc_size,
                )
            }
            EvmInstKind::EvmReturn(ret) if !self.derived_values.contains(ret.len()) => {
                self.value_addr_range_within_alloc(*ret.addr(), *ret.len(), alloc_size)
            }
            EvmInstKind::EvmRevert(revert) if !self.derived_values.contains(revert.len()) => {
                self.value_addr_range_within_alloc(*revert.addr(), *revert.len(), alloc_size)
            }
            _ => None,
        }
    }

    fn call_addr_ranges_are_bounded(
        &self,
        arg_addr: ValueId,
        arg_len: ValueId,
        ret_addr: ValueId,
        ret_len: ValueId,
        alloc_size: ValueId,
    ) -> Option<()> {
        if self.derived_values.contains(&arg_addr)
            && !self.derived_values.contains(&ret_addr)
            && value_imm_u32(self.function, ret_len) != Some(0)
        {
            return None;
        }
        self.value_addr_range_within_alloc(arg_addr, arg_len, alloc_size)?;
        self.value_addr_range_within_alloc(ret_addr, ret_len, alloc_size)
    }

    fn typed_addr_range_within_alloc(
        &self,
        addr: ValueId,
        ty: Type,
        alloc_size: ValueId,
    ) -> Option<()> {
        let size = u32::try_from(self.module.size_of(ty).ok()?).ok()?;
        self.addr_range_within_alloc(addr, size, alloc_size)
    }

    fn addr_range_within_alloc(&self, addr: ValueId, len: u32, alloc_size: ValueId) -> Option<()> {
        if len == 0 || !self.derived_values.contains(&addr) {
            return Some(());
        }

        let offset = u32::try_from(self.derived_const_offset(addr)?).ok()?;
        (offset.checked_add(len)? <= value_imm_u32(self.function, alloc_size)?).then_some(())
    }

    fn value_addr_range_within_alloc(
        &self,
        addr: ValueId,
        len: ValueId,
        alloc_size: ValueId,
    ) -> Option<()> {
        if self.derived_values.contains(&len) {
            return None;
        }
        if let Some(bytes) = value_imm_u32(self.function, len) {
            return self.addr_range_within_alloc(addr, bytes, alloc_size);
        }
        if !self.derived_values.contains(&addr) {
            return Some(());
        }

        // A dynamic or symbolic extent is bounded when it is exactly the
        // allocation's extent and the access starts at its base. Cyclic or
        // mixed-origin pointer phis cannot establish this exact base.
        (len == alloc_size && self.derived_const_offset(addr) == Some(0)).then_some(())
    }

    fn derived_const_offset(&self, value: ValueId) -> Option<i64> {
        self.derived_const_offset_impl(value, &mut FxHashSet::default())
    }

    fn derived_const_offset_impl(
        &self,
        value: ValueId,
        visiting: &mut FxHashSet<ValueId>,
    ) -> Option<i64> {
        if !self.derived_values.contains(&value) || !visiting.insert(value) {
            return None;
        }

        let offset = match self.function.dfg.get_value(value)? {
            Value::Inst {
                inst, result_idx, ..
            } if *inst == self.malloc && *result_idx == 0 => 0,
            Value::Inst {
                inst, result_idx, ..
            } => match self.resolve(*inst) {
                EvmInstKind::Bitcast(cast) => {
                    self.derived_const_offset_impl(*cast.from(), visiting)?
                }
                EvmInstKind::IntToPtr(cast) => {
                    self.derived_const_offset_impl(*cast.from(), visiting)?
                }
                EvmInstKind::PtrToInt(cast) => {
                    self.derived_const_offset_impl(*cast.from(), visiting)?
                }
                EvmInstKind::Add(add) => self.add_const_offset(*add.lhs(), *add.rhs(), visiting)?,
                EvmInstKind::Sub(sub) => {
                    let lhs = self.derived_const_offset_impl(*sub.lhs(), visiting)?;
                    let rhs = i64::from(value_imm_u32(self.function, *sub.rhs())?);
                    lhs.checked_sub(rhs)?
                }
                EvmInstKind::Uaddo(add) if *result_idx == 0 => {
                    self.add_const_offset(*add.lhs(), *add.rhs(), visiting)?
                }
                EvmInstKind::Saddo(add) if *result_idx == 0 => {
                    self.add_const_offset(*add.lhs(), *add.rhs(), visiting)?
                }
                EvmInstKind::Usubo(sub) if *result_idx == 0 => {
                    let lhs = self.derived_const_offset_impl(*sub.lhs(), visiting)?;
                    let rhs = i64::from(value_imm_u32(self.function, *sub.rhs())?);
                    lhs.checked_sub(rhs)?
                }
                EvmInstKind::Ssubo(sub) if *result_idx == 0 => {
                    let lhs = self.derived_const_offset_impl(*sub.lhs(), visiting)?;
                    let rhs = i64::from(value_imm_u32(self.function, *sub.rhs())?);
                    lhs.checked_sub(rhs)?
                }
                EvmInstKind::Phi(phi) => {
                    let mut args = phi.args().iter();
                    let (first, _) = args.next()?;
                    let first_offset = self.derived_const_offset_impl(*first, visiting)?;
                    if args.all(|(arg, _)| {
                        self.derived_const_offset_impl(*arg, visiting) == Some(first_offset)
                    }) {
                        first_offset
                    } else {
                        return None;
                    }
                }
                _ => return None,
            },
            _ => return None,
        };
        visiting.remove(&value);
        Some(offset)
    }

    fn add_const_offset(
        &self,
        lhs: ValueId,
        rhs: ValueId,
        visiting: &mut FxHashSet<ValueId>,
    ) -> Option<i64> {
        if self.derived_values.contains(&lhs) {
            let lhs = self.derived_const_offset_impl(lhs, visiting)?;
            let rhs = i64::from(value_imm_u32(self.function, rhs)?);
            lhs.checked_add(rhs)
        } else if self.derived_values.contains(&rhs) {
            let lhs = i64::from(value_imm_u32(self.function, lhs)?);
            let rhs = self.derived_const_offset_impl(rhs, visiting)?;
            lhs.checked_add(rhs)
        } else {
            None
        }
    }

    fn values_are_not_derived<const N: usize>(&self, values: [ValueId; N]) -> bool {
        values
            .into_iter()
            .all(|value| !self.derived_values.contains(&value))
    }

    fn static_overflow_predicate_is_false(
        &self,
        lhs: ValueId,
        rhs: ValueId,
        alloc_size_bytes: u32,
    ) -> Option<()> {
        if !self.value_is_add_of_base(lhs, rhs) {
            return None;
        }

        let offset = u32::try_from(self.derived_const_offset(lhs)?).ok()?;
        (offset <= alloc_size_bytes).then_some(())
    }

    fn inst_derives_address(&self, inst: InstId) -> bool {
        matches!(
            self.resolve(inst),
            EvmInstKind::Bitcast(_)
                | EvmInstKind::IntToPtr(_)
                | EvmInstKind::PtrToInt(_)
                | EvmInstKind::Gep(_)
                | EvmInstKind::Add(_)
                | EvmInstKind::Sub(_)
                | EvmInstKind::Phi(_)
                | EvmInstKind::Uaddo(_)
                | EvmInstKind::Saddo(_)
                | EvmInstKind::Usubo(_)
                | EvmInstKind::Ssubo(_)
        )
    }

    fn checked_overflow_flag(&self, inst: InstId) -> Option<ValueId> {
        match self.resolve(inst) {
            EvmInstKind::Uaddo(_)
            | EvmInstKind::Saddo(_)
            | EvmInstKind::Usubo(_)
            | EvmInstKind::Ssubo(_) => self.function.dfg.inst_results(inst).get(1).copied(),
            _ => None,
        }
    }

    fn checked_overflow_flag_is_private_control(&self, flag: ValueId) -> Option<bool> {
        let mut used = false;
        for block in self.function.layout.iter_block() {
            for user in self.function.layout.iter_inst(block) {
                if !self.inst_uses_value(user, flag) {
                    continue;
                }

                used = true;
                let EvmInstKind::Br(br) = self.resolve(user) else {
                    return None;
                };
                if br.cond() != &flag
                    || self
                        .function
                        .dfg
                        .inst(user)
                        .collect_values()
                        .iter()
                        .any(|value| self.derived_values.contains(value))
                {
                    return None;
                }
            }
        }
        Some(used)
    }

    fn address_overflow_predicate_requires_exact_heap_base(
        &self,
        inst: InstId,
        lhs: ValueId,
        rhs: ValueId,
    ) -> Option<bool> {
        (self.value_is_add_of_base(lhs, rhs) && self.inst_result_uses_are_private_branches(inst))
            .then_some(true)
    }

    fn value_is_add_of_base(&self, value: ValueId, base: ValueId) -> bool {
        if !self.derived_values.contains(&value) || !self.derived_values.contains(&base) {
            return false;
        }

        let Some(Value::Inst { inst, .. }) = self.function.dfg.get_value(value) else {
            return false;
        };
        let EvmInstKind::Add(add) = self.resolve(*inst) else {
            return false;
        };

        (*add.lhs() == base && self.function.dfg.value_is_imm(*add.rhs()))
            || (*add.rhs() == base && self.function.dfg.value_is_imm(*add.lhs()))
    }

    fn inst_result_uses_are_private_branches(&self, inst: InstId) -> bool {
        let [result] = self.function.dfg.inst_results(inst) else {
            return false;
        };

        for block in self.function.layout.iter_block() {
            for user in self.function.layout.iter_inst(block) {
                if user == inst || !self.inst_uses_value(user, *result) {
                    continue;
                }

                let EvmInstKind::Br(br) = self.resolve(user) else {
                    return false;
                };
                if br.cond() != result {
                    return false;
                }
            }
        }

        true
    }

    pub(crate) fn inst_uses_derived_value(&self, inst: InstId) -> bool {
        self.function
            .dfg
            .inst(inst)
            .collect_values()
            .iter()
            .any(|value| self.derived_values.contains(value))
    }

    pub(crate) fn is_derived_value(&self, value: ValueId) -> bool {
        self.derived_values.contains(&value)
    }

    fn value_is_used(&self, value: ValueId) -> bool {
        self.function.layout.iter_block().any(|block| {
            self.function
                .layout
                .iter_inst(block)
                .any(|inst| self.inst_uses_value(inst, value))
        })
    }

    fn inst_uses_value(&self, inst: InstId, value: ValueId) -> bool {
        self.function
            .dfg
            .inst(inst)
            .collect_values()
            .contains(&value)
    }

    fn resolve(&self, inst: InstId) -> EvmInstKind<'_> {
        self.isa
            .inst_set()
            .resolve_inst(self.function.dfg.inst(inst))
    }
}

pub(crate) fn malloc_private_uses_are_compatible_with_fixed_base(
    function: &Function,
    module: &ModuleCtx,
    isa: &Evm,
    malloc: InstId,
    exact_heap_base: bool,
) -> bool {
    let uses = PrivateMallocUseAnalysis::new(function, module, isa, malloc);
    uses.analyze_private_address_uses()
        .is_some_and(|info| !info.requires_exact_heap_base || exact_heap_base)
        || match uses.resolve(malloc) {
            // Bounded memory consumers, such as hashing a private buffer,
            // can also move with the allocation. This proof still rejects
            // storing the allocation's address into the consumed bytes.
            EvmInstKind::EvmMalloc(alloc) => uses
                .analyze_bounded_private_address_uses(*alloc.size(), exact_heap_base)
                .is_some(),
            _ => false,
        }
}
