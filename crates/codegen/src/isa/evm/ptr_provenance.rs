use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use sonatina_ir::{
    Function, InstId, InstSetExt, Type, ValueId,
    inst::evm::inst_set::EvmInstKind,
    isa::{Isa, evm::Evm},
    module::{FuncRef, ModuleCtx},
    types::{CompoundType, CompoundTypeRef},
};

use crate::analysis::memory_access::{BaseObject, MemoryAccessAnalysis};

use super::{prepare::value_imm_u32, ptr_escape::PtrEscapeSummary};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum PtrBase {
    Arg(u32),
    Alloca(InstId),
    Malloc(InstId),
}

impl PtrBase {
    fn key(self) -> (u8, u32) {
        match self {
            PtrBase::Arg(i) => (0, i),
            PtrBase::Alloca(inst) => (1, inst.as_u32()),
            PtrBase::Malloc(inst) => (2, inst.as_u32()),
        }
    }
}

/// A formal argument, optionally followed by memory loads. Distinct exact load
/// depths join to a lower bound, avoiding unbounded paths in recursive summaries.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct ArgumentOrigin {
    pub(crate) index: u32,
    pub(crate) depth: u32,
    pub(crate) transitive: bool,
    pub(crate) exact: bool,
}

impl ArgumentOrigin {
    pub(crate) fn value(index: u32) -> Self {
        Self {
            index,
            depth: 0,
            transitive: false,
            exact: true,
        }
    }

    pub(crate) fn loaded(self) -> Self {
        Self {
            depth: self
                .depth
                .checked_add(1)
                .expect("argument load depth overflow"),
            ..self
        }
    }

    pub(crate) fn join_into(origins: &mut SmallVec<[Self; 4]>, origin: Self) -> bool {
        // Direct value and loaded contents must stay distinct: merging depth 0
        // with depth 1 would conflate a descriptor address with its contents.
        if let Some(old) = origins
            .iter_mut()
            .find(|old| old.index == origin.index && (old.depth == 0) == (origin.depth == 0))
        {
            let joined = Self {
                index: old.index,
                depth: old.depth.min(origin.depth),
                transitive: old.transitive || origin.transitive || old.depth != origin.depth,
                exact: old.exact && origin.exact,
            };
            if *old == joined {
                return false;
            }
            *old = joined;
        } else {
            origins.push(origin);
        }
        origins.sort_unstable();
        true
    }
}

/// Pointer provenance facts for an SSA value or modeled memory cell.
///
/// Exact `bases` may coexist with unknown flags. For example, a call result can
/// be either a caller-local alloca or an unknown non-arg pointer; preserving the
/// exact alloca base lets later escape analysis report the local escape.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Provenance {
    bases: SmallVec<[PtrBase; 4]>,
    /// Address arithmetic may change the offset associated with an origin.
    imprecise: bool,
    /// Symbol addresses are code offsets. This fact only avoids inventing a
    /// linear-memory pointer for casts whose entire use chain stays in code.
    has_code_address: bool,
    /// Value forwarding is symbolic: an i256 formal need not contain a pointer.
    forwarded_args: SmallVec<[u32; 4]>,
    /// Incoming contents of argument-reachable memory, distinct from its address.
    arg_memory: SmallVec<[ArgumentOrigin; 4]>,
    /// Arg attribution retained after exact arg bases are collapsed.
    unknown_arg_indices: SmallVec<[u32; 4]>,
    /// The value may also be a non-arg pointer whose exact base is unknown.
    unknown_non_arg: bool,
    /// A heap pointer returned by a callee, without a caller-local malloc identity.
    /// Heap escape and reclamation remain conservative, but this fact alone does
    /// not make the value point at an arbitrary local alloca.
    unknown_heap: bool,
}

impl Provenance {
    pub(crate) fn is_empty(&self) -> bool {
        self.bases.is_empty() && self.arg_memory.is_empty() && !self.is_unknown_ptr()
    }

    pub(crate) fn has_no_known_bases(&self) -> bool {
        self.bases.is_empty()
    }

    pub(crate) fn is_unknown_ptr(&self) -> bool {
        self.unknown_heap || self.may_reference_unknown_local()
    }

    pub(crate) fn may_reference_unknown_local(&self) -> bool {
        self.unknown_non_arg || !self.unknown_arg_indices.is_empty()
    }

    pub(crate) fn may_reference_heap(&self) -> bool {
        self.unknown_heap || self.malloc_insts().next().is_some()
    }

    fn insert_arg_index(indices: &mut SmallVec<[u32; 4]>, idx: u32) -> bool {
        if indices.contains(&idx) {
            return false;
        }
        indices.push(idx);
        indices.sort_unstable();
        indices.dedup();
        true
    }

    fn add_unknown_arg_index(&mut self, idx: u32) -> bool {
        Self::insert_arg_index(&mut self.unknown_arg_indices, idx)
    }

    fn collapse_arg_bases_to_unknown_arg_indices(&mut self) -> bool {
        let arg_indices: SmallVec<[u32; 4]> = self
            .bases
            .iter()
            .filter_map(|base| match base {
                PtrBase::Arg(idx) => Some(*idx),
                _ => None,
            })
            .collect();
        let mut changed = false;
        for idx in arg_indices {
            changed |= self.add_unknown_arg_index(idx);
        }

        let old_len = self.bases.len();
        self.bases.retain(|base| !matches!(base, PtrBase::Arg(_)));
        changed || self.bases.len() != old_len
    }

    pub(crate) fn mark_unknown_non_arg(&mut self) -> bool {
        let mut changed = !self.unknown_non_arg;
        self.unknown_non_arg = true;
        changed |= self.collapse_arg_bases_to_unknown_arg_indices();
        changed
    }

    pub(crate) fn union_with(&mut self, other: &Self) -> bool {
        let mut changed = false;
        let mut bases_changed = false;
        changed |= other.imprecise && !self.imprecise;
        self.imprecise |= other.imprecise;
        changed |= other.has_code_address && !self.has_code_address;
        self.has_code_address |= other.has_code_address;

        for base in other.bases.iter().copied() {
            match base {
                PtrBase::Arg(idx) if self.unknown_non_arg => {
                    changed |= self.add_unknown_arg_index(idx);
                }
                _ => {
                    if !self.bases.contains(&base) {
                        self.bases.push(base);
                        bases_changed = true;
                    }
                }
            }
        }

        if bases_changed {
            self.bases.sort_unstable_by_key(|b| b.key());
            self.bases.dedup();
            changed = true;
        }

        for &idx in &other.forwarded_args {
            changed |= Self::insert_arg_index(&mut self.forwarded_args, idx);
        }
        for &idx in &other.arg_memory {
            changed |= ArgumentOrigin::join_into(&mut self.arg_memory, idx);
        }
        for idx in other.unknown_arg_indices.iter().copied() {
            changed |= self.add_unknown_arg_index(idx);
        }
        if other.unknown_non_arg {
            changed |= self.mark_unknown_non_arg();
        }
        changed |= other.unknown_heap && !self.unknown_heap;
        self.unknown_heap |= other.unknown_heap;
        changed
    }

    pub(crate) fn has_any_arg(&self) -> bool {
        self.bases.iter().any(|b| matches!(b, PtrBase::Arg(_)))
            || !self.unknown_arg_indices.is_empty()
            || !self.arg_memory.is_empty()
            || !self.forwarded_args.is_empty()
    }

    pub(crate) fn argument_origins(&self) -> impl Iterator<Item = ArgumentOrigin> + '_ {
        self.arg_indices()
            .chain(self.forwarded_args.iter().copied())
            .map(ArgumentOrigin::value)
            .chain(self.arg_memory.iter().copied())
            .map(|mut origin| {
                origin.exact &= !self.imprecise;
                origin
            })
    }

    pub(crate) fn arg_indices(&self) -> impl Iterator<Item = u32> + '_ {
        self.bases
            .iter()
            .filter_map(|b| match b {
                PtrBase::Arg(i) => Some(*i),
                PtrBase::Alloca(_) | PtrBase::Malloc(_) => None,
            })
            .chain(self.unknown_arg_indices.iter().copied())
    }

    pub(crate) fn is_local_addr(&self) -> bool {
        !self.is_unknown_ptr()
            && !self.has_no_known_bases()
            && self.arg_memory.is_empty()
            && self.forwarded_args.is_empty()
            && self.bases.iter().all(|b| matches!(b, PtrBase::Alloca(_)))
    }

    pub(crate) fn may_be_nonlocal_nonarg_without_malloc(&self) -> bool {
        self.unknown_non_arg
            || self.unknown_heap
            || (self.has_no_known_bases() && self.argument_origins().next().is_none())
    }

    pub(crate) fn alloca_insts(&self) -> impl Iterator<Item = InstId> + '_ {
        self.bases.iter().filter_map(|b| match b {
            PtrBase::Alloca(inst) => Some(*inst),
            PtrBase::Arg(_) => None,
            PtrBase::Malloc(_) => None,
        })
    }

    pub(crate) fn malloc_insts(&self) -> impl Iterator<Item = InstId> + '_ {
        self.bases.iter().filter_map(|b| match b {
            PtrBase::Malloc(inst) => Some(*inst),
            PtrBase::Arg(_) | PtrBase::Alloca(_) => None,
        })
    }
}

fn store_allocation_mem(
    mem: &mut FxHashMap<InstId, Provenance>,
    bases: impl Iterator<Item = InstId>,
    val_prov: &Provenance,
) -> bool {
    let mut changed = false;
    for base in bases {
        changed |= mem.entry(base).or_default().union_with(val_prov);
    }
    changed
}

fn poison_allocation_mem(
    mem: &mut FxHashMap<InstId, Provenance>,
    bases: impl Iterator<Item = InstId>,
) -> bool {
    let mut changed = false;
    for base in bases {
        changed |= mem
            .entry(base)
            .or_default()
            // Memory facts join writes from the entire function. Keep possible
            // exact bases: clearing them here can alternate forever with a
            // modeled store that adds the same bases on every iteration.
            .mark_unknown_non_arg();
    }
    changed
}

fn store_arg_mem(
    mem: &mut Vec<(ArgumentOrigin, Provenance)>,
    addr: &Provenance,
    value: &Provenance,
) -> bool {
    let mut changed = false;
    for origin in addr.argument_origins() {
        let key = (origin.index, origin.depth != 0);
        let index = match mem.binary_search_by_key(&key, |(old, _)| (old.index, old.depth != 0)) {
            Ok(index) => index,
            Err(index) => {
                mem.insert(index, (origin, Provenance::default()));
                changed = true;
                index
            }
        };
        let (old, stored) = &mut mem[index];
        let joined = ArgumentOrigin {
            index: old.index,
            depth: old.depth.min(origin.depth),
            transitive: old.transitive || origin.transitive || old.depth != origin.depth,
            exact: old.exact && origin.exact,
        };
        changed |= *old != joined;
        *old = joined;
        changed |= stored.union_with(value);
    }
    changed
}

fn poison_arg_mem(mem: &mut Vec<(ArgumentOrigin, Provenance)>, addr: &Provenance) -> bool {
    store_arg_mem(
        mem,
        addr,
        &Provenance {
            unknown_non_arg: true,
            ..Provenance::default()
        },
    )
}

pub(crate) fn memory_load(data: &EvmInstKind<'_>, module: &ModuleCtx) -> Option<(ValueId, usize)> {
    match data {
        EvmInstKind::Mload(load) => Some((*load.addr(), module.size_of_unchecked(*load.ty()))),
        EvmInstKind::EvmMload(load) => Some((*load.addr(), 32)),
        _ => None,
    }
}

pub(crate) fn memory_store(
    data: &EvmInstKind<'_>,
    module: &ModuleCtx,
) -> Option<(ValueId, ValueId, usize)> {
    match data {
        EvmInstKind::Mstore(store) => Some((
            *store.addr(),
            *store.value(),
            module.size_of_unchecked(*store.ty()),
        )),
        EvmInstKind::EvmMstore(store) => Some((*store.addr(), *store.value(), 32)),
        EvmInstKind::EvmMstore8(store) => Some((*store.addr(), *store.val(), 1)),
        _ => None,
    }
}

fn unmodeled_write_addr(data: &EvmInstKind) -> Option<ValueId> {
    match data {
        EvmInstKind::EvmMstore8(mstore8) => Some(*mstore8.addr()),
        EvmInstKind::EvmMcopy(mcopy) => Some(*mcopy.dest()),
        EvmInstKind::Memzero(memzero) => Some(*memzero.dest()),
        EvmInstKind::EvmCalldataCopy(copy) => Some(*copy.dst_addr()),
        EvmInstKind::EvmExtCodeCopy(copy) => Some(*copy.dst_addr()),
        EvmInstKind::EvmReturnDataCopy(copy) => Some(*copy.dst_addr()),
        EvmInstKind::EvmCall(call) => Some(*call.ret_addr()),
        EvmInstKind::EvmCallCode(call) => Some(*call.ret_addr()),
        EvmInstKind::EvmDelegateCall(call) => Some(*call.ret_addr()),
        EvmInstKind::EvmStaticCall(call) => Some(*call.ret_addr()),
        _ => None,
    }
}

pub(crate) fn type_can_carry_pointer_provenance(module: &ModuleCtx, ty: Type) -> bool {
    // TODO: This is dual-use encoded-pointer carrier logic, not provenance-specific.
    // Move it to a shared EVM helper with a clearer name and cache recursive type queries.
    let mut seen = FxHashSet::default();
    type_can_carry_pointer_provenance_inner(module, ty, &mut seen)
}

fn type_can_carry_pointer_provenance_inner(
    module: &ModuleCtx,
    ty: Type,
    seen: &mut FxHashSet<CompoundTypeRef>,
) -> bool {
    match ty {
        Type::I256 => true,
        Type::I1 | Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::I128 | Type::Unit => false,
        Type::EnumTag(_) => false,
        Type::Compound(compound) => {
            if !seen.insert(compound) {
                return false;
            }

            match module.with_ty_store(|store| store.resolve_compound(compound).clone()) {
                CompoundType::Ptr(_) | CompoundType::ObjRef(_) | CompoundType::ConstRef(_) => true,
                CompoundType::Array { elem, .. } => {
                    type_can_carry_pointer_provenance_inner(module, elem, seen)
                }
                CompoundType::Struct(data) => data
                    .fields
                    .iter()
                    .any(|&field| type_can_carry_pointer_provenance_inner(module, field, seen)),
                CompoundType::Enum(data) => data.variants.iter().any(|variant| {
                    variant
                        .fields
                        .iter()
                        .any(|&field| type_can_carry_pointer_provenance_inner(module, field, seen))
                }),
                CompoundType::Func { .. } => false,
            }
        }
    }
}

#[derive(Clone, Copy)]
struct AllocationAddress {
    base: InstId,
    offset_bytes: i64,
    allocation_bytes: Option<u32>,
}

struct MemoryCell {
    offset: i64,
    bytes: usize,
    stored: Provenance,
}

pub(crate) struct ProvenanceInfo {
    pub(crate) value: SecondaryMap<ValueId, Provenance>,
    pub(crate) local_mem: FxHashMap<InstId, Provenance>,
    pub(crate) malloc_mem: FxHashMap<InstId, Provenance>,
    /// Tracks what the callee stores to arg-backed memory addresses.
    /// Initialized empty (bottom); only callee-initiated stores are recorded.
    /// Used by mcopy handling to determine the provenance of bytes being copied
    /// from arg-addressed memory.
    pub(crate) arg_mem: Vec<(ArgumentOrigin, Provenance)>,
    exact_addresses: SecondaryMap<ValueId, Option<AllocationAddress>>,
    cells: FxHashMap<InstId, Vec<MemoryCell>>,
    imprecise_mem: FxHashMap<InstId, Provenance>,
}

impl ProvenanceInfo {
    /// Keep every known allocation reachable through local memory. This is a
    /// may-store closure: cycles terminate, and unknown contents never erase
    /// known roots. Symbolic argument contents are not expanded here.
    pub(crate) fn reachable_memory(&self, roots: &Provenance) -> Provenance {
        let mut out = roots.clone();
        let mut visited = FxHashSet::default();
        let mut work: SmallVec<[InstId; 8]> =
            roots.alloca_insts().chain(roots.malloc_insts()).collect();
        while let Some(base) = work.pop() {
            if !visited.insert(base) {
                continue;
            }
            if let Some(stored) = self
                .local_mem
                .get(&base)
                .or_else(|| self.malloc_mem.get(&base))
            {
                out.union_with(stored);
                work.extend(stored.alloca_insts().chain(stored.malloc_insts()));
            }
        }
        out
    }

    fn covers_allocation(&self, function: &Function, addr: ValueId, len: ValueId) -> bool {
        self.exact_addresses[addr].is_some_and(|addr| {
            addr.offset_bytes == 0
                && value_imm_u32(function, len)
                    .is_some_and(|bytes| addr.allocation_bytes == Some(bytes))
        })
    }

    /// Join all contents for a copy or other access with no known width.
    pub(crate) fn load_memory(&self, addr: &Provenance) -> Provenance {
        self.load_provenance_memory(addr, None)
    }

    fn load_provenance_memory(&self, addr: &Provenance, bytes: Option<usize>) -> Provenance {
        let mut out = Provenance::default();
        for base in addr.alloca_insts().chain(addr.malloc_insts()) {
            if let Some(bytes) = bytes.filter(|_| !addr.imprecise) {
                // Exact allocation roots denote offset zero, even when the
                // pointer itself arrived through a load or a call result.
                out.union_with(&self.load_allocation_memory(base, 0, bytes));
            } else if let Some(stored) = self
                .local_mem
                .get(&base)
                .or_else(|| self.malloc_mem.get(&base))
            {
                out.union_with(stored);
            }
        }
        for origin in addr.argument_origins() {
            ArgumentOrigin::join_into(&mut out.arg_memory, origin.loaded());
            for (written, stored) in &self.arg_mem {
                if origin.index == written.index
                    && (origin.depth == written.depth
                        || (origin.transitive && written.depth >= origin.depth)
                        || (written.transitive && origin.depth >= written.depth))
                {
                    out.union_with(stored);
                }
            }
        }
        // Callee-created heap objects lack an allocation identity here. Their
        // contents, like other unknown addresses, remain conservative.
        if addr.is_unknown_ptr() {
            out.mark_unknown_non_arg();
        }
        if bytes.is_some_and(|bytes| bytes != 32) {
            out.imprecise = true;
        }
        out
    }

    fn load_allocation_memory(&self, base: InstId, offset: i64, bytes: usize) -> Provenance {
        let mut out = self.imprecise_mem.get(&base).cloned().unwrap_or_default();
        if let Some(cells) = self.cells.get(&base) {
            for cell in cells {
                if i128::from(cell.offset) < i128::from(offset) + bytes as i128
                    && i128::from(offset) < i128::from(cell.offset) + cell.bytes as i128
                {
                    out.union_with(&cell.stored);
                }
            }
        }
        if bytes != 32 {
            out.imprecise = true;
        }
        out
    }

    fn load_value_memory(&self, value: ValueId, bytes: usize) -> Provenance {
        if let Some(addr) = self.exact_addresses[value] {
            self.load_allocation_memory(addr.base, addr.offset_bytes, bytes)
        } else {
            self.load_provenance_memory(&self.value[value], Some(bytes))
        }
    }

    fn store_value_memory(&mut self, addr: ValueId, value: &Provenance, bytes: usize) -> bool {
        let addr_prov = &self.value[addr];
        let mut changed =
            store_allocation_mem(&mut self.local_mem, addr_prov.alloca_insts(), value)
                | store_allocation_mem(&mut self.malloc_mem, addr_prov.malloc_insts(), value)
                | store_arg_mem(&mut self.arg_mem, addr_prov, value);
        if let Some(exact) = self.exact_addresses[addr] {
            let cells = self.cells.entry(exact.base).or_default();
            if let Some(cell) = cells
                .iter_mut()
                .find(|cell| cell.offset == exact.offset_bytes && cell.bytes == bytes)
            {
                changed |= cell.stored.union_with(value);
            } else {
                cells.push(MemoryCell {
                    offset: exact.offset_bytes,
                    bytes,
                    stored: value.clone(),
                });
                changed = true;
            }
        } else {
            changed |= store_allocation_mem(
                &mut self.imprecise_mem,
                addr_prov.alloca_insts().chain(addr_prov.malloc_insts()),
                value,
            );
        }
        changed
    }

    pub(crate) fn resolve_argument(&self, args: &[ValueId], origin: ArgumentOrigin) -> Provenance {
        let Some(&value) = args.get(origin.index as usize) else {
            return Provenance::default();
        };
        let mut out = self.value[value].clone();
        if origin.depth == 0 {
            out.imprecise |= !origin.exact;
            return out;
        }
        for step in 0..origin.depth {
            out = if step == 0 && origin.exact {
                self.load_value_memory(value, 32)
            } else {
                self.load_provenance_memory(&out, origin.exact.then_some(32))
            };
        }
        if origin.transitive {
            loop {
                let loaded = self.load_memory(&out);
                if !out.union_with(&loaded) {
                    break;
                }
            }
        }
        out.imprecise |= !origin.exact;
        out
    }

    fn store_memory(&mut self, addr: &Provenance, value: &Provenance) -> bool {
        store_allocation_mem(&mut self.local_mem, addr.alloca_insts(), value)
            | store_allocation_mem(&mut self.malloc_mem, addr.malloc_insts(), value)
            | store_allocation_mem(
                &mut self.imprecise_mem,
                addr.alloca_insts().chain(addr.malloc_insts()),
                value,
            )
            | store_arg_mem(&mut self.arg_mem, addr, value)
    }

    fn call_result(
        &self,
        args: &[ValueId],
        summary: &PtrEscapeSummary,
        ret_idx: usize,
    ) -> Provenance {
        let mut next = Provenance::default();
        if let Some(ret) = summary.returns.get(ret_idx) {
            for &origin in &ret.origins {
                next.union_with(&self.resolve_argument(args, origin));
            }
            next.unknown_heap |= ret.heap_pointer;
            if ret.unknown_pointer {
                next.mark_unknown_non_arg();
            }
        }
        next
    }
}

/// Values with any use outside code-address calculations. Prove the entire
/// use chain, including phi cycles, rather than classifying an integer-to-pointer
/// cast as nonlocal merely because one of its inputs came from a symbol.
fn non_code_address_uses(function: &Function, isa: &Evm) -> FxHashSet<ValueId> {
    let mut out = FxHashSet::default();
    let mut forwarding = Vec::new();
    for inst in function.layout.iter_all_insts() {
        match isa.inst_set().resolve_inst(function.dfg.inst(inst)) {
            EvmInstKind::Gep(_)
            | EvmInstKind::Bitcast(_)
            | EvmInstKind::IntToPtr(_)
            | EvmInstKind::PtrToInt(_)
            | EvmInstKind::Add(_)
            | EvmInstKind::Sub(_)
            | EvmInstKind::Phi(_) => forwarding.push(inst),
            EvmInstKind::EvmCodeCopy(copy) => {
                out.insert(*copy.dst_addr());
                out.insert(*copy.len());
            }
            _ => function.dfg.inst(inst).for_each_value(&mut |value| {
                out.insert(value);
            }),
        }
    }
    loop {
        let mut changed = false;
        for &inst in forwarding.iter().rev() {
            if function
                .dfg
                .inst_results(inst)
                .iter()
                .any(|value| out.contains(value))
            {
                function.dfg.inst(inst).for_each_value(&mut |value| {
                    changed |= out.insert(value);
                });
            }
        }
        if !changed {
            return out;
        }
    }
}

pub(crate) fn compute_provenance(
    function: &Function,
    module: &ModuleCtx,
    isa: &Evm,
    callee_summary: impl Fn(FuncRef) -> PtrEscapeSummary,
) -> ProvenanceInfo {
    let non_code_uses = non_code_address_uses(function, isa);
    let mut prov: SecondaryMap<ValueId, Provenance> = SecondaryMap::new();
    for value in function.dfg.value_ids() {
        let _ = &mut prov[value];
    }

    for (idx, &arg) in function.arg_values.iter().enumerate() {
        let ty = function.dfg.value_ty(arg);
        if type_can_carry_pointer_provenance(module, ty) {
            prov[arg].forwarded_args.push(idx as u32);
        }
        if ty.is_pointer(module) {
            prov[arg].bases.push(PtrBase::Arg(idx as u32));
        }
    }

    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));
            let [def] = function.dfg.inst_results(inst) else {
                continue;
            };
            match data {
                EvmInstKind::Alloca(_) => prov[*def].bases.push(PtrBase::Alloca(inst)),
                EvmInstKind::EvmMalloc(_) => prov[*def].bases.push(PtrBase::Malloc(inst)),
                _ => {}
            }
        }
    }

    let mut addresses = MemoryAccessAnalysis::new();
    let mut exact_addresses = SecondaryMap::new();
    for value in function.dfg.value_ids() {
        let address = addresses.canonical_linear_addr(function, value);
        exact_addresses[value] = match address.base {
            BaseObject::Alloca(base) | BaseObject::Malloc(base) => {
                let allocation_bytes = match isa.inst_set().resolve_inst(function.dfg.inst(base)) {
                    EvmInstKind::Alloca(alloca) => {
                        module.size_of_unchecked(*alloca.ty()).try_into().ok()
                    }
                    EvmInstKind::EvmMalloc(malloc) => value_imm_u32(function, *malloc.size()),
                    _ => unreachable!("canonical allocation must be alloca or malloc"),
                };
                Some(AllocationAddress {
                    base,
                    offset_bytes: address.offset,
                    allocation_bytes,
                })
            }
            _ => None,
        };
    }
    let mut info = ProvenanceInfo {
        value: prov,
        local_mem: FxHashMap::default(),
        malloc_mem: FxHashMap::default(),
        arg_mem: Vec::new(),
        exact_addresses,
        cells: FxHashMap::default(),
        imprecise_mem: FxHashMap::default(),
    };

    let mut changed = true;
    while changed {
        changed = false;

        for block in function.layout.iter_block() {
            for inst in function.layout.iter_inst(block) {
                let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));

                if let Some((addr, value, bytes)) = memory_store(&data, module) {
                    let value = info.value[value].clone();
                    changed |= info.store_value_memory(addr, &value, bytes);
                }

                if let EvmInstKind::EvmMcopy(copy) = &data {
                    let stored = info.load_memory(&info.value[*copy.addr()]);
                    let dest = info.value[*copy.dest()].clone();
                    changed |= info.store_memory(&dest, &stored);
                }

                // Complete zeroing cannot create pointer fragments; a complete
                // copy carries the source contents already joined above. Keep
                // all earlier may-writes, including unknown contributors. Partial
                // or unproved ranges still need the conservative clobber below.
                let complete_write = match &data {
                    EvmInstKind::Memzero(write) => {
                        info.covers_allocation(function, *write.dest(), *write.len())
                    }
                    EvmInstKind::EvmMcopy(copy) => {
                        info.covers_allocation(function, *copy.dest(), *copy.len())
                            && info.covers_allocation(function, *copy.addr(), *copy.len())
                    }
                    EvmInstKind::EvmCalldataCopy(copy) => {
                        function
                            .dfg
                            .value_inst(*copy.data_offset())
                            .is_some_and(|inst| {
                                matches!(
                                    isa.inst_set().resolve_inst(function.dfg.inst(inst)),
                                    EvmInstKind::EvmCalldataSize(_)
                                )
                            })
                            && info.covers_allocation(function, *copy.dst_addr(), *copy.len())
                    }
                    _ => false,
                };
                if let Some(dst) = unmodeled_write_addr(&data).filter(|_| !complete_write) {
                    changed |=
                        poison_allocation_mem(&mut info.local_mem, info.value[dst].alloca_insts());
                    changed |=
                        poison_allocation_mem(&mut info.malloc_mem, info.value[dst].malloc_insts());
                    changed |= poison_allocation_mem(
                        &mut info.imprecise_mem,
                        info.value[dst]
                            .alloca_insts()
                            .chain(info.value[dst].malloc_insts()),
                    );
                    changed |= poison_arg_mem(&mut info.arg_mem, &info.value[dst]);
                }

                if let EvmInstKind::Call(call) = &data {
                    let summary = callee_summary(*call.callee());
                    let args = call.args();
                    summary.for_each_store_effect(|source, dest| {
                        let src_prov = info.resolve_argument(args, source);
                        let dst_prov = info.resolve_argument(args, dest);
                        changed |= info.store_memory(&dst_prov, &src_prov);
                    });
                    for (origin, effect) in summary.argument_effects() {
                        if effect.stored_heap_pointer || effect.stored_unknown_pointer {
                            let stored = Provenance {
                                unknown_heap: effect.stored_heap_pointer,
                                unknown_non_arg: effect.stored_unknown_pointer,
                                ..Provenance::default()
                            };
                            let dest = info.resolve_argument(args, origin);
                            changed |= info.store_memory(&dest, &stored);
                        }
                    }
                    for (ret_idx, &def) in function.dfg.inst_results(inst).iter().enumerate() {
                        let mut next = info.call_result(args, &summary, ret_idx);
                        if function.dfg.value_ty(def).is_pointer(module) && next.is_empty() {
                            next.mark_unknown_non_arg();
                        }
                        if !type_can_carry_pointer_provenance(module, function.dfg.value_ty(def)) {
                            next.forwarded_args.clear();
                        }
                        if info.value[def] != next {
                            info.value[def] = next;
                            changed = true;
                        }
                    }
                    continue;
                }

                let [def] = function.dfg.inst_results(inst) else {
                    continue;
                };

                let mut next = Provenance::default();

                match data {
                    EvmInstKind::SymAddr(_) => next.has_code_address = true,
                    EvmInstKind::Alloca(_) => next.bases.push(PtrBase::Alloca(inst)),
                    EvmInstKind::EvmMalloc(_) => next.bases.push(PtrBase::Malloc(inst)),
                    EvmInstKind::Mload(_) | EvmInstKind::EvmMload(_) => {
                        let (addr, bytes) =
                            memory_load(&data, module).expect("matched a memory load");
                        next.union_with(&info.load_value_memory(addr, bytes));
                    }
                    EvmInstKind::Phi(phi) => {
                        for (val, _) in phi.args().iter() {
                            let _ = next.union_with(&info.value[*val]);
                        }
                    }
                    EvmInstKind::Gep(gep) => {
                        let Some(&base) = gep.values().first() else {
                            continue;
                        };
                        let _ = next.union_with(&info.value[base]);
                        next.imprecise |= gep.values().iter().skip(1).any(|value| {
                            !function
                                .dfg
                                .value_imm(*value)
                                .is_some_and(|imm| imm.is_zero())
                        });
                    }
                    EvmInstKind::Bitcast(bc) => {
                        let _ = next.union_with(&info.value[*bc.from()]);
                    }
                    EvmInstKind::BlackBox(black_box) => {
                        let _ = next.union_with(&info.value[*black_box.arg()]);
                    }
                    EvmInstKind::IntToPtr(i2p) => {
                        let from = *i2p.from();
                        let from_prov = &info.value[from];
                        let _ = next.union_with(from_prov);
                        if from_prov.is_empty()
                            && (!from_prov.has_code_address || non_code_uses.contains(def))
                        {
                            let _ = next.mark_unknown_non_arg();
                        }
                    }
                    EvmInstKind::PtrToInt(p2i) => {
                        let _ = next.union_with(&info.value[*p2i.from()]);
                    }
                    EvmInstKind::InsertValue(iv) => {
                        let _ = next.union_with(&info.value[*iv.dest()]);
                        let _ = next.union_with(&info.value[*iv.value()]);
                    }
                    EvmInstKind::ExtractValue(ev) => {
                        let _ = next.union_with(&info.value[*ev.dest()]);
                    }
                    EvmInstKind::Add(_)
                    | EvmInstKind::Sub(_)
                    | EvmInstKind::Mul(_)
                    | EvmInstKind::And(_)
                    | EvmInstKind::Or(_)
                    | EvmInstKind::Xor(_)
                    | EvmInstKind::Shl(_)
                    | EvmInstKind::Shr(_)
                    | EvmInstKind::Sar(_)
                    | EvmInstKind::Not(_)
                    | EvmInstKind::Sext(_)
                    | EvmInstKind::Zext(_)
                    | EvmInstKind::Trunc(_)
                    | EvmInstKind::EvmSdiv(_)
                    | EvmInstKind::EvmUdiv(_)
                    | EvmInstKind::EvmUmod(_)
                    | EvmInstKind::EvmSmod(_)
                    | EvmInstKind::EvmAddMod(_)
                    | EvmInstKind::EvmMulMod(_)
                    | EvmInstKind::EvmExp(_)
                    | EvmInstKind::EvmSignExtend(_)
                    | EvmInstKind::EvmByte(_)
                    | EvmInstKind::EvmClz(_) => {
                        function.dfg.inst(inst).for_each_value(&mut |v| {
                            let _ = next.union_with(&info.value[v]);
                        });
                        next.imprecise = true;
                    }
                    _ => {}
                }

                if !type_can_carry_pointer_provenance(module, function.dfg.value_ty(*def)) {
                    next.forwarded_args.clear();
                }
                if info.value[*def] != next {
                    info.value[*def] = next;
                    changed = true;
                }
            }
        }
    }

    info
}

pub(crate) fn compute_value_provenance(
    function: &Function,
    module: &ModuleCtx,
    isa: &Evm,
    callee_summary: impl Fn(FuncRef) -> PtrEscapeSummary,
) -> SecondaryMap<ValueId, Provenance> {
    compute_provenance(function, module, isa, callee_summary).value
}

#[cfg(test)]
mod tests {
    use super::{super::ptr_escape::compute_ptr_escape_summaries, *};
    use sonatina_parser::parse_module;
    use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

    fn ret_provenance(src: &str, func_name: &str) -> Provenance {
        let parsed = parse_module(src).expect("module parses");
        let funcs = parsed.module.funcs();
        let func_ref = parsed
            .module
            .funcs()
            .into_iter()
            .find(|&f| parsed.module.ctx.func_sig(f, |sig| sig.name() == func_name))
            .expect("function exists");

        let isa = Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        });

        let summaries = compute_ptr_escape_summaries(&parsed.module, &funcs, &isa);

        parsed.module.func_store.view(func_ref, |function| {
            let prov = compute_provenance(function, &parsed.module.ctx, &isa, |callee| {
                PtrEscapeSummary::get_or_conservative(&summaries, &parsed.module.ctx, callee)
            })
            .value;

            for block in function.layout.iter_block() {
                for inst in function.layout.iter_inst(block) {
                    let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));
                    if let EvmInstKind::Return(_) = data
                        && let Some(ret_val) = function
                            .dfg
                            .return_args(inst)
                            .and_then(|args| args.first().copied())
                    {
                        return prov[ret_val].clone();
                    }
                }
            }

            panic!("no return value in function");
        })
    }

    #[test]
    fn known_heap_memory_loads_keep_scalar_fields_separate() {
        let provenance = ret_provenance(
            r#"
target = "evm-ethereum-osaka"
func public %f() -> i256 {
block0:
    v0.*i256 = evm_malloc 32.i256;
    v1.*i8 = evm_malloc 64.i256;
    v2.*[i256; 2] = bitcast v1 *[i256; 2];
    v3.*i256 = gep v2 0.i256 0.i256;
    v4.*i256 = gep v2 0.i256 1.i256;
    mstore v3 v0 *i256;
    mstore v4 7.i256 i256;
    v5.i256 = mload v4 i256;
    return v5;
}
"#,
            "f",
        );
        assert!(
            provenance.is_empty(),
            "scalar heap data must not become an unknown pointer: {provenance:?}"
        );
    }

    #[test]
    fn known_heap_pointer_loads_retain_exact_roots_after_partial_writes() {
        for (clobber, unknown) in [("", false), ("evm_mstore8 v1 1.i8;", true)] {
            let source = format!(
                r#"
target = "evm-ethereum-osaka"
func public %f() -> *i256 {{
block0:
    v0.*i256 = evm_malloc 32.i256;
    v1.**i256 = evm_malloc 32.i256;
    mstore v1 v0 *i256;
    {clobber}
    v2.*i256 = mload v1 *i256;
    return v2;
}}
"#
            );
            let provenance = ret_provenance(&source, "f");
            assert_eq!(
                provenance.malloc_insts().count(),
                1,
                "{clobber}: {provenance:?}"
            );
            assert_eq!(
                provenance.is_unknown_ptr(),
                unknown,
                "{clobber}: {provenance:?}"
            );
        }
    }

    #[test]
    fn argument_pointer_roundtrip_through_private_heap_retains_origin() {
        let provenance = ret_provenance(
            r#"
target = "evm-ethereum-osaka"
func public %f(v0.*i256) -> *i256 {
block0:
    v1.**i256 = evm_malloc 32.i256;
    mstore v1 v0 *i256;
    v2.*i256 = mload v1 *i256;
    return v2;
}
"#,
            "f",
        );
        assert_eq!(
            provenance.arg_indices().collect::<Vec<_>>(),
            vec![0],
            "{provenance:?}"
        );
        assert!(!provenance.is_unknown_ptr(), "{provenance:?}");
        assert_eq!(provenance.malloc_insts().count(), 0);
    }

    #[test]
    fn complete_allocation_zeroing_does_not_invent_pointer_origins() {
        for allocation in ["alloca i256", "evm_malloc 32.i256"] {
            for write in [
                "memzero v0 32.i256;",
                "v2.i256 = evm_calldata_size;\n    evm_calldata_copy v0 v2 32.i256;",
            ] {
                let source = format!(
                    r#"
target = "evm-ethereum-osaka"
func public %f() -> i256 {{
block0:
    v0.*i256 = {allocation};
    mstore v0 7.i256 i256;
    {write}
    v1.i256 = mload v0 i256;
    return v1;
}}
"#
                );
                let provenance = ret_provenance(&source, "f");
                assert!(
                    provenance.is_empty(),
                    "{allocation}: {write}: {provenance:?}"
                );
            }
        }
    }

    #[test]
    fn complete_allocation_copies_preserve_origins_without_unknowns() {
        for allocation in ["alloca *i256", "evm_malloc 32.i256"] {
            let source = format!(
                r#"
target = "evm-ethereum-osaka"
func public %f(v0.*i256) -> *i256 {{
block0:
    v1.**i256 = {allocation};
    v2.**i256 = {allocation};
    mstore v1 v0 *i256;
    evm_mcopy v2 v1 32.i256;
    v3.*i256 = mload v2 *i256;
    return v3;
}}
"#
            );
            let provenance = ret_provenance(&source, "f");
            assert_eq!(provenance.arg_indices().collect::<Vec<_>>(), vec![0]);
            assert!(!provenance.is_unknown_ptr(), "{allocation}: {provenance:?}");
        }
    }

    #[test]
    fn partial_or_external_writes_keep_unknown_and_known_origins() {
        for write in [
            "memzero v1 1.i256;",
            "v4.i256 = evm_calldata_size;\n    evm_calldata_copy v1 v4 1.i256;",
            "evm_calldata_copy v1 0.i256 32.i256;",
            "evm_return_data_copy v1 0.i256 32.i256;",
            "evm_mcopy v1 v2 31.i256;",
            "evm_mcopy v1 v2 v3;",
            "memzero v1 v3;",
            "v4.i256 = ptr_to_int v2 i256;\n    v6.i256 = add v4 1.i256;\n    evm_mcopy v1 v6 32.i256;",
            "v4.i256 = ptr_to_int v1 i256;\n    v6.i256 = add v4 1.i256;\n    evm_mcopy v6 v2 32.i256;",
            "evm_return_data_copy v2 0.i256 32.i256;\n    evm_mcopy v1 v2 32.i256;",
            "evm_return_data_copy v1 0.i256 32.i256;\n    memzero v1 32.i256;",
        ] {
            let source = format!(
                r#"
target = "evm-ethereum-osaka"
func public %f(v0.*i256, v3.i256) -> *i256 {{
block0:
    v1.**i256 = evm_malloc 32.i256;
    v2.**i256 = alloca *i256;
    mstore v1 v0 *i256;
    mstore v2 v0 *i256;
    {write}
    v5.*i256 = mload v1 *i256;
    return v5;
}}
"#
            );
            let provenance = ret_provenance(&source, "f");
            assert_eq!(provenance.arg_indices().collect::<Vec<_>>(), vec![0]);
            assert!(provenance.is_unknown_ptr(), "{write}: {provenance:?}");
        }
    }

    #[test]
    fn symbol_casts_require_an_exclusively_code_address_use_chain() {
        for (extra, terminator, unknown) in [
            ("", "return 0.i256;", false),
            ("v4.i256 = mload v2 i256;", "return 0.i256;", true),
            ("call %consume v2;", "return 0.i256;", true),
            ("mstore v0 v2 *i256;", "return 0.i256;", true),
            ("v4.i1 = eq v2 v0;", "return 0.i256;", true),
            ("evm_code_copy v3 v3 32.i256;", "return 0.i256;", true),
            ("", "return v3;", true),
        ] {
            let source = format!(
                r#"
target = "evm-ethereum-osaka"
global private const [i256; 1] $data = [7];
func private %consume(v0.*i256) {{
block0:
    return;
}}
func public %f() -> i256 {{
block0:
    v0.*i256 = alloca i256;
    v1.i256 = sym_addr $data;
    v2.*i256 = int_to_ptr v1 *i256;
    v3.i256 = ptr_to_int v2 i256;
    evm_code_copy v0 v3 32.i256;
    {extra}
    {terminator}
}}
"#
            );
            let parsed = parse_module(&source).unwrap();
            let funcs = parsed.module.funcs();
            let func_ref = funcs
                .iter()
                .copied()
                .find(|&f| parsed.module.ctx.func_sig(f, |sig| sig.name() == "f"))
                .unwrap();
            let isa = Evm::new(TargetTriple {
                architecture: Architecture::Evm,
                vendor: Vendor::Ethereum,
                operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
            });
            let summaries = compute_ptr_escape_summaries(&parsed.module, &funcs, &isa);
            parsed.module.func_store.view(func_ref, |function| {
                let info = compute_provenance(function, &parsed.module.ctx, &isa, |callee| {
                    PtrEscapeSummary::get_or_conservative(&summaries, &parsed.module.ctx, callee)
                });
                let cast = parsed.debug.value(func_ref, "v2").unwrap();
                assert_eq!(
                    info.value[cast].may_reference_unknown_local(),
                    unknown,
                    "{extra} {terminator}"
                );
            });
        }
    }

    #[test]
    fn union_preserves_exact_bases_when_unknown_non_arg_is_present() {
        let alloca = InstId(1);
        let malloc = InstId(2);
        let mut lhs = Provenance {
            bases: SmallVec::from_vec(vec![PtrBase::Alloca(alloca), PtrBase::Arg(0)]),
            unknown_arg_indices: SmallVec::new(),
            unknown_non_arg: false,
            unknown_heap: false,
            ..Provenance::default()
        };
        let rhs = Provenance {
            bases: SmallVec::from_vec(vec![PtrBase::Malloc(malloc), PtrBase::Arg(1)]),
            unknown_arg_indices: SmallVec::from_vec(vec![2]),
            unknown_non_arg: true,
            unknown_heap: false,
            ..Provenance::default()
        };

        assert!(lhs.mark_unknown_non_arg());
        assert!(lhs.union_with(&rhs));

        assert!(lhs.is_unknown_ptr());
        assert_eq!(lhs.alloca_insts().collect::<Vec<_>>(), vec![alloca]);
        assert_eq!(lhs.malloc_insts().collect::<Vec<_>>(), vec![malloc]);
        assert_eq!(lhs.arg_indices().collect::<Vec<_>>(), vec![0, 1, 2]);
    }

    #[test]
    fn int_to_ptr_from_integer_is_unknown_non_arg() {
        let ret_prov = ret_provenance(
            r#"
target = "evm-ethereum-osaka"

func public %f() -> *i8 {
block0:
    v0.*i8 = int_to_ptr 0.i32 *i8;
    return v0;
}
"#,
            "f",
        );

        assert!(ret_prov.is_unknown_ptr());
        assert_eq!(
            ret_prov.arg_indices().collect::<Vec<_>>(),
            Vec::<u32>::new()
        );
    }

    #[test]
    fn ptr_to_int_int_to_ptr_roundtrip_keeps_arg_attribution() {
        let ret_prov = ret_provenance(
            r#"
target = "evm-ethereum-osaka"

func public %f(v0.*i8) -> *i8 {
block0:
    v1.i256 = ptr_to_int v0 i256;
    v2.i256 = add v1 32.i256;
    v3.*i8 = int_to_ptr v2 *i8;
    return v3;
}
"#,
            "f",
        );

        assert!(!ret_prov.is_unknown_ptr());
        assert_eq!(ret_prov.arg_indices().collect::<Vec<_>>(), vec![0]);
    }

    #[test]
    fn black_box_forwards_pointer_provenance() {
        let src = r#"
target = "evm-ethereum-osaka"

func public %boxed_malloc() -> i256 {
block0:
    v0.*i256 = evm_malloc 32.i256;
    v1.i256 = ptr_to_int v0 i256;
    v2.i256 = black_box v1;
    return v2;
}

func public %boxed_arg(v0.*i256) -> i256 {
block0:
    v1.i256 = ptr_to_int v0 i256;
    v2.i256 = black_box v1;
    return v2;
}

func private %forward(v0.i256) -> i256 {
block0:
    v1.i256 = black_box v0;
    return v1;
}

func public %forwarded_alloca() -> i256 {
block0:
    v0.*i256 = alloca i256;
    v1.i256 = ptr_to_int v0 i256;
    v2.i256 = call %forward v1;
    return v2;
}
"#;

        let malloc = ret_provenance(src, "boxed_malloc");
        assert_eq!(malloc.malloc_insts().count(), 1, "{malloc:?}");
        let arg = ret_provenance(src, "boxed_arg");
        assert_eq!(arg.arg_indices().collect::<Vec<_>>(), vec![0], "{arg:?}");
        let alloca = ret_provenance(src, "forwarded_alloca");
        assert!(alloca.is_local_addr(), "{alloca:?}");
    }

    #[test]
    fn local_mem_poison_preserves_arg_attribution() {
        let ret_prov = ret_provenance(
            r#"
target = "evm-ethereum-osaka"

func public %f(v0.*i8) -> *i8 {
block0:
    v1.*i256 = alloca i256;
    mstore v1 v0 *i8;
    v2.i256 = ptr_to_int v1 i256;
    evm_mstore8 v2 1.i8;
    v3.*i8 = mload v1 *i8;
    return v3;
}
"#,
            "f",
        );

        assert!(ret_prov.is_unknown_ptr());
        assert_eq!(ret_prov.arg_indices().collect::<Vec<_>>(), vec![0]);
    }

    #[test]
    fn local_mem_poison_preserves_possible_local_bases_and_converges() {
        let ret_prov = ret_provenance(
            r#"
target = "evm-ethereum-osaka"

func public %f() -> *i256 {
block0:
    v0.*i256 = alloca i256;
    v1.**i256 = alloca *i256;
    mstore v1 v0 *i256;
    evm_mstore8 v1 1.i8;
    v2.*i256 = mload v1 *i256;
    return v2;
}
"#,
            "f",
        );

        assert!(ret_prov.is_unknown_ptr());
        assert_eq!(ret_prov.alloca_insts().count(), 1);
    }

    #[test]
    fn codecopy_does_not_introduce_pointer_provenance() {
        let ret_prov = ret_provenance(
            r#"
target = "evm-ethereum-osaka"

func public %f() -> *i8 {
block0:
    v0.*i256 = alloca i256;
    v1.i256 = ptr_to_int v0 i256;
    evm_code_copy v1 0.i256 32.i256;
    v2.*i8 = mload v0 *i8;
    return v2;
}
"#,
            "f",
        );

        assert!(!ret_prov.is_unknown_ptr());
        assert_eq!(
            ret_prov.arg_indices().collect::<Vec<_>>(),
            Vec::<u32>::new()
        );
    }

    #[test]
    fn mixed_unknown_call_result_preserves_alloca_through_carrier() {
        let ret_prov = ret_provenance(
            r#"
target = "evm-ethereum-osaka"

func public %maybe_arg(v0.*i8, v1.i1) -> *i8 {
block0:
    br v1 block1 block2;

block1:
    return v0;

block2:
    v2.*i8 = int_to_ptr 0.i32 *i8;
    return v2;
}

func public %caller(v0.i1) -> *i8 {
block0:
    v1.*i8 = alloca i8;
    v2.*i8 = call %maybe_arg v1 v0;
    v3.i256 = ptr_to_int v2 i256;
    v4.i256 = add v3 0.i256;
    v5.*i8 = int_to_ptr v4 *i8;
    return v5;
}
"#,
            "caller",
        );

        assert!(ret_prov.is_unknown_ptr(), "{ret_prov:?}");
        assert_eq!(ret_prov.alloca_insts().count(), 1, "{ret_prov:?}");
    }

    #[test]
    fn call_result_preserves_i256_encoded_malloc_returned_in_aggregate() {
        let ret_prov = ret_provenance(
            r#"
target = "evm-ethereum-osaka"

type @Bytes = {i256, i256};

func public %from_ptr(v0.i256, v1.i256) -> @Bytes {
block0:
    v2.@Bytes = insert_value undef.@Bytes 0.i256 v0;
    v3.@Bytes = insert_value v2 1.i256 v1;
    return v3;
}

func public %caller() -> @Bytes {
block0:
    v0.*i8 = evm_malloc 32.i256;
    v1.i256 = ptr_to_int v0 i256;
    v2.@Bytes = call %from_ptr v1 32.i256;
    return v2;
}
"#,
            "caller",
        );

        assert!(!ret_prov.is_unknown_ptr(), "{ret_prov:?}");
        assert_eq!(ret_prov.malloc_insts().count(), 1, "{ret_prov:?}");
    }

    #[test]
    fn multi_result_call_preserves_i256_encoded_malloc_return() {
        let ret_prov = ret_provenance(
            r#"
target = "evm-ethereum-osaka"

func public %from_ptr(v0.i256, v1.i256) -> (i256, i256) {
block0:
    return (v0, v1);
}

func public %caller() -> i256 {
block0:
    v0.*i8 = evm_malloc 32.i256;
    v1.i256 = ptr_to_int v0 i256;
    (v2.i256, v3.i256) = call %from_ptr v1 32.i256;
    return v2;
}
"#,
            "caller",
        );

        assert!(!ret_prov.is_unknown_ptr(), "{ret_prov:?}");
        assert_eq!(ret_prov.malloc_insts().count(), 1, "{ret_prov:?}");
    }

    #[test]
    fn multi_result_call_does_not_taint_unrelated_i256_result() {
        let ret_prov = ret_provenance(
            r#"
target = "evm-ethereum-osaka"

func public %mk() -> (i256, i256) {
block0:
    v0.*i8 = evm_malloc 32.i256;
    v1.i256 = ptr_to_int v0 i256;
    return (7.i256, v1);
}

func public %caller() -> i256 {
block0:
    (v0.i256, v1.i256) = call %mk;
    return v0;
}
"#,
            "caller",
        );

        assert!(!ret_prov.is_unknown_ptr(), "{ret_prov:?}");
        assert_eq!(ret_prov.malloc_insts().count(), 0, "{ret_prov:?}");
    }

    #[test]
    fn scalar_i256_arg_forwarding_does_not_create_pointer_provenance() {
        let ret_prov = ret_provenance(
            r#"
target = "evm-ethereum-osaka"

func public %id(v0.i256) -> i256 {
block0:
    return v0;
}

func public %caller(v0.i256) -> i256 {
block0:
    v1.i256 = call %id v0;
    return v1;
}
"#,
            "caller",
        );

        assert!(!ret_prov.is_unknown_ptr(), "{ret_prov:?}");
        assert_eq!(
            ret_prov.arg_indices().collect::<Vec<_>>(),
            Vec::<u32>::new()
        );
        assert_eq!(ret_prov.malloc_insts().count(), 0, "{ret_prov:?}");
    }

    #[test]
    fn call_result_marks_i256_encoded_non_arg_pointer_return_unknown() {
        let ret_prov = ret_provenance(
            r#"
target = "evm-ethereum-osaka"

func public %mk() -> i256 {
block0:
    v0.*i8 = evm_malloc 32.i256;
    v1.i256 = ptr_to_int v0 i256;
    return v1;
}

func public %caller() -> i256 {
block0:
    v0.i256 = call %mk;
    return v0;
}
"#,
            "caller",
        );

        assert!(ret_prov.is_unknown_ptr(), "{ret_prov:?}");
        assert_eq!(
            ret_prov.arg_indices().collect::<Vec<_>>(),
            Vec::<u32>::new()
        );
    }

    #[test]
    fn callee_heap_origins_survive_forwarding_and_mixed_returns() {
        for (alternative, has_arg, has_unknown) in [
            ("v5.i256 = ptr_to_int v0 i256;", true, false),
            (
                "v4.*i256 = int_to_ptr 4096.i256 *i256;\nv5.i256 = ptr_to_int v4 i256;",
                false,
                true,
            ),
            (
                "v4.*i256 = evm_malloc 64.i256;\nv5.i256 = ptr_to_int v4 i256;",
                false,
                false,
            ),
        ] {
            let source = format!(
                r#"
target = "evm-ethereum-osaka"
func private %make(v0.*i256, v1.i1) -> i256 {{
block0:
    br v1 block1 block2;
block1:
    v2.*i256 = evm_malloc 32.i256;
    v3.i256 = ptr_to_int v2 i256;
    return v3;
block2:
    {alternative}
    return v5;
}}
func private %forward(v0.*i256, v1.i1) -> i256 {{
block0:
    v2.i256 = call %make v0 v1;
    return v2;
}}
func public %caller(v0.*i256, v1.i1) -> i256 {{
block0:
    v2.i256 = call %forward v0 v1;
    return v2;
}}
"#
            );
            let provenance = ret_provenance(&source, "caller");
            assert!(provenance.may_reference_heap(), "{provenance:?}");
            assert!(provenance.is_unknown_ptr(), "heap identity remains unknown");
            assert_eq!(
                provenance.may_reference_unknown_local(),
                has_unknown,
                "{provenance:?}"
            );
            assert_eq!(
                provenance.arg_indices().collect::<Vec<_>>(),
                if has_arg { vec![0] } else { vec![] }
            );
            assert_eq!(
                provenance.malloc_insts().count(),
                0,
                "callee allocations have no local instruction identity"
            );
        }
    }

    #[test]
    fn unknown_clobber_keeps_heap_and_local_possibilities() {
        let mut provenance = Provenance {
            unknown_heap: true,
            ..Provenance::default()
        };
        assert!(!provenance.may_reference_unknown_local());
        assert!(provenance.mark_unknown_non_arg());
        assert!(provenance.may_reference_unknown_local());
        assert!(provenance.may_reference_heap());
        let alloca = InstId(3);
        assert!(provenance.union_with(&Provenance {
            bases: SmallVec::from_vec(vec![PtrBase::Alloca(alloca)]),
            ..Provenance::default()
        }));
        assert_eq!(provenance.alloca_insts().collect::<Vec<_>>(), vec![alloca]);
        assert!(provenance.may_reference_unknown_local());
        assert!(provenance.may_reference_heap());
    }
}
