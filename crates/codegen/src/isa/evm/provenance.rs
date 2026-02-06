use cranelift_entity::SecondaryMap;
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use sonatina_ir::{
    Function, InstId, InstSetExt, ValueId,
    inst::evm::inst_set::EvmInstKind,
    isa::{Isa, evm::Evm},
    module::{FuncRef, ModuleCtx},
};

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

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Provenance {
    bases: SmallVec<[PtrBase; 4]>,
    unknown_ptr: bool,
}

impl Provenance {
    pub(crate) fn is_empty(&self) -> bool {
        self.bases.is_empty()
    }

    pub(crate) fn is_unknown_ptr(&self) -> bool {
        self.unknown_ptr
    }

    fn mark_unknown_ptr(&mut self) -> bool {
        let changed = !self.unknown_ptr || !self.bases.is_empty();
        self.unknown_ptr = true;
        self.bases.clear();
        changed
    }

    pub(crate) fn union_with(&mut self, other: &Self) -> bool {
        if self.unknown_ptr {
            return false;
        }

        if other.unknown_ptr {
            return self.mark_unknown_ptr();
        }

        if other.bases.is_empty() {
            return false;
        }

        let mut changed = false;
        for base in other.bases.iter().copied() {
            if !self.bases.contains(&base) {
                self.bases.push(base);
                changed = true;
            }
        }

        if changed {
            self.bases.sort_unstable_by_key(|b| b.key());
            self.bases.dedup();
        }
        changed
    }

    pub(crate) fn has_any_arg(&self) -> bool {
        self.bases.iter().any(|b| matches!(b, PtrBase::Arg(_)))
    }

    pub(crate) fn arg_indices(&self) -> impl Iterator<Item = u32> + '_ {
        self.bases.iter().filter_map(|b| match b {
            PtrBase::Arg(i) => Some(*i),
            PtrBase::Alloca(_) | PtrBase::Malloc(_) => None,
        })
    }

    pub(crate) fn is_local_addr(&self) -> bool {
        !self.unknown_ptr
            && !self.bases.is_empty()
            && self.bases.iter().all(|b| matches!(b, PtrBase::Alloca(_)))
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

fn store_local_mem(
    mem: &mut FxHashMap<InstId, Provenance>,
    addr_prov: &Provenance,
    val_prov: &Provenance,
) -> bool {
    if !addr_prov.is_local_addr() {
        return false;
    }

    let mut changed = false;
    for base in addr_prov.alloca_insts() {
        changed |= mem.entry(base).or_default().union_with(val_prov);
    }
    changed
}

fn load_local_mem(mem: &FxHashMap<InstId, Provenance>, addr_prov: &Provenance) -> Provenance {
    let mut out = Provenance::default();
    if addr_prov.is_local_addr() {
        for base in addr_prov.alloca_insts() {
            if let Some(stored) = mem.get(&base) {
                let _ = out.union_with(stored);
            }
        }
    }
    out
}

fn poison_local_mem(mem: &mut FxHashMap<InstId, Provenance>, addr_prov: &Provenance) -> bool {
    if !addr_prov.is_local_addr() {
        return false;
    }

    let mut changed = false;
    for base in addr_prov.alloca_insts() {
        changed |= mem.entry(base).or_default().mark_unknown_ptr();
    }
    changed
}

fn unmodeled_write_addr(data: &EvmInstKind) -> Option<ValueId> {
    match data {
        EvmInstKind::EvmMstore8(mstore8) => Some(*mstore8.addr()),
        EvmInstKind::EvmMcopy(mcopy) => Some(*mcopy.dest()),
        EvmInstKind::EvmCalldataCopy(copy) => Some(*copy.dst_addr()),
        EvmInstKind::EvmCodeCopy(copy) => Some(*copy.dst_addr()),
        EvmInstKind::EvmExtCodeCopy(copy) => Some(*copy.dst_addr()),
        EvmInstKind::EvmReturnDataCopy(copy) => Some(*copy.dst_addr()),
        EvmInstKind::EvmCall(call) => Some(*call.ret_addr()),
        EvmInstKind::EvmCallCode(call) => Some(*call.ret_addr()),
        EvmInstKind::EvmDelegateCall(call) => Some(*call.ret_addr()),
        EvmInstKind::EvmStaticCall(call) => Some(*call.ret_addr()),
        _ => None,
    }
}

pub(crate) struct ProvenanceInfo {
    pub(crate) value: SecondaryMap<ValueId, Provenance>,
    pub(crate) local_mem: FxHashMap<InstId, Provenance>,
}

pub(crate) fn compute_provenance(
    function: &Function,
    module: &ModuleCtx,
    isa: &Evm,
    callee_arg_may_be_returned: impl Fn(FuncRef) -> Vec<bool>,
) -> ProvenanceInfo {
    let mut prov: SecondaryMap<ValueId, Provenance> = SecondaryMap::new();
    for value in function.dfg.values.keys() {
        let _ = &mut prov[value];
    }

    for (idx, &arg) in function.arg_values.iter().enumerate() {
        // Always track argument provenance regardless of type.
        // On EVM all values are i256 (no pointer types), so is_pointer() would miss
        // arguments that are semantically pointers, making escape analysis unsound.
        prov[arg].bases.push(PtrBase::Arg(idx as u32));
    }

    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));
            if let Some(def) = function.dfg.inst_result(inst) {
                match data {
                    EvmInstKind::Alloca(_) => prov[def].bases.push(PtrBase::Alloca(inst)),
                    EvmInstKind::EvmMalloc(_) => prov[def].bases.push(PtrBase::Malloc(inst)),
                    _ => {}
                }
            }
        }
    }

    let mut mem: FxHashMap<InstId, Provenance> = FxHashMap::default();

    let mut changed = true;
    while changed {
        changed = false;

        for block in function.layout.iter_block() {
            for inst in function.layout.iter_inst(block) {
                let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));

                if let EvmInstKind::Mstore(mstore) = &data {
                    changed |=
                        store_local_mem(&mut mem, &prov[*mstore.addr()], &prov[*mstore.value()]);
                }

                if let Some(dst) = unmodeled_write_addr(&data) {
                    changed |= poison_local_mem(&mut mem, &prov[dst]);
                }

                let Some(def) = function.dfg.inst_result(inst) else {
                    continue;
                };

                let mut next = Provenance::default();

                match data {
                    EvmInstKind::Alloca(_) => next.bases.push(PtrBase::Alloca(inst)),
                    EvmInstKind::EvmMalloc(_) => next.bases.push(PtrBase::Malloc(inst)),
                    EvmInstKind::Mload(mload) => {
                        let _ = next.union_with(&load_local_mem(&mem, &prov[*mload.addr()]));
                    }
                    EvmInstKind::Phi(phi) => {
                        for (val, _) in phi.args().iter() {
                            let _ = next.union_with(&prov[*val]);
                        }
                    }
                    EvmInstKind::Gep(gep) => {
                        let Some(&base) = gep.values().first() else {
                            continue;
                        };
                        let _ = next.union_with(&prov[base]);
                    }
                    EvmInstKind::Bitcast(bc) => {
                        let _ = next.union_with(&prov[*bc.from()]);
                    }
                    EvmInstKind::IntToPtr(i2p) => {
                        let from = *i2p.from();
                        let from_prov = &prov[from];
                        let _ = next.union_with(from_prov);
                        if from_prov.bases.is_empty() && !from_prov.unknown_ptr {
                            next.unknown_ptr = true;
                        }
                    }
                    EvmInstKind::PtrToInt(p2i) => {
                        let _ = next.union_with(&prov[*p2i.from()]);
                    }
                    EvmInstKind::InsertValue(iv) => {
                        let _ = next.union_with(&prov[*iv.dest()]);
                        let _ = next.union_with(&prov[*iv.value()]);
                    }
                    EvmInstKind::ExtractValue(ev) => {
                        let _ = next.union_with(&prov[*ev.dest()]);
                    }
                    EvmInstKind::Call(call) => {
                        let arg_may_be_returned = callee_arg_may_be_returned(*call.callee());
                        for (idx, &arg) in call.args().iter().enumerate() {
                            if arg_may_be_returned.get(idx).copied().unwrap_or(false) {
                                let _ = next.union_with(&prov[arg]);
                            }
                        }
                        if function.dfg.value_ty(def).is_pointer(module)
                            && next.bases.is_empty()
                            && !next.unknown_ptr
                        {
                            // Calls that return pointers with no tracked base still produce
                            // pointer-typed results; treat these as unknown to avoid
                            // unsoundly classifying overlapping mallocs as transient.
                            next.unknown_ptr = true;
                        }
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
                    | EvmInstKind::EvmByte(_)
                    | EvmInstKind::EvmClz(_) => {
                        function.dfg.inst(inst).for_each_value(&mut |v| {
                            let _ = next.union_with(&prov[v]);
                        });
                    }
                    _ => {}
                }

                let cur = &mut prov[def];
                if *cur != next {
                    *cur = next;
                    changed = true;
                }
            }
        }
    }

    ProvenanceInfo {
        value: prov,
        local_mem: mem,
    }
}

pub(crate) fn compute_value_provenance(
    function: &Function,
    module: &ModuleCtx,
    isa: &Evm,
    callee_arg_may_be_returned: impl Fn(FuncRef) -> Vec<bool>,
) -> SecondaryMap<ValueId, Provenance> {
    compute_provenance(function, module, isa, callee_arg_may_be_returned).value
}
