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
}

impl Provenance {
    pub(crate) fn is_empty(&self) -> bool {
        self.bases.is_empty()
    }

    pub(crate) fn union_with(&mut self, other: &Self) -> bool {
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
        !self.bases.is_empty() && self.bases.iter().all(|b| matches!(b, PtrBase::Alloca(_)))
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

pub(crate) fn compute_value_provenance(
    function: &Function,
    module: &ModuleCtx,
    isa: &Evm,
    callee_arg_may_be_returned: impl Fn(FuncRef) -> Vec<bool>,
) -> SecondaryMap<ValueId, Provenance> {
    let mut prov: SecondaryMap<ValueId, Provenance> = SecondaryMap::new();
    for value in function.dfg.values.keys() {
        let _ = &mut prov[value];
    }

    for (idx, &arg) in function.arg_values.iter().enumerate() {
        if function.dfg.value_ty(arg).is_pointer(module) {
            prov[arg].bases.push(PtrBase::Arg(idx as u32));
        }
    }

    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));
            if let EvmInstKind::Alloca(_) = data
                && let Some(def) = function.dfg.inst_result(inst)
            {
                prov[def].bases.push(PtrBase::Alloca(inst));
            }

            if let EvmInstKind::EvmMalloc(_) = data
                && let Some(def) = function.dfg.inst_result(inst)
            {
                prov[def].bases.push(PtrBase::Malloc(inst));
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

                if let EvmInstKind::Mstore(mstore) = data {
                    let addr = *mstore.addr();
                    let addr_prov = &prov[addr];
                    if addr_prov.is_local_addr() {
                        let val = *mstore.value();
                        let val_prov = &prov[val];
                        for base in addr_prov.alloca_insts() {
                            let entry = mem.entry(base).or_default();
                            if entry.union_with(val_prov) {
                                changed = true;
                            }
                        }
                    }
                }

                let Some(def) = function.dfg.inst_result(inst) else {
                    continue;
                };

                let mut next = Provenance::default();

                match data {
                    EvmInstKind::Alloca(_) => next.bases.push(PtrBase::Alloca(inst)),
                    EvmInstKind::EvmMalloc(_) => next.bases.push(PtrBase::Malloc(inst)),
                    EvmInstKind::Mload(mload) => {
                        let addr = *mload.addr();
                        let addr_prov = &prov[addr];
                        if addr_prov.is_local_addr() {
                            for base in addr_prov.alloca_insts() {
                                if let Some(stored) = mem.get(&base) {
                                    let _ = next.union_with(stored);
                                }
                            }
                        }
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
                        let _ = next.union_with(&prov[*i2p.from()]);
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
                    | EvmInstKind::Trunc(_) => {
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

    prov
}
