use crate::bitset::BitSet;
use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use sonatina_ir::{
    BlockId, Function, InstId, InstSetExt, ValueId,
    inst::evm::inst_set::EvmInstKind,
    isa::{Isa, evm::Evm},
    module::{FuncRef, ModuleCtx},
};
use std::{cmp::Reverse, collections::BinaryHeap};

use super::{
    memory_plan::{AllocaClass, StackObjectPlan, WORD_BYTES},
    ptr_escape::PtrEscapeSummary,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum PtrBase {
    Arg(u32),
    Alloca(InstId),
}

impl PtrBase {
    fn key(self) -> (u8, u32) {
        match self {
            PtrBase::Arg(i) => (0, i),
            PtrBase::Alloca(inst) => (1, inst.as_u32()),
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Provenance {
    bases: SmallVec<[PtrBase; 4]>,
}

impl Provenance {
    fn union_with(&mut self, other: &Self) {
        if other.bases.is_empty() {
            return;
        }

        for base in other.bases.iter().copied() {
            if !self.bases.contains(&base) {
                self.bases.push(base);
            }
        }

        self.bases.sort_unstable_by_key(|b| b.key());
        self.bases.dedup();
    }

    fn is_local_addr(&self) -> bool {
        !self.bases.is_empty() && self.bases.iter().all(|b| matches!(b, PtrBase::Alloca(_)))
    }

    fn alloca_insts(&self) -> impl Iterator<Item = InstId> + '_ {
        self.bases.iter().filter_map(|b| match b {
            PtrBase::Alloca(inst) => Some(*inst),
            PtrBase::Arg(_) => None,
        })
    }
}

#[derive(Clone, Copy, Debug)]
struct AllocaObject {
    inst: InstId,
    start_pos: u32,
    end_pos: u32,
    size_words: u32,
}

#[derive(Clone, Copy, Debug)]
struct FreeBlock {
    offset_words: u32,
    size_words: u32,
}

#[derive(Default)]
pub(crate) struct StackAllocaLayout {
    pub(crate) plan: FxHashMap<InstId, StackObjectPlan>,
    pub(crate) persistent_words: u32,
    pub(crate) transient_words: u32,
}

pub(crate) fn compute_stack_alloca_layout(
    func_ref: FuncRef,
    function: &Function,
    module: &ModuleCtx,
    isa: &Evm,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
    call_live_values: &BitSet<ValueId>,
    block_order: &[BlockId],
) -> StackAllocaLayout {
    let (inst_order, inst_pos) = compute_inst_order(function, block_order);

    let mut allocas: FxHashMap<InstId, u32> = FxHashMap::default();
    for &inst in &inst_order {
        let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));
        let EvmInstKind::Alloca(alloca) = data else {
            continue;
        };

        let size_bytes: u32 = isa
            .type_layout()
            .size_of(*alloca.ty(), module)
            .expect("alloca has invalid type") as u32;
        let size_words = size_bytes.div_ceil(WORD_BYTES);
        allocas.insert(inst, size_words);
    }

    if allocas.is_empty() {
        return StackAllocaLayout::default();
    }

    let prov = compute_value_provenance(function, module, isa, ptr_escape);

    let escaping = compute_escaping_allocas(function, module, isa, ptr_escape, &prov);
    if !escaping.is_empty() {
        let name = module.func_sig(func_ref, |sig| sig.name().to_string());
        let mut ids: Vec<u32> = escaping.iter().map(|i| i.as_u32()).collect();
        ids.sort_unstable();
        panic!("alloca escapes in {name}: {ids:?}");
    }

    let mut persistent: FxHashSet<InstId> = FxHashSet::default();
    for val in call_live_values.iter() {
        for inst in prov[val].alloca_insts() {
            persistent.insert(inst);
        }
    }

    let mut last_use: FxHashMap<InstId, u32> = FxHashMap::default();
    for &inst in allocas.keys() {
        let pos = inst_pos.get(&inst).copied().unwrap_or_default();
        last_use.insert(inst, pos);
    }

    for &inst in &inst_order {
        let pos = inst_pos.get(&inst).copied().unwrap_or_default();
        function.dfg.inst(inst).for_each_value(&mut |v| {
            for base in prov[v].alloca_insts() {
                let entry = last_use.get_mut(&base).expect("missing alloca last-use");
                *entry = (*entry).max(pos);
            }
        });
    }

    let mut persistent_objects: Vec<AllocaObject> = Vec::new();
    let mut transient_objects: Vec<AllocaObject> = Vec::new();
    for (&inst, &size_words) in &allocas {
        let start_pos = inst_pos.get(&inst).copied().unwrap_or_default();
        let end_pos = last_use.get(&inst).copied().unwrap_or(start_pos);
        let obj = AllocaObject {
            inst,
            start_pos,
            end_pos,
            size_words,
        };

        if persistent.contains(&inst) {
            persistent_objects.push(obj);
        } else {
            transient_objects.push(obj);
        }
    }

    let (persistent_offsets, persistent_words) = color_allocas(&mut persistent_objects);
    let (transient_offsets, transient_words) = color_allocas(&mut transient_objects);

    let mut plan: FxHashMap<InstId, StackObjectPlan> = FxHashMap::default();
    for obj in persistent_objects {
        let offset_words = persistent_offsets.get(&obj.inst).copied().unwrap_or(0);
        plan.insert(
            obj.inst,
            StackObjectPlan {
                class: AllocaClass::Persistent,
                offset_words,
            },
        );
    }
    for obj in transient_objects {
        let offset_words = transient_offsets.get(&obj.inst).copied().unwrap_or(0);
        plan.insert(
            obj.inst,
            StackObjectPlan {
                class: AllocaClass::Transient,
                offset_words,
            },
        );
    }

    StackAllocaLayout {
        plan,
        persistent_words,
        transient_words,
    }
}

fn compute_inst_order(
    function: &Function,
    block_order: &[BlockId],
) -> (Vec<InstId>, FxHashMap<InstId, u32>) {
    let mut blocks: Vec<BlockId> = Vec::new();
    let mut seen: FxHashSet<BlockId> = FxHashSet::default();

    for &b in block_order {
        if seen.insert(b) {
            blocks.push(b);
        }
    }

    for b in function.layout.iter_block() {
        if seen.insert(b) {
            blocks.push(b);
        }
    }

    let mut order: Vec<InstId> = Vec::new();
    let mut pos: FxHashMap<InstId, u32> = FxHashMap::default();
    let mut next: u32 = 0;
    for b in blocks {
        for inst in function.layout.iter_inst(b) {
            pos.insert(inst, next);
            order.push(inst);
            next = next.checked_add(1).expect("instruction position overflow");
        }
    }

    (order, pos)
}

fn conservative_unknown_ptr_summary(module: &ModuleCtx, func_ref: FuncRef) -> PtrEscapeSummary {
    let arg_count = module.func_sig(func_ref, |sig| sig.args().len());
    PtrEscapeSummary {
        arg_may_escape: vec![true; arg_count],
        arg_may_be_returned: vec![true; arg_count],
        returns_any_ptr: module.func_sig(func_ref, |sig| sig.ret_ty().is_pointer(module)),
    }
}

fn compute_escaping_allocas(
    function: &Function,
    module: &ModuleCtx,
    isa: &Evm,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
    prov: &SecondaryMap<ValueId, Provenance>,
) -> FxHashSet<InstId> {
    let mut escaping: FxHashSet<InstId> = FxHashSet::default();

    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));
            match data {
                EvmInstKind::Return(ret) => {
                    let Some(ret_val) = *ret.arg() else {
                        continue;
                    };
                    for base in prov[ret_val].alloca_insts() {
                        escaping.insert(base);
                    }
                }
                EvmInstKind::Mstore(mstore) => {
                    let addr = *mstore.addr();
                    if prov[addr].is_local_addr() {
                        continue;
                    }

                    let val = *mstore.value();
                    for base in prov[val].alloca_insts() {
                        escaping.insert(base);
                    }
                }
                EvmInstKind::Call(call) => {
                    let callee = *call.callee();
                    let callee_sum = ptr_escape
                        .get(&callee)
                        .cloned()
                        .unwrap_or_else(|| conservative_unknown_ptr_summary(module, callee));
                    for (idx, &arg) in call.args().iter().enumerate() {
                        if idx < callee_sum.arg_may_escape.len() && callee_sum.arg_may_escape[idx] {
                            for base in prov[arg].alloca_insts() {
                                escaping.insert(base);
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }

    escaping
}

fn compute_value_provenance(
    function: &Function,
    module: &ModuleCtx,
    isa: &Evm,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
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
        }
    }

    let mut changed = true;
    while changed {
        changed = false;

        for block in function.layout.iter_block() {
            for inst in function.layout.iter_inst(block) {
                let Some(def) = function.dfg.inst_result(inst) else {
                    continue;
                };

                let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));
                let mut next = Provenance::default();

                match data {
                    EvmInstKind::Alloca(_) => next.bases.push(PtrBase::Alloca(inst)),
                    EvmInstKind::Phi(phi) => {
                        for (val, _) in phi.args().iter() {
                            next.union_with(&prov[*val]);
                        }
                    }
                    EvmInstKind::Gep(gep) => {
                        let Some(&base) = gep.values().first() else {
                            continue;
                        };
                        next.union_with(&prov[base]);
                    }
                    EvmInstKind::Bitcast(bc) => next.union_with(&prov[*bc.from()]),
                    EvmInstKind::IntToPtr(i2p) => next.union_with(&prov[*i2p.from()]),
                    EvmInstKind::PtrToInt(p2i) => next.union_with(&prov[*p2i.from()]),
                    EvmInstKind::InsertValue(iv) => {
                        next.union_with(&prov[*iv.dest()]);
                        next.union_with(&prov[*iv.value()]);
                    }
                    EvmInstKind::ExtractValue(ev) => next.union_with(&prov[*ev.dest()]),
                    EvmInstKind::Call(call) => {
                        let callee = *call.callee();
                        let callee_sum = ptr_escape
                            .get(&callee)
                            .cloned()
                            .unwrap_or_else(|| conservative_unknown_ptr_summary(module, callee));

                        for (idx, &arg) in call.args().iter().enumerate() {
                            if idx < callee_sum.arg_may_be_returned.len()
                                && callee_sum.arg_may_be_returned[idx]
                            {
                                next.union_with(&prov[arg]);
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
                            next.union_with(&prov[v]);
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

fn color_allocas(objects: &mut [AllocaObject]) -> (FxHashMap<InstId, u32>, u32) {
    objects.sort_unstable_by_key(|obj| (obj.start_pos, obj.end_pos, obj.inst.as_u32()));

    let mut offsets: FxHashMap<InstId, u32> = FxHashMap::default();
    let mut heap: BinaryHeap<Reverse<(u32, u32, u32)>> = BinaryHeap::new(); // (end, offset, size)
    let mut free: Vec<FreeBlock> = Vec::new();
    let mut pool_words: u32 = 0;

    for obj in objects.iter().copied() {
        while let Some(Reverse((end, offset, size))) = heap.peek().copied()
            && end < obj.start_pos
        {
            heap.pop();
            free.push(FreeBlock {
                offset_words: offset,
                size_words: size,
            });
        }

        if obj.size_words == 0 {
            offsets.insert(obj.inst, 0);
            continue;
        }

        let mut best_idx: Option<usize> = None;
        for (idx, block) in free.iter().enumerate() {
            if block.size_words < obj.size_words {
                continue;
            }
            match best_idx {
                None => best_idx = Some(idx),
                Some(best) if free[best].size_words > block.size_words => best_idx = Some(idx),
                _ => {}
            }
        }

        let offset_words = if let Some(idx) = best_idx {
            let block = &mut free[idx];
            let offset = block.offset_words;
            if block.size_words == obj.size_words {
                free.swap_remove(idx);
            } else {
                block.offset_words = block
                    .offset_words
                    .checked_add(obj.size_words)
                    .expect("alloca offset overflow");
                block.size_words = block
                    .size_words
                    .checked_sub(obj.size_words)
                    .expect("alloca free block underflow");
            }
            offset
        } else {
            let offset = pool_words;
            pool_words = pool_words
                .checked_add(obj.size_words)
                .expect("alloca pool overflow");
            offset
        };

        offsets.insert(obj.inst, offset_words);
        heap.push(Reverse((obj.end_pos, offset_words, obj.size_words)));
    }

    (offsets, pool_words)
}
