use crate::{bitset::BitSet, liveness::InstLiveness};
use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    BlockId, Function, InstId, InstSetExt, ValueId,
    inst::evm::inst_set::EvmInstKind,
    isa::{Isa, evm::Evm},
    module::{FuncRef, ModuleCtx},
};
use std::{cmp::Reverse, collections::BinaryHeap};

use super::{
    memory_plan::{AllocaClass, StackObjectPlan, WORD_BYTES},
    provenance::{Provenance, compute_value_provenance},
    ptr_escape::PtrEscapeSummary,
};

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

#[derive(Clone, Copy)]
pub(crate) struct AllocaLayoutLiveness<'a> {
    pub(crate) call_live_values: &'a BitSet<ValueId>,
    pub(crate) inst_liveness: &'a InstLiveness,
}

pub(crate) fn compute_stack_alloca_layout(
    func_ref: FuncRef,
    function: &Function,
    module: &ModuleCtx,
    isa: &Evm,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
    live: AllocaLayoutLiveness<'_>,
    block_order: &[BlockId],
) -> StackAllocaLayout {
    let (inst_order, inst_pos) = compute_inst_order(function, block_order);
    let block_end_pos = compute_block_end_pos(function, &inst_pos);

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

    let prov = compute_value_provenance(function, module, isa, |callee| {
        ptr_escape
            .get(&callee)
            .cloned()
            .unwrap_or_else(|| conservative_unknown_ptr_summary(module, callee))
            .arg_may_be_returned
    });

    let escaping_sites = compute_escaping_allocas(function, module, isa, ptr_escape, &prov);
    if !escaping_sites.is_empty() {
        let name = module.func_sig(func_ref, |sig| sig.name().to_string());
        let mut allocas: Vec<(InstId, Vec<AllocaEscapeSite>)> =
            escaping_sites.into_iter().collect();
        allocas.sort_unstable_by_key(|(inst, _)| inst.as_u32());

        let mut msg = String::new();
        msg.push_str(&format!("alloca escapes in {name}:\n"));
        for (alloca_inst, mut sites) in allocas {
            sites.sort_unstable_by_key(|s| (s.escape_inst().as_u32(), s.derived_value().as_u32()));
            msg.push_str(&format!("  alloca inst {}:\n", alloca_inst.as_u32()));
            for site in sites {
                msg.push_str("    - ");
                msg.push_str(&site.render(module));
                msg.push('\n');
            }
        }
        panic!("{msg}");
    }

    let mut persistent: FxHashSet<InstId> = FxHashSet::default();
    for val in live.call_live_values.iter() {
        for inst in prov[val].alloca_insts() {
            persistent.insert(inst);
        }
    }

    let mut last_live: FxHashMap<InstId, u32> = FxHashMap::default();
    for &inst in allocas.keys() {
        let pos = inst_pos.get(&inst).copied().unwrap_or_default();
        last_live.insert(inst, pos);
    }

    for &inst in &inst_order {
        let pos = inst_pos.get(&inst).copied().unwrap_or_default();
        let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));
        if let EvmInstKind::Phi(phi) = data {
            for (val, pred) in phi.args().iter() {
                let use_pos = block_end_pos.get(pred).copied().unwrap_or_default();
                for base in prov[*val].alloca_insts() {
                    let entry = last_live.get_mut(&base).expect("missing alloca last-live");
                    *entry = (*entry).max(use_pos);
                }
            }
        } else {
            function.dfg.inst(inst).for_each_value(&mut |v| {
                for base in prov[v].alloca_insts() {
                    let entry = last_live.get_mut(&base).expect("missing alloca last-live");
                    *entry = (*entry).max(pos);
                }
            });
        }

        for val in live.inst_liveness.live_out(inst).iter() {
            if prov[val].is_empty() {
                continue;
            }
            for base in prov[val].alloca_insts() {
                let entry = last_live.get_mut(&base).expect("missing alloca last-live");
                *entry = (*entry).max(pos);
            }
        }
    }

    let mut persistent_objects: Vec<AllocaObject> = Vec::new();
    let mut transient_objects: Vec<AllocaObject> = Vec::new();
    for (&inst, &size_words) in &allocas {
        let start_pos = inst_pos.get(&inst).copied().unwrap_or_default();
        let end_pos = last_live.get(&inst).copied().unwrap_or(start_pos);
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

fn compute_block_end_pos(
    function: &Function,
    inst_pos: &FxHashMap<InstId, u32>,
) -> FxHashMap<BlockId, u32> {
    let mut out: FxHashMap<BlockId, u32> = FxHashMap::default();
    for block in function.layout.iter_block() {
        let mut end: Option<u32> = None;
        for inst in function.layout.iter_inst(block) {
            end = Some(inst_pos.get(&inst).copied().unwrap_or_default());
        }
        out.insert(block, end.unwrap_or(0));
    }
    out
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
) -> FxHashMap<InstId, Vec<AllocaEscapeSite>> {
    let mut escaping: FxHashMap<InstId, Vec<AllocaEscapeSite>> = FxHashMap::default();

    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));
            match data {
                EvmInstKind::Return(ret) => {
                    let Some(ret_val) = *ret.arg() else {
                        continue;
                    };
                    for base in prov[ret_val].alloca_insts() {
                        escaping
                            .entry(base)
                            .or_default()
                            .push(AllocaEscapeSite::Return {
                                inst,
                                value: ret_val,
                            });
                    }
                }
                EvmInstKind::Mstore(mstore) => {
                    let addr = *mstore.addr();
                    if prov[addr].is_local_addr() {
                        continue;
                    }

                    let val = *mstore.value();
                    for base in prov[val].alloca_insts() {
                        escaping
                            .entry(base)
                            .or_default()
                            .push(AllocaEscapeSite::NonLocalStore {
                                inst,
                                addr,
                                value: val,
                            });
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
                                escaping
                                    .entry(base)
                                    .or_default()
                                    .push(AllocaEscapeSite::CallArg {
                                        inst,
                                        callee,
                                        arg_index: idx,
                                        value: arg,
                                    });
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

#[derive(Clone, Debug)]
enum AllocaEscapeSite {
    Return {
        inst: InstId,
        value: ValueId,
    },
    NonLocalStore {
        inst: InstId,
        addr: ValueId,
        value: ValueId,
    },
    CallArg {
        inst: InstId,
        callee: FuncRef,
        arg_index: usize,
        value: ValueId,
    },
}

impl AllocaEscapeSite {
    fn escape_inst(&self) -> InstId {
        match self {
            AllocaEscapeSite::Return { inst, .. }
            | AllocaEscapeSite::NonLocalStore { inst, .. }
            | AllocaEscapeSite::CallArg { inst, .. } => *inst,
        }
    }

    fn derived_value(&self) -> ValueId {
        match self {
            AllocaEscapeSite::Return { value, .. }
            | AllocaEscapeSite::NonLocalStore { value, .. }
            | AllocaEscapeSite::CallArg { value, .. } => *value,
        }
    }

    fn render(&self, module: &ModuleCtx) -> String {
        match self {
            AllocaEscapeSite::Return { inst, value } => {
                format!("return of v{} at inst {}", value.as_u32(), inst.as_u32())
            }
            AllocaEscapeSite::NonLocalStore { inst, addr, value } => format!(
                "non-local store of v{} to addr v{} at inst {}",
                value.as_u32(),
                addr.as_u32(),
                inst.as_u32()
            ),
            AllocaEscapeSite::CallArg {
                inst,
                callee,
                arg_index,
                value,
            } => {
                let callee_name = module.func_sig(*callee, |sig| sig.name().to_string());
                format!(
                    "call arg {arg_index} v{} to %{callee_name} at inst {}",
                    value.as_u32(),
                    inst.as_u32()
                )
            }
        }
    }
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        domtree::DomTree,
        liveness::{InstLiveness, Liveness},
    };
    use sonatina_ir::cfg::ControlFlowGraph;
    use sonatina_parser::parse_module;
    use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

    #[test]
    fn phi_uses_are_accounted_on_predecessor_edges() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func public %f() -> i256 {
block0:
    v0.*i256 = alloca i256;
    jump block1;

block1:
    v2.*i256 = phi (v0 block0) (v2 block3);
    v3.i32 = phi (0.i32 block0) (v6 block3);
    v4.i1 = lt v3 1.i32;
    br v4 block2 block4;

block2:
    v5.*i256 = alloca i256;
    mstore v5 1.i256 i256;
    v6.i32 = add v3 1.i32;
    jump block3;

block3:
    jump block1;

block4:
    return 0.i256;
}
"#,
        )
        .unwrap();

        let f = parsed
            .module
            .funcs()
            .into_iter()
            .find(|&f| parsed.module.ctx.func_sig(f, |sig| sig.name() == "f"))
            .expect("missing function f");

        let isa = Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        });

        parsed.module.func_store.view(f, |function| {
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(function);

            let mut liveness = Liveness::new();
            liveness.compute(function, &cfg);

            let mut inst_liveness = InstLiveness::new();
            inst_liveness.compute(function, &cfg, &liveness);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let block_order = dom.rpo().to_owned();

            let call_live_values = BitSet::default();
            let layout = compute_stack_alloca_layout(
                f,
                function,
                &parsed.module.ctx,
                &isa,
                &FxHashMap::default(),
                AllocaLayoutLiveness {
                    call_live_values: &call_live_values,
                    inst_liveness: &inst_liveness,
                },
                &block_order,
            );

            assert_eq!(layout.persistent_words, 0);
            assert_eq!(layout.transient_words, 2);

            let mut allocas: Vec<InstId> = Vec::new();
            for block in function.layout.iter_block() {
                for inst in function.layout.iter_inst(block) {
                    if matches!(
                        isa.inst_set().resolve_inst(function.dfg.inst(inst)),
                        EvmInstKind::Alloca(_)
                    ) {
                        allocas.push(inst);
                    }
                }
            }
            allocas.sort_unstable_by_key(|inst| inst.as_u32());
            assert_eq!(allocas.len(), 2);

            let off0 = layout
                .plan
                .get(&allocas[0])
                .expect("missing alloca plan")
                .offset_words;
            let off1 = layout
                .plan
                .get(&allocas[1])
                .expect("missing alloca plan")
                .offset_words;
            assert_ne!(off0, off1, "allocas should not overlap in memory");
        });
    }

    #[test]
    #[should_panic(expected = "alloca escapes in f")]
    fn alloca_escape_through_local_store_load_is_rejected() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func public %f() -> *i256 {
block0:
    v0.*i256 = alloca i256;
    v1.**i256 = alloca *i256;
    mstore v1 v0 *i256;
    v2.*i256 = mload v1 *i256;
    return v2;
}
"#,
        )
        .unwrap();

        let f = parsed
            .module
            .funcs()
            .into_iter()
            .find(|&f| parsed.module.ctx.func_sig(f, |sig| sig.name() == "f"))
            .expect("missing function f");

        let isa = Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        });

        parsed.module.func_store.view(f, |function| {
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(function);

            let mut liveness = Liveness::new();
            liveness.compute(function, &cfg);

            let mut inst_liveness = InstLiveness::new();
            inst_liveness.compute(function, &cfg, &liveness);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let block_order = dom.rpo().to_owned();

            let call_live_values = BitSet::default();
            let _ = compute_stack_alloca_layout(
                f,
                function,
                &parsed.module.ctx,
                &isa,
                &FxHashMap::default(),
                AllocaLayoutLiveness {
                    call_live_values: &call_live_values,
                    inst_liveness: &inst_liveness,
                },
                &block_order,
            );
        });
    }
}
