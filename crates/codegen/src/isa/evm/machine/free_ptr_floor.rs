use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    AccessKind, BlockId, Function, InstId, InstSetExt, Module, ValueId,
    cfg::ControlFlowGraph,
    inst::evm::inst_set::{EvmInstKind, EvmInstSet},
    isa::{Isa, evm::Evm},
    module::{FuncRef, ModuleCtx},
};

use crate::isa::evm::{
    EvmBackend, FREE_PTR_SLOT, WORD_BYTES,
    prepare::{memory_access_may_touch_free_ptr_slot, value_imm_u32},
    provenance::{Provenance, compute_value_provenance},
    ptr_escape::PtrEscapeSummary,
};

use super::placement::MallocPlacement;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
enum FreePtrFloor {
    #[default]
    Unknown,
    Known(u32),
}

impl FreePtrFloor {
    fn join(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Self::Known(lhs), Self::Known(rhs)) => Self::Known(lhs.min(rhs)),
            (Self::Unknown, _) | (_, Self::Unknown) => Self::Unknown,
        }
    }

    fn establish_min(self, min_base: u32) -> Self {
        match self {
            Self::Unknown => Self::Known(min_base),
            Self::Known(floor) => Self::Known(floor.max(min_base)),
        }
    }

    fn as_option(self) -> Option<u32> {
        match self {
            Self::Unknown => None,
            Self::Known(floor) => Some(floor),
        }
    }
}

pub(crate) fn compute_free_ptr_write_summaries(
    module: &Module,
    funcs: &[FuncRef],
    local_writes: &FxHashMap<FuncRef, bool>,
    isa: &Evm,
) -> FxHashMap<FuncRef, bool> {
    let funcs_set: FxHashSet<FuncRef> = funcs.iter().copied().collect();
    let mut writes = local_writes.clone();
    let mut changed = true;
    while changed {
        changed = false;
        for &func in funcs {
            let mut func_writes = writes.get(&func).copied().unwrap_or(true);
            if !func_writes {
                func_writes = module.func_store.view(func, |function| {
                    function.layout.iter_block().any(|block| {
                        function.layout.iter_inst(block).any(|inst| {
                            let EvmInstKind::Call(call) =
                                isa.inst_set().resolve_inst(function.dfg.inst(inst))
                            else {
                                return false;
                            };
                            let callee = *call.callee();
                            !funcs_set.contains(&callee)
                                || writes.get(&callee).copied().unwrap_or(true)
                        })
                    })
                });
            }
            if writes.insert(func, func_writes) != Some(func_writes) {
                changed = true;
            }
        }
    }
    writes
}

pub(crate) fn compute_free_ptr_floor_before_malloc(
    function: &Function,
    module: &ModuleCtx,
    backend: &EvmBackend,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
    source_is: &EvmInstSet,
    malloc_placements: &FxHashMap<InstId, MallocPlacement>,
    free_ptr_write_summaries: &FxHashMap<FuncRef, bool>,
) -> FxHashMap<InstId, Option<u32>> {
    let mut cfg = ControlFlowGraph::new();
    cfg.compute(function);

    let prov = compute_value_provenance(function, module, &backend.isa, |callee| {
        ptr_escape
            .get(&callee)
            .cloned()
            .unwrap_or_else(|| PtrEscapeSummary::conservative_unknown_ctx(module, callee))
    });

    let mut block_in = SecondaryMap::<BlockId, FreePtrFloor>::new();
    let mut block_out = SecondaryMap::<BlockId, FreePtrFloor>::new();
    for block in function.dfg.block_ids() {
        let _ = &mut block_in[block];
        let _ = &mut block_out[block];
    }

    let transfer = TransferCtx {
        function,
        module,
        source_is,
        malloc_placements,
        free_ptr_write_summaries,
        prov: &prov,
    };
    let mut changed = true;
    while changed {
        changed = false;
        for block in function.layout.iter_block() {
            let entry = block_entry_floor(&cfg, block, &block_out);
            let exit = transfer.block(block, entry, None);
            if block_in[block] != entry {
                block_in[block] = entry;
                changed = true;
            }
            if block_out[block] != exit {
                block_out[block] = exit;
                changed = true;
            }
        }
    }

    let mut before_malloc = FxHashMap::default();
    for block in function.layout.iter_block() {
        transfer.block(block, block_in[block], Some(&mut before_malloc));
    }
    before_malloc
}

fn block_entry_floor(
    cfg: &ControlFlowGraph,
    block: BlockId,
    block_out: &SecondaryMap<BlockId, FreePtrFloor>,
) -> FreePtrFloor {
    let mut floor = FreePtrFloor::Unknown;
    for pred in cfg.preds_of(block) {
        floor = floor.join(block_out[*pred]);
    }
    floor
}

struct TransferCtx<'a> {
    function: &'a Function,
    module: &'a ModuleCtx,
    source_is: &'a EvmInstSet,
    malloc_placements: &'a FxHashMap<InstId, MallocPlacement>,
    free_ptr_write_summaries: &'a FxHashMap<FuncRef, bool>,
    prov: &'a SecondaryMap<ValueId, Provenance>,
}

impl TransferCtx<'_> {
    fn block(
        &self,
        block: BlockId,
        mut floor: FreePtrFloor,
        mut before_malloc: Option<&mut FxHashMap<InstId, Option<u32>>>,
    ) -> FreePtrFloor {
        for inst in self.function.layout.iter_inst(block) {
            match self.source_is.resolve_inst(self.function.dfg.inst(inst)) {
                EvmInstKind::EvmMalloc(_) => {
                    if let Some(placement) = self.malloc_placements.get(&inst).copied() {
                        if let Some(before_malloc) = before_malloc.as_deref_mut() {
                            before_malloc.insert(inst, floor.as_option());
                        }
                        if let MallocPlacement::Heap {
                            min_base,
                            update_free_ptr: true,
                            ..
                        } = placement
                        {
                            // Compiler-managed free-pointer updates are part of the allocator
                            // invariant: they cannot wrap below the established floor.
                            floor = floor.establish_min(min_base);
                        }
                    }
                }
                EvmInstKind::Call(call) => {
                    if self
                        .free_ptr_write_summaries
                        .get(call.callee())
                        .copied()
                        .unwrap_or(true)
                    {
                        floor = FreePtrFloor::Unknown;
                    }
                }
                _ => {
                    if let Some(stored_floor) = self.exact_free_ptr_store_floor(inst) {
                        floor = stored_floor.map_or(FreePtrFloor::Unknown, FreePtrFloor::Known);
                    } else if self.inst_writes_free_ptr_slot(inst) {
                        floor = FreePtrFloor::Unknown;
                    }
                }
            }
        }
        floor
    }

    fn exact_free_ptr_store_floor(&self, inst: InstId) -> Option<Option<u32>> {
        match self.source_is.resolve_inst(self.function.dfg.inst(inst)) {
            EvmInstKind::Mstore(mstore)
                if self.module.size_of(*mstore.ty()).ok() == Some(WORD_BYTES as usize)
                    && value_imm_u32(self.function, *mstore.addr())
                        == Some(FREE_PTR_SLOT as u32) =>
            {
                Some(value_imm_u32(self.function, *mstore.value()))
            }
            EvmInstKind::EvmMstore(mstore)
                if value_imm_u32(self.function, *mstore.addr()) == Some(FREE_PTR_SLOT as u32) =>
            {
                Some(value_imm_u32(self.function, *mstore.value()))
            }
            _ => None,
        }
    }

    fn inst_writes_free_ptr_slot(&self, inst: InstId) -> bool {
        self.function
            .dfg
            .effects(inst)
            .accesses
            .iter()
            .any(|access| {
                access.kind == AccessKind::Write
                    && memory_access_may_touch_free_ptr_slot(self.function, access, self.prov)
            })
    }
}
