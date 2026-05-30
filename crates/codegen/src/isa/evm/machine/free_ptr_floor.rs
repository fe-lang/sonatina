use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    AccessKind, BlockId, Function, InstId, InstSetExt, Module, ValueId,
    cfg::ControlFlowGraph,
    inst::evm::inst_set::{EvmInstKind, EvmInstSet},
    isa::{Isa, evm::Evm},
    module::{FuncRef, ModuleCtx},
};
use std::iter;

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

pub(crate) struct ProgramFreePtrFloorInput<'a> {
    pub(crate) module: &'a Module,
    pub(crate) funcs: &'a [FuncRef],
    pub(crate) section_entry: FuncRef,
    pub(crate) section_includes: &'a [FuncRef],
    pub(crate) backend: &'a EvmBackend,
    pub(crate) ptr_escape: &'a FxHashMap<FuncRef, PtrEscapeSummary>,
    pub(crate) source_is: &'a EvmInstSet,
    pub(crate) malloc_placements: &'a FxHashMap<FuncRef, FxHashMap<InstId, MallocPlacement>>,
    pub(crate) free_ptr_write_summaries: &'a FxHashMap<FuncRef, bool>,
}

pub(crate) fn compute_program_free_ptr_floor_before_malloc(
    input: ProgramFreePtrFloorInput<'_>,
) -> FxHashMap<FuncRef, FxHashMap<InstId, Option<u32>>> {
    let ProgramFreePtrFloorInput {
        module,
        funcs,
        section_entry,
        section_includes,
        backend,
        ptr_escape,
        source_is,
        malloc_placements,
        free_ptr_write_summaries,
    } = input;
    let funcs_set: FxHashSet<FuncRef> = funcs.iter().copied().collect();
    let exit_floor_summaries = compute_exit_floor_summaries(
        module,
        funcs,
        backend,
        ptr_escape,
        source_is,
        malloc_placements,
        free_ptr_write_summaries,
    );
    let mut entry_floors: FxHashMap<FuncRef, Option<FreePtrFloor>> =
        funcs.iter().copied().map(|func| (func, None)).collect();
    for root in iter::once(section_entry).chain(section_includes.iter().copied()) {
        if funcs_set.contains(&root) {
            entry_floors.insert(root, Some(FreePtrFloor::Unknown));
        }
    }

    let mut changed = true;
    while changed {
        changed = false;
        let mut next_entry_floors = entry_floors.clone();
        for &func in funcs {
            let Some(entry_floor) = entry_floors.get(&func).copied().flatten() else {
                continue;
            };
            let call_floors = module.func_store.view(func, |function| {
                let empty_placements = FxHashMap::default();
                let malloc_placements = malloc_placements.get(&func).unwrap_or(&empty_placements);
                FuncFreePtrFloorCtx {
                    module: &module.ctx,
                    backend,
                    ptr_escape,
                    source_is,
                    malloc_placements,
                    free_ptr_write_summaries,
                    exit_floor_summaries: &exit_floor_summaries,
                }
                .compute(function, entry_floor)
                .before_call
            });

            for (callee, floor) in call_floors {
                if funcs_set.contains(&callee) {
                    let next = next_entry_floors.entry(callee).or_insert(None);
                    *next = Some(next.map_or(floor, |old| old.join(floor)));
                }
            }
        }
        for &func in funcs {
            if next_entry_floors.get(&func) != entry_floors.get(&func) {
                changed = true;
                break;
            }
        }
        entry_floors = next_entry_floors;
    }

    funcs
        .iter()
        .copied()
        .map(|func| {
            let entry_floor = entry_floors
                .get(&func)
                .copied()
                .flatten()
                .unwrap_or(FreePtrFloor::Unknown);
            let before_malloc = module.func_store.view(func, |function| {
                let empty_placements = FxHashMap::default();
                let malloc_placements = malloc_placements.get(&func).unwrap_or(&empty_placements);
                FuncFreePtrFloorCtx {
                    module: &module.ctx,
                    backend,
                    ptr_escape,
                    source_is,
                    malloc_placements,
                    free_ptr_write_summaries,
                    exit_floor_summaries: &exit_floor_summaries,
                }
                .compute(function, entry_floor)
                .before_malloc
            });
            (func, before_malloc)
        })
        .collect()
}

fn compute_exit_floor_summaries(
    module: &Module,
    funcs: &[FuncRef],
    backend: &EvmBackend,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
    source_is: &EvmInstSet,
    malloc_placements: &FxHashMap<FuncRef, FxHashMap<InstId, MallocPlacement>>,
    free_ptr_write_summaries: &FxHashMap<FuncRef, bool>,
) -> FxHashMap<FuncRef, Option<u32>> {
    let mut summaries: FxHashMap<FuncRef, Option<u32>> =
        funcs.iter().copied().map(|func| (func, None)).collect();

    let mut changed = true;
    while changed {
        changed = false;
        for &func in funcs {
            let summary = module.func_store.view(func, |function| {
                let empty_placements = FxHashMap::default();
                let malloc_placements = malloc_placements.get(&func).unwrap_or(&empty_placements);
                FuncFreePtrFloorCtx {
                    module: &module.ctx,
                    backend,
                    ptr_escape,
                    source_is,
                    malloc_placements,
                    free_ptr_write_summaries,
                    exit_floor_summaries: &summaries,
                }
                .compute(function, FreePtrFloor::Unknown)
                .exit_floor
                .as_option()
            });
            if summaries.insert(func, summary) != Some(summary) {
                changed = true;
            }
        }
    }

    summaries
}

struct FuncFreePtrFloors {
    before_malloc: FxHashMap<InstId, Option<u32>>,
    before_call: Vec<(FuncRef, FreePtrFloor)>,
    exit_floor: FreePtrFloor,
}

struct FuncFreePtrFloorCtx<'a> {
    module: &'a ModuleCtx,
    backend: &'a EvmBackend,
    ptr_escape: &'a FxHashMap<FuncRef, PtrEscapeSummary>,
    source_is: &'a EvmInstSet,
    malloc_placements: &'a FxHashMap<InstId, MallocPlacement>,
    free_ptr_write_summaries: &'a FxHashMap<FuncRef, bool>,
    exit_floor_summaries: &'a FxHashMap<FuncRef, Option<u32>>,
}

impl FuncFreePtrFloorCtx<'_> {
    fn compute(&self, function: &Function, entry_floor: FreePtrFloor) -> FuncFreePtrFloors {
        let mut cfg = ControlFlowGraph::new();
        cfg.compute(function);

        let prov = compute_value_provenance(function, self.module, &self.backend.isa, |callee| {
            self.ptr_escape
                .get(&callee)
                .cloned()
                .unwrap_or_else(|| PtrEscapeSummary::conservative_unknown_ctx(self.module, callee))
        });

        let mut block_in = SecondaryMap::<BlockId, FreePtrFloor>::new();
        let mut block_out = SecondaryMap::<BlockId, FreePtrFloor>::new();
        for block in function.dfg.block_ids() {
            block_in[block] = entry_floor;
            block_out[block] = entry_floor;
        }

        let transfer = TransferCtx {
            function,
            module: self.module,
            source_is: self.source_is,
            malloc_placements: self.malloc_placements,
            free_ptr_write_summaries: self.free_ptr_write_summaries,
            exit_floor_summaries: self.exit_floor_summaries,
            prov: &prov,
        };
        let mut changed = true;
        while changed {
            changed = false;
            for block in function.layout.iter_block() {
                let entry = block_entry_floor(&cfg, block, &block_out, entry_floor);
                let exit = transfer.block(block, entry, None, None);
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
        let mut before_call = Vec::new();
        for block in function.layout.iter_block() {
            transfer.block(
                block,
                block_in[block],
                Some(&mut before_malloc),
                Some(&mut before_call),
            );
        }
        FuncFreePtrFloors {
            before_malloc,
            before_call,
            exit_floor: function_exit_floor(function, self.source_is, &block_out),
        }
    }
}

fn function_exit_floor(
    function: &Function,
    source_is: &EvmInstSet,
    block_out: &SecondaryMap<BlockId, FreePtrFloor>,
) -> FreePtrFloor {
    let mut out = None;
    for block in function.layout.iter_block() {
        let returns_to_caller = function.layout.iter_inst(block).last().is_some_and(|inst| {
            matches!(
                source_is.resolve_inst(function.dfg.inst(inst)),
                EvmInstKind::Return(_)
            )
        });
        if returns_to_caller {
            out = Some(out.map_or(block_out[block], |floor: FreePtrFloor| {
                floor.join(block_out[block])
            }));
        }
    }
    out.unwrap_or(FreePtrFloor::Unknown)
}

fn block_entry_floor(
    cfg: &ControlFlowGraph,
    block: BlockId,
    block_out: &SecondaryMap<BlockId, FreePtrFloor>,
    entry_floor: FreePtrFloor,
) -> FreePtrFloor {
    let mut floor = FreePtrFloor::Unknown;
    let mut has_pred = false;
    for pred in cfg.preds_of(block) {
        has_pred = true;
        floor = floor.join(block_out[*pred]);
    }
    if has_pred { floor } else { entry_floor }
}

struct TransferCtx<'a> {
    function: &'a Function,
    module: &'a ModuleCtx,
    source_is: &'a EvmInstSet,
    malloc_placements: &'a FxHashMap<InstId, MallocPlacement>,
    free_ptr_write_summaries: &'a FxHashMap<FuncRef, bool>,
    exit_floor_summaries: &'a FxHashMap<FuncRef, Option<u32>>,
    prov: &'a SecondaryMap<ValueId, Provenance>,
}

impl TransferCtx<'_> {
    fn block(
        &self,
        block: BlockId,
        mut floor: FreePtrFloor,
        mut before_malloc: Option<&mut FxHashMap<InstId, Option<u32>>>,
        mut before_call: Option<&mut Vec<(FuncRef, FreePtrFloor)>>,
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
                    if let Some(before_call) = before_call.as_deref_mut() {
                        before_call.push((*call.callee(), floor));
                    }
                    if self
                        .free_ptr_write_summaries
                        .get(call.callee())
                        .copied()
                        .unwrap_or(true)
                    {
                        floor = FreePtrFloor::Unknown;
                    } else if let Some(exit_floor) = self
                        .exit_floor_summaries
                        .get(call.callee())
                        .copied()
                        .flatten()
                    {
                        floor = floor.establish_min(exit_floor);
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
