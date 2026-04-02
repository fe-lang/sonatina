mod backend;
pub(crate) mod dyn_sp;
mod emit;
mod heap_plan;
mod late_alias;
mod late_block_merge;
mod late_section_merge;
mod lazy_frame;
mod malloc_plan;
mod mem_effects;
mod memory_plan;
pub mod opcode;
mod pipeline;
mod prepare;
mod provenance;
mod ptr_escape;
mod scratch_effects;
mod scratch_plan;
pub(crate) mod static_arena_alloc;
mod verify;

pub use backend::{EvmBackend, LateCleanupProfile, PushWidthPolicy};
pub use late_alias::canonicalize_alias_value;
pub use prepare::EvmPreparedSection;

pub(crate) use dyn_sp::FrontierInitKind;
pub(crate) use emit::{
    fold_stack_actions, immediate_u32, is_plain_inst, is_push_opcode, referenced_insn_label_targets,
};
pub(crate) use late_alias::normalize_alias_map;
pub(crate) use lazy_frame::{FrameSite, FrameSummary, LazyFramePlan};
pub(crate) use memory_plan::{
    DYN_SP_SLOT, FREE_PTR_SLOT, FuncMemPlan, ObjLoc, PreserveMode, STATIC_BASE, WORD_BYTES,
};
pub(crate) use opcode::OpCode;
pub(crate) use prepare::{EvmFunctionPlan, EvmSectionPlan, prepare_free_ptr_restore};
pub(crate) use ptr_escape::{PtrEscapeSummary, compute_ptr_escape_summaries};
pub(crate) use sonatina_ir::{isa::evm::Evm, module::FuncRef};
pub(crate) use verify::{collect_unsupported_evm_multi_return, validate_supported_lowering_ir};

#[cfg(test)]
#[allow(unused_imports)]
use cranelift_entity::SecondaryMap;
#[cfg(test)]
#[allow(unused_imports)]
use rustc_hash::{FxHashMap, FxHashSet};
#[cfg(test)]
#[allow(unused_imports)]
use smallvec::{SmallVec, smallvec};
#[cfg(test)]
#[allow(unused_imports)]
use sonatina_ir::{
    BlockId, Function, Immediate, InstId, InstSetExt, Module, Type, U256, ValueId,
    cfg::ControlFlowGraph,
    inst::{control_flow::BranchKind, data::SymbolRef, evm::inst_set::EvmInstKind},
    isa::Isa,
    module::ModuleCtx,
    types::{CompoundType, CompoundTypeRef},
};
#[cfg(test)]
#[allow(unused_imports)]
use sonatina_triple::{EvmVersion, OperatingSystem};

#[cfg(test)]
#[allow(unused_imports)]
use crate::{
    critical_edge::CriticalEdgeSplitter,
    domtree::DomTree,
    liveness::{InstLiveness, Liveness},
    loop_analysis::LoopTree,
    machinst::{
        lower::{Lower, LoweredFunction, SectionCodeUnit, SectionWorkModule},
        vcode::{Label, SymFixup, SymFixupKind, VCode, VCodeFixup, VCodeInst},
    },
    module_analysis::{CallGraph, SccBuilder},
    stackalloc::{Action, Actions, Allocator, StackifyAlloc, StackifyBuilder},
    transform::aggregate::{assert_aggregate_legalized, shape},
};

#[cfg(test)]
#[allow(unused_imports)]
use self::{
    dyn_sp::{DynSpPlan, FuncDynSpPlan, compute_dyn_sp_plan},
    emit::{
        EvmFunctionLowering, FinalAlloc, LateBlockAliasPlan, compute_function_entry_jump_targets,
        compute_late_block_alias_plan, frame_slot_sp_relative_bytes, materialize_jumpdests,
        perform_actions, prune_redundant_opcode_sequences, push_op,
        rewrite_evm_local_fallthrough_layout,
    },
    lazy_frame::compute_frame_summary,
    memory_plan::{
        ArenaCostModel, ProgramMemoryPlan, StableMode, compute_abs_clobber_words,
        compute_program_memory_plan, topo_sort_sccs,
    },
    prepare::compute_return_escape_caller_clamp_words,
};

#[cfg(test)]
mod tests;
