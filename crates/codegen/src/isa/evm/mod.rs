mod backend;
pub(crate) mod dyn_sp;
mod emit;
mod frame_layout;
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
#[doc(hidden)]
pub mod test_util;
mod verify;

pub use backend::{EvmBackend, LateCleanupProfile, PushWidthPolicy};
pub use late_alias::canonicalize_alias_value;
pub use prepare::EvmPreparedSection;

pub(crate) use dyn_sp::DynSpInitKind;
pub(crate) use emit::{
    fold_stack_actions, immediate_u32, is_plain_inst, is_push_opcode, referenced_insn_label_targets,
};
pub(crate) use frame_layout::{DynamicFrameLayout, FrameLocalWord};
pub(crate) use late_alias::normalize_alias_map;
pub(crate) use lazy_frame::{FrameSite, FrameSummary, LazyFramePlan};
pub(crate) use memory_plan::{
    DYN_SP_SLOT, FREE_PTR_SLOT, FuncMemPlan, ObjLoc, PreserveMode, STATIC_BASE, WORD_BYTES,
};
pub(crate) use opcode::OpCode;
pub(crate) use prepare::{EvmFunctionPlan, EvmSectionPlan, prepare_free_ptr_restore};
pub(crate) use ptr_escape::{PtrEscapeSummary, compute_ptr_escape_summaries};
pub(crate) use sonatina_ir::{isa::evm::Evm, module::FuncRef};
pub(crate) use verify::{collect_unsupported_evm_calls, validate_supported_lowering_ir};

#[cfg(test)]
mod tests;
