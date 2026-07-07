mod backend;
pub(crate) mod dyn_sp;
mod emit;
mod escape_scan;
mod exact_func_merge;
mod frame_layout;
mod heap_plan;
mod high_alias;
mod immediate;
mod late_block_merge;
mod late_section_merge;
mod machine;
mod malloc_plan;
mod mem_effects;
mod memory_plan;
pub mod opcode;
mod pipeline;
mod placement_search;
mod prepare;
mod provenance;
mod ptr_escape;
mod scratch_plan;
pub(crate) mod static_arena_alloc;
#[doc(hidden)]
pub mod test_util;
mod verify;

pub use backend::{EvmBackend, ImmediateMaterializationMode, LateCleanupProfile, PushWidthPolicy};
pub use prepare::EvmPreparedSection;

pub(crate) use dyn_sp::DynSpInitKind;
#[cfg(test)]
pub(crate) use emit::fold_stack_actions;
pub(crate) use emit::{
    immediate_u32, is_plain_inst, is_push_opcode, referenced_insn_label_targets,
};
pub(crate) use frame_layout::{DynamicFrameLayout, FrameLocalWord};
pub(crate) use high_alias::canonicalize_alias_value;
pub(crate) use immediate::{
    ImmediateMaterializationPlan, immediate_materialization_code_len,
    immediate_materialization_cost_i256, immediate_materialization_plan, u32_to_be, u256_to_be,
};
pub(crate) use memory_plan::{
    DYN_SP_SLOT, FREE_PTR_SLOT, FuncMemPlan, ObjLoc, PreserveMode, STATIC_BASE, WORD_BYTES,
};
pub(crate) use opcode::OpCode;
pub(crate) use prepare::{EvmFunctionPlan, EvmSectionPlan, prepare_free_ptr_restore};
pub(crate) use ptr_escape::{PtrEscapeSummary, compute_ptr_escape_summaries};
#[cfg(test)]
pub(crate) use sonatina_ir::isa::evm::Evm;
pub(crate) use sonatina_ir::module::FuncRef;
pub(crate) use verify::{collect_unsupported_evm_calls, validate_supported_lowering_ir};

#[cfg(test)]
mod tests;
