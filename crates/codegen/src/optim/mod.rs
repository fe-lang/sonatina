pub mod adce;
pub mod aggregate;
mod bit_scan;
pub mod bool_phi_fold;
pub mod branch_canonicalize;
pub(crate) mod call_purity;
pub mod cfg_cleanup;
pub mod checked_arith_elim;
pub mod coalesce_object_copies;
pub mod code_sink;
pub mod compare_sub_fusion;
pub(crate) mod const_eval;
pub(crate) mod constref_specialize;
pub mod dead_arg;
pub mod dead_func;
mod dead_malloc;
pub mod dead_ret;
pub mod forwarded_ret;
pub mod gvn;
pub mod hoist_insert_chains;
pub mod if_convert;
pub mod inliner;
pub mod jump_thread;
pub mod known_bits_simplify;
pub mod licm;
pub mod load_store;
pub mod loop_rotate;
pub mod loop_strength_reduce;
pub mod loop_unroll;
pub mod merge_index_checks;
pub mod multi_result_legalize;
pub mod narrow_object_loads;
pub mod pipeline;
pub mod range_branch_simplify;
pub mod return_thread;
pub mod scalar_canonicalize;
pub mod sccp;
mod sccp_simplify;
pub(crate) mod signature_rewrite;
mod simplify_expr;
pub(crate) mod steps;
pub mod switch_formation;
pub(crate) mod uniform_const_arg;

pub use pipeline::{Pass, Pipeline, Step};
use sonatina_ir::{Function, InstId, inst::data::AggMake};

/// The instructions `inst` stands for in a size budget: one, or one per
/// operand for an `agg.make`, as for the insert chain it replaces, so that how
/// a fresh aggregate is spelled does not change what a budget allows.
pub(crate) fn inst_size(func: &Function, inst: InstId) -> usize {
    func.dfg
        .downcast::<&AggMake>(inst)
        .map_or(1, |make| make.values().len())
}
