pub mod adce;
pub mod aggregate;
pub(crate) mod call_purity;
pub mod cfg_cleanup;
pub mod dead_func;
pub mod egraph;
pub mod gvn;
pub mod inliner;
pub mod licm;
pub mod multi_result_legalize;
pub mod pipeline;
pub mod sccp;
mod sccp_simplify;
mod simplify_expr;

pub use pipeline::{Pass, Pipeline, Step, run_func_passes};
