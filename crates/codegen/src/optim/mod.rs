pub mod adce;
pub(crate) mod call_purity;
pub mod cfg_cleanup;
pub mod dead_func;
pub mod egraph;
pub mod inliner;
pub mod licm;
pub mod pipeline;
pub mod sccp;
mod sccp_simplify;

pub use pipeline::{Pass, Pipeline, Step, run_func_passes};
