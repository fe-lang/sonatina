pub mod adce;
pub mod cfg_cleanup;
pub mod egraph;
pub mod inliner;
pub mod licm;
pub mod pipeline;
pub mod sccp;
mod sccp_simplify;

pub use pipeline::{Pass, Pipeline, Step, run_func_passes};
