// We allow `needless_collect` due to some false positive.
// See <https://github.com/rust-lang/rust-clippy/issues/7512> and <https://github.com/rust-lang/rust-clippy/issues/7336>
#![allow(clippy::needless_collect)]

pub mod cfg;
pub mod contract;
pub mod critical_edge;
pub mod domtree;
pub mod ir;
pub mod isa;
pub mod loop_analysis;
pub mod optim;
pub mod post_domtree;

pub use ir::{Block, Function, Insn, Signature, Type, Value, Variable};
pub use isa::TargetIsa;
