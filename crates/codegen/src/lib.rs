pub mod ir;

pub mod cfg;
pub mod critical_edge;
pub mod domtree;

pub use ir::{Block, Function, Insn, Signature, Type, Value, Variable};
