use super::{DataFlowGraph, Layout, Type};

pub struct Function {
    /// Name of the function.
    pub name: String,

    /// Signature of the function.
    pub sig: Signature,

    pub dfg: DataFlowGraph,
    pub layout: Layout,
}

pub struct Signature {
    pub args: Vec<Type>,
    pub rets: Vec<Type>,
}
