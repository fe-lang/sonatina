use std::fmt;

use fxhash::FxHashMap;
use smallvec::SmallVec;

use super::{module::FuncRef, DataFlowGraph, Layout, Type, Value};

#[derive(Debug, Clone)]
pub struct Function {
    /// Signature of the function.
    pub sig: Signature,
    pub arg_values: smallvec::SmallVec<[Value; 8]>,

    pub dfg: DataFlowGraph,
    pub layout: Layout,

    /// Stores signature of the functions that called by the function.
    pub callees: FxHashMap<FuncRef, Signature>,
}

impl Function {
    pub fn new(sig: Signature) -> Self {
        let mut dfg = DataFlowGraph::default();
        let arg_values = sig
            .args()
            .iter()
            .enumerate()
            .map(|(idx, arg_ty)| {
                let value = dfg.make_arg_value(arg_ty, idx);
                dfg.make_value(value)
            })
            .collect();

        Self {
            sig,
            arg_values,
            dfg,
            layout: Layout::default(),
            callees: FxHashMap::default(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Signature {
    /// Name of the function.
    name: String,

    /// Linkage of the function.
    linkage: Linkage,

    args: SmallVec<[Type; 8]>,
    ret_ty: Type,
}

impl Signature {
    pub fn new(name: &str, linkage: Linkage, args: &[Type], ret_ty: &Type) -> Self {
        Self {
            name: name.to_string(),
            linkage,
            args: args.into(),
            ret_ty: ret_ty.clone(),
        }
    }
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn linkage(&self) -> Linkage {
        self.linkage
    }

    pub fn append_arg(&mut self, arg: Type) {
        self.args.push(arg);
    }

    pub fn args(&self) -> &[Type] {
        &self.args
    }

    pub fn ret_ty(&self) -> &Type {
        &self.ret_ty
    }

    #[doc(hidden)]
    pub fn set_ret_ty(&mut self, ty: Type) {
        self.ret_ty = ty;
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// Linkage of the function.
pub enum Linkage {
    /// The function is defined in the contract, and can be called from another accounts.
    Public,

    /// The function is defined in the contract, and can NOT be called from another accounts.
    Private,

    /// The function is defined outside of the contract.
    External,
}

impl fmt::Display for Linkage {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> fmt::Result {
        match self {
            Self::Public => write!(f, "public"),
            Self::Private => write!(f, "private"),
            Self::External => write!(f, "external"),
        }
    }
}
