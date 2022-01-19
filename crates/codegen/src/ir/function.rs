use smallvec::SmallVec;

use super::{DataFlowGraph, Layout, Type, Value};

#[derive(Debug, Clone)]
pub struct Function {
    /// Signature of the function.
    pub sig: Signature,
    pub arg_values: smallvec::SmallVec<[Value; 8]>,

    pub dfg: DataFlowGraph,
    pub layout: Layout,
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
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct Signature {
    /// Name of the function.
    name: String,

    args: SmallVec<[Type; 8]>,
    ret: Option<Type>,
}

impl Signature {
    pub fn new(name: &str, args: &[Type], ret: Option<&Type>) -> Self {
        Self {
            name: name.to_string(),
            args: args.into(),
            ret: ret.cloned(),
        }
    }
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn append_arg(&mut self, arg: Type) {
        self.args.push(arg);
    }

    pub fn set_ret_ty(&mut self, ty: &Type) {
        debug_assert!(self.ret.is_none());
        self.ret = Some(ty.clone());
    }

    pub fn args(&self) -> &[Type] {
        &self.args
    }

    pub fn ret_ty(&self) -> Option<&Type> {
        self.ret.as_ref()
    }
}
