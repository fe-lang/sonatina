use smallvec::SmallVec;

use crate::{module::FuncRef, Block, Type, Value};

pub trait Inst {
    fn visit_values(&self, f: &mut dyn FnMut(Value));
    fn visit_values_mut(&mut self, f: &mut dyn FnMut(&mut Value));
    fn has_side_effect(&self) -> bool;
    fn as_str(&self) -> &'static str;
}

macro_rules! define_inst {
    ($(($purity:ident, $ty:ident, $name:literal, $arity:literal)),* $(,)?) => {
        $(
            define_inst!($purity, $ty, $name, $arity);
        )*
    };

    ($purity: ident, $ty: ident, $name:literal, $arity:literal) => {
        #[derive(Debug, Clone, PartialEq, Eq, Hash)]
        pub struct $ty {
            args: define_inst!(__arg_ty $arity),
        }

        impl Inst for $ty {
            fn visit_values(&self, f: &mut dyn FnMut(Value)) {
                for &v in &self.args {
                    f(v)
                }
            }

            fn visit_values_mut(&mut self, f: &mut dyn FnMut(&mut Value)) {
                for v in &mut self.args {
                    f(v)
                }
            }

            fn has_side_effect(&self) -> bool {
                define_inst!(__has_side_effect_impl $purity)
            }

            fn as_str(&self) -> &'static str {
                $name
            }
        }
    };

    ($purity: ident, $ty: ident, $name:literal, $arity:literal) => {
        #[derive(Debug, Clone, PartialEq, Eq, Hash)]
        pub struct $ty {
            pub args: define_inst!(__arg_ty $arity),
        }

        impl Inst for $ty {
            fn visit_values(&self, f: &mut dyn FnMut(Value)) {
                self.args.iter().copied().for_each(f)
            }

            fn visit_values_mut(&mut self, f: &mut dyn FnMut(&mut Value)) {
                self.args.iter_mut().for_each(f)
            }

            fn has_side_effect(&self) -> bool {
                define_inst!(__has_side_effect_impl $purity)
            }

            fn as_str(&self) -> &'static str {
                $name
            }
        }
    };

    (__arg_ty 1) => {
        Value
    };

    (__arg_ty $arity:literal) => {
        [Value; $arity]
    };

    (__has_side_effect_impl pure) => {
       true
    };

    (__has_side_effect_impl non_pure) => {
       true
    };
}

define_inst! {
    (pure, Not, "not", 1),
    (pure, Neg, "neg", 1),
    // Arithmetic instructions.
    (pure, Add, "add", 2),
    (pure, Mul, "mul", 2),
    (pure, Sub, "sub", 2),
    (non_pure, Sdiv, "sdiv", 2),
    (non_pure, Udiv, "udiv", 2),
    // Comp instructions.
    (pure, Lt, "lt", 2),
    (pure, Gt, "gt", 2),
    (pure, Slt, "slt", 2),
    (pure, Sgt, "sgt", 2),
    (pure, Le, "le", 2),
    (pure, Ge, "ge", 2),
    (pure, Sle, "sle", 2),
    (pure, Sge, "sge", 2),
    (pure, Eq, "eq", 2),
    (pure, Ne, "ne", 2),
    (pure, And, "And", 2),
    (pure, Or, "Or", 2),
    (pure, Xor, "xor", 2),
    // Cast instructions.
    (pure, Sext, "sext", 2),
    (pure, Zext, "zext", 2),
    (pure, Trunc, "trunc", 2),
    (pure, BitCast, "bitcast", 2),
    // Memory operations.
    (non_pure, Mload, "mload", 1),
    (non_pure, Mstore, "mstore", 2),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Call {
    pub args: SmallVec<[Value; 8]>,
    pub callee: FuncRef,
    pub ret_ty: Type,
}

impl Inst for Call {
    fn visit_values(&self, f: &mut dyn FnMut(Value)) {
        self.args.iter().copied().for_each(f)
    }

    fn visit_values_mut(&mut self, f: &mut dyn FnMut(&mut Value)) {
        self.args.iter_mut().for_each(f)
    }

    fn has_side_effect(&self) -> bool {
        // TODO: We need to add funciton attribute that can specify a purity of function.
        true
    }

    fn as_str(&self) -> &'static str {
        "call"
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Jump {
    pub dest: Block,
}
impl Inst for Jump {
    fn visit_values(&self, _f: &mut dyn FnMut(Value)) {}

    fn visit_values_mut(&mut self, _f: &mut dyn FnMut(&mut Value)) {}

    fn has_side_effect(&self) -> bool {
        false
    }

    fn as_str(&self) -> &'static str {
        "jump"
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Br {
    pub cond: Value,
    pub z_dest: Block,
    pub nz_dest: Block,
}
impl Inst for Br {
    fn visit_values(&self, f: &mut dyn FnMut(Value)) {
        f(self.cond)
    }

    fn visit_values_mut(&mut self, f: &mut dyn FnMut(&mut Value)) {
        f(&mut self.cond)
    }

    fn has_side_effect(&self) -> bool {
        false
    }

    fn as_str(&self) -> &'static str {
        "br"
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BrTable {
    pub scrutinee: Value,
    pub table: Vec<(Value, Block)>,
    pub default: Option<Block>,
}

impl Inst for BrTable {
    fn visit_values(&self, f: &mut dyn FnMut(Value)) {
        f(self.scrutinee);
        self.table.iter().for_each(|(v, _)| f(*v))
    }

    fn visit_values_mut(&mut self, f: &mut dyn FnMut(&mut Value)) {
        f(&mut self.scrutinee);
        self.table.iter_mut().for_each(|(v, _)| f(v))
    }

    fn has_side_effect(&self) -> bool {
        false
    }

    fn as_str(&self) -> &'static str {
        "br_table"
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Alloca {
    pub ty: Type,
}
impl Inst for Alloca {
    fn visit_values(&self, _f: &mut dyn FnMut(Value)) {}

    fn visit_values_mut(&mut self, _f: &mut dyn FnMut(&mut Value)) {}

    fn has_side_effect(&self) -> bool {
        true
    }

    fn as_str(&self) -> &'static str {
        "alloca"
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Return {
    pub arg: Option<Value>,
}
impl Inst for Return {
    fn visit_values(&self, f: &mut dyn FnMut(Value)) {
        if let Some(v) = self.arg {
            f(v)
        }
    }

    fn visit_values_mut(&mut self, f: &mut dyn FnMut(&mut Value)) {
        if let Some(v) = self.arg.as_mut() {
            f(v)
        }
    }

    fn has_side_effect(&self) -> bool {
        true
    }

    fn as_str(&self) -> &'static str {
        "return"
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Gep {
    values: SmallVec<[Value; 8]>,
}
impl Inst for Gep {
    fn visit_values(&self, f: &mut dyn FnMut(Value)) {
        self.values.iter().copied().for_each(f)
    }

    fn visit_values_mut(&mut self, f: &mut dyn FnMut(&mut Value)) {
        self.values.iter_mut().for_each(f)
    }

    fn has_side_effect(&self) -> bool {
        false
    }

    fn as_str(&self) -> &'static str {
        "gep"
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Phi {
    pub values: Vec<(Value, Block)>,
    pub ty: Type,
}
impl Inst for Phi {
    fn visit_values(&self, f: &mut dyn FnMut(Value)) {
        self.values.iter().for_each(|(v, _)| f(*v))
    }

    fn visit_values_mut(&mut self, f: &mut dyn FnMut(&mut Value)) {
        self.values.iter_mut().for_each(|(v, _)| f(v))
    }

    fn has_side_effect(&self) -> bool {
        true
    }

    fn as_str(&self) -> &'static str {
        "phi"
    }
}
