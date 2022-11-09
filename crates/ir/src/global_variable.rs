use std::fmt;

use cranelift_entity::PrimaryMap;
use fxhash::FxHashMap;

use crate::{Immediate, Linkage, Type};

#[derive(Debug, Default)]
pub struct GlobalVariableStore {
    gv_data: PrimaryMap<GlobalVariable, GlobalVariableData>,
    symbols: FxHashMap<String, GlobalVariable>,
}

impl GlobalVariableStore {
    pub fn make_gv(&mut self, gv_data: GlobalVariableData) -> GlobalVariable {
        match self.symbols.entry(gv_data.symbol.to_string()) {
            std::collections::hash_map::Entry::Occupied(_) => {
                panic!("duplicate global symbol `{}`", gv_data.symbol);
            }
            std::collections::hash_map::Entry::Vacant(v) => {
                let gv = self.gv_data.push(gv_data);
                v.insert(gv);
                gv
            }
        }
    }

    pub fn gv_data(&self, gv: GlobalVariable) -> &GlobalVariableData {
        &self.gv_data[gv]
    }

    pub fn gv_by_symbol(&self, symbol: &str) -> Option<GlobalVariable> {
        self.symbols.get(symbol).copied()
    }

    pub fn init_data(&self, gv: GlobalVariable) -> Option<&ConstantValue> {
        self.gv_data[gv].data.as_ref()
    }

    pub fn is_const(&self, gv: GlobalVariable) -> bool {
        self.gv_data[gv].is_const
    }

    pub fn ty(&self, gv: GlobalVariable) -> Type {
        self.gv_data[gv].ty
    }

    pub fn all_gv_data(&self) -> impl Iterator<Item = &GlobalVariableData> {
        self.gv_data.values()
    }
}

/// An opaque reference to [`GlobalVariableData`].
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Copy, Hash)]
pub struct GlobalVariable(pub u32);
cranelift_entity::entity_impl!(GlobalVariable);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GlobalVariableData {
    pub symbol: String,
    pub ty: Type,
    pub linkage: Linkage,
    pub is_const: bool,
    pub data: Option<ConstantValue>,
}

impl GlobalVariableData {
    pub fn new(symbol: String, ty: Type, linkage: Linkage, is_const: bool) -> Self {
        Self {
            symbol,
            ty,
            linkage,
            is_const,
            data: None,
        }
    }

    pub fn constant(symbol: String, ty: Type, linkage: Linkage, data: ConstantValue) -> Self {
        Self {
            symbol,
            ty,
            linkage,
            is_const: true,
            data: Some(data),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConstantValue {
    Immediate { data: Immediate },
    Array { data: Vec<ConstantValue> },
    Struct { data: Vec<ConstantValue> },
}

impl ConstantValue {
    pub fn make_imm(data: impl Into<Immediate>) -> Self {
        Self::Immediate { data: data.into() }
    }

    pub fn make_array(data: Vec<ConstantValue>) -> Self {
        Self::Array { data }
    }

    pub fn make_struct(data: Vec<ConstantValue>) -> Self {
        Self::Struct { data }
    }
}

impl fmt::Display for ConstantValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Immediate { data } => write!(f, "{}", data),
            Self::Array { data } => {
                write!(f, "[")?;
                for (i, v) in data.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", v)?;
                }
                write!(f, "]")
            }
            Self::Struct { data } => {
                write!(f, "{{")?;
                for (i, v) in data.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", v)?;
                }
                write!(f, "}}")
            }
        }
    }
}
