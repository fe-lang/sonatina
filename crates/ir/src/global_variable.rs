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
}

/// An opaque reference to [`GlobalVariableData`].
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Copy, Hash)]
pub struct GlobalVariable(pub u32);
cranelift_entity::entity_impl!(GlobalVariable);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GlobalVariableData {
    symbol: String,
    ty: Type,
    linkage: Linkage,
    is_const: bool,
    data: Option<ConstantValue>,
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
    Immediate {
        ty: Type,
        data: Immediate,
    },
    Array {
        elem_ty: Type,
        len: usize,
        data: Vec<ConstantValue>,
    },
    Struct {
        ty: Type,
        data: Vec<ConstantValue>,
    },
}

impl ConstantValue {
    pub fn make_imm(ty: Type, data: impl Into<Immediate>) -> Self {
        Self::Immediate {
            ty,
            data: data.into(),
        }
    }

    pub fn make_array(elem_ty: Type, data: Vec<ConstantValue>) -> Self {
        Self::Array {
            elem_ty,
            len: data.len(),
            data,
        }
    }

    pub fn make_struct(ty: Type, data: Vec<ConstantValue>) -> Self {
        Self::Struct { ty, data }
    }
}
