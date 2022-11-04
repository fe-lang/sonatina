//! This module contains Sonatina IR types definitions.

use std::cmp;

use cranelift_entity::PrimaryMap;
use fxhash::FxHashMap;

#[derive(Debug, Default)]
pub struct TypeStore {
    compounds: PrimaryMap<CompoundType, CompoundTypeData>,
    rev_types: FxHashMap<CompoundTypeData, CompoundType>,
    struct_types: FxHashMap<String, CompoundType>,
}

impl TypeStore {
    pub fn make_ptr(&mut self, ty: Type) -> Type {
        let ty = self.make_compound(CompoundTypeData::Ptr(ty));
        Type::Compound(ty)
    }

    pub fn make_array(&mut self, elem: Type, len: usize) -> Type {
        let ty = self.make_compound(CompoundTypeData::Array { elem, len });
        Type::Compound(ty)
    }

    pub fn make_struct(&mut self, name: &str, fields: &[Type], packed: bool) -> Type {
        let compound_data = CompoundTypeData::Struct {
            name: name.to_string(),
            fields: fields.to_vec(),
            packed,
        };
        let compound = self.make_compound(compound_data);
        debug_assert!(
            !self.struct_types.contains_key(name),
            "struct {name} is already defined"
        );
        self.struct_types.insert(name.to_string(), compound);
        Type::Compound(compound)
    }

    pub fn struct_type_by_name(&self, name: &str) -> Option<Type> {
        self.struct_types.get(name).map(|ty| Type::Compound(*ty))
    }

    pub fn deref(&self, ptr: Type) -> Option<Type> {
        match ptr {
            Type::Compound(ty) => {
                let ty_data = &self.compounds[ty];
                match ty_data {
                    CompoundTypeData::Ptr(ty) => Some(*ty),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    pub fn is_integral(&self, ty: Type) -> bool {
        ty.is_integral()
    }

    pub fn is_ptr(&self, ty: Type) -> bool {
        match ty {
            Type::Compound(compound) => self.compounds[compound].is_ptr(),
            _ => false,
        }
    }

    pub fn is_array(&self, ty: Type) -> bool {
        match ty {
            Type::Compound(compound) => self.compounds[compound].is_array(),
            _ => false,
        }
    }

    pub fn make_compound(&mut self, data: CompoundTypeData) -> CompoundType {
        if let Some(compound) = self.rev_types.get(&data) {
            *compound
        } else {
            let compound = self.compounds.push(data.clone());
            self.rev_types.insert(data, compound);
            compound
        }
    }

    pub fn resolve_compound(&self, compound: CompoundType) -> &CompoundTypeData {
        &self.compounds[compound]
    }
}

/// Sonatina IR types definition.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Type {
    I1,
    I8,
    I16,
    I32,
    I64,
    I128,
    I256,
    Compound(CompoundType),
    Void,
}

/// An opaque reference to [`CompoundTypeData`].
#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash, PartialOrd, Ord)]
pub struct CompoundType(u32);
cranelift_entity::entity_impl!(CompoundType);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CompoundTypeData {
    Array {
        elem: Type,
        len: usize,
    },
    Ptr(Type),
    Struct {
        name: String,
        fields: Vec<Type>,
        packed: bool,
    },
}

impl CompoundTypeData {
    pub fn is_array(&self) -> bool {
        matches!(self, Self::Array { .. })
    }

    pub fn is_ptr(&self) -> bool {
        matches!(self, Self::Ptr(_))
    }
}

impl Type {
    pub fn is_integral(&self) -> bool {
        matches!(
            self,
            Self::I1 | Self::I8 | Self::I16 | Self::I32 | Self::I64 | Self::I128 | Self::I256
        )
    }
}

impl cmp::PartialOrd for Type {
    fn partial_cmp(&self, rhs: &Self) -> Option<cmp::Ordering> {
        use Type::*;

        if self == rhs {
            return Some(cmp::Ordering::Equal);
        }

        if !self.is_integral() || !rhs.is_integral() {
            return None;
        }

        match (self, rhs) {
            (I1, _) => Some(cmp::Ordering::Less),
            (I8, I1) => Some(cmp::Ordering::Greater),
            (I8, _) => Some(cmp::Ordering::Less),
            (I16, I1 | I8) => Some(cmp::Ordering::Greater),
            (I16, _) => Some(cmp::Ordering::Less),
            (I32, I1 | I8 | I16) => Some(cmp::Ordering::Greater),
            (I32, _) => Some(cmp::Ordering::Less),
            (I64, I128 | I256) => Some(cmp::Ordering::Less),
            (I64, _) => Some(cmp::Ordering::Greater),
            (I128, I256) => Some(cmp::Ordering::Less),
            (I128, _) => Some(cmp::Ordering::Greater),
            (I256, _) => Some(cmp::Ordering::Greater),
            (_, _) => unreachable!(),
        }
    }
}
