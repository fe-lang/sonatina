//! This module contains Sonatina IR types definitions.
use std::{cmp, io};

use cranelift_entity::PrimaryMap;
use indexmap::IndexMap;
use rustc_hash::FxHashMap;
use smallvec::SmallVec;

use crate::{ir_writer::IrWrite, module::ModuleCtx};

#[derive(Debug, Default)]
pub struct TypeStore {
    compounds: PrimaryMap<CompoundTypeRef, CompoundTypeData>,
    rev_types: FxHashMap<CompoundTypeData, CompoundTypeRef>,
    struct_types: IndexMap<String, CompoundTypeRef>,
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
        let compound_data = CompoundTypeData::Struct(StructData {
            name: name.to_string(),
            fields: fields.to_vec(),
            packed,
        });
        let compound = self.make_compound(compound_data);
        debug_assert!(
            !self.struct_types.contains_key(name),
            "struct {name} is already defined"
        );
        self.struct_types.insert(name.to_string(), compound);
        Type::Compound(compound)
    }

    pub fn make_func(&mut self, args: &[Type], ret_ty: Type) -> Type {
        let compound = self.make_compound(CompoundTypeData::Func {
            args: args.into(),
            ret_ty,
        });
        Type::Compound(compound)
    }

    /// Returns `[StructData]` if the given type is a struct type.
    pub fn struct_def(&self, ty: Type) -> Option<&StructData> {
        match ty {
            Type::Compound(compound) => match self.compounds[compound] {
                CompoundTypeData::Struct(ref def) => Some(def),
                _ => None,
            },
            _ => None,
        }
    }

    pub fn array_def(&self, ty: Type) -> Option<(Type, usize)> {
        match ty {
            Type::Compound(compound) => match self.compounds[compound] {
                CompoundTypeData::Array { elem, len } => Some((elem, len)),
                _ => None,
            },
            _ => None,
        }
    }

    pub fn struct_type_by_name(&self, name: &str) -> Option<Type> {
        self.struct_types.get(name).map(|ty| Type::Compound(*ty))
    }

    pub fn all_struct_data(&self) -> impl Iterator<Item = &StructData> {
        self.struct_types
            .values()
            .map(|compound_type| match self.compounds[*compound_type] {
                CompoundTypeData::Struct(ref def) => def,
                _ => unreachable!(),
            })
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

    pub fn make_compound(&mut self, data: CompoundTypeData) -> CompoundTypeRef {
        if let Some(compound) = self.rev_types.get(&data) {
            *compound
        } else {
            let compound = self.compounds.push(data.clone());
            self.rev_types.insert(data, compound);
            compound
        }
    }

    pub fn resolve_compound(&self, compound: CompoundTypeRef) -> &CompoundTypeData {
        &self.compounds[compound]
    }
}

/// Sonatina IR types definition.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum Type {
    I1,
    I8,
    I16,
    I32,
    I64,
    I128,
    I256,
    Compound(CompoundTypeRef),
    #[default]
    Unit,
}

impl Type {
    pub fn is_integral(self) -> bool {
        matches!(
            self,
            Self::I1 | Self::I8 | Self::I16 | Self::I32 | Self::I64 | Self::I128 | Self::I256
        )
    }

    pub fn is_unit(self) -> bool {
        matches!(self, Self::Unit)
    }

    pub fn is_pointer(self, ctx: &ModuleCtx) -> bool {
        ctx.with_ty_store(|store| store.is_ptr(self))
    }

    pub fn resolve_compound(self, ctx: &ModuleCtx) -> Option<CompoundTypeData> {
        let Self::Compound(cmpd) = self else {
            return None;
        };

        Some(ctx.with_ty_store(|s| s.resolve_compound(cmpd).clone()))
    }

    pub fn to_ptr(self, ctx: &ModuleCtx) -> Type {
        ctx.with_ty_store_mut(|s| s.make_ptr(self))
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

impl<Ctx> IrWrite<Ctx> for Type
where
    Ctx: AsRef<ModuleCtx>,
{
    fn write<W>(&self, w: &mut W, ctx: &Ctx) -> io::Result<()>
    where
        W: io::Write,
    {
        match self {
            Type::I1 => write!(w, "i1"),
            Type::I8 => write!(w, "i8"),
            Type::I16 => write!(w, "i16"),
            Type::I32 => write!(w, "i32"),
            Type::I64 => write!(w, "i64"),
            Type::I128 => write!(w, "i128"),
            Type::I256 => write!(w, "i256"),
            Type::Compound(cmpd_ty) => cmpd_ty.write(w, ctx),
            Type::Unit => write!(w, "unit"),
        }
    }
}

/// An opaque reference to [`CompoundTypeData`].
#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash, PartialOrd, Ord)]
pub struct CompoundTypeRef(u32);
cranelift_entity::entity_impl!(CompoundTypeRef);

impl<Ctx> IrWrite<Ctx> for CompoundTypeRef
where
    Ctx: AsRef<ModuleCtx>,
{
    fn write<W>(&self, w: &mut W, ctx: &Ctx) -> io::Result<()>
    where
        W: io::Write,
    {
        ctx.as_ref()
            .with_ty_store(|s| match s.resolve_compound(*self) {
                CompoundTypeData::Array { elem: ty, len } => {
                    write!(w, "[")?;
                    ty.write(w, ctx)?;
                    write!(w, "; {len}]")
                }
                CompoundTypeData::Ptr(ty) => {
                    write!(w, "*")?;
                    ty.write(w, ctx)
                }
                CompoundTypeData::Struct(StructData { name, packed, .. }) => {
                    if *packed {
                        write!(w, "@<{name}>")
                    } else {
                        write!(w, "@{name}")
                    }
                }

                CompoundTypeData::Func { args, ret_ty: ret } => {
                    write!(w, "(")?;
                    args.write_with_delim(w, ", ", ctx)?;
                    write!(w, ") -> ")?;
                    ret.write(w, ctx)
                }
            })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CompoundTypeData {
    Array {
        elem: Type,
        len: usize,
    },
    Ptr(Type),
    Struct(StructData),
    Func {
        args: SmallVec<[Type; 8]>,
        ret_ty: Type,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructData {
    pub name: String,
    pub fields: Vec<Type>,
    pub packed: bool,
}

impl<Ctx> IrWrite<Ctx> for StructData
where
    Ctx: AsRef<ModuleCtx>,
{
    fn write<W>(&self, w: &mut W, ctx: &Ctx) -> io::Result<()>
    where
        W: io::Write,
    {
        write!(w, "type @{} = ", self.name)?;
        if self.packed {
            write!(w, "<{{")?;
        } else {
            write!(w, "{{")?;
        }

        self.fields.write_with_delim(w, ", ", ctx)?;
        if self.packed {
            write!(w, "}}>;")
        } else {
            write!(w, "}};")
        }
    }
}

impl CompoundTypeData {
    pub fn is_array(&self) -> bool {
        matches!(self, Self::Array { .. })
    }

    pub fn is_ptr(&self) -> bool {
        matches!(self, Self::Ptr(_))
    }
}
