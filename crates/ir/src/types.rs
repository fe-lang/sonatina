//! This module contains Sonatina IR types definitions.
use std::{cmp, io};

use cranelift_entity::PrimaryMap;
use indexmap::IndexMap;
use rustc_hash::FxHashMap;
use smallvec::SmallVec;

use crate::{ir_writer::IrWrite, module::ModuleCtx};

#[derive(Debug, Default)]
pub struct TypeStore {
    compounds: PrimaryMap<CompoundTypeRef, CompoundType>,
    rev_types: FxHashMap<CompoundType, CompoundTypeRef>,
    struct_types: IndexMap<String, CompoundTypeRef>,
    enum_types: IndexMap<String, CompoundTypeRef>,
}

impl TypeStore {
    pub fn make_ptr(&mut self, ty: Type) -> Type {
        let ty = self.make_compound(CompoundType::Ptr(ty));
        Type::Compound(ty)
    }

    pub fn make_obj_ref(&mut self, ty: Type) -> Type {
        let ty = self.make_compound(CompoundType::ObjRef(ty));
        Type::Compound(ty)
    }

    pub fn make_array(&mut self, elem: Type, len: usize) -> Type {
        let ty = self.make_compound(CompoundType::Array { elem, len });
        Type::Compound(ty)
    }

    pub fn make_struct(&mut self, name: &str, fields: &[Type], packed: bool) -> Type {
        let compound_data = CompoundType::Struct(StructData {
            name: name.to_string(),
            fields: fields.to_vec(),
            packed,
        });

        let cmpd_ref = self.make_compound(compound_data);
        Type::Compound(cmpd_ref)
    }

    pub fn make_enum(&mut self, name: &str, variants: &[VariantData], repr: EnumReprHint) -> Type {
        let compound_data = CompoundType::Enum(EnumData {
            name: name.to_string(),
            repr,
            variants: variants.to_vec(),
        });

        let cmpd_ref = self.make_compound(compound_data);
        Type::Compound(cmpd_ref)
    }

    pub fn make_func(&mut self, args: &[Type], ret_tys: &[Type]) -> Type {
        let cmpd_ref = self.make_compound(CompoundType::Func {
            args: args.into(),
            ret_tys: ret_tys.into(),
        });
        Type::Compound(cmpd_ref)
    }

    /// Returns `[StructData]` if the given type is a struct type.
    pub fn struct_def(&self, ty: Type) -> Option<&StructData> {
        match ty {
            Type::Compound(cmpd_ref) => match self.compounds[cmpd_ref] {
                CompoundType::Struct(ref def) => Some(def),
                _ => None,
            },
            _ => None,
        }
    }

    pub fn all_compounds(&self) -> impl Iterator<Item = (CompoundTypeRef, &CompoundType)> {
        self.compounds.iter()
    }

    pub fn all_compound_refs(&self) -> impl Iterator<Item = CompoundTypeRef> {
        self.compounds.keys()
    }

    pub fn array_def(&self, ty: Type) -> Option<(Type, usize)> {
        match ty {
            Type::Compound(cmpd_ref) => match self.compounds[cmpd_ref] {
                CompoundType::Array { elem, len } => Some((elem, len)),
                _ => None,
            },
            _ => None,
        }
    }

    /// Lookup the struct type by name.
    pub fn lookup_struct(&self, name: &str) -> Option<CompoundTypeRef> {
        self.struct_types.get(name).copied()
    }

    pub fn lookup_enum(&self, name: &str) -> Option<CompoundTypeRef> {
        self.enum_types.get(name).copied()
    }

    pub fn lookup_named_type(&self, name: &str) -> Option<CompoundTypeRef> {
        self.lookup_struct(name).or_else(|| self.lookup_enum(name))
    }

    /// Update struct fields.
    /// The corresponding `CompoundTypeRef` is still valid after the update.
    ///
    /// # Panic
    /// This function panics if the struct type with the given name is not
    /// found.
    pub fn update_struct_fields(&mut self, name: &str, fields: &[Type]) {
        let Some(cmpd_ref) = self.struct_types.get(name).cloned() else {
            panic!("struct {name} is not found");
        };

        let cmpd = &mut self.compounds[cmpd_ref];
        // Remove old struct data from reverse lookup table.
        self.rev_types.remove(cmpd);

        let CompoundType::Struct(s_data) = cmpd else {
            return;
        };

        // Update struct data.
        s_data.fields = fields.to_vec();
        // Update reverse lookup table.
        self.rev_types.insert(cmpd.clone(), cmpd_ref);
    }

    pub fn update_enum_variants(
        &mut self,
        name: &str,
        variants: &[VariantData],
        repr: EnumReprHint,
    ) {
        let Some(cmpd_ref) = self.enum_types.get(name).cloned() else {
            panic!("enum {name} is not found");
        };

        let cmpd = &mut self.compounds[cmpd_ref];
        self.rev_types.remove(cmpd);

        let CompoundType::Enum(e_data) = cmpd else {
            return;
        };

        e_data.repr = repr;
        e_data.variants = variants.to_vec();
        self.rev_types.insert(cmpd.clone(), cmpd_ref);
    }

    pub fn all_struct_data(&self) -> impl Iterator<Item = &StructData> {
        self.struct_types
            .values()
            .map(|compound_type| match self.compounds[*compound_type] {
                CompoundType::Struct(ref def) => def,
                _ => unreachable!(),
            })
    }

    pub fn all_enum_data(&self) -> impl Iterator<Item = &EnumData> {
        self.enum_types
            .values()
            .map(|compound_type| match self.compounds[*compound_type] {
                CompoundType::Enum(ref def) => def,
                _ => unreachable!(),
            })
    }

    pub fn enum_def(&self, ty: Type) -> Option<&EnumData> {
        let Type::Compound(cmpd_ref) = ty else {
            return None;
        };
        self.enum_data(cmpd_ref)
    }

    pub fn enum_data(&self, cmpd_ref: CompoundTypeRef) -> Option<&EnumData> {
        match self.compounds.get(cmpd_ref)? {
            CompoundType::Enum(data) => Some(data),
            _ => None,
        }
    }

    pub fn enum_variant_ref(&self, enum_ty: CompoundTypeRef, name: &str) -> Option<EnumVariantRef> {
        let data = self.enum_data(enum_ty)?;
        let index = data
            .variants
            .iter()
            .position(|variant| variant.name == name)?;
        Some(EnumVariantRef::new(
            enum_ty,
            u32::try_from(index).expect("enum variant index overflow"),
        ))
    }

    pub fn enum_variant_data(&self, variant: EnumVariantRef) -> Option<&VariantData> {
        let index = usize::try_from(variant.index()).ok()?;
        self.enum_data(variant.enum_ty())?.variants.get(index)
    }

    pub fn deref(&self, ptr: Type) -> Option<Type> {
        match ptr {
            Type::Compound(ty) => {
                let ty_data = &self.compounds[ty];
                match ty_data {
                    CompoundType::Ptr(ty) => Some(*ty),
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
            Type::Compound(cmpd_ref) => self.compounds[cmpd_ref].is_ptr(),
            _ => false,
        }
    }

    pub fn is_obj_ref(&self, ty: Type) -> bool {
        match ty {
            Type::Compound(cmpd_ref) => self.compounds[cmpd_ref].is_obj_ref(),
            _ => false,
        }
    }

    pub fn is_array(&self, ty: Type) -> bool {
        match ty {
            Type::Compound(cmpd_ref) => self.compounds[cmpd_ref].is_array(),
            _ => false,
        }
    }

    pub fn is_struct(&self, ty: Type) -> bool {
        match ty {
            Type::Compound(cmpd_ref) => self.compounds[cmpd_ref].is_struct(),
            _ => false,
        }
    }

    pub fn is_enum(&self, ty: Type) -> bool {
        match ty {
            Type::Compound(cmpd_ref) => self.compounds[cmpd_ref].is_enum(),
            _ => false,
        }
    }

    pub fn is_func(&self, ty: Type) -> bool {
        match ty {
            Type::Compound(cmpd_ref) => self.compounds[cmpd_ref].is_func(),
            _ => false,
        }
    }

    pub fn make_compound(&mut self, data: CompoundType) -> CompoundTypeRef {
        match self.rev_types.get(&data) {
            Some(cmpd_ref) => *cmpd_ref,
            None => {
                let cmpd_ref = self.compounds.push(data.clone());
                if let CompoundType::Struct(s) = &data {
                    let name = &s.name;
                    assert!(
                        !self.struct_types.contains_key(name)
                            && !self.enum_types.contains_key(name),
                        "type {name} is already defined"
                    );
                    self.struct_types.insert(name.to_string(), cmpd_ref);
                } else if let CompoundType::Enum(e) = &data {
                    let name = &e.name;
                    assert!(
                        !self.struct_types.contains_key(name)
                            && !self.enum_types.contains_key(name),
                        "type {name} is already defined"
                    );
                    self.enum_types.insert(name.to_string(), cmpd_ref);
                }

                self.rev_types.insert(data, cmpd_ref);
                cmpd_ref
            }
        }
    }

    pub fn resolve_compound(&self, cmpd_ref: CompoundTypeRef) -> &CompoundType {
        &self.compounds[cmpd_ref]
    }

    pub fn get_compound(&self, cmpd_ref: CompoundTypeRef) -> Option<&CompoundType> {
        self.compounds.get(cmpd_ref)
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
    EnumTag(CompoundTypeRef),
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

    pub fn is_compound(self) -> bool {
        matches!(self, Type::Compound(_))
    }

    pub fn is_unit(self) -> bool {
        matches!(self, Self::Unit)
    }

    pub fn is_enum_tag(self) -> bool {
        matches!(self, Self::EnumTag(_))
    }

    pub fn is_pointer(self, ctx: &ModuleCtx) -> bool {
        ctx.with_ty_store(|store| store.is_ptr(self))
    }

    pub fn is_obj_ref(self, ctx: &ModuleCtx) -> bool {
        ctx.with_ty_store(|store| store.is_obj_ref(self))
    }

    pub fn resolve_compound(self, ctx: &ModuleCtx) -> Option<CompoundType> {
        let Self::Compound(cmpd) = self else {
            return None;
        };

        Some(ctx.with_ty_store(|s| s.resolve_compound(cmpd).clone()))
    }

    pub fn to_ptr(self, ctx: &ModuleCtx) -> Type {
        ctx.with_ty_store_mut(|s| s.make_ptr(self))
    }

    pub fn to_obj_ref(self, ctx: &ModuleCtx) -> Type {
        ctx.with_ty_store_mut(|s| s.make_obj_ref(self))
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
            Type::EnumTag(enum_ty) => {
                write!(w, "enumtag(")?;
                enum_ty.write(w, ctx)?;
                write!(w, ")")
            }
            Type::Compound(cmpd_ty) => cmpd_ty.write(w, ctx),
            Type::Unit => write!(w, "unit"),
        }
    }
}

/// An opaque reference to [`CompoundType`].
#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash, PartialOrd, Ord)]
pub struct CompoundTypeRef(u32);
cranelift_entity::entity_impl!(CompoundTypeRef);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EnumVariantRef {
    enum_ty: CompoundTypeRef,
    index: u32,
}

impl EnumVariantRef {
    pub const fn new(enum_ty: CompoundTypeRef, index: u32) -> Self {
        Self { enum_ty, index }
    }

    pub const fn enum_ty(self) -> CompoundTypeRef {
        self.enum_ty
    }

    pub const fn index(self) -> u32 {
        self.index
    }
}

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
                CompoundType::Array { elem: ty, len } => {
                    write!(w, "[")?;
                    ty.write(w, ctx)?;
                    write!(w, "; {len}]")
                }
                CompoundType::Ptr(ty) => {
                    write!(w, "*")?;
                    ty.write(w, ctx)
                }
                CompoundType::ObjRef(ty) => {
                    write!(w, "objref<")?;
                    ty.write(w, ctx)?;
                    write!(w, ">")
                }
                CompoundType::Struct(StructData { name, packed, .. }) => {
                    if *packed {
                        write!(w, "@<{name}>")
                    } else {
                        write!(w, "@{name}")
                    }
                }
                CompoundType::Enum(EnumData { name, .. }) => write!(w, "@{name}"),

                CompoundType::Func { args, ret_tys } => {
                    write!(w, "(")?;
                    args.write_with_delim(w, ", ", ctx)?;
                    write!(w, ") -> ")?;
                    match ret_tys.as_slice() {
                        [] => Type::Unit.write(w, ctx),
                        [ret_ty] => ret_ty.write(w, ctx),
                        ret_tys => {
                            write!(w, "(")?;
                            ret_tys.write_with_delim(w, ", ", ctx)?;
                            write!(w, ")")
                        }
                    }
                }
            })
    }
}

impl<Ctx> IrWrite<Ctx> for EnumVariantRef
where
    Ctx: AsRef<ModuleCtx>,
{
    fn write<W>(&self, w: &mut W, ctx: &Ctx) -> io::Result<()>
    where
        W: io::Write,
    {
        let variant_name = ctx
            .as_ref()
            .with_ty_store(|store| {
                store
                    .enum_variant_data(*self)
                    .map(|variant| variant.name.clone())
            })
            .expect("enum variant ref must point to an existing variant");
        write!(w, "#{variant_name}")
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CompoundType {
    Array {
        elem: Type,
        len: usize,
    },
    Ptr(Type),
    ObjRef(Type),
    Struct(StructData),
    Enum(EnumData),
    Func {
        args: SmallVec<[Type; 8]>,
        ret_tys: SmallVec<[Type; 2]>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructData {
    pub name: String,
    pub fields: Vec<Type>,
    pub packed: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EnumData {
    pub name: String,
    pub repr: EnumReprHint,
    pub variants: Vec<VariantData>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VariantData {
    pub name: String,
    pub explicit_discriminant: Option<u128>,
    pub fields: Vec<Type>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum EnumReprHint {
    #[default]
    Default,
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

impl<Ctx> IrWrite<Ctx> for EnumData
where
    Ctx: AsRef<ModuleCtx>,
{
    fn write<W>(&self, w: &mut W, ctx: &Ctx) -> io::Result<()>
    where
        W: io::Write,
    {
        writeln!(w, "type @{} = enum {{", self.name)?;
        for variant in &self.variants {
            write!(w, "    #{}", variant.name)?;
            if !variant.fields.is_empty() {
                write!(w, "(")?;
                variant.fields.write_with_delim(w, ", ", ctx)?;
                write!(w, ")")?;
            }
            writeln!(w, ",")?;
        }
        write!(w, "}};")
    }
}

impl CompoundType {
    pub fn is_array(&self) -> bool {
        matches!(self, Self::Array { .. })
    }

    pub fn is_ptr(&self) -> bool {
        matches!(self, Self::Ptr(_))
    }

    pub fn is_obj_ref(&self) -> bool {
        matches!(self, Self::ObjRef(_))
    }

    pub fn is_struct(&self) -> bool {
        matches!(self, Self::Struct(..))
    }

    pub fn is_enum(&self) -> bool {
        matches!(self, Self::Enum(..))
    }

    pub fn is_func(&self) -> bool {
        matches!(self, Self::Func { .. })
    }
}
