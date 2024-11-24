use sonatina_triple::TargetTriple;

use crate::{module::ModuleCtx, InstSetBase, Type};

pub mod evm;

pub trait Isa {
    type InstSet: InstSetBase + 'static;

    fn triple(&self) -> TargetTriple;
    fn inst_set(&self) -> &'static Self::InstSet;
    fn type_layout(&self) -> &'static dyn TypeLayout;
}

pub trait TypeLayout: Send + Sync {
    fn size_of(&self, ty: Type, ctx: &ModuleCtx) -> Result<usize, TypeLayoutError>;
    fn align_of(&self, ty: Type, ctx: &ModuleCtx) -> Result<usize, TypeLayoutError>;
    fn pointer_repl(&self) -> Type;
    fn endian(&self) -> Endian;
}

#[derive(Debug, Clone)]
pub enum TypeLayoutError {
    /// The type is unsupported by the ISA.
    UnsupportedType(Type),

    /// An error indicating that the given type cannot be represented in memory.
    ///
    /// This error occurs when attempting to compute the size or alignment of a
    /// type that is abstract or has no concrete representation in memory.
    /// For example, function types or unresolved abstract types cannot be
    /// laid out in memory.
    UnrepresentableType(Type),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Endian {
    Be,
    Le,
}
