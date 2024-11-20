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
    fn size_of(&self, ty: Type, ctx: &ModuleCtx) -> usize;
    fn align_of(&self, ty: Type, ctx: &ModuleCtx) -> usize;
    fn pointer_repl(&self) -> Type;
    fn endian(&self) -> Endian;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Endian {
    Be,
    Le,
}
