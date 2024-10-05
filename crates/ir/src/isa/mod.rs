use sonatina_triple::TargetTriple;

use crate::{types::TypeStore, InstSetBase, Type};

pub mod evm;

pub trait Isa {
    type InstSet: InstSetBase + 'static;

    fn triple(&self) -> TargetTriple;
    fn inst_set(&self) -> &'static Self::InstSet;
    fn type_layout(&self) -> &'static dyn TypeLayout;
}

pub trait TypeLayout {
    fn size_of(&self, ty: Type, ty_store: &TypeStore) -> usize;

    fn endian(&self) -> Endian;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Endian {
    Be,
    Le,
}
