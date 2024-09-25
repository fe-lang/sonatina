use sonatina_triple::TargetTriple;

use crate::InstSetBase;

pub mod evm;

pub trait Isa {
    type InstSet: InstSetBase + 'static;

    fn triple(&self) -> TargetTriple;
    fn inst_set(&self) -> &'static Self::InstSet;
    fn type_layout(&self) -> &'static dyn TypeLayout;
}

pub trait TypeLayout {
    fn pointer_size(&self) -> usize;
}
