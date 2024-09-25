use sonatina_triple::TargetTriple;

use crate::InstSetBase;

pub mod evm;

pub trait Isa {
    type InstSet: InstSetBase;

    fn triple(&self) -> TargetTriple;
    fn inst_set() -> &'static dyn InstSetBase;
    fn type_layout() -> &'static dyn TypeLayout;
}

pub trait TypeLayout {
    fn pointer_size(&self) -> usize;
}
