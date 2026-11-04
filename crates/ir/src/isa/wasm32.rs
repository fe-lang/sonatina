//! The `wasm32` ISA: 32-bit pointers into a single linear memory.
//!
//! It shares the instruction vocabulary, address space and little-endian type
//! layout of the [native](super::native) ISA. The only difference is the width
//! of a pointer or reference: 4 bytes, represented as an `i32`.

use sonatina_triple::{Architecture, TargetTriple};

use super::{
    Isa, TypeLayout,
    native::{self, NATIVE_ADDRESS_SPACES_INFO, WASM32_TYPE_LAYOUT},
};
use crate::{AddressSpaceInfo, inst::native::inst_set::NativeInstSet};

pub use super::native::space;

#[derive(Debug, Clone, Copy)]
pub struct Wasm32 {
    triple: TargetTriple,
}

impl Wasm32 {
    pub fn new(triple: TargetTriple) -> Self {
        assert!(matches!(triple.architecture, Architecture::Wasm32));
        Self { triple }
    }
}

impl Isa for Wasm32 {
    type InstSet = NativeInstSet;

    fn triple(&self) -> TargetTriple {
        self.triple
    }

    fn type_layout(&self) -> &'static dyn TypeLayout {
        &WASM32_TYPE_LAYOUT
    }

    fn address_spaces(&self) -> &'static dyn AddressSpaceInfo {
        &NATIVE_ADDRESS_SPACES_INFO
    }

    fn inst_set(&self) -> &'static Self::InstSet {
        native::inst_set()
    }
}

#[cfg(test)]
mod tests {
    use sonatina_triple::{Architecture, OperatingSystem, TargetTriple, Vendor};

    use super::{Wasm32, space};
    use crate::{AddressSpaceKind, Module, Type, isa::Isa};

    fn wasm32_isa() -> Wasm32 {
        Wasm32::new(TargetTriple::new(
            Architecture::Wasm32,
            Vendor::Unknown,
            OperatingSystem::Native,
        ))
    }

    #[test]
    fn pointers_are_four_bytes_and_represented_as_i32() {
        let isa = wasm32_isa();
        assert_eq!(isa.type_layout().pointer_repl(), Type::I32);
        assert_eq!(isa.address_spaces().default_space(), space::MEMORY);
        assert_eq!(
            isa.address_spaces().desc(space::MEMORY).kind,
            AddressSpaceKind::Linear
        );

        let module = Module::new(&isa);
        let (pointer, structure) = module.ctx.with_ty_store_mut(|store| {
            let pointer = store.make_ptr(Type::I8);
            let structure = store.make_struct("Pair", &[pointer, Type::I64], false);
            (pointer, structure)
        });
        assert_eq!(module.ctx.size_of_unchecked(pointer), 4);
        assert_eq!(module.ctx.align_of_unchecked(pointer), 4);
        assert_eq!(module.ctx.size_of_unchecked(structure), 16);
        assert_eq!(module.ctx.align_of_unchecked(structure), 8);
    }

    #[test]
    fn instruction_set_matches_the_native_vocabulary() {
        use crate::InstSetBase;

        let isa = wasm32_isa();
        let inst_set = isa.inst_set();
        assert!(inst_set.has_add().is_some());
        assert!(inst_set.has_umulo().is_some());
        assert!(inst_set.has_mload().is_some());
        assert!(inst_set.has_call().is_some());
        assert!(inst_set.has_evm_stop().is_none());
    }
}
