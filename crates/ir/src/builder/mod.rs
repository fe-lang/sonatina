mod func_builder;
mod module_builder;
mod ssa;

pub use func_builder::FunctionBuilder;
pub use module_builder::ModuleBuilder;
pub use ssa::Variable;

pub mod test_util {
    use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

    use super::*;
    use crate::{
        func_cursor::InstInserter,
        ir_writer::FuncWriter,
        isa::evm::Evm,
        module::{FuncRef, ModuleCtx},
        Linkage, Module, Signature, Type,
    };

    pub fn test_isa() -> Evm {
        let triple = TargetTriple::new(
            Architecture::Evm,
            Vendor::Ethereum,
            OperatingSystem::Evm(EvmVersion::London),
        );

        Evm::new(triple)
    }

    pub fn test_func_builder(args: &[Type], ret_ty: Type) -> (Evm, FunctionBuilder<InstInserter>) {
        let ctx = ModuleCtx::new(&test_isa());
        let mut mb = ModuleBuilder::new(ctx);

        let sig = Signature::new("test_func", Linkage::Public, args, ret_ty);
        let func_ref = mb.declare_function(sig);
        (test_isa(), mb.build_function(func_ref))
    }

    pub fn dump_func(module: &Module, func_ref: FuncRef) -> String {
        let func = &module.funcs[func_ref];
        FuncWriter::new(func, func_ref).dump_string()
    }
}
