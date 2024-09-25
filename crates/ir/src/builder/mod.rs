mod func_builder;
mod module_builder;
mod ssa;

pub use func_builder::FunctionBuilder;
pub use module_builder::ModuleBuilder;

pub use ssa::Variable;

pub mod test_util {
    use super::*;

    use sonatina_triple::EvmVersion;

    use crate::{
        func_cursor::InstInserter,
        isa::evm::Evm,
        module::{FuncRef, ModuleCtx},
        Linkage, Module, Signature, Type,
    };

    pub fn test_isa() -> Evm {
        Evm::new(EvmVersion::London)
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
        format!("{func}")
    }
}
