mod func_builder;
mod module_builder;
mod ssa;

pub use func_builder::FunctionBuilder;
pub use module_builder::ModuleBuilder;

pub use ssa::Variable;

pub mod test_util {
    use super::*;

    use sonatina_triple::TargetTriple;

    use crate::{
        func_cursor::InsnInserter,
        ir_writer::FuncWriter,
        isa::{IsaBuilder, TargetIsa},
        module::ModuleCtx,
        Function, Linkage, Signature, Type,
    };

    pub fn build_test_isa() -> TargetIsa {
        let triple = TargetTriple::parse("evm-ethereum-london").unwrap();
        IsaBuilder::new(triple).build()
    }

    pub fn test_func_builder(args: &[Type], ret_ty: Type) -> FunctionBuilder<InsnInserter> {
        let ctx = ModuleCtx::new(build_test_isa());
        let mut mb = ModuleBuilder::new(ctx);

        let sig = Signature::new("test_func", Linkage::Public, args, ret_ty);
        let func_ref = mb.declare_function(sig);
        mb.build_function(func_ref)
    }

    pub fn dump_func(func: &Function) -> String {
        let mut writer = FuncWriter::new(func);
        writer.dump_string().unwrap()
    }
}
