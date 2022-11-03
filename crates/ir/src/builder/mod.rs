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
        ir_writer::FuncWriter,
        isa::{IsaBuilder, TargetIsa},
        module::{FuncRef, Module, ModuleCtx},
        Function, Linkage, Signature, Type,
    };

    pub fn build_test_isa() -> TargetIsa {
        let triple = TargetTriple::parse("evm-ethereum-london").unwrap();
        IsaBuilder::new(triple).build()
    }

    pub struct TestModuleBuilder {
        module_builder: ModuleBuilder,
        func_ref: Option<FuncRef>,
    }

    impl TestModuleBuilder {
        pub fn new() -> Self {
            Self::default()
        }

        pub fn func_builder(&mut self, args: &[Type], ret_ty: &Type) -> FunctionBuilder {
            let sig = Signature::new("test_func", Linkage::Public, args, ret_ty);
            let func_ref = self.module_builder.declare_function(sig);
            self.func_ref = Some(func_ref);
            self.module_builder.func_builder(func_ref)
        }

        pub fn build(self) -> Module {
            self.module_builder.build()
        }
    }

    pub fn dump_func(func: &Function) -> String {
        let mut writer = FuncWriter::new(func);
        writer.dump_string().unwrap()
    }

    impl Default for TestModuleBuilder {
        fn default() -> Self {
            Self {
                module_builder: ModuleBuilder::new(ModuleCtx::default(), build_test_isa()),
                func_ref: None,
            }
        }
    }
}
