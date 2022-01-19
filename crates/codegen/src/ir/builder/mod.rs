mod func_builder;
mod module_builder;
mod ssa;

pub use func_builder::FunctionBuilder;
pub use module_builder::ModuleBuilder;

pub use ssa::Variable;

#[cfg(test)]
pub(crate) mod test_util {
    use super::*;

    use sonatina_triple::TargetTriple;

    use crate::{
        ir::{
            ir_writer::FuncWriter,
            module::{FuncRef, Linkage, Module},
            Function, Signature, Type,
        },
        isa::{IsaBuilder, TargetIsa},
    };

    pub(crate) fn build_test_isa() -> TargetIsa {
        let triple = TargetTriple::parse("evm-ethereum-london").unwrap();
        IsaBuilder::new(triple).build()
    }

    pub(crate) struct TestModuleBuilder {
        module_builder: ModuleBuilder,
        func_ref: Option<FuncRef>,
    }

    impl TestModuleBuilder {
        pub(crate) fn new() -> Self {
            Self {
                module_builder: ModuleBuilder::new(build_test_isa()),
                func_ref: None,
            }
        }

        pub fn func_builder(&mut self, args: &[Type], ret: Option<&Type>) -> FunctionBuilder {
            let sig = Signature::new("test_func", args, ret);
            let func_ref = self.module_builder.declare_function(sig, Linkage::Private);
            self.func_ref = Some(func_ref);
            self.module_builder.func_builder(func_ref)
        }

        pub fn build(self) -> Module {
            self.module_builder.build()
        }
    }

    pub(crate) fn dump_func(func: &Function) -> String {
        let mut writer = FuncWriter::new(func);
        writer.dump_string().unwrap()
    }
}
