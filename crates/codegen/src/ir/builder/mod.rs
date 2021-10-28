pub mod builder;
mod ssa;

pub use ssa::Variable;

pub use builder::{Context, FunctionBuilder};

#[cfg(test)]
pub(crate) mod test_util {
    use super::*;

    use crate::ir::ir_writer::FuncWriter;

    use crate::{Function, Signature, Type};

    pub struct TestContext {}

    impl Context for TestContext {
        fn hash_type(&self) -> Type {
            Type::I256
        }

        fn address_type(&self) -> Type {
            Type::make_array(Type::I8, 20)
        }

        fn balance_type(&self) -> Type {
            Type::I256
        }

        fn gas_type(&self) -> Type {
            Type::I256
        }
    }

    pub(crate) fn func_builder(args: Vec<Type>, rets: Vec<Type>) -> FunctionBuilder {
        let sig = Signature::new(args, rets);
        let ctxt = TestContext {};
        FunctionBuilder::new("test_func".into(), sig, Box::new(ctxt))
    }

    pub(crate) fn dump_func(func: &Function) -> String {
        let mut writer = FuncWriter::new(&func);
        writer.dump_string().unwrap()
    }
}
