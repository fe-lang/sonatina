mod func_builder;
mod ssa;

pub use func_builder::FunctionBuilder;

pub use ssa::Variable;

#[cfg(test)]
pub(crate) mod test_util {
    use super::*;

    use sonatina_triple::TargetTriple;

    use crate::{
        ir::{ir_writer::FuncWriter, Function, Signature, Type},
        isa::{IsaBuilder, TargetIsa},
    };

    pub(crate) fn build_test_isa() -> TargetIsa {
        let triple = TargetTriple::parse("evm-ethereum-london").unwrap();
        IsaBuilder::new(triple).build()
    }

    pub(crate) fn func_builder<'isa>(
        args: &[Type],
        ret: Option<&Type>,
        isa: &'isa TargetIsa,
    ) -> FunctionBuilder<'isa> {
        let sig = Signature::new("test_func", args, ret);
        FunctionBuilder::new(sig, isa)
    }

    pub(crate) fn dump_func(func: &Function) -> String {
        let mut writer = FuncWriter::new(func);
        writer.dump_string().unwrap()
    }
}
