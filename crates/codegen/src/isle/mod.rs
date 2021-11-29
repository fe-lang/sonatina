pub(crate) mod prelude {
    pub(crate) use crate::ir::{Block, DataFlowGraph, Insn, InsnData, Type, Value};

    pub(crate) type ValueArray1 = [Value; 1];
    pub(crate) type ValueArray2 = [Value; 2];

    pub(crate) type BlockArray1 = [Block; 1];
    pub(crate) type BlockArray2 = [Block; 2];

    macro_rules! impl_prelude_ctx {
        () => {
            fn unpack_value_array1(&mut self, arg0: &ValueArray1) -> Value {
                arg0[0]
            }

            fn pack_value_array1(&mut self, arg0: Value) -> ValueArray1 {
                [arg0]
            }

            fn unpack_value_array2(&mut self, arg0: &ValueArray2) -> (Value, Value) {
                (arg0[0], arg0[1])
            }

            fn pack_value_array2(&mut self, arg0: Value, arg1: Value) -> ValueArray2 {
                [arg0, arg1]
            }

            fn unpack_block_array1(&mut self, arg0: &BlockArray1) -> Block {
                arg0[0]
            }

            fn pack_block_array1(&mut self, arg0: Block) -> BlockArray1 {
                [arg0]
            }

            fn unpack_block_array2(&mut self, arg0: &BlockArray2) -> (Block, Block) {
                (arg0[0], arg0[1])
            }

            fn pack_block_array2(&mut self, arg0: Block, arg1: Block) -> BlockArray2 {
                [arg0, arg1]
            }

            fn insn_data(&mut self, arg0: Insn) -> InsnData {
                self.dfg().insn_data(arg0).clone()
            }

            fn value_ty(&mut self, arg0: Value) -> Type {
                self.dfg().value_ty(arg0).clone()
            }

            fn value_insn(&mut self, arg0: Value) -> Option<Insn> {
                self.dfg().value_insn(arg0)
            }
        };
    }

    pub(crate) use impl_prelude_ctx;
}
