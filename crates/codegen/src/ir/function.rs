use super::{Block, BlockData, DataFlowGraph, Insn, InsnData, Layout, Type};

pub struct Function {
    /// Name of the function.
    pub name: String,

    /// Signature of the function.
    pub sig: Signature,

    pub dfg: DataFlowGraph,
    pub layout: Layout,
}

pub struct Signature {
    pub args: Vec<Type>,
    pub rets: Vec<Type>,
}

pub struct FunctionCursor<'a> {
    func: &'a mut Function,
    loc: CursorLocation,
}

pub enum CursorLocation {
    At(Insn),
    BlockTop(Block),
    BlockBottom(Block),
}

impl<'a> FunctionCursor<'a> {
    pub fn at(&mut self, loc: CursorLocation) {
        self.loc = loc;
    }

    pub fn insert_insn(&mut self, data: InsnData) -> Insn {
        todo!()
    }

    pub fn insert_block(&mut self, block_data: BlockData) -> Block {
        todo!()
    }

    pub fn remove_insn(&mut self, insn: Insn) {
}
