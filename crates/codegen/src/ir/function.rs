use super::{Block, DataFlowGraph, Insn, InsnData, Layout, Type};

#[derive(Debug, Clone)]
pub struct Function {
    /// Name of the function.
    pub name: String,

    /// Signature of the function.
    pub sig: Signature,

    pub dfg: DataFlowGraph,
    pub layout: Layout,
}

#[derive(Debug, Clone, Default)]
pub struct Signature {
    pub args: Vec<Type>,
    pub rets: Vec<Type>,
}

#[derive(Debug)]
pub struct FunctionCursor<'a> {
    func: &'a mut Function,
    loc: CursorLocation,
}

#[derive(Debug, Clone, Copy)]
pub enum CursorLocation {
    At(Insn),
    BlockTop(Block),
    BlockBottom(Block),
    NoWhere,
}

impl<'a> FunctionCursor<'a> {
    pub fn at(&mut self, loc: CursorLocation) {
        self.loc = loc;
    }

    pub fn insert_insn(&mut self, data: InsnData) -> Insn {
        let new_insn = self.func.dfg.make_insn(data);
        match self.loc {
            CursorLocation::At(insn) => self.func.layout.insert_insn_before(new_insn, insn),
            CursorLocation::BlockTop(block) => self.func.layout.prepend_insn(new_insn, block),
            CursorLocation::BlockBottom(block) => self.func.layout.append_insn(new_insn, block),
            CursorLocation::NoWhere => panic!("cursor loc points to `NoWhere`"),
        }

        new_insn
    }

    pub fn append_insn(&mut self, data: InsnData) -> Insn {
        let new_insn = self.func.dfg.make_insn(data);
        let current_block = self.block().expect("cursor loc points to `NoWhere`");
        self.func.layout.append_insn(new_insn, current_block);
        new_insn
    }

    pub fn prepend_insn(&mut self, data: InsnData) -> Insn {
        let new_insn = self.func.dfg.make_insn(data);
        let current_block = self.block().expect("cursor loc points to `NoWhere`");
        self.func.layout.prepend_insn(new_insn, current_block);
        new_insn
    }

    pub fn insert_block(&mut self) -> Block {
        let new_block = self.func.dfg.make_block();
        let block = self.block().expect("cursor loc points to `NoWhere`");
        self.func.layout.insert_block_before(new_block, block);
        new_block
    }

    pub fn remove_insn(&mut self) {
        let insn = self
            .insn()
            .expect("current cursor location doesn't point to insn");
        self.proceed();
        self.func.layout.remove_insn(insn);
    }

    pub fn remove_block(&mut self) {
        let block = match self.loc {
            CursorLocation::At(insn) => self.func.layout.insn_block(insn),
            CursorLocation::BlockTop(block) | CursorLocation::BlockBottom(block) => block,
            CursorLocation::NoWhere => panic!("cursor loc points `NoWhere`"),
        };

        let next_block = self.func.layout.next_block_of(block);
        if let Some(next_block) = next_block {
            self.loc = CursorLocation::BlockTop(next_block);
        } else {
            self.loc = CursorLocation::NoWhere;
        }

        self.func.layout.remove_block(block)
    }

    pub fn current_loc(&self) -> CursorLocation {
        self.loc
    }

    pub fn block(&self) -> Option<Block> {
        match self.loc {
            CursorLocation::At(insn) => Some(self.func.layout.insn_block(insn)),
            CursorLocation::BlockTop(block) | CursorLocation::BlockBottom(block) => Some(block),
            CursorLocation::NoWhere => None,
        }
    }

    pub fn insn(&self) -> Option<Insn> {
        if let CursorLocation::At(insn) = self.loc {
            Some(insn)
        } else {
            None
        }
    }

    pub fn next(&self) -> CursorLocation {
        match self.loc {
            CursorLocation::At(insn) => self.func.layout.next_insn_of(insn).map_or_else(
                || CursorLocation::BlockBottom(self.func.layout.insn_block(insn)),
                |next_insn| CursorLocation::At(next_insn),
            ),
            CursorLocation::BlockTop(block) => self.func.layout.first_insn_of(block).map_or_else(
                || CursorLocation::BlockBottom(block),
                |insn| CursorLocation::At(insn),
            ),
            CursorLocation::BlockBottom(block) => self
                .func
                .layout
                .next_block_of(block)
                .map_or(CursorLocation::NoWhere, |next_block| {
                    CursorLocation::BlockTop(next_block)
                }),
            CursorLocation::NoWhere => CursorLocation::NoWhere,
        }
    }

    pub fn prev(&self) -> CursorLocation {
        match self.loc {
            CursorLocation::At(insn) => self.func.layout.prev_insn_of(insn).map_or_else(
                || CursorLocation::BlockTop(self.func.layout.insn_block(insn)),
                |prev_insn| CursorLocation::At(prev_insn),
            ),
            CursorLocation::BlockTop(block) => self
                .func
                .layout
                .prev_block_of(block)
                .map_or(CursorLocation::NoWhere, |prev_block| {
                    CursorLocation::BlockBottom(prev_block)
                }),
            CursorLocation::BlockBottom(block) => self.func.layout.last_insn_of(block).map_or_else(
                || CursorLocation::BlockTop(block),
                |last_insn| CursorLocation::At(last_insn),
            ),
            CursorLocation::NoWhere => CursorLocation::NoWhere,
        }
    }

    pub fn next_block(&self) -> Option<Block> {
        let block = self.block()?;
        self.func.layout.next_block_of(block)
    }

    pub fn prev_block(&self) -> Option<Block> {
        let block = self.block()?;
        self.func.layout.prev_block_of(block)
    }

    pub fn proceed(&mut self) {
        self.loc = self.next();
    }

    pub fn back(&mut self) {
        self.loc = self.prev();
    }
}
