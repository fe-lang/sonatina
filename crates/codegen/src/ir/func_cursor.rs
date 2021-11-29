use super::{Block, Function, Insn, InsnData, Value};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CursorLocation {
    At(Insn),
    BlockTop(Block),
    BlockBottom(Block),
    NoWhere,
}

pub trait FuncCursor {
    fn set_loc(&mut self, loc: CursorLocation);
    fn func(&self) -> &Function;
    fn func_mut(&mut self) -> &mut Function;
    fn loc(&self) -> CursorLocation;

    fn insert_insn(&mut self, insn: Insn) {
        match self.loc() {
            CursorLocation::At(at) => self.func_mut().layout.insert_insn_after(insn, at),
            CursorLocation::BlockTop(block) => self.func_mut().layout.prepend_insn(insn, block),
            CursorLocation::BlockBottom(block) => self.func_mut().layout.append_insn(insn, block),
            CursorLocation::NoWhere => panic!("cursor loc points to `NoWhere`"),
        }
    }

    fn append_insn(&mut self, insn: Insn) {
        let current_block = self.expect_block();
        self.func_mut().layout.append_insn(insn, current_block);
    }

    fn prepend_insn(&mut self, insn: Insn) {
        let current_block = self.expect_block();
        self.func_mut().layout.prepend_insn(insn, current_block);
    }

    fn replace(&mut self, insn_data: InsnData) {
        let insn = self.expect_insn();
        self.func_mut().dfg.replace_insn(insn, insn_data);
    }

    fn remove_insn(&mut self) {
        let insn = self.expect_insn();
        let next_loc = self.next_loc();

        for idx in 0..self.func().dfg.insn_args_num(insn) {
            let arg = self.func().dfg.insn_arg(insn, idx);
            self.func_mut().dfg.remove_user(arg, insn);
        }
        self.func_mut().layout.remove_insn(insn);

        self.set_loc(next_loc);
    }

    fn remove_block(&mut self) {
        let block = match self.loc() {
            CursorLocation::At(insn) => self.func_mut().layout.insn_block(insn),
            CursorLocation::BlockTop(block) | CursorLocation::BlockBottom(block) => block,
            CursorLocation::NoWhere => panic!("cursor loc points `NoWhere`"),
        };

        // Store next block of the current block for later use.
        let next_block = self.func().layout.next_block_of(block);

        // Remove all insns in the current block.
        if let Some(first_insn) = self.func().layout.first_insn_of(block) {
            self.set_loc(CursorLocation::At(first_insn));
            while matches!(self.loc(), CursorLocation::At(..)) {
                self.remove_insn();
            }
        }
        // Remove current block.
        self.func_mut().layout.remove_block(block);

        // Set cursor location to next block if exists.
        if let Some(next_block) = next_block {
            self.set_loc(CursorLocation::BlockTop(next_block))
        } else {
            self.set_loc(CursorLocation::NoWhere)
        }
    }

    fn insn(&self) -> Option<Insn> {
        if let CursorLocation::At(insn) = self.loc() {
            Some(insn)
        } else {
            None
        }
    }

    fn expect_insn(&self) -> Insn {
        self.insn()
            .expect("current cursor location doesn't point to insn")
    }

    fn block(&self) -> Option<Block> {
        match self.loc() {
            CursorLocation::At(insn) => Some(self.func().layout.insn_block(insn)),
            CursorLocation::BlockTop(block) | CursorLocation::BlockBottom(block) => Some(block),
            CursorLocation::NoWhere => None,
        }
    }

    fn expect_block(&self) -> Block {
        self.block().expect("cursor loc points to `NoWhere`")
    }

    fn insert_block(&mut self, block: Block) {
        if let Some(current) = self.block() {
            self.func_mut().layout.insert_block_after(block, current)
        } else {
            panic!("cursor loc points `NoWhere`")
        }
    }

    fn insert_block_before(&mut self, block: Block) {
        if let Some(current) = self.block() {
            self.func_mut().layout.insert_block_before(block, current)
        } else {
            panic!("cursor loc points `NoWhere`")
        }
    }

    fn append_block(&mut self, block: Block) {
        self.func_mut().layout.append_block(block);
    }

    fn next_loc(&self) -> CursorLocation {
        match self.loc() {
            CursorLocation::At(insn) => self.func().layout.next_insn_of(insn).map_or_else(
                || CursorLocation::BlockBottom(self.func().layout.insn_block(insn)),
                CursorLocation::At,
            ),
            CursorLocation::BlockTop(block) => self
                .func()
                .layout
                .first_insn_of(block)
                .map_or_else(|| CursorLocation::BlockBottom(block), CursorLocation::At),
            CursorLocation::BlockBottom(block) => self
                .func()
                .layout
                .next_block_of(block)
                .map_or(CursorLocation::NoWhere, |next_block| {
                    CursorLocation::BlockTop(next_block)
                }),
            CursorLocation::NoWhere => CursorLocation::NoWhere,
        }
    }

    fn prev_loc(&self) -> CursorLocation {
        match self.loc() {
            CursorLocation::At(insn) => self.func().layout.prev_insn_of(insn).map_or_else(
                || CursorLocation::BlockTop(self.func().layout.insn_block(insn)),
                CursorLocation::At,
            ),
            CursorLocation::BlockTop(block) => self
                .func()
                .layout
                .prev_block_of(block)
                .map_or(CursorLocation::NoWhere, |prev_block| {
                    CursorLocation::BlockBottom(prev_block)
                }),
            CursorLocation::BlockBottom(block) => self
                .func()
                .layout
                .last_insn_of(block)
                .map_or_else(|| CursorLocation::BlockTop(block), CursorLocation::At),
            CursorLocation::NoWhere => CursorLocation::NoWhere,
        }
    }

    fn proceed(&mut self) {
        self.set_loc(self.next_loc());
    }

    fn back(&mut self) {
        self.set_loc(self.prev_loc());
    }

    fn next_block(&self) -> Option<Block> {
        let block = self.block()?;
        self.func().layout.next_block_of(block)
    }

    fn prev_block(&self) -> Option<Block> {
        let block = self.block()?;
        self.func().layout.prev_block_of(block)
    }
}

#[derive(Debug)]
pub struct InsnInserter<'a> {
    func: &'a mut Function,
    loc: CursorLocation,
}

impl<'a> FuncCursor for InsnInserter<'a> {
    fn set_loc(&mut self, loc: CursorLocation) {
        self.loc = loc;
    }

    fn func(&self) -> &Function {
        self.func
    }

    fn func_mut(&mut self) -> &mut Function {
        &mut self.func
    }

    fn loc(&self) -> CursorLocation {
        self.loc
    }
}

impl<'a> InsnInserter<'a> {
    pub fn new(func: &'a mut Function, loc: CursorLocation) -> Self {
        Self { func, loc }
    }

    pub fn insert_insn_data(&mut self, data: InsnData) -> Insn {
        let insn = self.func.dfg.make_insn(data);
        self.insert_insn(insn);
        insn
    }

    pub fn append_insn_data(&mut self, data: InsnData) -> Insn {
        let insn = self.func.dfg.make_insn(data);
        self.append_insn(insn);
        insn
    }

    pub fn prepend_insn_data(&mut self, data: InsnData) -> Insn {
        let insn = self.func.dfg.make_insn(data);
        self.prepend_insn(insn);
        insn
    }

    pub fn make_result(&mut self, insn: Insn) -> Option<Value> {
        let value_data = self.func.dfg.make_result(insn)?;
        Some(self.func.dfg.make_value(value_data))
    }

    pub fn attach_result(&mut self, insn: Insn, value: Value) {
        self.func.dfg.attach_result(insn, value)
    }

    pub fn make_block(&mut self) -> Block {
        self.func.dfg.make_block()
    }
}
