use super::{Block, Function, Insn, InsnData, ValueId};

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
pub enum CursorLocation {
    At(Insn),
    BlockTop(Block),
    BlockBottom(Block),
    #[default]
    NoWhere,
}

pub trait FuncCursor {
    fn at_location(loc: CursorLocation) -> Self;
    fn set_location(&mut self, loc: CursorLocation);
    fn loc(&self) -> CursorLocation;

    fn set_to_entry(&mut self, func: &Function) {
        let loc = if let Some(entry) = func.layout.entry_block() {
            CursorLocation::BlockTop(entry)
        } else {
            CursorLocation::NoWhere
        };

        self.set_location(loc);
    }

    fn insert_insn(&mut self, func: &mut Function, insn: Insn) {
        match self.loc() {
            CursorLocation::At(at) => func.layout.insert_insn_after(insn, at),
            CursorLocation::BlockTop(block) => func.layout.prepend_insn(insn, block),
            CursorLocation::BlockBottom(block) => func.layout.append_insn(insn, block),
            CursorLocation::NoWhere => panic!("cursor loc points to `NoWhere`"),
        }
    }

    fn append_insn(&mut self, func: &mut Function, insn: Insn) {
        let current_block = self.expect_block(func);
        func.layout.append_insn(insn, current_block);
    }

    fn prepend_insn(&mut self, func: &mut Function, insn: Insn) {
        let current_block = self.expect_block(func);
        func.layout.prepend_insn(insn, current_block);
    }

    fn insert_insn_data(&mut self, func: &mut Function, data: InsnData) -> Insn {
        let insn = func.dfg.make_insn(data);
        self.insert_insn(func, insn);
        insn
    }

    fn append_insn_data(&mut self, func: &mut Function, data: InsnData) -> Insn {
        let insn = func.dfg.make_insn(data);
        self.append_insn(func, insn);
        insn
    }

    fn prepend_insn_data(&mut self, func: &mut Function, data: InsnData) -> Insn {
        let insn = func.dfg.make_insn(data);
        self.prepend_insn(func, insn);
        insn
    }

    fn replace(&mut self, func: &mut Function, insn_data: InsnData) {
        let insn = self.expect_insn();
        func.dfg.replace_insn(insn, insn_data);
    }

    fn remove_insn(&mut self, func: &mut Function) {
        let insn = self.expect_insn();
        let next_loc = self.next_loc(func);

        for idx in 0..func.dfg.insn_args_num(insn) {
            let arg = func.dfg.insn_arg(insn, idx);
            func.dfg.remove_user(arg, insn);
        }
        func.layout.remove_insn(insn);

        self.set_location(next_loc);
    }

    fn make_result(&mut self, func: &mut Function, insn: Insn) -> Option<ValueId> {
        let value_data = func.dfg.make_result(insn)?;
        Some(func.dfg.make_value(value_data))
    }

    fn attach_result(&mut self, func: &mut Function, insn: Insn, value: ValueId) {
        func.dfg.attach_result(insn, value)
    }

    fn make_block(&mut self, func: &mut Function) -> Block {
        func.dfg.make_block()
    }

    fn remove_block(&mut self, func: &mut Function) {
        let block = match self.loc() {
            CursorLocation::At(insn) => func.layout.insn_block(insn),
            CursorLocation::BlockTop(block) | CursorLocation::BlockBottom(block) => block,
            CursorLocation::NoWhere => panic!("cursor loc points `NoWhere`"),
        };

        // Store next block of the current block for later use.
        let next_block = func.layout.next_block_of(block);

        // Remove all insns in the current block.
        if let Some(first_insn) = func.layout.first_insn_of(block) {
            self.set_location(CursorLocation::At(first_insn));
            while matches!(self.loc(), CursorLocation::At(..)) {
                self.remove_insn(func);
            }
        }
        // Remove current block.
        func.layout.remove_block(block);

        // Set cursor location to next block if exists.
        if let Some(next_block) = next_block {
            self.set_location(CursorLocation::BlockTop(next_block))
        } else {
            self.set_location(CursorLocation::NoWhere)
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

    fn block(&self, func: &Function) -> Option<Block> {
        match self.loc() {
            CursorLocation::At(insn) => Some(func.layout.insn_block(insn)),
            CursorLocation::BlockTop(block) | CursorLocation::BlockBottom(block) => Some(block),
            CursorLocation::NoWhere => None,
        }
    }

    fn expect_block(&self, func: &Function) -> Block {
        self.block(func).expect("cursor loc points to `NoWhere`")
    }

    fn insert_block(&mut self, func: &mut Function, block: Block) {
        if let Some(current) = self.block(func) {
            func.layout.insert_block_after(block, current)
        } else {
            panic!("cursor loc points `NoWhere`")
        }
    }

    fn insert_block_before(&mut self, func: &mut Function, block: Block) {
        if let Some(current) = self.block(func) {
            func.layout.insert_block_before(block, current)
        } else {
            panic!("cursor loc points `NoWhere`")
        }
    }

    fn append_block(&mut self, func: &mut Function, block: Block) {
        func.layout.append_block(block);
    }

    fn next_loc(&self, func: &Function) -> CursorLocation {
        match self.loc() {
            CursorLocation::At(insn) => func.layout.next_insn_of(insn).map_or_else(
                || CursorLocation::BlockBottom(func.layout.insn_block(insn)),
                CursorLocation::At,
            ),
            CursorLocation::BlockTop(block) => func
                .layout
                .first_insn_of(block)
                .map_or_else(|| CursorLocation::BlockBottom(block), CursorLocation::At),
            CursorLocation::BlockBottom(block) => func
                .layout
                .next_block_of(block)
                .map_or(CursorLocation::NoWhere, |next_block| {
                    CursorLocation::BlockTop(next_block)
                }),
            CursorLocation::NoWhere => CursorLocation::NoWhere,
        }
    }

    fn prev_loc(&self, func: &Function) -> CursorLocation {
        match self.loc() {
            CursorLocation::At(insn) => func.layout.prev_insn_of(insn).map_or_else(
                || CursorLocation::BlockTop(func.layout.insn_block(insn)),
                CursorLocation::At,
            ),
            CursorLocation::BlockTop(block) => func
                .layout
                .prev_block_of(block)
                .map_or(CursorLocation::NoWhere, |prev_block| {
                    CursorLocation::BlockBottom(prev_block)
                }),
            CursorLocation::BlockBottom(block) => func
                .layout
                .last_insn_of(block)
                .map_or_else(|| CursorLocation::BlockTop(block), CursorLocation::At),
            CursorLocation::NoWhere => CursorLocation::NoWhere,
        }
    }

    fn proceed(&mut self, func: &Function) {
        self.set_location(self.next_loc(func));
    }

    fn proceed_block(&mut self, func: &mut Function) {
        let loc = if let Some(block) = self.next_block(func) {
            CursorLocation::BlockTop(block)
        } else {
            CursorLocation::NoWhere
        };
        self.set_location(loc)
    }

    fn back(&mut self, func: &Function) {
        self.set_location(self.prev_loc(func));
    }

    fn next_block(&self, func: &Function) -> Option<Block> {
        let block = self.block(func)?;
        func.layout.next_block_of(block)
    }

    fn prev_block(&self, func: &Function) -> Option<Block> {
        let block = self.block(func)?;
        func.layout.prev_block_of(block)
    }
}

#[derive(Debug)]
pub struct InsnInserter {
    loc: CursorLocation,
}

impl FuncCursor for InsnInserter {
    fn at_location(loc: CursorLocation) -> Self {
        Self { loc }
    }

    fn set_location(&mut self, loc: CursorLocation) {
        self.loc = loc;
    }

    fn loc(&self) -> CursorLocation {
        self.loc
    }
}
