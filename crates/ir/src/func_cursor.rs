use crate::{Inst, InstId};

use super::{BlockId, Function, ValueId};

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
pub enum CursorLocation {
    At(InstId),
    BlockTop(BlockId),
    BlockBottom(BlockId),
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

    fn insert_inst(&mut self, func: &mut Function, inst: InstId) {
        match self.loc() {
            CursorLocation::At(at) => func.layout.insert_inst_after(inst, at),
            CursorLocation::BlockTop(block) => func.layout.prepend_inst(inst, block),
            CursorLocation::BlockBottom(block) => func.layout.append_inst(inst, block),
            CursorLocation::NoWhere => panic!("cursor loc points to `NoWhere`"),
        }
    }

    fn append_inst(&mut self, func: &mut Function, inst: InstId) {
        let current_block = self.expect_block(func);
        func.layout.append_inst(inst, current_block);
    }

    fn prepend_inst(&mut self, func: &mut Function, inst: InstId) {
        let current_block = self.expect_block(func);
        func.layout.prepend_inst(inst, current_block);
    }

    fn insert_inst_data<I: Inst>(&mut self, func: &mut Function, data: I) -> InstId {
        let inst = func.dfg.make_inst(data);
        self.insert_inst(func, inst);
        inst
    }

    fn append_inst_data<I: Inst>(&mut self, func: &mut Function, data: I) -> InstId {
        let inst = func.dfg.make_inst(data);
        self.append_inst(func, inst);
        inst
    }

    fn prepend_inst_data<I: Inst>(&mut self, func: &mut Function, data: I) -> InstId {
        let inst = func.dfg.make_inst(data);
        self.prepend_inst(func, inst);
        inst
    }

    fn replace<I: Inst>(&mut self, func: &mut Function, data: I) {
        let old = self.expect_inst();
        func.dfg.replace_inst(old, Box::new(data));
    }

    fn remove_inst(&mut self, func: &mut Function) {
        let inst_id = self.expect_inst();
        func.dfg.untrack_inst(inst_id);
        func.layout.remove_inst(inst_id);

        let next_loc = self.next_loc(func);
        self.set_location(next_loc);
    }

    fn attach_result(&mut self, func: &mut Function, inst: InstId, value: ValueId) {
        func.dfg.attach_result(inst, value)
    }

    fn make_block(&mut self, func: &mut Function) -> BlockId {
        func.dfg.make_block()
    }

    fn remove_block(&mut self, func: &mut Function) {
        let block = match self.loc() {
            CursorLocation::At(inst) => func.layout.inst_block(inst),
            CursorLocation::BlockTop(block) | CursorLocation::BlockBottom(block) => block,
            CursorLocation::NoWhere => panic!("cursor loc points `NoWhere`"),
        };

        // Store next block of the current block for later use.
        let next_block = func.layout.next_block_of(block);

        // Remove all insts in the current block.
        if let Some(first_inst) = func.layout.first_inst_of(block) {
            self.set_location(CursorLocation::At(first_inst));
            while matches!(self.loc(), CursorLocation::At(..)) {
                self.remove_inst(func);
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

    fn inst(&self) -> Option<InstId> {
        if let CursorLocation::At(inst) = self.loc() {
            Some(inst)
        } else {
            None
        }
    }

    fn expect_inst(&self) -> InstId {
        self.inst()
            .expect("current cursor location doesn't point to inst")
    }

    fn block(&self, func: &Function) -> Option<BlockId> {
        match self.loc() {
            CursorLocation::At(inst) => Some(func.layout.inst_block(inst)),
            CursorLocation::BlockTop(block) | CursorLocation::BlockBottom(block) => Some(block),
            CursorLocation::NoWhere => None,
        }
    }

    fn expect_block(&self, func: &Function) -> BlockId {
        self.block(func).expect("cursor loc points to `NoWhere`")
    }

    fn insert_block(&mut self, func: &mut Function, block: BlockId) {
        if let Some(current) = self.block(func) {
            func.layout.insert_block_after(block, current)
        } else {
            panic!("cursor loc points `NoWhere`")
        }
    }

    fn insert_block_before(&mut self, func: &mut Function, block: BlockId) {
        if let Some(current) = self.block(func) {
            func.layout.insert_block_before(block, current)
        } else {
            panic!("cursor loc points `NoWhere`")
        }
    }

    fn append_block(&mut self, func: &mut Function, block: BlockId) {
        func.layout.append_block(block);
    }

    fn next_loc(&self, func: &Function) -> CursorLocation {
        match self.loc() {
            CursorLocation::At(inst) => func.layout.next_inst_of(inst).map_or_else(
                || CursorLocation::BlockBottom(func.layout.inst_block(inst)),
                CursorLocation::At,
            ),
            CursorLocation::BlockTop(block) => func
                .layout
                .first_inst_of(block)
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
            CursorLocation::At(inst) => func.layout.prev_inst_of(inst).map_or_else(
                || CursorLocation::BlockTop(func.layout.inst_block(inst)),
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
                .last_inst_of(block)
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

    fn next_block(&self, func: &Function) -> Option<BlockId> {
        let block = self.block(func)?;
        func.layout.next_block_of(block)
    }

    fn prev_block(&self, func: &Function) -> Option<BlockId> {
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
