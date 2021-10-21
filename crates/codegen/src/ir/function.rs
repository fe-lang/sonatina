use super::{Block, DataFlowGraph, Insn, InsnData, Layout, Type, Value};

#[derive(Debug, Clone)]
pub struct Function {
    /// Name of the function.
    pub name: String,

    /// Signature of the function.
    pub sig: Signature,
    pub arg_values: Vec<Value>,

    pub dfg: DataFlowGraph,
    pub layout: Layout,
}

impl Function {
    pub fn new(name: String, sig: Signature) -> Self {
        let mut dfg = DataFlowGraph::default();
        let arg_values = sig
            .args()
            .iter()
            .enumerate()
            .map(|(idx, arg_ty)| dfg.make_arg_value(arg_ty, idx))
            .collect();

        Self {
            name,
            sig,
            arg_values,
            dfg,
            layout: Layout::default(),
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct Signature {
    args: Vec<Type>,
    rets: Vec<Type>,
}

impl Signature {
    pub fn new(args: Vec<Type>, rets: Vec<Type>) -> Self {
        Self { args, rets }
    }

    pub fn append_arg(&mut self, arg: Type) {
        self.args.push(arg);
    }

    pub fn append_return(&mut self, ret: Type) {
        self.rets.push(ret);
    }

    pub fn args(&self) -> &[Type] {
        &self.args
    }

    pub fn returns(&self) -> &[Type] {
        &self.rets
    }
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
    pub fn new(func: &'a mut Function, loc: CursorLocation) -> Self {
        Self { func, loc }
    }

    pub fn at(&mut self, loc: CursorLocation) {
        self.loc = loc;
    }

    pub fn insert_insn(&mut self, data: InsnData) -> Insn {
        let new_insn = self.func.dfg.make_insn(data);
        match self.loc {
            CursorLocation::At(insn) => self.func.layout.insert_insn_after(new_insn, insn),
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

    pub fn make_result(&mut self, insn: Insn) -> Option<Value> {
        let value_data = self.func.dfg.make_result(insn)?;
        Some(self.func.dfg.make_value(value_data))
    }

    pub fn attach_result(&mut self, insn: Insn, value: Value) {
        self.func.dfg.attach_result(insn, value)
    }

    pub fn insert_block(&mut self) -> Block {
        let new_block = self.func.dfg.make_block();
        let block = self.block().expect("cursor loc points to `NoWhere`");
        self.func.layout.insert_block_before(new_block, block);
        new_block
    }

    pub fn append_block(&mut self) -> Block {
        let new_block = self.func.dfg.make_block();
        self.func.layout.append_block(new_block);
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
                CursorLocation::At,
            ),
            CursorLocation::BlockTop(block) => self
                .func
                .layout
                .first_insn_of(block)
                .map_or_else(|| CursorLocation::BlockBottom(block), CursorLocation::At),
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
                CursorLocation::At,
            ),
            CursorLocation::BlockTop(block) => self
                .func
                .layout
                .prev_block_of(block)
                .map_or(CursorLocation::NoWhere, |prev_block| {
                    CursorLocation::BlockBottom(prev_block)
                }),
            CursorLocation::BlockBottom(block) => self
                .func
                .layout
                .last_insn_of(block)
                .map_or_else(|| CursorLocation::BlockTop(block), CursorLocation::At),
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
