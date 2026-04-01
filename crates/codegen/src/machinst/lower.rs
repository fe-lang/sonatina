use super::vcode::{Label, SectionCodeUnitId, SymFixup, VCode, VCodeFixup, VCodeInst};
use crate::stackalloc::Allocator;
use rustc_hash::FxHashMap;
use sonatina_ir::{
    BlockId, Function, Immediate, Inst, InstId, Type, Value, ValueId,
    module::ModuleCtx,
    object::{EmbedSymbol, ObjectName, SectionName},
};

pub struct LoweredFunction<Op> {
    pub vcode: VCode<Op>,
    pub block_order: Vec<BlockId>,
}

pub struct SectionCodeUnit<Op> {
    pub id: SectionCodeUnitId,
    pub name: String,
    pub vcode: VCode<Op>,
    pub block_order: Vec<BlockId>,
}

pub struct SectionLoweringCtx<'a> {
    pub object: &'a ObjectName,
    pub section: &'a SectionName,
    pub embed_symbols: &'a [EmbedSymbol],
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FixupUpdate {
    Unchanged,
    ContentChanged,
    LayoutChanged,
}

#[derive(Debug)]
pub struct CodegenError {}
pub type CodegenResult<T> = Result<T, CodegenError>;

pub struct Lower<'a, Op> {
    pub module: &'a ModuleCtx,
    function: &'a Function,
    vcode: VCode<Op>,

    cur_insn: Option<InstId>,
    cur_block: Option<BlockId>,

    // Optional mapping from block -> next block in the final emission layout.
    //
    // When present, `is_next_block` uses this instead of the IR block layout, so
    // fallthrough optimizations match the actual assembled `block_order`.
    next_block_in_layout: Option<FxHashMap<BlockId, BlockId>>,
}

impl<'a, Op: Default> Lower<'a, Op> {
    pub fn new(module: &'a ModuleCtx, function: &'a Function, block_order: &'a [BlockId]) -> Self {
        let mut next_block_in_layout = FxHashMap::default();
        for window in block_order.windows(2) {
            next_block_in_layout.insert(window[0], window[1]);
        }

        Lower {
            module,
            function,
            vcode: VCode::default(),
            cur_insn: None,
            cur_block: None,
            next_block_in_layout: Some(next_block_in_layout),
        }
    }

    pub fn lower(
        mut self,
        alloc: &mut dyn Allocator,
        mut enter_block: impl FnMut(&mut Self, &mut dyn Allocator, BlockId),
        mut enter_function: impl FnMut(&mut Self, &mut dyn Allocator, &Function),
        mut lower_insn: impl FnMut(&mut Self, &mut dyn Allocator, InstId),
    ) -> CodegenResult<VCode<Op>> {
        let function = self.function;
        let entry = function.layout.entry_block();
        for block in function.layout.iter_block() {
            self.cur_block = Some(block);
            self.cur_insn = None;
            enter_block(&mut self, alloc, block);
            if entry == Some(block) {
                enter_function(&mut self, alloc, function);
            }

            for insn in function.layout.iter_inst(block) {
                self.cur_insn = Some(insn);
                lower_insn(&mut self, alloc, insn);
            }
        }

        Ok(self.vcode)
    }

    pub fn push(&mut self, op: Op) -> VCodeInst {
        self.vcode
            .add_inst_to_block(op, self.cur_insn, self.cur_block.unwrap())
    }

    pub fn push_with_imm(&mut self, op: Op, bytes: &[u8]) {
        let i = self.push(op);
        self.add_immediate(i, bytes);
    }

    pub fn push_jump_target(&mut self, op: Op, dest: Label) {
        let op = self.push(op);
        self.add_label_reference(op, dest);
    }

    pub fn next_insn(&self) -> VCodeInst {
        self.vcode.insts.next_key()
    }

    pub fn add_immediate(&mut self, inst: VCodeInst, bytes: &[u8]) {
        self.vcode.inst_imm_bytes.insert((inst, bytes.into()));
    }

    pub fn add_label_reference(&mut self, inst: VCodeInst, dest: Label) {
        let label = self.vcode.labels.push(dest);
        self.vcode.fixups.insert((inst, VCodeFixup::Label(label)));
    }

    pub fn add_sym_fixup(&mut self, inst: VCodeInst, fixup: SymFixup) {
        self.vcode.fixups.insert((inst, VCodeFixup::Sym(fixup)));
    }

    pub fn push_sym_fixup(&mut self, op: Op, fixup: SymFixup) -> VCodeInst {
        let inst = self.push(op);
        self.add_immediate(inst, &[]);
        self.add_sym_fixup(inst, fixup);
        inst
    }

    pub fn insn_data(&self, inst: InstId) -> &dyn Inst {
        self.function.dfg.inst(inst)
    }

    pub fn value_imm(&self, value: ValueId) -> Option<Immediate> {
        self.function.dfg.value_imm(value)
    }

    pub fn value_ty(&self, value: ValueId) -> Type {
        self.function.dfg.value_ty(value)
    }

    pub fn insn_results(&self, inst: InstId) -> &[ValueId] {
        self.function.dfg.inst_results(inst)
    }

    pub fn insn_result_at(&self, inst: InstId, idx: usize) -> Option<ValueId> {
        self.function.dfg.inst_result_at(inst, idx)
    }

    pub fn insn_result(&self, inst: InstId) -> Option<ValueId> {
        self.function.dfg.single_inst_result(inst)
    }

    pub fn value_def_inst(&self, value: ValueId) -> Option<InstId> {
        self.value_def_inst_result(value).map(|(inst, _)| inst)
    }

    pub fn value_def_inst_result(&self, value: ValueId) -> Option<(InstId, usize)> {
        let Value::Inst {
            inst, result_idx, ..
        } = self.function.dfg.value(value)
        else {
            return None;
        };
        Some((*inst, usize::from(*result_idx)))
    }

    pub fn insn_block(&self, inst: InstId) -> BlockId {
        self.function.layout.inst_block(inst)
    }

    pub fn is_entry(&self, block: BlockId) -> bool {
        self.function.layout.entry_block() == Some(block)
    }

    /// Check if the given `BlockId` is next in the layout.
    /// Used for avoiding unnecessary `jump` operations.
    pub fn is_next_block(&self, block: BlockId) -> bool {
        let Some(cur) = self.cur_block else {
            return false;
        };

        if let Some(next_block_in_layout) = &self.next_block_in_layout {
            return next_block_in_layout.get(&cur).copied() == Some(block);
        }

        self.function.layout.next_block_of(cur) == Some(block)
    }
}
