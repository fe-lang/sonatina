use super::vcode::{Label, VCode, VCodeInst};
use crate::stackalloc::Allocator;
use smallvec::SmallVec;
use sonatina_ir::{module::ModuleCtx, BlockId, Function, Immediate, Inst, InstId, Type, ValueId};

pub trait LowerBackend {
    type MInst;

    fn lower(&self, ctx: &mut Lower<Self::MInst>, alloc: &mut dyn Allocator, inst: InstId);
    // -> Option<InstOutput> == SmallVec<[ValueRegs<Reg>; 2]>

    fn enter_function(
        &self,
        ctx: &mut Lower<Self::MInst>,
        alloc: &mut dyn Allocator,
        function: &Function,
    );
    fn enter_block(&self, ctx: &mut Lower<Self::MInst>, alloc: &mut dyn Allocator, block: BlockId);

    fn update_opcode_with_immediate_bytes(
        &self,
        opcode: &mut Self::MInst,
        bytes: &mut SmallVec<[u8; 8]>,
    );

    fn update_opcode_with_label(
        &self,
        opcode: &mut Self::MInst,
        label_offset: u32,
    ) -> SmallVec<[u8; 4]>;

    fn emit_opcode(&self, opcode: &Self::MInst, buf: &mut Vec<u8>);
    fn emit_immediate_bytes(&self, bytes: &[u8], buf: &mut Vec<u8>);
    fn emit_label(&self, address: u32, buf: &mut Vec<u8>);
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
}

impl<'a, Op: Default> Lower<'a, Op> {
    pub fn new(module: &'a ModuleCtx, function: &'a Function) -> Self {
        Lower {
            module,
            function,
            vcode: VCode::default(),
            cur_insn: None,
            cur_block: None,
        }
    }

    pub fn lower<B: LowerBackend<MInst = Op>>(
        mut self,
        backend: &B,
        alloc: &mut dyn Allocator,
    ) -> CodegenResult<VCode<Op>> {
        let function = self.function;
        let entry = function.layout.entry_block();
        for block in function.layout.iter_block() {
            self.cur_block = Some(block);
            self.cur_insn = None;
            backend.enter_block(&mut self, alloc, block);
            if entry == Some(block) {
                backend.enter_function(&mut self, alloc, function);
            }

            for insn in function.layout.iter_inst(block) {
                self.cur_insn = Some(insn);
                backend.lower(&mut self, alloc, insn);
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
        self.vcode.label_uses.insert((inst, label));
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

    pub fn insn_result(&self, inst: InstId) -> Option<ValueId> {
        self.function.dfg.inst_result(inst)
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
        self.function.layout.next_block_of(cur) == Some(block)
    }
}
