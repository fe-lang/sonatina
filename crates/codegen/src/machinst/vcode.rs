use cranelift_entity::{
    entity_impl,
    packed_option::{PackedOption, ReservedValue},
    EntityList, EntityRef, ListPool, PrimaryMap, SecondaryMap, SparseMap, SparseMapValue,
};
use smallvec::SmallVec;
use sonatina_ir::{
    ir_writer::{FuncWriteCtx, FunctionSignature, InstStatement, IrWrite},
    module::FuncRef,
    BlockId, InstId, U256,
};
use std::{fmt, io};

// xxx offset reference graph?
//  fn call graph

#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash, PartialOrd, Ord)]
pub struct LabelId(pub u32);
entity_impl!(LabelId);

#[derive(Debug, Copy, Clone)]
pub enum Label {
    Insn(VCodeInst),
    Block(BlockId),
    Function(FuncRef),
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash, PartialOrd, Ord)]
pub struct VCodeInst(pub u32);
entity_impl!(VCodeInst);

pub struct VCode<Op> {
    pub insts: PrimaryMap<VCodeInst, Op>,
    pub inst_ir: SecondaryMap<VCodeInst, PackedOption<InstId>>,

    /// Immediate bytes for PUSH* ops
    pub inst_imm_bytes: SparseMap<VCodeInst, (VCodeInst, SmallVec<[u8; 8]>)>,

    pub labels: PrimaryMap<LabelId, Label>,
    /// Instructions that contain label offsets that will need to updated
    /// when the bytecode is emitted
    pub label_uses: SparseMap<VCodeInst, (VCodeInst, LabelId)>,

    pub blocks: SecondaryMap<BlockId, EntityList<VCodeInst>>,

    pub insts_pool: ListPool<VCodeInst>,
}

impl<Op> VCode<Op> {
    pub fn add_inst_to_block(
        &mut self,
        op: Op,
        source_insn: Option<InstId>,
        block: BlockId,
    ) -> VCodeInst {
        let inst = self.insts.push(op);
        self.inst_ir[inst] = source_insn.into();
        self.blocks[block].push(inst, &mut self.insts_pool);
        inst
    }

    pub fn block_insns(&self, block: BlockId) -> impl Iterator<Item = VCodeInst> + '_ {
        EntityIter {
            list: &self.blocks[block],
            pool: &self.insts_pool,
            next: 0,
        }
    }

    // pub fn emit(self, alloc: &sonatina_stackalloc::Output)
}

impl<Op> IrWrite<FuncWriteCtx<'_>> for VCode<Op>
where
    Op: fmt::Debug,
{
    fn write<W>(&self, w: &mut W, ctx: &FuncWriteCtx) -> std::io::Result<()>
    where
        W: io::Write,
    {
        write!(w, "// ")?;
        FunctionSignature.write(w, ctx)?;
        writeln!(w)?;
        ctx.module_ctx()
            .func_sig(ctx.func_ref, |sig| writeln!(w, "{}:", sig.name()))?;

        let mut cur_ir = None;
        for block in self.blocks.keys() {
            if self.block_insns(block).count() > 0 {
                writeln!(w, "  block{}:", block.0)?;
            }
            for (idx, insn) in self.block_insns(block).enumerate() {
                write!(w, "    {:?}", self.insts[insn])?;
                if let Some((_, bytes)) = self.inst_imm_bytes.get(insn) {
                    let mut be = [0; 32];
                    be[32 - bytes.len()..].copy_from_slice(bytes);
                    let imm = U256::from_big_endian(&be);
                    write!(w, " 0x{imm:x} ({imm})")?;
                } else if let Some((_, label)) = self.label_uses.get(insn) {
                    match self.labels[*label] {
                        Label::Block(BlockId(n)) => write!(w, " block{n}"),
                        Label::Insn(insn) => {
                            let pos = self
                                .block_insns(block)
                                .position(|i| i == insn)
                                .expect("Label::Insn must be in same block");
                            let offset: i32 = pos as i32 - idx as i32;
                            write!(w, " `pc + ({offset})`")
                        }
                        Label::Function(func) => write!(w, " {func:?}"),
                    }?;
                }

                if let Some(ir) = self.inst_ir[insn].expand() {
                    if cur_ir != Some(ir) {
                        cur_ir = Some(ir);
                        write!(w, "  // ")?;
                        InstStatement(ir).write(w, ctx)?;
                    }
                }
                writeln!(w)?;
            }
        }
        Ok(())
    }
}

impl<Op> Default for VCode<Op> {
    fn default() -> Self {
        Self {
            insts: Default::default(),
            inst_ir: Default::default(),
            inst_imm_bytes: SparseMap::new(), // no `Default` impl
            labels: PrimaryMap::default(),
            label_uses: SparseMap::new(),
            blocks: Default::default(),
            insts_pool: Default::default(),
        }
    }
}

impl<T> SparseMapValue<VCodeInst> for (VCodeInst, T) {
    fn key(&self) -> VCodeInst {
        self.0
    }
}

struct EntityIter<'a, T>
where
    T: EntityRef + ReservedValue,
{
    list: &'a EntityList<T>,
    pool: &'a ListPool<T>,
    next: usize,
}

impl<'a, T> Iterator for EntityIter<'a, T>
where
    T: EntityRef + ReservedValue,
{
    type Item = T;

    fn next(&mut self) -> Option<T> {
        let next = self.list.get(self.next, self.pool)?;
        self.next += 1;
        Some(next)
    }
}
