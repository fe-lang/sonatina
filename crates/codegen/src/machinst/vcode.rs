use cranelift_entity::packed_option::PackedOption;
use cranelift_entity::{
    entity_impl, packed_option::ReservedValue, EntityList, EntityRef, ListPool, PrimaryMap,
    SecondaryMap,
};
use indexmap::IndexMap;
use smallvec::SmallVec;
use sonatina_ir::{module::FuncRef, Block, Function, Insn};
use std::collections::BTreeMap;
use std::fmt;

#[derive(Debug, Copy, Clone)]
pub enum Label {
    Insn(VCodeInst),
    Block(Block),
    Function(FuncRef),
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash, PartialOrd, Ord)]
pub struct VCodeInst(pub u32);
entity_impl!(VCodeInst);

#[derive(Default)]
pub struct VCode<Op> {
    pub insts: PrimaryMap<VCodeInst, Op>,
    pub inst_ir: SecondaryMap<VCodeInst, PackedOption<Insn>>,

    /// Immediate bytes for PUSH* ops
    pub inst_imm_bytes: BTreeMap<VCodeInst, SmallVec<[u8; 8]>>,

    /// Instructions that contain label offsets that will need to updated
    /// when the bytecode is emitted
    pub jump_fixups: IndexMap<VCodeInst, Label>,

    // Or PrimaryMap<VCodeBlock, ..>?
    blocks: SecondaryMap<Block, EntityList<VCodeInst>>,

    insts_pool: ListPool<VCodeInst>,
}

impl<Op> VCode<Op> {
    pub fn add_inst_to_block(
        &mut self,
        op: Op,
        source_insn: Option<Insn>,
        block: Block,
    ) -> VCodeInst {
        let inst = self.insts.push(op);
        self.inst_ir[inst] = source_insn.into();
        self.blocks[block].push(inst, &mut self.insts_pool);
        inst
    }

    pub fn block_insns(&self, block: Block) -> impl Iterator<Item = VCodeInst> + '_ {
        EntityIter {
            list: &self.blocks[block],
            pool: &self.insts_pool,
            next: 0,
        }
    }

    // pub fn emit(self, alloc: &sonatina_stackalloc::Output)
}

impl<Op> VCode<Op>
where
    Op: fmt::Debug,
{
    pub fn print(&self, mut w: impl std::io::Write, func: &Function) -> std::io::Result<()> {
        use sonatina_ir::ir_writer::{FuncWriter, IrWrite};
        let mut writer = FuncWriter::new(func);
        let mut cur_ir = None;

        write!(w, "// ")?;
        writer.write_signature(&mut w)?;
        writeln!(w)?;
        writeln!(w, "{}:", func.sig.name())?;

        for block in self.blocks.keys() {
            if self.block_insns(block).count() > 0 {
                writeln!(w, "  block{}:", block.0)?;
            }
            for (idx, insn) in self.block_insns(block).enumerate() {
                write!(w, "    {:?}", self.insts[insn])?;
                if let Some(bytes) = self.inst_imm_bytes.get(&insn) {
                    write!(w, " {bytes:?}")?;
                } else if let Some(label) = self.jump_fixups.get(&insn) {
                    match label {
                        Label::Block(Block(n)) => write!(w, " block{n}"),
                        Label::Insn(insn) => {
                            let pos = self
                                .block_insns(block)
                                .position(|i| i == *insn)
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
                        ir.write(&mut writer, &mut w)?;
                    }
                }
                writeln!(w)?;
            }
        }
        Ok(())
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
