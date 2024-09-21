use std::io;

use macros::Inst;
use smallvec::SmallVec;

use crate::{
    ir_writer::{FuncWriter, IrWrite},
    module::FuncRef,
    BlockId, Inst, Type, ValueId,
};

use super::InstDowncast;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(terminator)]
pub struct Jump {
    dest: BlockId,
}
impl IrWrite for Jump {
    fn write(&self, writer: &mut FuncWriter, w: &mut dyn io::Write) -> io::Result<()> {
        write!(w, "{}", self.as_text())?;
        writer.space(&mut *w)?;
        self.dest.write(writer, w)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(terminator)]
pub struct Br {
    #[inst(value)]
    cond: ValueId,
    z_dest: BlockId,
    nz_dest: BlockId,
}
impl IrWrite for Br {
    fn write(&self, writer: &mut FuncWriter, w: &mut dyn io::Write) -> io::Result<()> {
        write!(w, "{}", self.as_text())?;
        writer.space(&mut *w)?;

        self.cond.write(writer, w)?;
        writer.space(&mut *w)?;

        self.z_dest.write(writer, w)?;
        writer.space(&mut *w)?;

        self.nz_dest.write(writer, w)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(terminator)]
pub struct BrTable {
    #[inst(value)]
    scrutinee: ValueId,
    #[inst(value)]
    table: Vec<(ValueId, BlockId)>,

    default: Option<BlockId>,
}
impl IrWrite for BrTable {
    fn write(&self, writer: &mut FuncWriter, w: &mut dyn io::Write) -> io::Result<()> {
        write!(w, "{}", self.as_text())?;
        writer.space(&mut *w)?;

        self.scrutinee.write(writer, w)?;
        writer.space(&mut *w)?;

        if let Some(default) = self.default {
            default.write(writer, &mut *w)?;
        } else {
            write!(w, "undef")?;
        }
        writer.space(&mut *w)?;

        let mut table_args = vec![];
        for (value, block) in &self.table {
            let mut arg = vec![b'('];
            value.write(writer, &mut arg)?;
            writer.space(&mut arg)?;
            block.write(writer, &mut arg)?;
            arg.push(b')');
            table_args.push(arg);
        }

        writer.write_iter_with_delim(table_args.iter(), " ", &mut *w)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
pub struct Phi {
    #[inst(value)]
    args: Vec<(ValueId, BlockId)>,
    ty: Type,
}
impl Phi {
    pub fn append_phi_arg(&mut self, value: ValueId, block: BlockId) {
        self.args.push((value, block))
    }
}
impl IrWrite for Phi {
    fn write(&self, writer: &mut FuncWriter, w: &mut dyn io::Write) -> io::Result<()> {
        write!(w, "{}", self.as_text())?;
        writer.space(&mut *w)?;

        let mut args = vec![];
        for (value, block) in &self.args {
            let mut arg = vec![b'('];
            value.write(writer, &mut arg)?;
            writer.space(&mut arg)?;
            block.write(writer, &mut arg)?;
            arg.push(b')');
            args.push(arg);
        }

        writer.write_iter_with_delim(args.iter(), " ", &mut *w)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
#[inst(terminator)]
pub struct Call {
    #[inst(value)]
    args: SmallVec<[ValueId; 8]>,
    callee: FuncRef,
    ret_ty: Type,
}
impl IrWrite for Call {
    fn write(&self, writer: &mut FuncWriter, w: &mut dyn io::Write) -> io::Result<()> {
        write!(w, "{}", self.as_text())?;
        writer.space(&mut *w)?;

        write!(w, "%{}", writer.func.callees[&self.callee].name())?;

        writer.space(&mut *w)?;
        writer.write_inst_values(self, &mut *w)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
#[inst(terminator)]
pub struct Return {
    #[inst(value)]
    arg: Option<ValueId>,
}
impl IrWrite for Return {
    fn write(&self, writer: &mut FuncWriter, w: &mut dyn io::Write) -> io::Result<()> {
        write!(w, "{}", self.as_text())?;
        if let Some(arg) = self.arg {
            writer.space(&mut *w)?;
            arg.write(writer, &mut *w)?;
        }

        Ok(())
    }
}

#[derive(Clone, Copy)]
pub enum BranchInfo<'i> {
    Jump(&'i Jump),
    Br(&'i Br),
    BrTable(&'i BrTable),
}

impl<'i> BranchInfo<'i> {
    pub fn iter_dests(self) -> impl Iterator<Item = BlockId> + 'i {
        BranchDestIter {
            branch_info: self,
            idx: 0,
        }
    }

    pub fn num_dests(self) -> usize {
        match self {
            Self::Jump(_) => 1,
            Self::Br(_) => 2,
            Self::BrTable(brt) => {
                let ent_len = brt.table.len();
                if brt.default.is_some() {
                    ent_len + 1
                } else {
                    ent_len
                }
            }
        }
    }
}

impl<'i> InstDowncast for BranchInfo<'i> {
    fn downcast(isb: &dyn crate::InstSetBase, inst: &dyn super::Inst) -> Option<Self> {
        InstDowncast::map(isb, inst, BranchInfo::Jump)
            .or_else(|| InstDowncast::map(isb, inst, BranchInfo::Br))
            .or_else(|| InstDowncast::map(isb, inst, BranchInfo::BrTable))
    }
}

#[derive(Clone, Copy)]
pub struct BranchDestIter<'i> {
    branch_info: BranchInfo<'i>,
    idx: usize,
}

impl<'i> Iterator for BranchDestIter<'i> {
    type Item = BlockId;

    fn next(&mut self) -> Option<Self::Item> {
        let idx = self.idx;
        if idx >= self.branch_info.num_dests() {
            return None;
        }
        self.idx += 1;

        match self.branch_info {
            BranchInfo::Jump(j) => Some(j.dest),

            BranchInfo::Br(br) => {
                let dest = if idx == 0 { br.z_dest } else { br.nz_dest };
                Some(dest)
            }

            BranchInfo::BrTable(brt) => {
                if brt.table.len() < idx {
                    Some(brt.table[idx].1)
                } else {
                    brt.default
                }
            }
        }
    }
}
