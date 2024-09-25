use std::fmt;

use macros::Inst;
use smallvec::SmallVec;

use crate::{
    ir_writer::{DisplayWithFunc, DisplayableWithFunc},
    module::FuncRef,
    BlockId, Function, Inst, Type, ValueId,
};

use super::InstDowncast;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(terminator)]
pub struct Jump {
    dest: BlockId,
}
impl DisplayWithFunc for Jump {
    fn fmt(&self, func: &Function, formatter: &mut fmt::Formatter) -> fmt::Result {
        let name = self.as_text();
        let block = DisplayableWithFunc(self.dest, func);

        write!(formatter, "{name} {block}")
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
impl DisplayWithFunc for Br {
    fn fmt(&self, func: &Function, formatter: &mut fmt::Formatter) -> fmt::Result {
        let name = self.as_text();
        let cond = DisplayableWithFunc(self.cond, func);
        let z_dest = DisplayableWithFunc(self.z_dest, func);
        let nz_dest = DisplayableWithFunc(self.nz_dest, func);

        write!(formatter, "{name} {cond} {z_dest} {nz_dest}")
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(terminator)]
pub struct BrTable {
    #[inst(value)]
    scrutinee: ValueId,

    default: Option<BlockId>,
    #[inst(value)]
    table: Vec<(ValueId, BlockId)>,
}
impl DisplayWithFunc for BrTable {
    fn fmt(&self, func: &Function, formatter: &mut fmt::Formatter) -> fmt::Result {
        let name = self.as_text();
        let scrutinee = DisplayableWithFunc(self.scrutinee, func);
        write!(formatter, "{name} {scrutinee}")?;
        if let Some(default) = self.default {
            let default = DisplayableWithFunc(default, func);
            write!(formatter, " {default}")?;
        } else {
            write!(formatter, " undef")?;
        };

        for (value, block) in &self.table {
            let value = DisplayableWithFunc(value, func);
            let block = DisplayableWithFunc(block, func);
            write!(formatter, " ({value} {block})")?;
        }

        Ok(())
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
impl DisplayWithFunc for Phi {
    fn fmt(&self, func: &Function, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "{}", self.as_text())?;

        for (value, block) in &self.args {
            let value = DisplayableWithFunc(value, func);
            let block = DisplayableWithFunc(block, func);
            write!(formatter, " ({value} {block})")?;
        }

        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
#[inst(terminator)]
pub struct Call {
    callee: FuncRef,

    #[inst(value)]
    args: SmallVec<[ValueId; 8]>,
    ret_ty: Type,
}
impl DisplayWithFunc for Call {
    fn fmt(&self, func: &Function, formatter: &mut fmt::Formatter) -> fmt::Result {
        let name = self.as_text();
        let callee = func.callees[&self.callee].name();
        write!(formatter, "{name} %{callee}")?;
        for value in &self.args {
            let value = DisplayableWithFunc(value, func);
            write!(formatter, " {value}")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
#[inst(terminator)]
pub struct Return {
    #[inst(value)]
    arg: Option<ValueId>,
}
impl DisplayWithFunc for Return {
    fn fmt(&self, func: &Function, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "{}", self.as_text())?;
        if let Some(arg) = self.arg {
            let arg = DisplayableWithFunc(arg, func);
            write!(formatter, " {arg}")?;
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
                if idx < brt.table.len() {
                    Some(brt.table[idx].1)
                } else {
                    brt.default
                }
            }
        }
    }
}
