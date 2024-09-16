use macros::Inst;
use smallvec::SmallVec;

use crate::{module::FuncRef, Block, Type, ValueId};

use super::InstDowncast;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(terminator)]
pub struct Jump {
    dest: Block,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(terminator)]
pub struct Br {
    #[inst(value)]
    cond: ValueId,
    z_dest: Block,
    nz_dest: Block,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(terminator)]
pub struct BrTable {
    #[inst(value)]
    scrutinee: ValueId,
    #[inst(value)]
    table: Vec<(ValueId, Block)>,

    default: Option<Block>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
pub struct Phi {
    #[inst(value)]
    values: Vec<(ValueId, Block)>,
    ty: Type,
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

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
#[inst(terminator)]
pub struct Return {
    #[inst(value)]
    arg: Option<ValueId>,
}

#[derive(Clone, Copy)]
pub enum BranchInfo<'i> {
    Jump(&'i Jump),
    Br(&'i Br),
    BrTable(&'i BrTable),
}

impl<'i> BranchInfo<'i> {
    pub fn iter_dests(self) -> impl Iterator<Item = Block> + 'i {
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
    type Item = Block;

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
