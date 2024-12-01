use macros::{inst_prop, Inst};
use smallvec::SmallVec;

use crate::{module::FuncRef, BlockId, Inst, InstSetBase, ValueId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(terminator)]
pub struct Jump {
    dest: BlockId,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(terminator)]
pub struct Br {
    #[inst(value)]
    cond: ValueId,
    nz_dest: BlockId,
    z_dest: BlockId,
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

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
pub struct Phi {
    #[inst(value)]
    args: Vec<(ValueId, BlockId)>,
}

impl Phi {
    pub fn iter_args(&self) -> impl Iterator<Item = &(ValueId, BlockId)> {
        self.args.iter()
    }

    pub fn append_phi_arg(&mut self, value: ValueId, block: BlockId) {
        self.args.push((value, block))
    }

    /// Remove phi argument from the `block`.
    pub fn remove_phi_arg(&mut self, block: BlockId) -> Option<ValueId> {
        let pos = self.args.iter().position(|(_, b)| *b == block)?;
        Some(self.args.remove(pos).0)
    }

    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(BlockId) -> bool,
    {
        self.args.retain(|(_, block)| f(*block))
    }
}

// TODO: We need to perform analysis or modify function signature definition to
// know if
// * the function call has side effect
// * the function call is terminator
#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(super::SideEffect::Write))]
pub struct Call {
    callee: FuncRef,

    #[inst(value)]
    args: SmallVec<[ValueId; 8]>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(super::SideEffect::Write))]
#[inst(terminator)]
pub struct Return {
    #[inst(value)]
    arg: Option<ValueId>,
}

#[inst_prop]
pub trait Branch {
    fn dests(&self) -> Vec<BlockId>;
    fn num_dests(&self) -> usize;
    fn remove_dest(&self, isb: &dyn InstSetBase, dest: BlockId) -> Box<dyn Inst>;
    fn rewrite_dest(&self, isb: &dyn InstSetBase, from: BlockId, to: BlockId) -> Box<dyn Inst>;
    fn branch_kind(&self) -> BranchKind;

    type Members = (Jump, Br, BrTable);
}

impl Branch for Jump {
    fn dests(&self) -> Vec<BlockId> {
        vec![self.dest]
    }

    fn num_dests(&self) -> usize {
        1
    }

    fn remove_dest(&self, _isb: &dyn InstSetBase, dest: BlockId) -> Box<dyn Inst> {
        if dest == self.dest {
            panic!("can't remove destination from `Jump` inst")
        }
        Box::new(*self)
    }

    fn rewrite_dest(&self, _isb: &dyn InstSetBase, from: BlockId, to: BlockId) -> Box<dyn Inst> {
        let mut jump = *self;
        rewrite_if_match(&mut jump.dest, from, to);
        Box::new(jump)
    }

    fn branch_kind(&self) -> BranchKind {
        BranchKind::Jump(self)
    }
}

impl Branch for Br {
    fn dests(&self) -> Vec<BlockId> {
        vec![self.nz_dest, self.z_dest]
    }

    fn num_dests(&self) -> usize {
        2
    }

    fn remove_dest(&self, isb: &dyn InstSetBase, dest: BlockId) -> Box<dyn Inst> {
        let remain = if self.z_dest == dest {
            self.nz_dest
        } else if self.nz_dest == dest {
            self.z_dest
        } else {
            return Box::new(self.clone());
        };

        let jump = Jump::new(isb.jump(), remain);
        Box::new(jump)
    }

    fn rewrite_dest(&self, isb: &dyn InstSetBase, from: BlockId, to: BlockId) -> Box<dyn Inst> {
        let mut br = self.clone();
        rewrite_if_match(&mut br.nz_dest, from, to);
        rewrite_if_match(&mut br.z_dest, from, to);

        try_convert_branch_to_jump(isb, &br).unwrap_or_else(|| Box::new(br))
    }

    fn branch_kind(&self) -> BranchKind {
        BranchKind::Br(self)
    }
}

impl Branch for BrTable {
    fn dests(&self) -> Vec<BlockId> {
        let mut dests = if let Some(default) = self.default {
            vec![default]
        } else {
            vec![]
        };
        dests.extend(self.table.iter().map(|(_, block)| *block));

        dests
    }

    fn num_dests(&self) -> usize {
        let num = self.table.len();
        if self.default.is_some() {
            num + 1
        } else {
            num
        }
    }

    fn remove_dest(&self, isb: &dyn InstSetBase, dest: BlockId) -> Box<dyn Inst> {
        let mut brt = self.clone();

        if Some(dest) == self.default {
            *brt.default_mut() = None;
        }

        let keep = brt
            .table()
            .iter()
            .copied()
            .filter(|(_, b)| *b != dest)
            .collect();
        brt.table = keep;

        let dest_num = brt.dests().len();
        if dest_num == 1 {
            let jump = Jump::new(isb.jump(), brt.dests()[0]);
            Box::new(jump)
        } else {
            Box::new(brt)
        }
    }

    fn rewrite_dest(&self, isb: &dyn InstSetBase, from: BlockId, to: BlockId) -> Box<dyn Inst> {
        let mut brt = self.clone();
        if let Some(default) = &mut brt.default {
            rewrite_if_match(default, from, to);
        }

        brt.table
            .iter_mut()
            .for_each(|(_, block)| rewrite_if_match(block, from, to));

        try_convert_branch_to_jump(isb, &brt).unwrap_or_else(|| Box::new(brt))
    }

    fn branch_kind(&self) -> BranchKind {
        BranchKind::BrTable(self)
    }
}

pub enum BranchKind<'i> {
    Jump(&'i Jump),
    Br(&'i Br),
    BrTable(&'i BrTable),
}

/// Attempts to convert a branch instruction into a jump instruction.
///
/// This function checks if all the destinations of the branch instruction
/// are the same. If so, it converts the branch into a single jump
/// instruction targeting that destination. Otherwise, it returns `None`.
fn try_convert_branch_to_jump(isb: &dyn InstSetBase, branch: &dyn Branch) -> Option<Box<dyn Inst>> {
    let first_dest = branch.dests()[0];
    let is_dest_unique = branch
        .dests()
        .iter()
        .skip(1)
        .all(|dest| *dest == first_dest);
    if is_dest_unique {
        let jump = Jump::new(isb.jump(), first_dest);
        Some(Box::new(jump))
    } else {
        None
    }
}

fn rewrite_if_match(block: &mut BlockId, from: BlockId, to: BlockId) {
    if *block == from {
        *block = to
    }
}
