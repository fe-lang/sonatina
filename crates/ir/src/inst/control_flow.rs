use std::fmt;

use macros::{inst_prop, Inst};
use smallvec::SmallVec;

use crate::{
    ir_writer::{DisplayWithFunc, DisplayableWithFunc},
    module::FuncRef,
    BlockId, Function, Inst, Type, ValueId,
};

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
    nz_dest: BlockId,
    z_dest: BlockId,
}
impl DisplayWithFunc for Br {
    fn fmt(&self, func: &Function, formatter: &mut fmt::Formatter) -> fmt::Result {
        let name = self.as_text();
        let cond = DisplayableWithFunc(self.cond, func);
        let nz_dest = DisplayableWithFunc(self.nz_dest, func);
        let z_dest = DisplayableWithFunc(self.z_dest, func);

        write!(formatter, "{name} {cond} {nz_dest} {z_dest}")
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

#[inst_prop(Subset = "BranchInfo")]
pub trait Branch {
    fn dests(&self) -> Vec<BlockId>;
    fn num_dests(&self) -> usize;

    type Members = (Jump, Br, BrTable);
}

impl Branch for Jump {
    fn dests(&self) -> Vec<BlockId> {
        vec![self.dest]
    }

    fn num_dests(&self) -> usize {
        1
    }
}

impl Branch for Br {
    fn dests(&self) -> Vec<BlockId> {
        vec![self.nz_dest, self.z_dest]
    }

    fn num_dests(&self) -> usize {
        2
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
}

#[inst_prop(Subset = "BranchInfoMut")]
pub trait BranchMut {
    fn rewrite_branch_dest(&mut self, from: BlockId, to: BlockId);
    type Members = (Jump, Br, BrTable);
}

impl BranchMut for Jump {
    fn rewrite_branch_dest(&mut self, from: BlockId, to: BlockId) {
        rewrite_if_match(&mut self.dest, from, to)
    }
}

impl BranchMut for Br {
    fn rewrite_branch_dest(&mut self, from: BlockId, to: BlockId) {
        rewrite_if_match(&mut self.nz_dest, from, to);
        rewrite_if_match(&mut self.z_dest, from, to);
    }
}

impl BranchMut for BrTable {
    fn rewrite_branch_dest(&mut self, from: BlockId, to: BlockId) {
        if let Some(default) = &mut self.default {
            rewrite_if_match(default, from, to);
        }

        self.table
            .iter_mut()
            .for_each(|(_, block)| rewrite_if_match(block, from, to));
    }
}

fn rewrite_if_match(block: &mut BlockId, from: BlockId, to: BlockId) {
    if *block == from {
        *block = to
    }
}
