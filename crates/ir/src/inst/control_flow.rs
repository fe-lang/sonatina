use std::fmt;

use macros::{inst_prop, Inst};
use smallvec::SmallVec;

use super::InstDowncastMut;
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

    type Members = (Jump, Br, BrTable);
}

impl Branch for Jump {
    fn dests(&self) -> Vec<BlockId> {
        todo!()
    }
}

impl Branch for Br {
    fn dests(&self) -> Vec<BlockId> {
        todo!()
    }
}

impl Branch for BrTable {
    fn dests(&self) -> Vec<BlockId> {
        todo!()
    }
}

pub enum BranchInfoMut<'i> {
    Jump(&'i mut Jump),
    Br(&'i mut Br),
    BrTable(&'i mut BrTable),
}

impl<'i> BranchInfoMut<'i> {
    pub fn rewrite_branch_dest(&mut self, from: BlockId, to: BlockId) {
        let repalce_if_match = |block: &mut BlockId| {
            if *block == from {
                *block = to
            }
        };

        match self {
            Self::Jump(j) => repalce_if_match(&mut j.dest),

            Self::Br(br) => {
                repalce_if_match(&mut br.z_dest);
                repalce_if_match(&mut br.nz_dest);
            }

            Self::BrTable(brt) => {
                if let Some(default) = &mut brt.default {
                    repalce_if_match(default);
                }

                brt.table
                    .iter_mut()
                    .for_each(|(_, block)| repalce_if_match(block));
            }
        }
    }

    pub fn num_dests(&self) -> usize {
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

impl<'i> InstDowncastMut for BranchInfoMut<'i> {
    fn downcast_mut(isb: &dyn crate::InstSetBase, inst: &mut dyn super::Inst) -> Option<Self> {
        InstDowncastMut::map_mut(isb, inst, BranchInfoMut::Jump)
            .or_else(|| InstDowncastMut::map_mut(isb, inst, BranchInfoMut::Br))
            .or_else(|| InstDowncastMut::map_mut(isb, inst, BranchInfoMut::BrTable))
    }
}
