use macros::{Inst, inst_prop};
use smallvec::{SmallVec, smallvec};

use crate::{
    BlockId, HasInst, Inst, InstSetBase, ValueId,
    ir_writer::{FuncWriteCtx, IrWrite},
    module::FuncRef,
    visitor::{Visitable, VisitableMut, Visitor, VisitorMut},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(terminator)]
pub struct Jump {
    dest: BlockId,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(terminator)]
pub struct Br {
    cond: ValueId,
    nz_dest: BlockId,
    z_dest: BlockId,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(terminator)]
#[inst(arity(at_least(2)))]
pub struct BrTable {
    scrutinee: ValueId,

    default: Option<BlockId>,
    table: Vec<(ValueId, BlockId)>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(arity(at_least(1)))]
#[inst(kind(phi))]
pub struct Phi {
    args: Vec<(ValueId, BlockId)>,
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

// TODO: We need to perform analysis or modify function signature definition to
// know if
// * the function call has side effect
// * the function call is terminator
#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(super::SideEffect::Write))]
#[inst(arity(at_least(1)))]
pub struct Call {
    callee: FuncRef,

    args: SmallVec<[ValueId; 8]>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(super::SideEffect::Control))]
#[inst(terminator)]
#[inst(arity(at_least(0)))]
pub struct Return {
    args: ReturnArgs,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct ReturnArgs(SmallVec<[ValueId; 2]>);

impl ReturnArgs {
    pub fn as_slice(&self) -> &[ValueId] {
        self.0.as_slice()
    }

    pub fn first(&self) -> Option<&ValueId> {
        self.0.first()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = &ValueId> {
        self.0.iter()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }
}

impl From<SmallVec<[ValueId; 2]>> for ReturnArgs {
    fn from(args: SmallVec<[ValueId; 2]>) -> Self {
        Self(args)
    }
}

impl Visitable for ReturnArgs {
    fn accept(&self, visitor: &mut dyn Visitor) {
        self.0.accept(visitor);
    }
}

impl VisitableMut for ReturnArgs {
    fn accept_mut(&mut self, visitor: &mut dyn VisitorMut) {
        self.0.accept_mut(visitor);
    }
}

impl IrWrite<FuncWriteCtx<'_>> for ReturnArgs {
    fn write<W>(&self, w: &mut W, ctx: &FuncWriteCtx<'_>) -> std::io::Result<()>
    where
        W: std::io::Write,
    {
        match self.0.as_slice() {
            [] => Ok(()),
            [arg] => arg.write(w, ctx),
            args => {
                write!(w, "(")?;
                args.write_with_delim(w, ", ", ctx)?;
                write!(w, ")")
            }
        }
    }

    fn has_content(&self) -> bool {
        !self.0.is_empty()
    }
}

impl Return {
    pub fn new_unit(has_inst: &dyn HasInst<Self>) -> Self {
        Self::new(has_inst, ReturnArgs::default())
    }

    pub fn new_single(has_inst: &dyn HasInst<Self>, arg: ValueId) -> Self {
        Self::new(has_inst, ReturnArgs::from(smallvec![arg]))
    }

    pub fn returns_unit(&self) -> bool {
        self.args.is_empty()
    }

    pub fn returns_single(&self) -> bool {
        self.args.len() == 1
    }

    pub fn arg(&self) -> Option<&ValueId> {
        assert!(
            self.args.len() <= 1,
            "arg called on multi-value return instruction"
        );
        self.args.first()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(super::SideEffect::Control))]
#[inst(terminator)]
pub struct Unreachable {}

/// A trait for instructions that can be used as a call.
#[inst_prop]
pub trait CallInfo {
    fn callee(&self) -> FuncRef;

    type Members = (Call,);
}

impl CallInfo for Call {
    fn callee(&self) -> FuncRef {
        self.callee
    }
}

/// A trait for instructions that can be used as a jump or branching.
#[inst_prop]
pub trait BranchInfo {
    fn dests(&self) -> SmallVec<[BlockId; 2]>;
    fn num_dests(&self) -> usize;
    fn remove_dest(&self, isb: &dyn InstSetBase, dest: BlockId) -> Box<dyn Inst>;
    fn rewrite_dest(&self, isb: &dyn InstSetBase, from: BlockId, to: BlockId) -> Box<dyn Inst>;
    fn branch_kind(&self) -> BranchKind<'_>;

    type Members = (Jump, Br, BrTable);
}

impl BranchInfo for Jump {
    fn dests(&self) -> SmallVec<[BlockId; 2]> {
        smallvec![self.dest]
    }

    fn num_dests(&self) -> usize {
        1
    }

    fn remove_dest(&self, isb: &dyn InstSetBase, dest: BlockId) -> Box<dyn Inst> {
        if dest == self.dest {
            Box::new(Unreachable::new_unchecked(isb))
        } else {
            Box::new(*self)
        }
    }

    fn rewrite_dest(&self, _isb: &dyn InstSetBase, from: BlockId, to: BlockId) -> Box<dyn Inst> {
        let mut jump = *self;
        rewrite_if_match(&mut jump.dest, from, to);
        Box::new(jump)
    }

    fn branch_kind(&self) -> BranchKind<'_> {
        BranchKind::Jump(self)
    }
}

impl BranchInfo for Br {
    fn dests(&self) -> SmallVec<[BlockId; 2]> {
        smallvec![self.nz_dest, self.z_dest]
    }

    fn num_dests(&self) -> usize {
        2
    }

    fn remove_dest(&self, isb: &dyn InstSetBase, dest: BlockId) -> Box<dyn Inst> {
        let nz = self.nz_dest;
        let z = self.z_dest;

        if nz == dest && z == dest {
            return Box::new(Unreachable::new_unchecked(isb));
        }
        if nz == dest {
            return Box::new(Jump::new(isb.jump(), z));
        }
        if z == dest {
            return Box::new(Jump::new(isb.jump(), nz));
        }

        Box::new(self.clone())
    }

    fn rewrite_dest(&self, isb: &dyn InstSetBase, from: BlockId, to: BlockId) -> Box<dyn Inst> {
        let mut br = self.clone();
        rewrite_if_match(&mut br.nz_dest, from, to);
        rewrite_if_match(&mut br.z_dest, from, to);

        try_convert_branch_to_jump(isb, &br).unwrap_or_else(|| Box::new(br))
    }

    fn branch_kind(&self) -> BranchKind<'_> {
        BranchKind::Br(self)
    }
}

impl BranchInfo for BrTable {
    fn dests(&self) -> SmallVec<[BlockId; 2]> {
        let mut dests = if let Some(default) = self.default {
            smallvec![default]
        } else {
            smallvec![]
        };
        dests.extend(self.table.iter().map(|(_, block)| *block));

        dests
    }

    fn num_dests(&self) -> usize {
        let num = self.table.len();
        if self.default.is_some() { num + 1 } else { num }
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
        match dest_num {
            0 => Box::new(Unreachable::new_unchecked(isb)),
            1 => Box::new(Jump::new(isb.jump(), brt.dests()[0])),
            _ => Box::new(brt),
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

    fn branch_kind(&self) -> BranchKind<'_> {
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
fn try_convert_branch_to_jump(
    isb: &dyn InstSetBase,
    branch: &dyn BranchInfo,
) -> Option<Box<dyn Inst>> {
    let dests = branch.dests();
    let Some(&first_dest) = dests.first() else {
        return Some(Box::new(Unreachable::new_unchecked(isb)));
    };

    if dests.iter().all(|dest| *dest == first_dest) {
        Some(Box::new(Jump::new(isb.jump(), first_dest)))
    } else {
        None
    }
}

fn rewrite_if_match(block: &mut BlockId, from: BlockId, to: BlockId) {
    if *block == from {
        *block = to
    }
}
