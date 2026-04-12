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
    /// Returns branch destinations in canonical outgoing-edge order, preserving duplicates.
    ///
    /// The edge-slot order is:
    /// - [`Jump`][]: `dest`
    /// - [`Br`][]: `nz_dest`, then `z_dest`
    /// - [`BrTable`][]: `default` if present, then keyed table entries in stored order
    fn dests(&self) -> SmallVec<[BlockId; 2]>;
    fn num_dests(&self) -> usize;
    fn remove_edges_to_block(&self, isb: &dyn InstSetBase, dest: BlockId) -> Box<dyn Inst>;
    fn rewrite_edges_to_block(
        &self,
        isb: &dyn InstSetBase,
        from: BlockId,
        to: BlockId,
    ) -> Box<dyn Inst>;
    fn remove_edge(&self, isb: &dyn InstSetBase, edge_idx: usize) -> Box<dyn Inst>;
    fn rewrite_edge_dest(
        &self,
        isb: &dyn InstSetBase,
        edge_idx: usize,
        to: BlockId,
    ) -> Box<dyn Inst>;
    fn retain_edges(&self, isb: &dyn InstSetBase, keep_mask: &[bool]) -> Box<dyn Inst>;
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

    fn remove_edges_to_block(&self, isb: &dyn InstSetBase, dest: BlockId) -> Box<dyn Inst> {
        if dest == self.dest {
            Box::new(Unreachable::new_unchecked(isb))
        } else {
            Box::new(*self)
        }
    }

    fn rewrite_edges_to_block(
        &self,
        _isb: &dyn InstSetBase,
        from: BlockId,
        to: BlockId,
    ) -> Box<dyn Inst> {
        let mut jump = *self;
        rewrite_if_match(&mut jump.dest, from, to);
        Box::new(jump)
    }

    fn remove_edge(&self, isb: &dyn InstSetBase, edge_idx: usize) -> Box<dyn Inst> {
        assert_eq!(edge_idx, 0, "jump edge index out of bounds: {edge_idx}");
        Box::new(Unreachable::new_unchecked(isb))
    }

    fn rewrite_edge_dest(
        &self,
        isb: &dyn InstSetBase,
        edge_idx: usize,
        to: BlockId,
    ) -> Box<dyn Inst> {
        assert_eq!(edge_idx, 0, "jump edge index out of bounds: {edge_idx}");
        Box::new(Jump::new(isb.jump(), to))
    }

    fn retain_edges(&self, isb: &dyn InstSetBase, keep_mask: &[bool]) -> Box<dyn Inst> {
        assert_eq!(
            keep_mask.len(),
            1,
            "jump keep mask has wrong length: expected 1, found {}",
            keep_mask.len()
        );
        if keep_mask[0] {
            Box::new(*self)
        } else {
            Box::new(Unreachable::new_unchecked(isb))
        }
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

    fn remove_edges_to_block(&self, isb: &dyn InstSetBase, dest: BlockId) -> Box<dyn Inst> {
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

    fn rewrite_edges_to_block(
        &self,
        isb: &dyn InstSetBase,
        from: BlockId,
        to: BlockId,
    ) -> Box<dyn Inst> {
        let mut br = self.clone();
        rewrite_if_match(&mut br.nz_dest, from, to);
        rewrite_if_match(&mut br.z_dest, from, to);

        try_convert_branch_to_jump(isb, &br).unwrap_or_else(|| Box::new(br))
    }

    fn remove_edge(&self, isb: &dyn InstSetBase, edge_idx: usize) -> Box<dyn Inst> {
        match edge_idx {
            0 => Box::new(Jump::new(isb.jump(), self.z_dest)),
            1 => Box::new(Jump::new(isb.jump(), self.nz_dest)),
            _ => panic!("branch edge index out of bounds: {edge_idx}"),
        }
    }

    fn rewrite_edge_dest(
        &self,
        isb: &dyn InstSetBase,
        edge_idx: usize,
        to: BlockId,
    ) -> Box<dyn Inst> {
        let mut br = self.clone();
        match edge_idx {
            0 => br.nz_dest = to,
            1 => br.z_dest = to,
            _ => panic!("branch edge index out of bounds: {edge_idx}"),
        }
        try_convert_branch_to_jump(isb, &br).unwrap_or_else(|| Box::new(br))
    }

    fn retain_edges(&self, isb: &dyn InstSetBase, keep_mask: &[bool]) -> Box<dyn Inst> {
        assert_eq!(
            keep_mask.len(),
            2,
            "branch keep mask has wrong length: expected 2, found {}",
            keep_mask.len()
        );
        match keep_mask {
            [false, false] => Box::new(Unreachable::new_unchecked(isb)),
            [true, false] => Box::new(Jump::new(isb.jump(), self.nz_dest)),
            [false, true] => Box::new(Jump::new(isb.jump(), self.z_dest)),
            [true, true] => {
                try_convert_branch_to_jump(isb, self).unwrap_or_else(|| Box::new(self.clone()))
            }
            _ => unreachable!("branch keep mask length already validated"),
        }
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

    fn remove_edges_to_block(&self, isb: &dyn InstSetBase, dest: BlockId) -> Box<dyn Inst> {
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

    fn rewrite_edges_to_block(
        &self,
        isb: &dyn InstSetBase,
        from: BlockId,
        to: BlockId,
    ) -> Box<dyn Inst> {
        let mut brt = self.clone();
        if let Some(default) = &mut brt.default {
            rewrite_if_match(default, from, to);
        }

        brt.table
            .iter_mut()
            .for_each(|(_, block)| rewrite_if_match(block, from, to));

        try_convert_branch_to_jump(isb, &brt).unwrap_or_else(|| Box::new(brt))
    }

    fn remove_edge(&self, isb: &dyn InstSetBase, edge_idx: usize) -> Box<dyn Inst> {
        let mut keep_mask = vec![true; self.num_dests()];
        let keep = keep_mask
            .get_mut(edge_idx)
            .unwrap_or_else(|| panic!("br_table edge index out of bounds: {edge_idx}"));
        *keep = false;
        self.retain_edges(isb, &keep_mask)
    }

    fn rewrite_edge_dest(
        &self,
        isb: &dyn InstSetBase,
        edge_idx: usize,
        to: BlockId,
    ) -> Box<dyn Inst> {
        let mut brt = self.clone();
        if let Some(default) = &mut brt.default
            && edge_idx == 0
        {
            *default = to;
            return try_convert_branch_to_jump(isb, &brt).unwrap_or_else(|| Box::new(brt));
        }

        let table_idx = edge_idx - usize::from(self.default.is_some());
        let (_, dest) = brt
            .table
            .get_mut(table_idx)
            .unwrap_or_else(|| panic!("br_table edge index out of bounds: {edge_idx}"));
        *dest = to;
        try_convert_branch_to_jump(isb, &brt).unwrap_or_else(|| Box::new(brt))
    }

    fn retain_edges(&self, isb: &dyn InstSetBase, keep_mask: &[bool]) -> Box<dyn Inst> {
        assert_eq!(
            keep_mask.len(),
            self.num_dests(),
            "br_table keep mask has wrong length: expected {}, found {}",
            self.num_dests(),
            keep_mask.len()
        );

        let mut default = None;
        let table_offset = usize::from(self.default.is_some());
        if let Some(default_dest) = self.default
            && keep_mask[0]
        {
            default = Some(default_dest);
        }

        let table = self
            .table
            .iter()
            .copied()
            .enumerate()
            .filter_map(|(idx, entry)| keep_mask[table_offset + idx].then_some(entry))
            .collect();
        let mut brt = self.clone();
        *brt.default_mut() = default;
        *brt.table_mut() = table;
        match brt.num_dests() {
            0 => Box::new(Unreachable::new_unchecked(isb)),
            1 => Box::new(Jump::new(isb.jump(), brt.dests()[0])),
            _ => try_convert_branch_to_jump(isb, &brt).unwrap_or_else(|| Box::new(brt)),
        }
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

#[cfg(test)]
mod tests {
    use crate::{
        DataFlowGraph, Immediate, builder::test_util::test_isa, inst::downcast, isa::Isa,
        module::ModuleCtx,
    };

    use super::{BrTable, BranchInfo, Jump};

    #[test]
    fn br_table_remove_edge_preserves_other_duplicate_dest() {
        let isa = test_isa();
        let mut dfg = DataFlowGraph::new(ModuleCtx::new(&isa));
        let is = isa.inst_set();

        let scrutinee = dfg.make_imm_value(Immediate::I8(0));
        let case0 = dfg.make_imm_value(Immediate::I8(0));
        let case1 = dfg.make_imm_value(Immediate::I8(1));
        let case2 = dfg.make_imm_value(Immediate::I8(2));
        let _b0 = dfg.make_block();
        let b1 = dfg.make_block();
        let b2 = dfg.make_block();

        let br_table = BrTable::new(
            is,
            scrutinee,
            None,
            vec![(case0, b1), (case1, b2), (case2, b1)],
        );
        let rewritten = br_table.remove_edge(is, 0);
        let rewritten = downcast::<&BrTable>(is, rewritten.as_ref()).unwrap();

        assert_eq!(rewritten.table(), &[(case1, b2), (case2, b1)]);
    }

    #[test]
    fn br_table_rewrite_edge_dest_retargets_single_slot() {
        let isa = test_isa();
        let mut dfg = DataFlowGraph::new(ModuleCtx::new(&isa));
        let is = isa.inst_set();

        let scrutinee = dfg.make_imm_value(Immediate::I8(0));
        let case0 = dfg.make_imm_value(Immediate::I8(0));
        let case1 = dfg.make_imm_value(Immediate::I8(1));
        let case2 = dfg.make_imm_value(Immediate::I8(2));
        let b0 = dfg.make_block();
        let b1 = dfg.make_block();
        let b2 = dfg.make_block();

        let br_table = BrTable::new(
            is,
            scrutinee,
            Some(b0),
            vec![(case0, b1), (case1, b2), (case2, b1)],
        );
        let rewritten = br_table.rewrite_edge_dest(is, 3, b2);
        let rewritten = downcast::<&BrTable>(is, rewritten.as_ref()).unwrap();

        assert_eq!(rewritten.default(), &Some(b0));
        assert_eq!(rewritten.table(), &[(case0, b1), (case1, b2), (case2, b2)]);
    }

    #[test]
    fn br_table_retain_edges_canonicalizes_to_jump() {
        let isa = test_isa();
        let mut dfg = DataFlowGraph::new(ModuleCtx::new(&isa));
        let is = isa.inst_set();

        let scrutinee = dfg.make_imm_value(Immediate::I8(0));
        let case0 = dfg.make_imm_value(Immediate::I8(0));
        let case1 = dfg.make_imm_value(Immediate::I8(1));
        let b0 = dfg.make_block();
        let b1 = dfg.make_block();

        let br_table = BrTable::new(is, scrutinee, Some(b0), vec![(case0, b1), (case1, b0)]);
        let retained = br_table.retain_edges(is, &[true, false, true]);
        let jump = downcast::<&Jump>(is, retained.as_ref()).unwrap();

        assert_eq!(*jump.dest(), b0);
    }
}
