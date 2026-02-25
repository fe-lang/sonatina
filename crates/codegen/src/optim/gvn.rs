//! This module contains a solver for complete Global Value Numbering.
//!
//! The algorithm here is based on Karthik Gargi.: A sparse algorithm for predicated global value numbering:
//! PLDI 2002 Pages 45–56: <https://dl.acm.org/doi/10.1145/512529.512536>.
//!
//! Also, to accomplish complete GVN, we use the `ValuePhi` concept which is described in
//! Rekha R. Pai.: Detection of Redundant Expressions: A Complete and Polynomial-Time Algorithm in SSA:
//! APLAS 2015 pp49-65: <https://link.springer.com/chapter/10.1007/978-3-319-26529-2_4>

use std::collections::BTreeSet;

use cranelift_entity::{PrimaryMap, SecondaryMap, entity_impl, packed_option::PackedOption};
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    BlockId, ControlFlowGraph, DataFlowGraph, Function, Immediate, InstId, Type, Value, ValueId,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{
        BinaryInstKind, CastInstKind, InstClassKind, InstKeyExt, OwnedInstKey, UnaryInstKind,
        control_flow::{BranchKind, Jump, Unreachable},
    },
};

use crate::{
    domtree::{DomTree, DominatorTreeTraversable},
    optim::simplify_expr::{
        SimplifyExprResult, simplify_binary_with_known_imm, simplify_cast,
        simplify_unary_with_same_inner,
    },
};

///  An initial class that assigned to all values.
///  If a value still has the initial class after value numbering, then the insn that defines the value is
///  unreachable.
const INITIAL_CLASS: Class = Class(0);

/// The rank reserved for immediates.
const IMMEDIATE_RANK: u32 = 0;

fn inst_to_gvn_key(func: &Function, inst_id: InstId) -> OwnedInstKey {
    let inst = func.dfg.inst(inst_id);
    let result_ty = func
        .dfg
        .inst_result(inst_id)
        .map(|result| func.dfg.value_ty(result));
    inst.owned_key(result_ty)
}

/// A GVN solver.
#[derive(Debug)]
pub struct GvnSolver {
    /// Store classes.
    classes: PrimaryMap<Class, ClassData>,

    /// Maps [`Value`] to [`GvnValue`].
    values: SecondaryMap<ValueId, GvnValue>,

    /// Maps [`GvnInsn`] to [`Class`].
    insn_table: FxHashMap<GvnInsn, Class>,

    /// Store edges.
    edges: PrimaryMap<Edge, EdgeData>,

    /// Maps [`Block`] to [`GvnBlock`]
    blocks: SecondaryMap<BlockId, GvnBlock>,

    value_phi_table: FxHashMap<ValuePhi, Class>,

    /// Hold always available values, i.e. immediates, globals, or function arguments.
    always_avail: Vec<ValueId>,
}

impl GvnSolver {
    pub fn new() -> Self {
        Self {
            classes: PrimaryMap::default(),
            values: SecondaryMap::default(),
            insn_table: FxHashMap::default(),
            edges: PrimaryMap::default(),
            blocks: SecondaryMap::default(),
            value_phi_table: FxHashMap::default(),
            always_avail: Vec::default(),
        }
    }
    /// The main entry point of the struct.
    /// `cfg` and `domtree` is modified to reflect graph structure change.
    pub fn run(&mut self, func: &mut Function, cfg: &mut ControlFlowGraph, domtree: &mut DomTree) {
        self.clear();

        // Return if the function has no blocks.
        if func.layout.entry_block().is_none() {
            return;
        }

        // Make dummy INITIAL_CLASS to which all values belong before congruence finding.
        self.classes.push(ClassData {
            values: BTreeSet::new(),
            gvn_insn: GvnInsn::Value(ValueId(u32::MAX)),
            value_phi: None,
        });
        debug_assert!(self.classes.len() == 1);

        // Make and assign classes for immediate values.
        for &value in func.dfg.immediates.values() {
            self.assign_class_to_imm_value(value);
        }

        // Make and assign classes for global values.
        for &value in func.dfg.globals.values() {
            self.assign_class_to_global_value(value);
        }

        // Assign rank to function arguments and create class for them.
        let mut rank = IMMEDIATE_RANK + 1;
        for &arg in &func.arg_values {
            self.values[arg].rank = rank;
            rank += 1;
            let gvn_insn = GvnInsn::Value(arg);
            self.always_avail.push(arg);
            let class = self.make_class(gvn_insn, None);
            self.assign_class(arg, class);
        }

        // Iterate all insns in RPO to assign ranks and analyze edges information.
        for &block in domtree.rpo() {
            // Assign rank to the block.
            self.blocks[block].rank = rank;
            rank += 1;

            let insts: Vec<_> = func.layout.iter_inst(block).collect();
            for insn in insts {
                if let Some(inst_result) = func.dfg.inst_result(insn) {
                    self.values[inst_result].rank = rank;
                    rank += 1;
                }

                // Make edge data and attach the edge to the originating block and the destinating block.
                if let Some(branch) = func.dfg.branch_info(insn) {
                    match branch.branch_kind() {
                        BranchKind::Jump(jump) => {
                            let dest = *jump.dest();
                            self.add_edge_info(block, dest, None, None, None);
                        }
                        BranchKind::Br(branch) => {
                            let cond = *branch.cond();
                            debug_assert_eq!(func.dfg.value_ty(cond), Type::I1);

                            let then_block = *branch.nz_dest();
                            let else_block = *branch.z_dest();

                            // Create predicate for each edges.
                            // TODO: We need more elaborate representation of predicate.
                            let then_predicate = self.extract_edge_predicate(func, cond, true);
                            let else_predicate = self.extract_edge_predicate(func, cond, false);

                            // Make immediates to which the predicate and `cond` is evaluated when the edge is selected.
                            let then_imm = self.make_imm(&mut func.dfg, true);
                            let else_imm = self.make_imm(&mut func.dfg, false);

                            self.add_edge_info(
                                block,
                                then_block,
                                Some(cond),
                                then_predicate,
                                Some(then_imm),
                            );
                            self.add_edge_info(
                                block,
                                else_block,
                                Some(cond),
                                else_predicate,
                                Some(else_imm),
                            );
                        }
                        BranchKind::BrTable(br_table) => {
                            // Add edge destinating to default block.
                            if let Some(default) = *br_table.default() {
                                self.add_edge_info(block, default, None, None, None);
                            }
                            let cond = *br_table.scrutinee();

                            for (value, dest) in br_table.table() {
                                self.add_edge_info(block, *dest, Some(cond), None, Some(*value));
                            }
                        }
                    }
                }
            }
        }

        // Make the entry block reachable.
        let entry = func.layout.entry_block().unwrap();
        self.blocks[entry].reachable = true;

        // Reassign congruence classes until no more change happens.
        // TODO: We don't need to iterate all insns, it's enough to iterate all `touched` insns as
        // described in the paper.
        let mut changed = true;
        while changed {
            changed = false;
            for &block in domtree.rpo() {
                // If block is unreachable, skip all insns in the block.
                if !self.blocks[block].reachable {
                    continue;
                }

                let mut next_insn = func.layout.first_inst_of(block);
                while let Some(insn) = next_insn {
                    // Reassign congruence class to the result value of the insn.
                    if let Some(inst_result) = func.dfg.inst_result(insn) {
                        changed |= self.reassign_congruence(func, domtree, insn, inst_result);
                    }
                    next_insn = func.layout.next_inst_of(insn);
                }

                // If insn is terminator, analyze it to update edge and block reachability.
                if let Some(last_insn) = func.layout.last_inst_of(block) {
                    changed |= self.analyze_last_insn(func, domtree, block, last_insn);
                }
            }
        }

        // Remove redundant insn and unreachable block.
        let mut remover = RedundantCodeRemover::new(self);
        remover.remove_redundant_code(func, cfg, domtree);
    }

    /// Clear all internal data of the solver.
    pub fn clear(&mut self) {
        self.classes.clear();
        self.values.clear();
        self.insn_table.clear();
        self.edges.clear();
        self.blocks.clear();
        self.value_phi_table.clear();
        self.always_avail.clear();
    }

    /// Analyze the last insn of the block.
    /// This function updates reachability of the edges and blocks.
    ///
    /// Returns `true` if reachability is changed.
    fn analyze_last_insn(
        &mut self,
        func: &Function,
        domtree: &DomTree,
        block: BlockId,
        insn: InstId,
    ) -> bool {
        match func
            .dfg
            .branch_info(insn)
            .map(|branch| branch.branch_kind())
        {
            Some(BranchKind::Jump(_)) => {
                let out_edges = &self.blocks[block].out_edges;
                debug_assert_eq!(out_edges.len(), 1);
                let out_edge = out_edges[0];
                self.mark_edge_reachable(out_edge)
            }

            Some(BranchKind::Br(branch)) => {
                let cond = *branch.cond();
                let out_edges = &self.blocks[block].out_edges;
                debug_assert_eq!(out_edges.len(), 2);
                let then_edge = out_edges[0];
                let else_edge = out_edges[1];
                let then_dest = *branch.nz_dest();
                let else_dest = *branch.z_dest();

                // `br cond X X` is semantically an unconditional jump to `X`.
                // Both CFG edges must be marked reachable; otherwise later edge-pruning can
                // remove destination `X` and incorrectly turn the branch into `unreachable`.
                if then_dest == else_dest {
                    let changed = self.mark_edge_reachable(then_edge);
                    return changed || self.mark_edge_reachable(else_edge);
                }

                // Try to infer reachability of edges.
                if self.infer_edge_reachability(func, cond, then_edge, domtree) {
                    self.mark_edge_reachable(then_edge)
                } else if self.infer_edge_reachability(func, cond, else_edge, domtree) {
                    self.mark_edge_reachable(else_edge)
                } else {
                    // Mark both edges if inference failed.
                    let changed = self.mark_edge_reachable(then_edge);
                    changed || self.mark_edge_reachable(else_edge)
                }
            }

            Some(BranchKind::BrTable(br_table)) => {
                let cond = *br_table.scrutinee();
                let out_edges = self.blocks[block].out_edges.clone();
                let table_offset = usize::from(br_table.default().is_some());
                debug_assert_eq!(out_edges.len(), br_table.table().len() + table_offset);

                // Iterate table entry, if one of the entry value is congruent to cond, then mark
                // the edge as reachable and stop marking.
                for (idx, _) in br_table.table().iter().enumerate() {
                    let edge = out_edges[table_offset + idx];
                    if self.infer_edge_reachability(func, cond, edge, domtree) {
                        return self.mark_edge_reachable(edge);
                    }
                }

                // If `cond` is a known immediate and no keyed edge is selected, the default edge
                // is the only reachable edge.
                if table_offset == 1
                    && func
                        .dfg
                        .value_imm(self.infer_value_at_block(func, domtree, cond, block))
                        .is_some()
                {
                    return self.mark_edge_reachable(out_edges[0]);
                }

                // If none of entry values is congruent to the cond, then mark all edges as
                // reachable.
                let mut changed = false;
                for edge in out_edges {
                    changed |= self.mark_edge_reachable(edge);
                }

                changed
            }

            None => false,
        }
    }

    /// Search and assign congruence class to the `inst_result`.
    /// Returns `true` if congruence class is changed.
    fn reassign_congruence(
        &mut self,
        func: &mut Function,
        domtree: &DomTree,
        insn: InstId,
        inst_result: ValueId,
    ) -> bool {
        // Perform symbolic evaluation for the insn.
        let block = func.layout.inst_block(insn);
        let gvn_insn =
            self.perform_symbolic_evaluation(func, domtree, inst_to_gvn_key(func, insn), block);

        // If insn has a side effect, create new class if the value still belongs to
        // `INITIAL_CLASS`.
        if func.dfg.side_effect(insn).has_effect() {
            if self.value_class(inst_result) == INITIAL_CLASS {
                let class = self.make_class(gvn_insn, None);
                self.assign_class(inst_result, class);
                return true;
            } else {
                return false;
            }
        }

        let mut changed = false;
        let new_class = if let GvnInsn::Value(value) = &gvn_insn {
            // If `gvn_insn` is value itself, just use the class of the value.
            self.value_class(*value)
        } else if let Some(class) = self.insn_table.get(&gvn_insn).copied() {
            // If gvn_insn is already inserted, use corresponding class.

            // We need to recompute value phi for the class to reflect reachability changes and
            // leader changes.
            changed |= self.recompute_value_phi(func, &gvn_insn, inst_result);
            class
        } else if let Some(value_phi) =
            ValuePhiFinder::new(self, inst_result).compute_value_phi(func, &gvn_insn)
        {
            if let Some(class) = self.value_phi_table.get(&value_phi) {
                *class
            } else {
                self.make_class(gvn_insn.clone(), Some(value_phi))
            }
        } else {
            self.make_class(gvn_insn.clone(), None)
        };

        let old_class = self.value_class(inst_result);
        if old_class == new_class {
            changed
        } else {
            self.assign_class(inst_result, new_class);
            true
        }
    }

    /// Perform value phi computation for the value.
    ///
    /// Returns `true` if computed value phi is changed from the old value phi of the value class.
    /// The computed value phi is assigned to the class's value phi.
    fn recompute_value_phi(
        &mut self,
        func: &mut Function,
        insn_data: &GvnInsn,
        inst_result: ValueId,
    ) -> bool {
        let value_phi = ValuePhiFinder::new(self, inst_result).compute_value_phi(func, insn_data);
        let class = self.value_class(inst_result);
        self.update_class_value_phi(class, value_phi)
    }

    /// Mark the edge and its destinating block as reachable if they are still unreachable.
    ///
    /// Returns `true` if edge becomes reachable.
    fn mark_edge_reachable(&mut self, edge: Edge) -> bool {
        let edge_data = &mut self.edges[edge];
        let dest = edge_data.to;

        if !edge_data.reachable {
            edge_data.reachable = true;
            self.blocks[dest].reachable = true;
            true
        } else {
            false
        }
    }

    /// Returns `true` if the `edge` is inferred as being reachable.
    /// If this function returns `true` then other outgoing edges from the same originating block
    /// are guaranteed to be unreachable.
    ///
    /// Edge is inferred as reachable if inferred cond value is congruent to the `resolved_cond` of the edge.
    fn infer_edge_reachability(
        &self,
        func: &Function,
        cond: ValueId,
        edge: Edge,
        domtree: &DomTree,
    ) -> bool {
        let edge_data = &self.edges[edge];
        // If `resolved_cond` doesn't exist, then the edge must be non conditional jump.
        let resolved_cond = match edge_data.resolved_cond.expand() {
            Some(cond) => cond,
            None => return true,
        };

        let inferred_value = self.infer_value_at_block(func, domtree, cond, edge_data.from);
        self.is_congruent_value(inferred_value, resolved_cond)
    }

    /// Returns representative value at the block by using edge's predicate.
    ///
    /// `value` can be inferred to `value2` if
    /// 1. The predicate of dominant incoming edge is represented as `value1 == value2`.
    /// 2. `value` is congruent to value1
    /// 3. `value2`.rank < `value`.rank.
    ///
    /// This process is recursively applied while tracing idom chain.
    /// If the dominant edge is back edge, then this process is stopped to avoid infinite loop.
    ///
    /// # Example
    /// In the below example, `value` inside if block is inferred to `value2`.
    ///
    /// ```pseudo
    /// let value2 = .. (rank0)
    /// let value1 = .. (rank1)
    /// let value = value1 + 0 (rank2)
    /// if value1 == value2 {
    ///     use value
    /// }
    /// ```
    fn infer_value_at_block(
        &self,
        func: &Function,
        domtree: &DomTree,
        value: ValueId,
        target_block: BlockId,
    ) -> ValueId {
        let mut rep_value = self.leader(value);

        let mut current_block = Some(target_block);
        // Try to infer value until the representative value becomes immediate or current block
        // becomes `None`.
        while current_block.is_some() && (!func.dfg.value_is_imm(rep_value)) {
            let block = current_block.unwrap();
            if let Some(dominant_edge) = self.dominant_reachable_in_edges(block) {
                // Stop looking up the value to avoid infinite lookup loop.
                if self.is_back_edge(dominant_edge) {
                    break;
                }

                // If the value inference succeeds, restart inference with the new representative value.
                if let Some(value) = self.infer_value_impl(dominant_edge, rep_value) {
                    if self.value_rank(value) < self.value_rank(rep_value) {
                        rep_value = value;
                        current_block = Some(target_block);
                    } else {
                        current_block = Some(self.edge_data(dominant_edge).from);
                    }
                } else {
                    // If the inference failed, change the current block to the originating block
                    // of the edge.
                    current_block = Some(self.edge_data(dominant_edge).from);
                }
            } else {
                // If no dominant edge found, change the current block to the immediate dominator
                // of the current block.
                current_block = domtree.idom_of(block);
            }
        }

        rep_value
    }

    /// Returns representative value at the edge by using edge's predicate.
    ///
    /// This is used to infer phi arguments which is guaranteed to flow through the specified edge.
    fn infer_value_at_edge(
        &self,
        func: &Function,
        domtree: &DomTree,
        value: ValueId,
        edge: Edge,
    ) -> ValueId {
        let mut rep_value = self.leader(value);

        if let Some(inferred_value) = self.infer_value_impl(edge, rep_value) {
            rep_value = inferred_value;
        }

        self.infer_value_at_block(func, domtree, rep_value, self.edge_data(edge).from)
    }

    /// A helper function to infer value using edge predicate.
    ///
    /// Returns inferred `value2` iff
    /// 1. The predicate of the `edge` is represented as `value1 == value2`.
    /// 2. `value` is congruent to value1
    /// 3. `value2`.rank < `value`.rank.
    fn infer_value_impl(&self, edge: Edge, value: ValueId) -> Option<ValueId> {
        let edge_data = self.edge_data(edge);
        let edge_cond = edge_data.cond.expand()?;
        // If value is congruent to edge cond value, then return resolved cond of the edge.
        if self.is_congruent_value(edge_cond, value) {
            return Some(edge_data.resolved_cond.unwrap());
        }

        let predicate = edge_data.predicate.as_ref()?;

        match predicate {
            PredicateRelation::Eq { lhs, rhs } => {
                if self.is_congruent_value(*lhs, value)
                    && self.value_rank(*rhs) < self.value_rank(value)
                {
                    Some(*rhs)
                } else if self.is_congruent_value(*rhs, value)
                    && self.value_rank(*lhs) < self.value_rank(value)
                {
                    Some(*lhs)
                } else {
                    None
                }
            }
        }
    }

    /// Returns reachable incoming edges of the block.
    fn reachable_in_edges(&self, block: BlockId) -> impl Iterator<Item = &Edge> {
        self.blocks[block]
            .in_edges
            .iter()
            .filter(|edge| self.edge_data(**edge).reachable)
    }

    /// Returns unreachable outgoing edges of the block.
    fn unreachable_out_edges(&self, block: BlockId) -> impl Iterator<Item = &Edge> {
        self.blocks[block]
            .out_edges
            .iter()
            .filter(|edge| !self.edge_data(**edge).reachable)
    }

    /// Returns the incoming edge if the edge is only one reachable edge to the block.
    fn dominant_reachable_in_edges(&self, block: BlockId) -> Option<Edge> {
        let mut edges = self.reachable_in_edges(block);

        let dominant = edges.next()?;
        if edges.next().is_none() {
            Some(*dominant)
        } else {
            None
        }
    }

    /// Returns `true` if two values are congruent.
    /// NOTE: Returns `false` if both values belong to `INITIAL_CLASS`.
    fn is_congruent_value(&self, lhs: ValueId, rhs: ValueId) -> bool {
        let lhs_class = self.values[lhs].class;
        let rhs_class = self.values[rhs].class;
        (lhs_class == rhs_class) && (lhs_class != INITIAL_CLASS)
    }

    /// Perform symbolic evaluation for the `insn_data`.
    fn perform_symbolic_evaluation(
        &mut self,
        func: &mut Function,
        domtree: &DomTree,
        insn_expr: OwnedInstKey,
        block: BlockId,
    ) -> GvnInsn {
        // Get canonicalized insn by swapping arguments with leader values.
        //
        // If the insn is commutative, then argument order is also canonicalized.
        // And if the insn is phi, arguments from unreachable edges are omitted.
        let insn_expr = if let Some(phi_args) = insn_expr.phi_args() {
            let edges = &self.blocks[block].in_edges;
            let mut canonical_phi_args = Vec::with_capacity(phi_args.len());
            for &(value, from) in phi_args {
                match self.reachable_edge_state(edges, from, block) {
                    ReachableEdgeState::None => continue,
                    ReachableEdgeState::One(edge) => {
                        let inferred_value = self.infer_value_at_edge(func, domtree, value, edge);
                        canonical_phi_args.push((inferred_value, from));
                    }
                    // Phi arguments are keyed by predecessor block, not by edge. When multiple
                    // reachable edges exist from the same predecessor to this block, edge-specific
                    // predicate inference is not valid.
                    ReachableEdgeState::Many => {
                        let inferred_value = self.infer_value_at_block(func, domtree, value, from);
                        canonical_phi_args.push((inferred_value, from));
                    }
                }
            }

            // Canonicalize the argument order by block rank.
            canonical_phi_args.sort_unstable_by(|(_, block1), (_, block2)| {
                self.block_rank(*block1).cmp(&self.block_rank(*block2))
            });
            insn_expr.with_phi_args(canonical_phi_args).unwrap()
        } else if let Some(arg) = insn_expr.unary_arg() {
            let arg = self.infer_value_at_block(func, domtree, arg, block);
            insn_expr.with_unary_arg(arg).unwrap()
        } else if let Some((lhs, rhs)) = insn_expr.binary_args() {
            let mut lhs = self.infer_value_at_block(func, domtree, lhs, block);
            let mut rhs = self.infer_value_at_block(func, domtree, rhs, block);

            if insn_expr.is_commutative_binary() && self.value_rank(rhs) < self.value_rank(lhs) {
                std::mem::swap(&mut lhs, &mut rhs);
            }

            insn_expr.with_binary_args(lhs, rhs).unwrap()
        } else if let Some((arg, _)) = insn_expr.cast_arg_ty() {
            let arg = self.infer_value_at_block(func, domtree, arg, block);
            insn_expr.with_cast_arg(arg).unwrap()
        } else {
            let canonical_values: Vec<_> = insn_expr
                .values()
                .iter()
                .map(|&value| self.infer_value_at_block(func, domtree, value, block))
                .collect();
            if canonical_values.as_slice() == insn_expr.values() {
                insn_expr
            } else {
                insn_expr.with_values(canonical_values).unwrap_or(insn_expr)
            }
        };

        if let Some(imm) = self.perform_constant_folding(func, &insn_expr) {
            GvnInsn::Value(imm)
        } else if let Some(result) = self.perform_simplification(func, &insn_expr) {
            result
        } else {
            GvnInsn::Expr(insn_expr)
        }
    }

    /// Perform constant folding.
    fn perform_constant_folding(
        &mut self,
        func: &mut Function,
        insn_expr: &OwnedInstKey,
    ) -> Option<ValueId> {
        let imm = if let InstClassKind::Unary(kind) = insn_expr.kind() {
            let arg = func.dfg.value_imm(insn_expr.unary_arg()?)?;
            match kind {
                UnaryInstKind::Neg => -arg,
                UnaryInstKind::Not => !arg,
                UnaryInstKind::IsZero => arg.is_zero().into(),
                UnaryInstKind::EvmClz => return None,
            }
        } else if let InstClassKind::Binary(kind) = insn_expr.kind() {
            let (lhs, rhs) = insn_expr.binary_args()?;
            match kind {
                BinaryInstKind::Add => func.dfg.value_imm(lhs)? + func.dfg.value_imm(rhs)?,
                BinaryInstKind::Mul => func.dfg.value_imm(lhs)? * func.dfg.value_imm(rhs)?,
                BinaryInstKind::Sub => func.dfg.value_imm(lhs)? - func.dfg.value_imm(rhs)?,
                BinaryInstKind::Sdiv => {
                    let lhs = func.dfg.value_imm(lhs)?;
                    let rhs = func.dfg.value_imm(rhs)?;
                    (!rhs.is_zero()).then_some(lhs.sdiv(rhs))?
                }
                BinaryInstKind::Udiv => {
                    let lhs = func.dfg.value_imm(lhs)?;
                    let rhs = func.dfg.value_imm(rhs)?;
                    (!rhs.is_zero()).then_some(lhs.udiv(rhs))?
                }
                BinaryInstKind::Umod => {
                    let lhs = func.dfg.value_imm(lhs)?;
                    let rhs = func.dfg.value_imm(rhs)?;
                    (!rhs.is_zero()).then_some(lhs.urem(rhs))?
                }
                BinaryInstKind::Smod => {
                    let lhs = func.dfg.value_imm(lhs)?;
                    let rhs = func.dfg.value_imm(rhs)?;
                    (!rhs.is_zero()).then_some(lhs.srem(rhs))?
                }
                BinaryInstKind::Lt => func.dfg.value_imm(lhs)?.lt(func.dfg.value_imm(rhs)?),
                BinaryInstKind::Gt => func.dfg.value_imm(lhs)?.gt(func.dfg.value_imm(rhs)?),
                BinaryInstKind::Slt => func.dfg.value_imm(lhs)?.slt(func.dfg.value_imm(rhs)?),
                BinaryInstKind::Sgt => func.dfg.value_imm(lhs)?.sgt(func.dfg.value_imm(rhs)?),
                BinaryInstKind::Le => func.dfg.value_imm(lhs)?.le(func.dfg.value_imm(rhs)?),
                BinaryInstKind::Ge => func.dfg.value_imm(lhs)?.ge(func.dfg.value_imm(rhs)?),
                BinaryInstKind::Sle => func.dfg.value_imm(lhs)?.sle(func.dfg.value_imm(rhs)?),
                BinaryInstKind::Sge => func.dfg.value_imm(lhs)?.sge(func.dfg.value_imm(rhs)?),
                BinaryInstKind::Eq => func.dfg.value_imm(lhs)?.imm_eq(func.dfg.value_imm(rhs)?),
                BinaryInstKind::Ne => func.dfg.value_imm(lhs)?.imm_ne(func.dfg.value_imm(rhs)?),
                BinaryInstKind::And => func.dfg.value_imm(lhs)? & func.dfg.value_imm(rhs)?,
                BinaryInstKind::Or => func.dfg.value_imm(lhs)? | func.dfg.value_imm(rhs)?,
                BinaryInstKind::Xor => func.dfg.value_imm(lhs)? ^ func.dfg.value_imm(rhs)?,
                BinaryInstKind::Shl
                | BinaryInstKind::Shr
                | BinaryInstKind::Sar
                | BinaryInstKind::EvmUdiv
                | BinaryInstKind::EvmSdiv
                | BinaryInstKind::EvmUmod
                | BinaryInstKind::EvmSmod
                | BinaryInstKind::EvmExp
                | BinaryInstKind::EvmByte => return None,
            }
        } else if let InstClassKind::Cast(kind) = insn_expr.kind() {
            let (arg, ty) = insn_expr.cast_arg_ty()?;
            if !ty.is_integral() {
                return None;
            }

            let value = func.dfg.value_imm(arg)?;
            match kind {
                CastInstKind::Sext => value.sext(ty),
                CastInstKind::Zext => value.zext(ty),
                CastInstKind::Trunc => value.trunc(ty),
                CastInstKind::Bitcast | CastInstKind::IntToPtr | CastInstKind::PtrToInt => {
                    Immediate::from_i256(value.as_i256(), ty)
                }
            }
        } else {
            return None;
        };

        Some(self.make_imm(&mut func.dfg, imm))
    }

    /// Perform insn simplification.
    fn perform_simplification(
        &mut self,
        func: &mut Function,
        insn_expr: &OwnedInstKey,
    ) -> Option<GvnInsn> {
        if let InstClassKind::Unary(kind) = insn_expr.kind() {
            let arg = insn_expr.unary_arg()?;
            let simplified = simplify_unary_with_same_inner(kind, arg, |arg, expected| {
                let Value::Inst { inst, .. } = func.dfg.value(arg) else {
                    return None;
                };
                let inner = inst_to_gvn_key(func, *inst);
                (inner.kind() == InstClassKind::Unary(expected))
                    .then_some(())
                    .and_then(|_| inner.unary_arg())
            });
            if !simplified.is_no_change() {
                return Some(self.simplify_expr_result_to_gvn(func, simplified));
            }
        }

        if let InstClassKind::Binary(kind) = insn_expr.kind() {
            let (lhs, rhs) = insn_expr.binary_args()?;
            let simplified = simplify_binary_with_known_imm(
                func,
                kind,
                lhs,
                rhs,
                |value| func.dfg.value_imm(value),
                |lhs, rhs| self.same_non_undef(func, lhs, rhs),
            );
            if !simplified.is_no_change() {
                return Some(self.simplify_expr_result_to_gvn(func, simplified));
            }
        }

        if let InstClassKind::Cast(kind) = insn_expr.kind() {
            let (arg, ty) = insn_expr.cast_arg_ty()?;
            let simplified = simplify_cast(func, kind, arg, ty);
            if !simplified.is_no_change() {
                return Some(self.simplify_expr_result_to_gvn(func, simplified));
            }
        }

        if let Some(phi_args) = insn_expr.phi_args() {
            return phi_args
                .first()
                .map(|(value, _)| *value)
                .filter(|first| phi_args.iter().all(|(value, _)| value == first))
                .map(GvnInsn::Value);
        }

        None
    }

    fn same_non_undef(&self, func: &Function, lhs: ValueId, rhs: ValueId) -> bool {
        lhs == rhs && !self.may_be_undef(func, lhs)
    }

    fn may_be_undef(&self, func: &Function, value: ValueId) -> bool {
        let mut visiting = FxHashSet::default();
        self.may_be_undef_impl(func, value, &mut visiting)
    }

    fn may_be_undef_impl(
        &self,
        func: &Function,
        value: ValueId,
        visiting: &mut FxHashSet<ValueId>,
    ) -> bool {
        if !visiting.insert(value) {
            // Be conservative for cyclic value definitions.
            return true;
        }

        let may_be_undef = match func.dfg.value(value) {
            Value::Undef { .. } => true,
            Value::Immediate { .. } | Value::Arg { .. } | Value::Global { .. } => false,
            Value::Inst { inst, .. } => self.inst_result_may_be_undef(func, *inst, visiting),
        };

        visiting.remove(&value);
        may_be_undef
    }

    fn inst_result_may_be_undef(
        &self,
        func: &Function,
        inst: InstId,
        visiting: &mut FxHashSet<ValueId>,
    ) -> bool {
        let inst_data = func.dfg.inst(inst);
        let values = inst_data.collect_values();
        if values
            .iter()
            .copied()
            .any(|value| self.may_be_undef_impl(func, value, visiting))
        {
            return true;
        }

        if let InstClassKind::Binary(kind) = inst_data.kind()
            && matches!(
                kind,
                BinaryInstKind::Udiv
                    | BinaryInstKind::Sdiv
                    | BinaryInstKind::Umod
                    | BinaryInstKind::Smod
            )
        {
            let [_, rhs] = values.as_slice() else {
                return true;
            };
            return func.dfg.value_imm(*rhs).is_none_or(Immediate::is_zero);
        }

        false
    }

    fn simplify_expr_result_to_gvn(
        &mut self,
        func: &mut Function,
        simplified: SimplifyExprResult,
    ) -> GvnInsn {
        match simplified {
            SimplifyExprResult::Const(imm) => {
                let value = self.make_imm(&mut func.dfg, imm);
                GvnInsn::Value(value)
            }
            SimplifyExprResult::Copy(value) => GvnInsn::Value(value),
            SimplifyExprResult::NoChange => unreachable!(),
        }
    }

    fn extract_edge_predicate(
        &mut self,
        func: &mut Function,
        cond: ValueId,
        edge_truth: bool,
    ) -> Option<PredicateRelation> {
        let inst = func.dfg.value_inst(cond)?;
        let mut insn_expr = inst_to_gvn_key(func, inst);
        let mut expected_true = edge_truth;

        // Canonicalize predicates by peeling `not` and mapping `ne == false` to `eq`.
        for _ in 0..16 {
            if let Some(GvnInsn::Value(value)) = self.perform_simplification(func, &insn_expr)
                && let Some(value_inst) = func.dfg.value_inst(value)
            {
                insn_expr = inst_to_gvn_key(func, value_inst);
                continue;
            }

            if matches!(insn_expr.kind(), InstClassKind::Unary(UnaryInstKind::Not))
                && let Some(arg) = insn_expr.unary_arg()
                && let Some(inner_inst) = func.dfg.value_inst(arg)
            {
                insn_expr = inst_to_gvn_key(func, inner_inst);
                expected_true = !expected_true;
                continue;
            }

            if let InstClassKind::Binary(BinaryInstKind::Eq) = insn_expr.kind()
                && expected_true
            {
                let (lhs, rhs) = insn_expr.binary_args()?;
                return Some(PredicateRelation::Eq { lhs, rhs });
            }

            if let InstClassKind::Binary(BinaryInstKind::Ne) = insn_expr.kind()
                && !expected_true
            {
                let (lhs, rhs) = insn_expr.binary_args()?;
                return Some(PredicateRelation::Eq { lhs, rhs });
            }

            return None;
        }

        None
    }

    /// Make edge data and append incoming/outgoing edges of corresponding blocks.
    fn add_edge_info(
        &mut self,
        from: BlockId,
        to: BlockId,
        cond: Option<ValueId>,
        predicate: Option<PredicateRelation>,
        resolved_cond: Option<ValueId>,
    ) {
        let edge_data = EdgeData {
            from,
            to,
            cond: cond.into(),
            predicate,
            resolved_cond: resolved_cond.into(),
            reachable: false,
        };

        // Append incoming/outgoing edges of corresponding blocks.
        let edge = self.edges.push(edge_data);
        self.blocks[to].in_edges.push(edge);
        self.blocks[from].out_edges.push(edge);
    }

    /// Assign `class` to `value`.
    fn assign_class(&mut self, value: ValueId, class: Class) {
        let old_class = self.value_class(value);
        if old_class == class {
            return;
        }

        let value_rank = self.value_rank(value);

        // Add value to the class.
        let class_data = &mut self.classes[class];
        class_data.values.insert((value_rank, value));
        self.values[value].class = class;

        // Remove `value` from `old` class.
        let old_class_data = &mut self.classes[old_class];
        old_class_data.values.remove(&(value_rank, value));

        // Remove old insn and value phi if the class becomes empty.
        if let Some(insn_class) = self.insn_table.get_mut(&old_class_data.gvn_insn)
            && *insn_class == old_class
            && old_class_data.values.is_empty()
        {
            self.insn_table.remove(&old_class_data.gvn_insn);
            if let Some(value_phi) = &old_class_data.value_phi {
                self.value_phi_table.remove(value_phi);
            }
        }
    }

    /// Make value from immediate, also make a corresponding congruence class and update
    /// `insn_table` for the immediate value if they don't exist yet.
    fn make_imm(&mut self, dfg: &mut DataFlowGraph, imm: impl Into<Immediate>) -> ValueId {
        // `make_imm_value` return always same value for the same immediate.
        let value = dfg.make_imm_value(imm);

        // Assign new class to the `imm`.
        self.assign_class_to_imm_value(value);

        value
    }

    /// Make and assign class to immediate value.
    fn assign_class_to_imm_value(&mut self, value: ValueId) {
        let class = self.values[value].class;
        let gvn_insn = GvnInsn::Value(value);

        // If the congruence class for the value already exists, then return.
        if class != INITIAL_CLASS {
            debug_assert_eq!(self.values[value].rank, IMMEDIATE_RANK);
            return;
        }

        // Set rank.
        self.values[value].rank = IMMEDIATE_RANK;

        // Add the immediate to `always_avail` value.
        self.always_avail.push(value);

        // Create a congruence class for the immediate.
        let class = self.make_class(gvn_insn, None);
        self.assign_class(value, class);
    }

    /// Make and assign class to global value.
    fn assign_class_to_global_value(&mut self, value: ValueId) {
        // If the congruence class for the value already exists, then return.
        if self.values[value].class != INITIAL_CLASS {
            return;
        }

        // Set rank.
        self.values[value].rank = IMMEDIATE_RANK;

        // Add the global to `always_avail` value.
        self.always_avail.push(value);

        // Create a congruence class for the global.
        let class = self.make_class(GvnInsn::Value(value), None);
        self.assign_class(value, class);
    }

    /// Returns `true` if the edge is backedge.
    fn is_back_edge(&self, edge: Edge) -> bool {
        let from = self.edge_data(edge).from;
        let to = self.edge_data(edge).to;

        self.blocks[to].rank <= self.blocks[from].rank
    }

    /// Returns the leader value of the congruent class to which `value` belongs.
    fn leader(&self, value: ValueId) -> ValueId {
        let class = self.values[value].class;
        if class == INITIAL_CLASS {
            return value;
        }

        self.class_data(class)
            .values
            .iter()
            .next()
            .map_or(value, |(_, leader)| *leader)
    }

    /// Returns the leader value of the congruent class.
    /// This method is mainly for [`ValuePhiFinder`], use [`Self::leader`] whenever possible.
    fn class_leader(&self, class: Class) -> ValueId {
        self.class_data(class).values.iter().next().unwrap().1
    }

    /// Returns `EdgeData`.
    fn edge_data(&self, edge: Edge) -> &EdgeData {
        &self.edges[edge]
    }

    /// Returns `ClassData`.
    fn class_data(&self, class: Class) -> &ClassData {
        &self.classes[class]
    }

    /// Returns the class of the value.
    fn value_class(&self, value: ValueId) -> Class {
        self.values[value].class
    }

    /// Returns the rank of the value.
    fn value_rank(&self, value: ValueId) -> u32 {
        self.values[value].rank
    }

    /// Returns the rank of the block.
    fn block_rank(&self, block: BlockId) -> u32 {
        self.blocks[block].rank
    }

    /// Make a new class and update tables.
    /// To assign the class to the value, use [`Self::assign_class`].
    fn make_class(&mut self, gvn_insn: GvnInsn, value_phi: Option<ValuePhi>) -> Class {
        let class_data = ClassData {
            values: BTreeSet::new(),
            gvn_insn: gvn_insn.clone(),
            value_phi: value_phi.clone(),
        };
        let class = self.classes.push(class_data);

        // Update tables.
        self.insn_table.insert(gvn_insn, class);
        if let Some(value_phi) = value_phi {
            self.value_phi_table.insert(value_phi, class);
        }

        class
    }

    fn update_class_value_phi(&mut self, class: Class, value_phi: Option<ValuePhi>) -> bool {
        if self.classes[class].value_phi.as_ref() == value_phi.as_ref() {
            return false;
        }

        if let Some(old_value_phi) = self.classes[class].value_phi.take() {
            self.value_phi_table.remove(&old_value_phi);
        }
        if let Some(new_value_phi) = &value_phi {
            self.value_phi_table.insert(new_value_phi.clone(), class);
        }
        self.classes[class].value_phi = value_phi;
        true
    }

    fn reachable_edge_state(
        &self,
        edges: &[Edge],
        from: BlockId,
        to: BlockId,
    ) -> ReachableEdgeState {
        let mut one = None;
        for edge in edges {
            let data = self.edge_data(*edge);
            if data.from != from || data.to != to || !data.reachable {
                continue;
            }

            if one.is_some() {
                return ReachableEdgeState::Many;
            }
            one = Some(*edge);
        }

        one.map_or(ReachableEdgeState::None, ReachableEdgeState::One)
    }
}

impl Default for GvnSolver {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash, PartialOrd, Ord)]
struct Class(u32);
entity_impl!(Class);

/// A congruence class.
#[derive(Debug, Clone, PartialEq)]
struct ClassData {
    /// Values the class includes.
    /// NOTE: We need sort the value by rank.
    values: BTreeSet<(u32, ValueId)>,

    /// Representative insn of the class.
    gvn_insn: GvnInsn,

    /// A value phi of the class.
    value_phi: Option<ValuePhi>,
}

/// A collection of value data used by `GvnSolver`.
#[derive(Debug, Clone, PartialEq)]
struct GvnValue {
    /// A class to which the value belongs.
    class: Class,

    /// A rank of the value.
    /// If the value is immediate, then the rank is 0, otherwise the rank is assigned to each value in RPO order.
    /// This ensures `rankA` is defined earlier than `rankB` iff `rankA` < `rankB`.
    rank: u32,
}

impl Default for GvnValue {
    fn default() -> Self {
        Self {
            class: INITIAL_CLASS,
            rank: 0,
        }
    }
}

/// A canonicalized GVN value expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum GvnInsn {
    /// A value which occurs when insn is simplified/folded to value.
    Value(ValueId),
    /// A canonicalized expression key.
    Expr(OwnedInstKey),
}

impl From<ValueId> for GvnInsn {
    fn from(value: ValueId) -> Self {
        Self::Value(value)
    }
}

impl From<OwnedInstKey> for GvnInsn {
    fn from(insn: OwnedInstKey) -> Self {
        Self::Expr(insn)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash, PartialOrd, Ord)]
struct Edge(u32);
entity_impl!(Edge);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum PredicateRelation {
    Eq { lhs: ValueId, rhs: ValueId },
}

#[derive(Debug, Clone)]
struct EdgeData {
    /// An originating block.
    from: BlockId,

    /// A destinating block.
    to: BlockId,

    /// Hold a condition value if branch is conditional.
    cond: PackedOption<ValueId>,

    /// Hold a predicate relation if branch is conditional.
    predicate: Option<PredicateRelation>,

    /// An immediate to which cond is resolved if the edge is selected.
    resolved_cond: PackedOption<ValueId>,

    /// `true` if the edge is reachable.
    reachable: bool,
}

#[derive(Debug, Default, Clone)]
struct GvnBlock {
    /// Incoming edges.
    in_edges: Vec<Edge>,

    /// Outgoing edges.
    out_edges: Vec<Edge>,

    /// `true` if the block is reachable.
    reachable: bool,

    /// A rank of the block.
    /// The rank definition is same as `GvnValue::rank`.
    rank: u32,
}

/// This struct finds value phi that described in
/// `Detection of Redundant Expressions: A Complete and Polynomial-Time Algorithm in SSA`.
struct ValuePhiFinder<'a> {
    solver: &'a mut GvnSolver,
    /// Hold visited values to prevent infinite loop.
    visited: FxHashSet<ValueId>,
}

impl<'a> ValuePhiFinder<'a> {
    fn new(solver: &'a mut GvnSolver, inst_result: ValueId) -> Self {
        let mut visited = FxHashSet::default();
        visited.insert(inst_result);
        Self { solver, visited }
    }

    /// Main entry of this struct.
    fn compute_value_phi(&mut self, func: &mut Function, gvn_insn: &GvnInsn) -> Option<ValuePhi> {
        // Break infinite loop if the block has been already visited.
        let insn_expr = if let GvnInsn::Expr(insn_expr) = gvn_insn {
            insn_expr
        } else {
            return None;
        };

        if let Some(arg) = insn_expr.unary_arg() {
            let arg = self.get_phi_of(func, arg)?;
            let make_query = |value| insn_expr.with_unary_arg(value).unwrap();
            return self.compute_value_phi_for_unary(func, arg, make_query);
        }

        if let Some((lhs, rhs)) = insn_expr.binary_args() {
            let (lhs, rhs) = if lhs == rhs {
                let lhs_phi = self.get_phi_of(func, lhs)?;
                let rhs_phi = lhs_phi.clone();
                (lhs_phi, rhs_phi)
            } else {
                match (self.get_phi_of(func, lhs), self.get_phi_of(func, rhs)) {
                    (Some(lhs_phi), Some(rhs_phi)) => (lhs_phi, rhs_phi),
                    (Some(lhs_phi), None) => (lhs_phi, ValuePhi::Value(rhs)),
                    (None, Some(rhs_phi)) => (ValuePhi::Value(lhs), rhs_phi),
                    (None, None) => return None,
                }
            };

            let commutative = insn_expr.is_commutative_binary();
            let make_query = |lhs, rhs| insn_expr.with_binary_args(lhs, rhs).unwrap();
            return self.compute_value_phi_for_binary(func, lhs, rhs, commutative, make_query);
        }

        if let Some((arg, _)) = insn_expr.cast_arg_ty() {
            let arg = self.get_phi_of(func, arg)?;
            let make_query = |value| insn_expr.with_cast_arg(value).unwrap();
            return self.compute_value_phi_for_cast(func, arg, make_query);
        }

        None
    }

    fn compute_value_phi_for_unary<F>(
        &mut self,
        func: &mut Function,
        value_phi: ValuePhi,
        make_query: F,
    ) -> Option<ValuePhi>
    where
        F: Fn(ValueId) -> OwnedInstKey + Copy,
    {
        let value_phi_insn = if let ValuePhi::PhiInsn(insn) = value_phi {
            insn
        } else {
            return None;
        };

        let mut result =
            ValuePhiInsn::with_capacity(value_phi_insn.block, value_phi_insn.args.len());

        for (arg, block) in value_phi_insn.args.into_iter() {
            match arg {
                ValuePhi::Value(value) => {
                    let phi_arg = self.lookup_value_phi_arg(func, make_query(value))?;
                    result.args.push((phi_arg, block));
                }
                ValuePhi::PhiInsn(_) => {
                    let phi_arg = self.compute_value_phi_for_unary(func, arg, make_query)?;
                    result.args.push((phi_arg, block));
                }
            }
        }

        Some(result.canonicalize())
    }

    fn compute_value_phi_for_binary<F>(
        &mut self,
        func: &mut Function,
        lhs: ValuePhi,
        rhs: ValuePhi,
        commutative: bool,
        make_query: F,
    ) -> Option<ValuePhi>
    where
        F: Fn(ValueId, ValueId) -> OwnedInstKey + Copy,
    {
        // Unpack the value phis and create args to lookup value phi.
        //
        // 1. In case both lhs and rhs are phi insn.
        // lhs := PhiInsn(lhs_arg1: block1, .., lhs_argN: blockN, phi_block)
        // rhs := PhiInsn(rhs_arg1: block1, .., rhs_argN: blockN, phi_block)
        // args := [((lhs_arg1, rhs_arg1): block1), .., ((lhs_argN, rhs_argN), BlockN), phi_block)]
        //
        // 2. In case lhs is a phi insn and rhs is a value.
        // lhs := PhiInsn(lhs_arg1: block1, .., lhs_argN: blockN, phi_block)
        // rhs := rhs_value
        // args := [((lhs_arg1, rhs_value): block1), .., ((lhs_argN, rhs_value), blockN), phi_block)]
        //
        // 3. In case rhs is a phi insn and lhs is a value.
        // Same as 2.
        //
        // 4. In case both args are value, then return `None`.
        let (args, phi_block): (Vec<_>, _) = match (lhs, rhs) {
            (ValuePhi::PhiInsn(lhs_phi), ValuePhi::PhiInsn(rhs_phi)) => {
                // If two blocks are not identical or number of phi args are not the same, return.
                if lhs_phi.block != rhs_phi.block || lhs_phi.args.len() != rhs_phi.args.len() {
                    return None;
                }

                let mut args = Vec::with_capacity(lhs_phi.args.len());
                for ((lhs_arg, lhs_block), (rhs_arg, rhs_block)) in
                    lhs_phi.args.into_iter().zip(rhs_phi.args.into_iter())
                {
                    // If two blocks which phi arg passed through are not identical, return.
                    if lhs_block != rhs_block {
                        return None;
                    }
                    args.push(((lhs_arg, rhs_arg), lhs_block));
                }
                (args, lhs_phi.block)
            }

            (ValuePhi::PhiInsn(lhs_phi), ValuePhi::Value(rhs_value)) => (
                lhs_phi
                    .args
                    .into_iter()
                    .map(|(phi_arg, block)| ((phi_arg, ValuePhi::Value(rhs_value)), block))
                    .collect(),
                lhs_phi.block,
            ),

            (ValuePhi::Value(lhs_value), ValuePhi::PhiInsn(rhs_phi)) => (
                rhs_phi
                    .args
                    .into_iter()
                    .map(|(phi_arg, block)| ((ValuePhi::Value(lhs_value), phi_arg), block))
                    .collect(),
                rhs_phi.block,
            ),

            (ValuePhi::Value(_), ValuePhi::Value(_)) => return None,
        };

        let mut result = ValuePhiInsn::with_capacity(phi_block, args.len());
        for ((lhs_arg, rhs_arg), block) in args {
            match (lhs_arg, rhs_arg) {
                (ValuePhi::Value(mut lhs_value), ValuePhi::Value(mut rhs_value)) => {
                    if commutative
                        && self.solver.value_rank(rhs_value) < self.solver.value_rank(lhs_value)
                    {
                        // Reorder args if the insn is commutative.
                        std::mem::swap(&mut lhs_value, &mut rhs_value);
                    }
                    let phi_arg =
                        self.lookup_value_phi_arg(func, make_query(lhs_value, rhs_value))?;
                    result.args.push((phi_arg, block));
                }
                (lhs_arg, rhs_arg) => {
                    let phi_arg = self.compute_value_phi_for_binary(
                        func,
                        lhs_arg,
                        rhs_arg,
                        commutative,
                        make_query,
                    )?;
                    result.args.push((phi_arg, block));
                }
            }
        }

        Some(result.canonicalize())
    }

    fn compute_value_phi_for_cast<F>(
        &mut self,
        func: &mut Function,
        value_phi: ValuePhi,
        make_query: F,
    ) -> Option<ValuePhi>
    where
        F: Fn(ValueId) -> OwnedInstKey + Copy,
    {
        let value_phi_insn = if let ValuePhi::PhiInsn(insn) = value_phi {
            insn
        } else {
            return None;
        };

        let mut result =
            ValuePhiInsn::with_capacity(value_phi_insn.block, value_phi_insn.args.len());

        for (arg, block) in value_phi_insn.args.into_iter() {
            match arg {
                ValuePhi::Value(value) => {
                    let phi_arg = self.lookup_value_phi_arg(func, make_query(value))?;
                    result.args.push((phi_arg, block));
                }
                ValuePhi::PhiInsn(_) => {
                    let phi_arg = self.compute_value_phi_for_cast(func, arg, make_query)?;
                    result.args.push((phi_arg, block));
                }
            }
        }

        Some(result.canonicalize())
    }

    /// Lookup value phi argument.
    fn lookup_value_phi_arg(
        &mut self,
        func: &mut Function,
        query: OwnedInstKey,
    ) -> Option<ValuePhi> {
        // Perform constant folding and insn simplification to canonicalize query.
        let query = if let Some(imm) = self.solver.perform_constant_folding(func, &query) {
            // If constant folding succeeds, no need to further query for the argument.
            return Some(ValuePhi::Value(imm));
        } else if let Some(simplified) = self.solver.perform_simplification(func, &query) {
            // If query is simplified to a value, then no need to further query for the argument.
            if let GvnInsn::Value(value) = simplified {
                return Some(ValuePhi::Value(value));
            } else {
                simplified
            }
        } else {
            GvnInsn::Expr(query)
        };

        // If class already exists for the query, return the leader value of the class.
        if let Some(class) = self.solver.insn_table.get(&query) {
            let leader = self.solver.class_leader(*class);
            return Some(ValuePhi::Value(leader));
        }

        // Try to further compute value phi for the query insn.
        self.compute_value_phi(func, &query)
    }

    /// Returns the `ValuePhi` if the value is defined by the phi insn or the class of the value
    /// is annotated with `ValuePhi`.
    /// The result reflects the reachability of the incoming edges,
    /// i.e. if a phi arg pass through an unreachable incoming edge, then the arg and blocks
    /// are omitted from the result.
    ///
    /// The result is sorted in the block order.
    fn get_phi_of(&mut self, func: &Function, value: ValueId) -> Option<ValuePhi> {
        if !self.visited.insert(value) {
            return None;
        }

        let class = self.solver.value_class(value);
        let phi_block = func.layout.inst_block(func.dfg.value_inst(value)?);

        // if the gvn_insn of the value class is phi, then create `ValuePhi::PhiInsn` from its args.
        if let GvnInsn::Expr(insn_expr) = &self.solver.classes[class].gvn_insn
            && let Some(phi_args) = insn_expr.phi_args()
        {
            let mut result = ValuePhiInsn::with_capacity(phi_block, phi_args.len());
            let in_edges = &self.solver.blocks[phi_block].in_edges;

            for &(value, from) in phi_args {
                // Phi arguments are keyed by predecessor block.
                if !matches!(
                    self.solver.reachable_edge_state(in_edges, from, phi_block),
                    ReachableEdgeState::None
                ) {
                    result.args.push((ValuePhi::Value(value), from))
                }
            }

            return Some(result.canonicalize());
        };

        // If the value is annotated with value phi, then return it.
        let class = self.solver.value_class(value);
        match &self.solver.classes[class].value_phi {
            value_phi @ Some(ValuePhi::PhiInsn(..)) => value_phi.clone(),
            _ => None,
        }
    }
}

/// Value phi that described in
/// `Detection of Redundant Expressions: A Complete and Polynomial-Time Algorithm in SSA`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum ValuePhi {
    /// `ValuePhi` may become value itself if the all arguments of the `ValuePhiInsn` is the same
    /// value.
    Value(ValueId),
    /// Phi instruction which is resolved to a "normal" phi insn in the later pass of `GvnSolver`.
    PhiInsn(ValuePhiInsn),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ValuePhiInsn {
    /// The Block where the phi insn should be inserted.
    block: BlockId,
    /// Argument of the value phi.
    args: Vec<(ValuePhi, BlockId)>,
}

impl ValuePhiInsn {
    fn with_capacity(block: BlockId, cap: usize) -> Self {
        Self {
            block,
            args: Vec::with_capacity(cap),
        }
    }

    /// Canonicalize the value phi insn and convert into value phi.
    fn canonicalize(mut self) -> ValuePhi {
        let first_arg = &self.args[0].0;

        // If all arguments are the same, then return first argument.
        if self
            .args
            .iter()
            .all(|(value_phi, _)| value_phi == first_arg)
        {
            first_arg.clone()
        } else {
            // Sort arguments in block order.
            self.args.sort_by_key(|(_, block)| *block);
            ValuePhi::PhiInsn(self)
        }
    }
}

/// A struct for redundant code/edge/block removal.
/// This struct also resolve value phis and insert phi insns to the appropriate block.
struct RedundantCodeRemover<'a> {
    solver: &'a GvnSolver,

    /// Record pairs of available class and representative value in bottom of blocks.
    /// This is necessary to decide whether the args of inserted phi functions are dominated by its
    /// definitions.
    avail_set: SecondaryMap<BlockId, FxHashMap<Class, ValueId>>,

    /// Record resolved value phis.
    resolved_value_phis: FxHashMap<ValuePhi, ValueId>,

    renames: FxHashMap<ValueId, ValueId>,
}

impl<'a> RedundantCodeRemover<'a> {
    fn new(solver: &'a GvnSolver) -> Self {
        Self {
            solver,
            avail_set: SecondaryMap::default(),
            resolved_value_phis: FxHashMap::default(),
            renames: FxHashMap::default(),
        }
    }

    fn change_to_alias(&mut self, func: &mut Function, value: ValueId, target: ValueId) {
        func.dfg.change_to_alias(value, target);
        self.renames.insert(value, target);
    }

    fn resolve_alias(&self, mut value: ValueId) -> ValueId {
        for _ in 0..1 + self.renames.len() {
            match self.renames.get(&value) {
                Some(v) => value = *v,
                None => return value,
            }
        }
        panic!("alias loop detected");
    }

    /// The entry function of redundant code removal.
    ///
    /// This function
    /// 1. Removes unreachable edges and blocks.
    /// 2. Recomputes control flow graph and dominator tree.
    /// 3. Removes redundant code.
    /// 4. Resolves value phis and insert phi insns to the appropriate blocks. If value phi
    ///    resolution fails, then the value and its defining insn is left as is.
    fn remove_redundant_code(
        &mut self,
        func: &mut Function,
        cfg: &mut ControlFlowGraph,
        domtree: &mut DomTree,
    ) {
        // Remove unreachable edges and blocks before redundant code removal to calculate precise
        // dominator tree.
        self.remove_unreachable_edges(func);

        // Recompute cfg and domtree.
        cfg.compute(func);
        domtree.compute(cfg);

        // Compute domtree traversable.
        let mut domtree_traversable = DominatorTreeTraversable::default();
        domtree_traversable.compute(domtree);

        let entry = func.layout.entry_block().unwrap();
        let mut blocks = vec![entry];
        while let Some(block) = blocks.pop() {
            blocks.extend_from_slice(domtree_traversable.children_of(block));
            self.remove_code_in_block(func, domtree, block);
        }

        // Resolve value phis in the function.
        let mut next_block = Some(entry);
        while let Some(block) = next_block {
            self.resolve_value_phi_in_block(func, block);
            next_block = func.layout.next_block_of(block);
        }
    }

    /// Remove redundant code in the block.
    fn remove_code_in_block(&mut self, func: &mut Function, domtree: &DomTree, block: BlockId) {
        // Get avail set in the top of the block.
        let mut avails = if block == func.layout.entry_block().unwrap() {
            // Insert always available values to avail set of the entry block.
            let mut avails = FxHashMap::default();
            for &avail in &self.solver.always_avail {
                let class = self.solver.value_class(avail);
                avails.insert(class, avail);
            }
            avails
        } else {
            // Use avails of the immediate dominator.
            let idom = domtree.idom_of(block).unwrap();
            self.avail_set[idom].clone()
        };

        let mut inserter = InstInserter::at_location(CursorLocation::BlockTop(block));
        loop {
            match inserter.loc() {
                CursorLocation::BlockTop(_) => {
                    inserter.proceed(func);
                }

                CursorLocation::BlockBottom(..) | CursorLocation::NoWhere => {
                    break;
                }

                CursorLocation::At(insn) => {
                    let block = inserter.block(func).unwrap();
                    if let Some(inst_result) = func.dfg.inst_result(insn) {
                        let class = self.solver.value_class(inst_result);
                        // Use representative value if the class is in avail set.
                        if !func.dfg.side_effect(insn).has_effect()
                            && let Some(value) = avails.get(&class)
                        {
                            self.change_to_alias(func, inst_result, *value);
                            inserter.remove_inst(func);
                            continue;
                        }

                        // Try rewrite phi insn to reflect edge's reachability.
                        self.rewrite_phi(func, insn, block);
                        avails.insert(class, inst_result);
                    }

                    inserter.proceed(func);
                }
            }
        }

        // Record avail set at the bottom of the block.
        self.avail_set[block] = avails;
    }

    /// Resolve value phis in the block.
    fn resolve_value_phi_in_block(&mut self, func: &mut Function, block: BlockId) {
        let mut inserter = InstInserter::at_location(CursorLocation::BlockTop(block));
        loop {
            match inserter.loc() {
                CursorLocation::BlockTop(_) => {
                    inserter.proceed(func);
                }

                CursorLocation::BlockBottom(..) | CursorLocation::NoWhere => {
                    break;
                }

                CursorLocation::At(insn) => {
                    let block = inserter.block(func).unwrap();
                    if let Some(inst_result) = func.dfg.inst_result(insn) {
                        // If value phi exists for the `inst_result` and its resolution succeeds,
                        // then use resolved phi value and remove insn.
                        let class = self.solver.value_class(inst_result);
                        if let Some(value_phi) = &self.solver.classes[class].value_phi {
                            let ty = func.dfg.value_ty(inst_result);
                            if self.is_value_phi_resolvable(value_phi, block) {
                                let value = self.resolve_value_phi(
                                    func,
                                    &mut inserter,
                                    value_phi,
                                    ty,
                                    block,
                                );

                                self.change_to_alias(func, inst_result, value);
                                inserter.remove_inst(func);
                                continue;
                            }
                        }
                    }

                    inserter.proceed(func);
                }
            }
        }
    }

    /// Returns `true` if the `value_phi` can be resolved, i.e. all phi args are dominated by
    /// in the `block`.
    fn is_value_phi_resolvable(&self, value_phi: &ValuePhi, block: BlockId) -> bool {
        if self.resolved_value_phis.contains_key(value_phi) {
            return true;
        }

        match value_phi {
            ValuePhi::Value(value) => {
                let class = self.solver.value_class(*value);
                self.avail_set[block].contains_key(&class)
            }
            ValuePhi::PhiInsn(phi_insn) => {
                for (value_phi, phi_block) in &phi_insn.args {
                    if !self.is_value_phi_resolvable(value_phi, *phi_block) {
                        return false;
                    }
                }

                true
            }
        }
    }

    /// Insert phi insn to appropriate location and returns the value that defined by
    /// the inserted phi insn.
    fn resolve_value_phi(
        &mut self,
        func: &mut Function,
        inserter: &mut InstInserter,
        value_phi: &ValuePhi,
        ty: Type,
        block: BlockId,
    ) -> ValueId {
        debug_assert!(self.is_value_phi_resolvable(value_phi, block));

        if let Some(value) = self.resolved_value_phis.get(value_phi) {
            return *value;
        }

        match value_phi {
            ValuePhi::Value(value) => {
                let class = self.solver.value_class(*value);
                self.avail_set[block].get(&class).copied().unwrap()
            }

            ValuePhi::PhiInsn(phi_insn) => {
                // Memorize current inserter loc to restore later.
                let current_inserter_loc = inserter.loc();

                // Resolve phi value's arguments and append them to the newly inserted phi.
                let mut phi_args = Vec::with_capacity(phi_insn.args.len());
                for (value_phi, phi_block) in &phi_insn.args {
                    let resolved =
                        self.resolve_value_phi(func, inserter, value_phi, ty, *phi_block);
                    phi_args.push((self.resolve_alias(resolved), *phi_block));
                }
                let phi = func.dfg.make_phi(phi_args);

                // Insert new phi insn to top of the phi_insn block.
                inserter.set_location(CursorLocation::BlockTop(phi_insn.block));
                let insn = inserter.insert_inst_data(func, phi);
                let result = inserter.make_result(func, insn, ty);
                inserter.attach_result(func, insn, result);

                // Restore the inserter loc.
                inserter.set_location(current_inserter_loc);

                // Store resolved value phis.
                self.resolved_value_phis.insert(value_phi.clone(), result);

                // Returns inserted phi insn result.
                result
            }
        }
    }

    /// Remove unreachable edges and blocks.
    fn remove_unreachable_edges(&self, func: &mut Function) {
        let entry_block = func.layout.entry_block().unwrap();
        let mut inserter = InstInserter::at_location(CursorLocation::BlockTop(entry_block));
        let mut rebuild_users = false;

        loop {
            match inserter.loc() {
                CursorLocation::BlockTop(block) => {
                    if !self.solver.blocks[block].reachable {
                        inserter.remove_block(func);
                    } else {
                        inserter.proceed(func);
                    }
                }

                CursorLocation::BlockBottom(..) => inserter.proceed(func),

                CursorLocation::At(insn) => {
                    let block = inserter.block(func).unwrap();
                    if let Some(br_table) = func.dfg.cast_br_table(insn).cloned() {
                        let unreachable: FxHashSet<_> =
                            self.solver.unreachable_out_edges(block).copied().collect();

                        if !unreachable.is_empty() {
                            let out_edges = &self.solver.blocks[block].out_edges;
                            let table_offset = usize::from(br_table.default().is_some());
                            debug_assert_eq!(
                                out_edges.len(),
                                br_table.table().len() + table_offset
                            );

                            let mut default = *br_table.default();
                            if default.is_some() && unreachable.contains(&out_edges[0]) {
                                default = None;
                            }

                            let mut table = Vec::with_capacity(br_table.table().len());
                            for (idx, (value, dest)) in br_table.table().iter().enumerate() {
                                let edge = out_edges[table_offset + idx];
                                if !unreachable.contains(&edge) {
                                    table.push((*value, *dest));
                                }
                            }

                            let mut dests = FxHashSet::default();
                            if let Some(default) = default {
                                dests.insert(default);
                            }
                            for (_, dest) in &table {
                                dests.insert(*dest);
                            }

                            let is = func.inst_set();
                            func.dfg.insts[insn] = match dests.len() {
                                0 => Box::new(Unreachable::new_unchecked(is)),
                                1 => Box::new(Jump::new(is.jump(), *dests.iter().next().unwrap())),
                                _ => {
                                    let mut new_br_table = br_table.clone();
                                    *new_br_table.default_mut() = default;
                                    *new_br_table.table_mut() = table;
                                    Box::new(new_br_table)
                                }
                            };
                            rebuild_users = true;
                        }
                    } else if func.dfg.is_branch(insn) {
                        for &out_edge in self.solver.unreachable_out_edges(block) {
                            let edge_data = self.solver.edge_data(out_edge);
                            func.dfg.remove_branch_dest(insn, edge_data.to);
                        }
                    }
                    inserter.proceed(func);
                }

                CursorLocation::NoWhere => break,
            }
        }

        if rebuild_users {
            func.rebuild_users();
        }
    }

    /// Rewrite phi insn when there is at least one unreachable incoming edge to the block.
    fn rewrite_phi(&self, func: &mut Function, insn: InstId, block: BlockId) {
        if !func.dfg.is_phi(insn) {
            return;
        }

        let edges = &self.solver.blocks[block].in_edges;
        func.dfg.untrack_inst(insn);
        let phi = func.dfg.cast_phi_mut(insn).unwrap();
        phi.retain(|from| {
            !matches!(
                self.solver.reachable_edge_state(edges, from, block),
                ReachableEdgeState::None
            )
        });
        func.dfg.attach_user(insn);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ReachableEdgeState {
    None,
    One(Edge),
    Many,
}

#[cfg(test)]
mod tests {
    use super::{GvnInsn, GvnSolver, ValuePhi};
    use sonatina_ir::ValueId;

    #[test]
    fn update_class_value_phi_keeps_value_phi_table_synchronized() {
        let mut solver = GvnSolver::new();
        let class = solver.make_class(GvnInsn::Value(ValueId::from_u32(0)), None);

        let phi1 = ValuePhi::Value(ValueId::from_u32(1));
        assert!(solver.update_class_value_phi(class, Some(phi1.clone())));
        assert_eq!(solver.value_phi_table.get(&phi1), Some(&class));

        let phi2 = ValuePhi::Value(ValueId::from_u32(2));
        assert!(solver.update_class_value_phi(class, Some(phi2.clone())));
        assert!(!solver.value_phi_table.contains_key(&phi1));
        assert_eq!(solver.value_phi_table.get(&phi2), Some(&class));

        assert!(solver.update_class_value_phi(class, None));
        assert!(!solver.value_phi_table.contains_key(&phi2));
        assert!(!solver.update_class_value_phi(class, None));
    }
}
