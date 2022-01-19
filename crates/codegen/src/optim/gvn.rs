//! This module contains a solver for complete Global Value Numbering.
//!
//! The algorithm here is based on Karthik Gargi.: A sparse algorithm for predicated global value numbering:
//! PLDI 2002 Pages 45–56: <https://dl.acm.org/doi/10.1145/512529.512536>.
//!
//! Also, to accomplish complete GVN, we use the `ValuePhi` concept which is described in
//! Rekha R. Pai.: Detection of Redundant Expressions: A Complete and Polynomial-Time Algorithm in SSA:
//! APLAS 2015 pp49-65: <https://link.springer.com/chapter/10.1007/978-3-319-26529-2_4>

use std::collections::BTreeSet;

use cranelift_entity::{entity_impl, packed_option::PackedOption, PrimaryMap, SecondaryMap};
use fxhash::{FxHashMap, FxHashSet};

use crate::{
    cfg::ControlFlowGraph,
    domtree::{DomTree, DominatorTreeTraversable},
    ir::{
        func_cursor::{CursorLocation, FuncCursor, InsnInserter},
        insn::{BinaryOp, CastOp, InsnData, UnaryOp},
        Block, DataFlowGraph, Function, Immediate, Insn, Type, Value,
    },
    TargetIsa,
};

use super::{constant_folding, simplify_impl};

///  An initial class that assigned to all values.
///  If a value still has the initial class after value numbering, then the insn that defines the value is
///  unreachable.
const INITIAL_CLASS: Class = Class(0);

/// The rank reserved for immediates.
const IMMEDIATE_RANK: u32 = 0;

/// A GVN solver.
#[derive(Debug)]
pub struct GvnSolver<'isa> {
    /// Store classes.
    classes: PrimaryMap<Class, ClassData>,

    /// Maps [`Value`] to [`GvnValueData`].
    values: SecondaryMap<Value, GvnValueData>,

    /// Maps [`GvnInsn`] to [`Class`].
    insn_table: FxHashMap<GvnInsn, Class>,

    /// Store edges.
    edges: PrimaryMap<Edge, EdgeData>,

    /// Maps [`Block`] to [`GvnBlockData`]
    blocks: SecondaryMap<Block, GvnBlockData>,

    value_phi_table: FxHashMap<ValuePhi, Class>,

    /// Hold always available values, i.e. immediates or function arguments.
    always_avail: Vec<Value>,

    isa: &'isa TargetIsa,
}

impl<'isa> GvnSolver<'isa> {
    pub fn new(isa: &'isa TargetIsa) -> Self {
        Self {
            classes: PrimaryMap::default(),
            values: SecondaryMap::default(),
            insn_table: FxHashMap::default(),
            edges: PrimaryMap::default(),
            blocks: SecondaryMap::default(),
            value_phi_table: FxHashMap::default(),
            always_avail: Vec::default(),
            isa,
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
            gvn_insn: GvnInsn::Value(Value(u32::MAX)),
            value_phi: None,
        });
        debug_assert!(self.classes.len() == 1);

        // Make and assign classes for immediate values.
        for &value in func.dfg.immediates.values() {
            self.assign_class_to_imm_value(value);
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

            for insn in func.layout.iter_insn(block) {
                if let Some(insn_result) = func.dfg.insn_result(insn) {
                    self.values[insn_result].rank = rank;
                    rank += 1;
                }

                // Make edge data and attach the edge to the originating block and the destinating block.
                match func.dfg.insn_data(insn) {
                    InsnData::Jump { dests, .. } => {
                        let dest = dests[0];
                        self.add_edge_info(block, dest, None, None, None);
                    }

                    InsnData::Branch { args, dests } => {
                        let cond = args[0];
                        debug_assert_eq!(func.dfg.value_ty(cond), &Type::I1);

                        let then_block = dests[0];
                        let else_block = dests[1];

                        // Create predicate for each edges.
                        // TODO: We need more elaborate representation of predicate.
                        let then_predicate = func.dfg.value_insn(cond).map(|insn| {
                            let insn_data = func.dfg.insn_data(insn).clone();
                            self.perform_predicate_simplification(&mut func.dfg, insn_data)
                        });
                        let else_predicate = self.perform_predicate_simplification(
                            &mut func.dfg,
                            InsnData::unary(UnaryOp::Not, cond),
                        );

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
                            Some(else_predicate),
                            Some(else_imm),
                        );
                    }

                    InsnData::BrTable {
                        args,
                        default,
                        table,
                    } => {
                        // Add edge destinating to default block.
                        if let Some(default) = default {
                            self.add_edge_info(block, *default, None, None, None);
                        }
                        let cond = args[0];

                        for (value, dest) in args[1..].iter().zip(table.iter()) {
                            self.add_edge_info(block, *dest, Some(cond), None, Some(*value));
                        }
                    }

                    _ => {}
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

                let mut next_insn = func.layout.first_insn_of(block);
                while let Some(insn) = next_insn {
                    // Reassign congruence class to the result value of the insn.
                    if let Some(insn_result) = func.dfg.insn_result(insn) {
                        changed |= self.reassign_congruence(func, domtree, insn, insn_result);
                    }
                    next_insn = func.layout.next_insn_of(insn);
                }

                // If insn is terminator, analyze it to update edge and block reachability.
                if let Some(last_insn) = func.layout.last_insn_of(block) {
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
        block: Block,
        insn: Insn,
    ) -> bool {
        match func.dfg.insn_data(insn) {
            InsnData::Jump { .. } => {
                let out_edges = &self.blocks[block].out_edges;
                debug_assert_eq!(out_edges.len(), 1);
                let out_edge = out_edges[0];
                self.mark_edge_reachable(out_edge)
            }

            InsnData::Branch {
                args,
                dests: [then_dest, else_dest],
            } => {
                let cond = args[0];
                let out_edges = &self.blocks[block].out_edges;
                debug_assert_eq!(out_edges.len(), 2);

                let then_edge = *out_edges
                    .iter()
                    .find(|edge| self.edge_data(**edge).to == *then_dest)
                    .unwrap();
                let else_edge = *out_edges
                    .iter()
                    .find(|edge| self.edge_data(**edge).to == *else_dest)
                    .unwrap();

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

            InsnData::BrTable {
                args,
                default,
                table,
            } => {
                let cond = args[0];

                // Iterate table entry, if one of the entry value is congruent to cond, then mark
                // the edge as reachable and stop marking.
                for dest in table {
                    let edge = self.find_edge(&self.blocks[block].out_edges, block, *dest);
                    if self.infer_edge_reachability(func, cond, edge, domtree) {
                        return self.mark_edge_reachable(edge);
                    }
                }

                // If none of entry values is congruent to the cond, then mark all edges as
                // reachable.
                let mut changed = false;
                if let Some(default) = default {
                    let edge_to_default =
                        self.find_edge(&self.blocks[block].out_edges, block, *default);
                    changed |= self.mark_edge_reachable(edge_to_default);
                }
                for dest in table {
                    let edge = self.find_edge(&self.blocks[block].out_edges, block, *dest);
                    changed |= self.mark_edge_reachable(edge);
                }

                changed
            }

            _ => false,
        }
    }

    /// Search and assign congruence class to the `insn_result`.
    /// Returns `true` if congruence class is changed.
    fn reassign_congruence(
        &mut self,
        func: &mut Function,
        domtree: &DomTree,
        insn: Insn,
        insn_result: Value,
    ) -> bool {
        // Perform symbolic evaluation for the insn.
        let block = func.layout.insn_block(insn);
        let gvn_insn = self.perform_symbolic_evaluation(
            func,
            domtree,
            func.dfg.insn_data(insn).clone(),
            block,
        );

        // If insn has a side effect, create new class if the value still belongs to
        // `INITIAL_CLASS`.
        if func.dfg.has_side_effect(insn) {
            if self.value_class(insn_result) == INITIAL_CLASS {
                let class = self.make_class(gvn_insn, None);
                self.assign_class(insn_result, class);
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
            changed |= self.recompute_value_phi(func, &gvn_insn, insn_result);
            class
        } else if let Some(value_phi) =
            ValuePhiFinder::new(self, insn_result).compute_value_phi(func, &gvn_insn)
        {
            if let Some(class) = self.value_phi_table.get(&value_phi) {
                *class
            } else {
                self.make_class(gvn_insn.clone(), Some(value_phi))
            }
        } else {
            self.make_class(gvn_insn.clone(), None)
        };

        let old_class = self.value_class(insn_result);
        if old_class == new_class {
            changed
        } else {
            self.assign_class(insn_result, new_class);
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
        insn_result: Value,
    ) -> bool {
        let value_phi = ValuePhiFinder::new(self, insn_result).compute_value_phi(func, insn_data);
        let class = self.value_class(insn_result);

        let old_value_phi = &mut self.classes[class].value_phi;

        if &value_phi == old_value_phi {
            false
        } else {
            *old_value_phi = value_phi;
            true
        }
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
        cond: Value,
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
        value: Value,
        target_block: Block,
    ) -> Value {
        let mut rep_value = self.leader(value);

        let mut current_block = Some(target_block);
        // Try to infer value until the representative value becomes immediate or current block
        // becomes `None`.
        while current_block.is_some() && (!func.dfg.is_imm(rep_value)) {
            let block = current_block.unwrap();
            if let Some(dominant_edge) = self.dominant_reachable_in_edges(block) {
                // Stop looking up the value to avoid infinite lookup loop.
                if self.is_back_edge(dominant_edge) {
                    break;
                }

                // If the value inference succeeds, restart inference with the new representative value.
                if let Some(value) = self.infer_value_impl(dominant_edge, rep_value) {
                    rep_value = value;
                    current_block = Some(target_block);
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
        value: Value,
        edge: Edge,
    ) -> Value {
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
    fn infer_value_impl(&self, edge: Edge, value: Value) -> Option<Value> {
        let edge_data = self.edge_data(edge);
        let edge_cond = edge_data.cond.expand()?;
        // If value is congruent to edge cond value, then return resolved cond of the edge.
        if self.is_congruent_value(edge_cond, value) {
            return Some(edge_data.resolved_cond.unwrap());
        }

        let predicate = edge_data.predicate.as_ref()?;

        match predicate {
            InsnData::Binary {
                code: BinaryOp::Eq,
                args: [lhs, rhs],
            } => {
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
            _ => None,
        }
    }

    /// Returns reachable incoming edges of the block.
    fn reachable_in_edges(&self, block: Block) -> impl Iterator<Item = &Edge> {
        self.blocks[block]
            .in_edges
            .iter()
            .filter(|edge| self.edge_data(**edge).reachable)
    }

    /// Returns unreachable outgoing edges of the block.
    fn unreachable_out_edges(&self, block: Block) -> impl Iterator<Item = &Edge> {
        self.blocks[block]
            .out_edges
            .iter()
            .filter(|edge| !self.edge_data(**edge).reachable)
    }

    /// Returns the incoming edge if the edge is only one reachable edge to the block.
    fn dominant_reachable_in_edges(&self, block: Block) -> Option<Edge> {
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
    fn is_congruent_value(&self, lhs: Value, rhs: Value) -> bool {
        let lhs_class = self.values[lhs].class;
        let rhs_class = self.values[rhs].class;
        (lhs_class == rhs_class) && (lhs_class != INITIAL_CLASS)
    }

    /// Perform symbolic evaluation for the `insn_data`.
    fn perform_symbolic_evaluation(
        &mut self,
        func: &mut Function,
        domtree: &DomTree,
        insn_data: InsnData,
        block: Block,
    ) -> GvnInsn {
        // Get canonicalized insn by swapping arguments with leader values.
        //
        // If the insn is commutative, then argument order is also canonicalized.
        // And if the insn is phi, arguments from unreachable edges are omitted.
        let insn_data = match insn_data {
            InsnData::Unary { code, args: [arg] } => {
                let arg = self.infer_value_at_block(func, domtree, arg, block);
                InsnData::unary(code, arg)
            }

            InsnData::Binary {
                code,
                args: [lhs, rhs],
            } => {
                let mut lhs = self.infer_value_at_block(func, domtree, lhs, block);
                let mut rhs = self.infer_value_at_block(func, domtree, rhs, block);
                // Canonicalize the argument order if the insn is commutative.
                if code.is_commutative() && self.value_rank(rhs) < self.value_rank(lhs) {
                    std::mem::swap(&mut lhs, &mut rhs);
                }

                InsnData::binary(code, lhs, rhs)
            }

            InsnData::Cast {
                code,
                args: [arg],
                ty,
            } => {
                let arg = self.infer_value_at_block(func, domtree, arg, block);
                InsnData::cast(code, arg, ty)
            }

            InsnData::Store { .. }
            | InsnData::Load { .. }
            | InsnData::Jump { .. }
            | InsnData::Branch { .. }
            | InsnData::BrTable { .. }
            | InsnData::Alloca { .. }
            | InsnData::Return { .. } => insn_data.clone(),

            InsnData::Phi { values, blocks, ty } => {
                let edges = &self.blocks[block].in_edges;

                let mut phi_args = Vec::with_capacity(values.len());
                for (&value, &from) in (values).iter().zip(blocks.iter()) {
                    let edge = self.find_edge(edges, from, block);
                    // Ignore an argument from an unreachable block.
                    if !self.edge_data(edge).reachable {
                        continue;
                    }

                    let inferred_value = self.infer_value_at_edge(func, domtree, value, edge);
                    phi_args.push((inferred_value, from));
                }

                // Canonicalize the argument order by block rank.
                phi_args.sort_unstable_by(|(_, block1), (_, block2)| {
                    self.block_rank(*block1).cmp(&self.block_rank(*block2))
                });

                InsnData::Phi {
                    values: phi_args.iter().map(|(value, _)| *value).collect(),
                    blocks: phi_args.iter().map(|(_, block)| *block).collect(),
                    ty,
                }
            }
        };

        if let Some(imm) = self.perform_constant_folding(func, &insn_data) {
            GvnInsn::Value(imm)
        } else if let Some(result) = self.perform_simplification(&mut func.dfg, &insn_data) {
            result
        } else {
            GvnInsn::Insn(insn_data)
        }
    }

    /// Perform constant folding.
    fn perform_constant_folding(
        &mut self,
        func: &mut Function,
        insn_data: &InsnData,
    ) -> Option<Value> {
        constant_folding::fold_constant(&func.dfg, insn_data)
            .map(|imm| self.make_imm(&mut func.dfg, imm))
    }

    /// Perform insn simplification.
    fn perform_simplification(
        &mut self,
        dfg: &mut DataFlowGraph,
        insn_data: &InsnData,
    ) -> Option<GvnInsn> {
        simplify_impl::simplify_insn_data(dfg, self.isa, insn_data.clone()).map(|res| match res {
            simplify_impl::SimplifyResult::Value(value) => {
                // Handle immediate specially because we need to assign a new class to the immediate.
                // if the immediate is newly created in simplification process.
                if let Some(imm) = dfg.value_imm(value) {
                    GvnInsn::Value(self.make_imm(dfg, imm))
                } else {
                    GvnInsn::Value(value)
                }
            }
            simplify_impl::SimplifyResult::Insn(insn) => GvnInsn::Insn(insn),
        })
    }

    /// Perform predicate simplification.
    fn perform_predicate_simplification(
        &mut self,
        dfg: &mut DataFlowGraph,
        insn_data: InsnData,
    ) -> InsnData {
        if let Some(GvnInsn::Insn(insn)) = self.perform_simplification(dfg, &insn_data) {
            insn
        } else {
            insn_data.clone()
        }
    }

    /// Make edge data and append incoming/outgoing edges of corresponding blocks.
    fn add_edge_info(
        &mut self,
        from: Block,
        to: Block,
        cond: Option<Value>,
        predicate: Option<InsnData>,
        resolved_cond: Option<Value>,
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
    fn assign_class(&mut self, value: Value, class: Class) {
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
        if let Some(insn_class) = self.insn_table.get_mut(&old_class_data.gvn_insn) {
            if *insn_class == old_class && old_class_data.values.is_empty() {
                self.insn_table.remove(&old_class_data.gvn_insn);
                if let Some(value_phi) = &old_class_data.value_phi {
                    self.value_phi_table.remove(value_phi);
                }
            }
        }
    }

    /// Make value from immediate, also make a corresponding congruence class and update
    /// `insn_table` for the immediate value if they don't exist yet.
    fn make_imm(&mut self, dfg: &mut DataFlowGraph, imm: impl Into<Immediate>) -> Value {
        // `make_imm_value` return always same value for the same immediate.
        let value = dfg.make_imm_value(imm);

        // Assign new class to the `imm`.
        self.assign_class_to_imm_value(value);

        value
    }

    /// Make and assign class to immediate value.
    fn assign_class_to_imm_value(&mut self, value: Value) {
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

    /// Returns `true` if the edge is backedge.
    fn is_back_edge(&self, edge: Edge) -> bool {
        let from = self.edge_data(edge).from;
        let to = self.edge_data(edge).to;

        self.blocks[to].rank <= self.blocks[from].rank
    }

    /// Returns the leader value of the congruent class to which `value` belongs.
    fn leader(&self, value: Value) -> Value {
        let class = self.values[value].class;

        self.class_data(class).values.iter().next().unwrap().1
    }

    /// Returns the leader value of the congruent class.
    /// This method is mainly for [`ValuePhiFinder`], use [`Self::leader`] whenever possible.
    fn class_leader(&self, class: Class) -> Value {
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
    fn value_class(&self, value: Value) -> Class {
        self.values[value].class
    }

    /// Returns the rank of the value.
    fn value_rank(&self, value: Value) -> u32 {
        self.values[value].rank
    }

    /// Returns the rank of the block.
    fn block_rank(&self, block: Block) -> u32 {
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

    /// Find an edge that have corresponding `from` and `to` block.
    /// This method panics if an edge isn't found.
    fn find_edge(&self, edges: &[Edge], from: Block, to: Block) -> Edge {
        edges
            .iter()
            .find(|edge| {
                let data = self.edge_data(**edge);
                data.from == from && data.to == to
            })
            .copied()
            .unwrap()
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
    values: BTreeSet<(u32, Value)>,

    /// Representative insn of the class.
    gvn_insn: GvnInsn,

    /// A value phi of the class.
    value_phi: Option<ValuePhi>,
}

/// A collection of value data used by `GvnSolver`.
#[derive(Debug, Clone, PartialEq)]
struct GvnValueData {
    /// A class to which the value belongs.
    class: Class,

    /// A rank of the value.
    /// If the value is immediate, then the rank is 0, otherwise the rank is assigned to each value in RPO order.
    /// This ensures `rankA` is defined earlier than `rankB` iff `rankA` < `rankB`.
    rank: u32,
}

impl Default for GvnValueData {
    fn default() -> Self {
        Self {
            class: INITIAL_CLASS,
            rank: 0,
        }
    }
}

/// A insn data which represents canonicalized/simplified/folded insn.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum GvnInsn {
    /// A value which occurs when insn is simplified/folded to value.
    Value(Value),
    /// An insn data.
    Insn(InsnData),
}

impl From<Value> for GvnInsn {
    fn from(value: Value) -> Self {
        Self::Value(value)
    }
}

impl From<InsnData> for GvnInsn {
    fn from(insn: InsnData) -> Self {
        Self::Insn(insn)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash, PartialOrd, Ord)]
struct Edge(u32);
entity_impl!(Edge);

#[derive(Debug, Clone)]
struct EdgeData {
    /// An originating block.
    from: Block,

    /// A destinating block.
    to: Block,

    /// Hold a condition value if branch is conditional.
    cond: PackedOption<Value>,

    /// Hold a predicate insn if branch is conditional.
    predicate: Option<InsnData>,

    /// An immediate to which cond is resolved if the edge is selected.
    resolved_cond: PackedOption<Value>,

    /// `true` if the edge is reachable.
    reachable: bool,
}

#[derive(Debug, Default, Clone)]
struct GvnBlockData {
    /// Incoming edges.
    in_edges: Vec<Edge>,

    /// Outgoing edges.
    out_edges: Vec<Edge>,

    /// `true` if the block is reachable.
    reachable: bool,

    /// A rank of the block.
    /// The rank definition is same as `GvnValueData::rank`.
    rank: u32,
}

/// This struct finds value phi that described in
/// `Detection of Redundant Expressions: A Complete and Polynomial-Time Algorithm in SSA`.
struct ValuePhiFinder<'isa, 'a> {
    solver: &'a mut GvnSolver<'isa>,
    /// Hold visited values to prevent infinite loop.
    visited: FxHashSet<Value>,
}

impl<'isa, 'a> ValuePhiFinder<'isa, 'a> {
    fn new(solver: &'a mut GvnSolver<'isa>, insn_result: Value) -> Self {
        let mut visited = FxHashSet::default();
        visited.insert(insn_result);
        Self { solver, visited }
    }

    /// Main entry of this struct.
    fn compute_value_phi(&mut self, func: &mut Function, gvn_insn: &GvnInsn) -> Option<ValuePhi> {
        // Break infinite loop if the block has been already visited.
        let insn_data = if let GvnInsn::Insn(insn_data) = gvn_insn {
            insn_data
        } else {
            return None;
        };

        match insn_data {
            InsnData::Unary { code, args: [arg] } => {
                let arg = self.get_phi_of(func, *arg)?;
                self.compute_value_phi_for_unary(func, *code, arg)
            }

            InsnData::Binary {
                code,
                args: [lhs, rhs],
            } => {
                let (lhs, rhs) = if lhs == rhs {
                    let lhs_phi = self.get_phi_of(func, *lhs)?;
                    let rhs_phi = lhs_phi.clone();
                    (lhs_phi, rhs_phi)
                } else {
                    match (self.get_phi_of(func, *lhs), self.get_phi_of(func, *rhs)) {
                        (Some(lhs_phi), Some(rhs_phi)) => (lhs_phi, rhs_phi),
                        (Some(lhs_phi), None) => (lhs_phi, ValuePhi::Value(*rhs)),
                        (None, Some(rhs_phi)) => (ValuePhi::Value(*lhs), rhs_phi),
                        (None, None) => return None,
                    }
                };

                self.compute_value_phi_for_binary(func, *code, lhs, rhs)
            }

            InsnData::Cast {
                code,
                args: [arg],
                ty,
            } => {
                let arg = self.get_phi_of(func, *arg)?;
                self.compute_value_phi_for_cast(func, *code, arg, ty)
            }

            _ => None,
        }
    }

    fn compute_value_phi_for_unary(
        &mut self,
        func: &mut Function,
        code: UnaryOp,
        value_phi: ValuePhi,
    ) -> Option<ValuePhi> {
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
                    let query_insn = InsnData::unary(code, value);
                    let phi_arg = self.lookup_value_phi_arg(func, query_insn)?;
                    result.args.push((phi_arg, block));
                }
                ValuePhi::PhiInsn(_) => {
                    let phi_arg = self.compute_value_phi_for_unary(func, code, arg)?;
                    result.args.push((phi_arg, block));
                }
            }
        }

        Some(result.canonicalize())
    }

    fn compute_value_phi_for_binary(
        &mut self,
        func: &mut Function,
        code: BinaryOp,
        lhs: ValuePhi,
        rhs: ValuePhi,
    ) -> Option<ValuePhi> {
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
                    if code.is_commutative()
                        && self.solver.value_rank(rhs_value) < self.solver.value_rank(lhs_value)
                    {
                        // Reorder args if the insn is commutative.
                        std::mem::swap(&mut lhs_value, &mut rhs_value);
                    }
                    let query_insn = InsnData::binary(code, lhs_value, rhs_value);
                    let phi_arg = self.lookup_value_phi_arg(func, query_insn)?;
                    result.args.push((phi_arg, block));
                }
                (lhs_arg, rhs_arg) => {
                    let phi_arg =
                        self.compute_value_phi_for_binary(func, code, lhs_arg, rhs_arg)?;
                    result.args.push((phi_arg, block));
                }
            }
        }

        Some(result.canonicalize())
    }

    fn compute_value_phi_for_cast(
        &mut self,
        func: &mut Function,
        code: CastOp,
        value_phi: ValuePhi,
        ty: &Type,
    ) -> Option<ValuePhi> {
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
                    let query_insn = InsnData::cast(code, value, ty.clone());
                    let phi_arg = self.lookup_value_phi_arg(func, query_insn)?;
                    result.args.push((phi_arg, block));
                }
                ValuePhi::PhiInsn(_) => {
                    let phi_arg = self.compute_value_phi_for_cast(func, code, arg, ty)?;
                    result.args.push((phi_arg, block));
                }
            }
        }

        Some(result.canonicalize())
    }

    /// Lookup value phi argument.
    fn lookup_value_phi_arg(&mut self, func: &mut Function, query: InsnData) -> Option<ValuePhi> {
        // Perform constant folding and insn simplification to canonicalize query.
        let query = if let Some(imm) = self.solver.perform_constant_folding(func, &query) {
            // If constant folding succeeds, no need to further query for the argument.
            return Some(ValuePhi::Value(imm));
        } else if let Some(simplified) = self.solver.perform_simplification(&mut func.dfg, &query) {
            // If query is simplified to a value, then no need to further query for the argument.
            if let GvnInsn::Value(value) = simplified {
                return Some(ValuePhi::Value(value));
            } else {
                simplified
            }
        } else {
            GvnInsn::Insn(query)
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
    fn get_phi_of(&mut self, func: &Function, value: Value) -> Option<ValuePhi> {
        if !self.visited.insert(value) {
            return None;
        }

        let class = self.solver.value_class(value);
        let phi_block = func.layout.insn_block(func.dfg.value_insn(value)?);

        // if the gvn_insn of the value class is phi, then create `ValuePhi::Insn` from its args.
        if let GvnInsn::Insn(InsnData::Phi { values, blocks, .. }) =
            &self.solver.classes[class].gvn_insn
        {
            let mut result = ValuePhiInsn::with_capacity(phi_block, values.len());
            let in_edges = &self.solver.blocks[phi_block].in_edges;

            for (value, from) in values.iter().copied().zip(blocks.iter().copied()) {
                let edge = self.solver.find_edge(in_edges, from, phi_block);
                // If the corresponding edge is reachable, then add to the result.
                if self.solver.edges[edge].reachable {
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
    Value(Value),
    /// Phi instruction which is resolved to a "normal" phi insn in the later pass of `GvnSolver`.
    PhiInsn(ValuePhiInsn),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ValuePhiInsn {
    /// The Block where the phi insn should be inserted.
    block: Block,
    /// Argument of the value phi.
    args: Vec<(ValuePhi, Block)>,
}

impl ValuePhiInsn {
    fn with_capacity(block: Block, cap: usize) -> Self {
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
struct RedundantCodeRemover<'isa, 'a> {
    solver: &'a GvnSolver<'isa>,

    /// Record pairs of available class and representative value in bottom of blocks.
    /// This is necessary to decide whether the args of inserted phi functions are dominated by its
    /// definitions.
    avail_set: SecondaryMap<Block, FxHashMap<Class, Value>>,

    /// Record resolved value phis.
    resolved_value_phis: FxHashMap<ValuePhi, Value>,
}

impl<'isa, 'a> RedundantCodeRemover<'isa, 'a> {
    fn new(solver: &'a GvnSolver<'isa>) -> Self {
        Self {
            solver,
            avail_set: SecondaryMap::default(),
            resolved_value_phis: FxHashMap::default(),
        }
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
    fn remove_code_in_block(&mut self, func: &mut Function, domtree: &DomTree, block: Block) {
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

        let mut inserter =
            InsnInserter::new(func, self.solver.isa, CursorLocation::BlockTop(block));
        loop {
            match inserter.loc() {
                CursorLocation::BlockTop(_) => {
                    inserter.proceed();
                }

                CursorLocation::BlockBottom(..) | CursorLocation::NoWhere => {
                    break;
                }

                CursorLocation::At(insn) => {
                    let block = inserter.block().unwrap();
                    if let Some(insn_result) = inserter.func().dfg.insn_result(insn) {
                        let class = self.solver.value_class(insn_result);

                        // Use representative value if the class is in avail set.
                        if let Some(value) = avails.get(&class) {
                            inserter.func_mut().dfg.change_to_alias(insn_result, *value);
                            inserter.remove_insn();
                            continue;
                        }

                        // Try rewrite phi insn to reflect edge's reachability.
                        self.rewrite_phi(inserter.func_mut(), insn, block);
                        avails.insert(class, insn_result);
                    }

                    inserter.proceed();
                }
            }
        }

        // Record avail set at the bottom of the block.
        self.avail_set[block] = avails;
    }

    /// Resolve value phis in the block.
    fn resolve_value_phi_in_block(&mut self, func: &mut Function, block: Block) {
        let mut inserter =
            InsnInserter::new(func, self.solver.isa, CursorLocation::BlockTop(block));
        loop {
            match inserter.loc() {
                CursorLocation::BlockTop(_) => {
                    inserter.proceed();
                }

                CursorLocation::BlockBottom(..) | CursorLocation::NoWhere => {
                    break;
                }

                CursorLocation::At(insn) => {
                    let block = inserter.block().unwrap();
                    if let Some(insn_result) = inserter.func().dfg.insn_result(insn) {
                        // If value phi exists for the `insn_result` and its resolution succeeds,
                        // then use resolved phi value and remove insn.
                        let class = self.solver.value_class(insn_result);
                        if let Some(value_phi) = &self.solver.classes[class].value_phi {
                            let ty = inserter.func().dfg.value_ty(insn_result).clone();
                            if self.is_value_phi_resolvable(value_phi, block) {
                                let value =
                                    self.resolve_value_phi(&mut inserter, value_phi, ty, block);
                                inserter.func_mut().dfg.change_to_alias(insn_result, value);
                                inserter.remove_insn();
                                continue;
                            }
                        }
                    }

                    inserter.proceed();
                }
            }
        }
    }

    /// Returns `true` if the `value_phi` can be resolved, i.e. all phi args are dominated by
    /// in the `block`.
    fn is_value_phi_resolvable(&self, value_phi: &ValuePhi, block: Block) -> bool {
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
        inserter: &mut InsnInserter,
        value_phi: &ValuePhi,
        ty: Type,
        block: Block,
    ) -> Value {
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

                // Resolve phi value's arguments and append them to the newly `InsnData::Phi`.
                let mut phi = InsnData::phi(ty.clone());
                for (value_phi, phi_block) in &phi_insn.args {
                    let resolved =
                        self.resolve_value_phi(inserter, value_phi, ty.clone(), *phi_block);
                    phi.append_phi_arg(resolved, *phi_block);
                }

                // Insert new phi insn to top of the phi_insn block.
                inserter.set_loc(CursorLocation::BlockTop(phi_insn.block));
                let insn = inserter.insert_insn_data(phi);
                let result = inserter.make_result(insn).unwrap();
                inserter.attach_result(insn, result);

                // Restore the inserter loc.
                inserter.set_loc(current_inserter_loc);

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
        let mut inserter =
            InsnInserter::new(func, self.solver.isa, CursorLocation::BlockTop(entry_block));

        loop {
            match inserter.loc() {
                CursorLocation::BlockTop(block) => {
                    if !self.solver.blocks[block].reachable {
                        inserter.remove_block();
                    } else {
                        inserter.proceed();
                    }
                }

                CursorLocation::BlockBottom(..) => inserter.proceed(),

                CursorLocation::At(insn) => {
                    if inserter.func().dfg.is_branch(insn) {
                        let block = inserter.block().unwrap();
                        for &out_edge in self.solver.unreachable_out_edges(block) {
                            let edge_data = self.solver.edge_data(out_edge);
                            inserter
                                .func_mut()
                                .dfg
                                .remove_branch_dest(insn, edge_data.to);
                        }
                    }
                    inserter.proceed();
                }

                CursorLocation::NoWhere => break,
            }
        }
    }

    /// Rewrite phi insn when there is at least one unreachable incoming edge to the block.
    fn rewrite_phi(&self, func: &mut Function, insn: Insn, block: Block) {
        if !func.dfg.is_phi(insn) {
            return;
        }

        let edges = &self.solver.blocks[block].in_edges;
        for &edge in edges {
            let edge_data = self.solver.edge_data(edge);
            // Remove phi arg if the edge is unreachable.
            if !edge_data.reachable {
                func.dfg.remove_phi_arg(insn, edge_data.from);
            }
        }
    }
}
