//! This module contains a solver for complete Global Value Numbering.
//!
//! The algorithm here is based on Karthik Gargi.: A sparse algorithm for predicated global value numbering:
//! PLDI 2002 Pages 45–56: <https://dl.acm.org/doi/10.1145/512529.512536>.
//!
//! Also, to make the GVN complete, this algorithm is based on
//! Rekha R. Pai.: Detection of Redundant Expressions: A Complete and Polynomial-Time Algorithm in SSA:
//! Asian Symposium on Programming Languages and Systems 2015 pp49-65: <https://link.springer.com/chapter/10.1007/978-3-319-26529-2_4>

use std::collections::BTreeSet;

use cranelift_entity::{entity_impl, packed_option::PackedOption, PrimaryMap, SecondaryMap};
use fxhash::{FxHashMap, FxHashSet};

use crate::{
    cfg::ControlFlowGraph,
    domtree::{DomTree, DominatorTreeTraversable},
    ir::{
        func_cursor::{CursorLocation, FuncCursor, InsnInserter},
        insn::{BinaryOp, CastOp, InsnData, UnaryOp},
        DataFlowGraph, Immediate,
    },
    Block, Function, Insn, Type, Value,
};

use super::{constant_folding, simplify_impl};

///  An initial class that assigned to all values.
///  If a value still has the initial class after value numbering, then the insn that defines the value is
///  unreachable.
const INITIAL_CLASS: Class = Class(0);

/// The rank for immediates.
const MINIMUM_RANK: u32 = 0;

#[derive(Debug, Default)]
pub struct GvnSolver {
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

    /// Hold always available values, i.e. immediates or function arguments.
    always_avail: Vec<Value>,
}

impl GvnSolver {
    pub fn run(&mut self, func: &mut Function, cfg: &mut ControlFlowGraph, domtree: &mut DomTree) {
        self.clear();

        // Return if the function has no blocks.
        if func.layout.entry_block().is_none() {
            return;
        }

        // Make dummy INITIAL_CLASS.
        self.classes.push(ClassData {
            values: BTreeSet::new(),
            gvn_insn: GvnInsn::Value(Value(u32::MAX)),
        });
        debug_assert!(self.classes.len() == 1);

        // Make the entry block reachable.
        let entry = func.layout.entry_block().unwrap();
        self.blocks[entry].reachable = true;

        // Make classes for immediates.
        for &value in func.dfg.immediates.values() {
            self.assign_class_to_imm_value(value);
        }

        let mut rank = MINIMUM_RANK + 1;

        // Assign rank to function arguments and create class for them.
        for &arg in &func.arg_values {
            self.values[arg].rank = rank;
            rank += 1;
            let gvn_insn = GvnInsn::Value(arg);
            self.always_avail.push(arg);
            self.make_class(arg, gvn_insn);
        }

        // Iterate insns in RPO to assign ranks and analyze edges information.
        for &block in domtree.rpo() {
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

                        let then_predicate = func
                            .dfg
                            .value_insn(cond)
                            .map(|insn| func.dfg.insn_data(insn).clone());
                        let else_predicate = InsnData::unary(UnaryOp::Not, cond);

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

                    _ => {}
                }
            }
        }

        // Find congruence classes of all reachable insn.
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
                    if let Some(insn_result) = func.dfg.insn_result(insn) {
                        changed |= self.assign_congruence(func, domtree, insn, insn_result);
                    }
                    next_insn = func.layout.next_insn_of(insn);
                }

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
        self.always_avail.clear();
    }

    /// Analyze the last insn of the block.
    /// This function updates reachability of the edges and blocks.
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

                // Mark appropriate edge as reachable if predicate is congruent to immeidate.
                let leader = self.leader(cond);
                if let Some(cond_imm) = func.dfg.value_imm(leader) {
                    let edge = if cond_imm.is_zero() {
                        else_edge
                    } else {
                        then_edge
                    };
                    return self.mark_edge_reachable(edge);
                }

                // Try to infer reachability of edges.
                if self.infer_edge_reachability(then_edge, domtree) {
                    // Mark `then_edge` if its cond is inferred as being always true.
                    self.mark_edge_reachable(then_edge)
                } else if self.infer_edge_reachability(else_edge, domtree) {
                    // Mark `else_edge` if its cond is inferred as being always true.
                    self.mark_edge_reachable(else_edge)
                } else {
                    // Mark both edges if inference failed.
                    let changed = self.mark_edge_reachable(then_edge);
                    changed || self.mark_edge_reachable(else_edge)
                }
            }

            _ => false,
        }
    }

    /// Search and assign congruence class to the `insn_result`.
    /// Returns `true` if congruence class is changed.
    fn assign_congruence(
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
            let class = self.value_class(insn_result);
            if class == INITIAL_CLASS {
                self.make_class(insn_result, gvn_insn);
                return true;
            } else {
                return false;
            }
        }

        let mut changed = false;
        let old_class = self.value_class(insn_result);
        let new_class = if let GvnInsn::Value(value) = &gvn_insn {
            // If `gvn_insn` is value itself, then lookup value class of the value.
            self.value_class(*value)
        } else if let Some(class) = self.insn_table.get(&gvn_insn).copied() {
            // Perform value phi computation.
            changed |= self.perform_value_phi_computation(func, &gvn_insn, insn_result, block);
            // If gvn_insn is already inserted, return corresponding class.
            class
        } else {
            // If the value is not congruent with any known classes, then make a new class for the
            // value and its defining insn.
            let class = self.make_class(insn_result, gvn_insn.clone());

            // Perform value phi computation.
            changed |= self.perform_value_phi_computation(func, &gvn_insn, insn_result, block);
            class
        };

        if old_class == new_class {
            changed
        } else {
            self.replace_value_class(insn_result, old_class, new_class);
            true
        }
    }

    /// Perform value phi computation for the value.
    ///
    /// Returns `true` if computed value phi is changed from the old value phi of the value.
    /// The computed phi function is assigned to the value's field inside the function..
    fn perform_value_phi_computation(
        &mut self,
        func: &mut Function,
        insn_data: &GvnInsn,
        insn_result: Value,
        block: Block,
    ) -> bool {
        let value_phi =
            ValuePhiFinder::new(self, insn_result).compute_value_phi(func, insn_data, block);
        let value_data = &mut self.values[insn_result];

        if value_phi == value_data.value_phi {
            false
        } else {
            value_data.value_phi = value_phi;
            true
        }
    }

    /// Mark the edge and its destinating block as reachable.
    /// Returns `true` if edge reachability is changed by the call.
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

    /// Returns `true` if `edge` is inferred as being reachable.
    ///
    /// We assume `edge` is reachable iff any dominant edges to the originating block have
    /// congruent class with the predicate of the `edge`.
    fn infer_edge_reachability(&self, edge: Edge, domtree: &DomTree) -> bool {
        let edge_data = &self.edges[edge];
        // If `cond` doesn't exist, then the edge must be non conditional jump.
        let cond = match edge_data.cond.expand() {
            Some(cond) => cond,
            None => return true,
        };

        // If the edge has `cond`, then `resolved_cond` must exist.
        let resolved_cond = edge_data.resolved_cond.unwrap();

        // Look up dominator blocks of the edge's originating block.
        let mut block = Some(edge_data.from);
        while let Some(current_block) = block {
            if let Some(in_edge) = self.dominant_reachable_in_edges(current_block) {
                if let Some(inferred_value) = self.infer_value_by_edge(in_edge, cond) {
                    if self.is_congruent_value(inferred_value, resolved_cond) {
                        return true;
                    }
                } else {
                    block = Some(self.edge_data(in_edge).from);
                }
            } else {
                block = domtree.idom_of(current_block);
            }
        }

        false
    }

    /// Returns representative value at the block by using edge's predicate.
    ///
    /// `value` can be inferred to `value2` if
    /// 1. The predicate of dominant incoming edge is represented as `value1 == value2`.
    /// 2. `value` is congruent to value1
    /// 3. `value2`.rank < `value`.rank.
    ///
    /// This process is recursively applied while traversing the dominator tree in ascending order.
    /// If the dominant edge is back edge, then this process is stopped to avoid infinite loop.
    ///
    /// # Example
    /// ```
    /// let value2 = .. (rank0)
    /// let value1 = .. (rank1)
    /// let value = value1 + 0 (rank2)
    /// if value1 == value2 {
    ///     use value
    /// }
    /// ```
    /// The use of the `value` inside if-block is inferred to `value2` even if `value` and `value2`
    /// is not congruent in general.
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
        // reaches end block.
        while current_block.is_some() && (!func.dfg.is_imm(rep_value)) {
            let block = current_block.unwrap();
            if let Some(dominant_edge) = self.dominant_reachable_in_edges(block) {
                // Stop looking up the value to avoid infinite lookup loop.
                if self.is_back_edge(dominant_edge) {
                    break;
                }

                // If the value inference succeeds, restart inference with the new representative value.
                if let Some(value) = self.infer_value_by_edge(dominant_edge, rep_value) {
                    rep_value = value;
                    current_block = Some(target_block);
                } else {
                    // If the inference failed, go up the dominant edge.
                    current_block = Some(self.edge_data(dominant_edge).from);
                }
            } else {
                // If no dominant edge found, go up the dominator tree.
                current_block = domtree.idom_of(block);
            }
        }

        rep_value
    }

    /// Returns representative value at the edge by using edge's predicate.
    ///
    /// This is used to infer phi arguments which is guranteed to flow through the specified edge.
    fn infer_value_at_edge(
        &self,
        func: &Function,
        domtree: &DomTree,
        value: Value,
        edge: Edge,
    ) -> Value {
        let rep_value = self.leader(value);

        if let Some(rep_value) = self.infer_value_by_edge(edge, rep_value) {
            rep_value
        } else {
            self.infer_value_at_block(func, domtree, rep_value, self.edge_data(edge).from)
        }
    }

    /// Returns inferred `value2` iff
    /// 1. The predicate of dominant incoming edge is represented as `value1 == value2`.
    /// 2. `value` is congruent to value1
    /// 3. `value2`.rank < `value`.rank.
    fn infer_value_by_edge(&self, edge: Edge, value: Value) -> Option<Value> {
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

    /// Returns reachable outgoing edges of the block.
    fn reachable_out_edges(&self, block: Block) -> impl Iterator<Item = &Edge> {
        self.blocks[block]
            .out_edges
            .iter()
            .filter(|edge| self.edge_data(**edge).reachable)
    }

    /// Returns incoming edge if the edge is only one reachable edge to the block.
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

    /// Perform symbolic evaluation for the `insn`.
    fn perform_symbolic_evaluation(
        &mut self,
        func: &mut Function,
        domtree: &DomTree,
        insn_data: InsnData,
        block: Block,
    ) -> GvnInsn {
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
                // Canonicalize argument order if the insn is commutative.
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
            | InsnData::Return { .. } => insn_data.clone(),

            InsnData::Phi { values, blocks, ty } => {
                let edges = &self.blocks[block].in_edges;

                let mut phi_args = Vec::with_capacity(values.len());
                for (&value, &from) in (values).iter().zip(blocks.iter()) {
                    let edge = self.find_edge(edges, from, block);
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
        } else if let Some(result) = self.perform_simplification(func, &insn_data) {
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
        func: &mut Function,
        insn_data: &InsnData,
    ) -> Option<GvnInsn> {
        simplify_impl::simplify_insn_data(&mut func.dfg, insn_data.clone()).map(|res| match res {
            simplify_impl::SimplifyResult::Value(value) => {
                // Need to handle immediate specially.
                if let Some(imm) = func.dfg.value_imm(value) {
                    GvnInsn::Value(self.make_imm(&mut func.dfg, imm))
                } else {
                    GvnInsn::Value(value)
                }
            }
            simplify_impl::SimplifyResult::Insn(insn) => GvnInsn::Insn(insn),
        })
    }

    /// Make edge data and append in and out edges to corresponding blocks.
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

        let edge = self.edges.push(edge_data);
        self.blocks[to].in_edges.push(edge);
        self.blocks[from].out_edges.push(edge);
    }

    /// Replace the class of the `value` from `old` to `new`.
    fn replace_value_class(&mut self, value: Value, old: Class, new: Class) {
        debug_assert!(old != new);
        let value_rank = self.value_rank(value);

        // Remove `value` from `old` class.
        let old_class_data = &mut self.classes[old];
        old_class_data.values.remove(&(value_rank, value));

        // Remove old gvn_insn from the insn_table if the class becomes empty.
        if let Some(insn_class) = self.insn_table.get_mut(&old_class_data.gvn_insn) {
            if *insn_class == old && old_class_data.values.is_empty() {
                self.insn_table.remove(&old_class_data.gvn_insn);
            }
        }

        // Add `value` to `new` class.
        let new_class_data = &mut self.classes[new];
        new_class_data.values.insert((value_rank, value));

        // Change `value` class to point to `new`.
        self.values[value].class = new;
    }

    /// Make value from immediate, also make a corresponding congruence class and update
    /// `insn_table` for the immediate value if they don't exist yet.
    fn make_imm(&mut self, dfg: &mut DataFlowGraph, imm: impl Into<Immediate>) -> Value {
        // `make_imm_value` return always same value for the same immediate.
        let value = dfg.make_imm_value(imm);

        self.assign_class_to_imm_value(value);

        value
    }

    /// Assign class to immediate value.
    fn assign_class_to_imm_value(&mut self, value: Value) {
        let class = self.values[value].class;
        let gvn_insn = GvnInsn::Value(value);

        // If the congruence class for the value already exists, then return.
        if class != INITIAL_CLASS {
            debug_assert_eq!(self.values[value].rank, MINIMUM_RANK);
            return;
        }

        // Set rank.
        self.values[value].rank = MINIMUM_RANK;

        // Add the immediate to `always_avail` value.
        self.always_avail.push(value);

        // Create a congruence class for the immediate.
        self.make_class(value, gvn_insn);
    }

    fn is_back_edge(&self, edge: Edge) -> bool {
        let from = self.edge_data(edge).from;
        let to = self.edge_data(edge).to;

        self.blocks[to].rank <= self.blocks[from].rank
    }

    /// Returns the leader value of the congruent class to which `value` belongs.
    fn leader(&self, value: Value) -> Value {
        // If the value has `value_phi` and the `value_phi` is `ValuePhi::Value`, then returns the leader of
        // the value.
        if let Some(value) = self.values[value]
            .value_phi
            .as_ref()
            .map(|value_phi| value_phi.value())
            .flatten()
        {
            // Recursively resolve the value to leader.
            return self.leader(value);
        }

        let class = self.values[value].class;
        self.classes[class].values.iter().next().unwrap().1
    }

    /// Returns the leader value of the congruent class.
    /// This method is mainly for [`ValuePhiFinder`], use [`Self::leader`] whenever possible.
    fn class_leader(&self, class: Class) -> Value {
        self.classes[class].values.iter().next().unwrap().1
    }

    /// Returns `EdgeData`.
    fn edge_data(&self, edge: Edge) -> &EdgeData {
        &self.edges[edge]
    }

    /// Returns the class of the value.
    fn value_class(&self, value: Value) -> Class {
        self.values[value].class
    }

    /// Returns the rank of the given value.
    fn value_rank(&self, value: Value) -> u32 {
        self.values[value].rank
    }

    /// Returns the rank of the given block.
    fn block_rank(&self, block: Block) -> u32 {
        self.blocks[block].rank
    }

    /// Make new class for the value and its defining insn,
    /// also change belongings class of the value to the created class.
    fn make_class(&mut self, value: Value, gvn_insn: GvnInsn) -> Class {
        let mut values = BTreeSet::new();
        let rank = self.value_rank(value);
        values.insert((rank, value));
        let class_data = ClassData {
            values,
            gvn_insn: gvn_insn.clone(),
        };
        let class = self.classes.push(class_data);

        // Update the class the value belongs to.
        self.values[value].class = class;

        // Map insn to the congruence class.
        self.insn_table.insert(gvn_insn, class);

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

    /// Representative gvn insn of the class.
    gvn_insn: GvnInsn,
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

    /// A value phi which the value is congruent to.
    /// If the `value_phi is some, then the insn that defines the value is replaced with the phi
    /// function or `value` which made from `ValuePhi`.
    value_phi: Option<ValuePhi>,
}

impl Default for GvnValueData {
    fn default() -> Self {
        Self {
            class: INITIAL_CLASS,
            rank: 0,
            value_phi: None,
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

/// This struct finds value phi congruence that described in
/// `Detection of Redundant Expressions: A Complete and Polynomial-Time Algorithm in SSA`.
///
/// Value phi congruence is the congruence beyond phi functions.
///
/// For example, `v7` becomes congruent `v8` if we create `v8.i8 = phi (v3 block1) (v5 block5)` in
/// the top of `block3` in the below example.
///
/// ```
/// func %example(v0.i1, v1.i8):
///     block0:
///         br v0 block1 block2;
///
///     block1:
///         v2.i8 = 10.i8;
///         v3.i8 = add v2 v1;
///         jump block3;
///
///     block2:
///         v4.i8 = 20.i8;
///         v5.i8 = add v4 v1;
///         jump block3;
///
///     block3:
///         v6.i8 = phi (v2 block1) (v4 block2);
///         v7.i8 = add v6 v1;
/// ```
struct ValuePhiFinder<'a> {
    solver: &'a mut GvnSolver,
    insn_result: Value,
    /// Hold visited blocks while finding value phi to prevent infinite loop.
    visited: FxHashSet<Block>,
}

impl<'a> ValuePhiFinder<'a> {
    fn new(solver: &'a mut GvnSolver, insn_result: Value) -> Self {
        Self {
            solver,
            insn_result,
            visited: FxHashSet::default(),
        }
    }

    /// Main entry of this struct.
    fn compute_value_phi(
        &mut self,
        func: &mut Function,
        gvn_insn: &GvnInsn,
        block: Block,
    ) -> Option<ValuePhi> {
        // Break infinite loop if the block has been already visited.
        if !self.visited.insert(block) {
            return None;
        }

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
                let (lhs, rhs) = match (self.get_phi_of(func, *lhs), self.get_phi_of(func, *rhs)) {
                    (Some(lhs_phi), Some(rhs_phi)) => (lhs_phi, rhs_phi),
                    (Some(lhs_phi), None) => ((lhs_phi, ValuePhi::Value(*rhs))),
                    (None, Some(rhs_phi)) => ((ValuePhi::Value(*lhs), rhs_phi)),
                    (None, None) => return None,
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
                    let phi_arg = self.lookup_value_phi_arg(func, query_insn, block)?;
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
                    // If two blocks where phi arg passed through are not identical, return.
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
                        std::mem::swap(&mut lhs_value, &mut rhs_value);
                    }
                    let query_insn = InsnData::binary(code, lhs_value, rhs_value);
                    let phi_arg = self.lookup_value_phi_arg(func, query_insn, block)?;
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
                    let phi_arg = self.lookup_value_phi_arg(func, query_insn, block)?;
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
    fn lookup_value_phi_arg(
        &mut self,
        func: &mut Function,
        query: InsnData,
        block: Block,
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
            GvnInsn::Insn(query)
        };

        // If class already exists for the query, return the leader value of the class.
        if let Some(class) = self.solver.insn_table.get(&query) {
            let leader = self.solver.class_leader(*class);
            return Some(ValuePhi::Value(leader));
        }

        // Try to further compute value phi for the query insn.
        self.compute_value_phi(func, &query, block)
    }

    /// Returns the phi args and blocks if the insn defining the `value` is phi or `value` has
    /// `ValuePhi::Insn`.
    /// The result reflects the reachability of the incoming edges,
    /// i.e. if a phi arg pass through an unreachable incoming edge, then the arg and blocks
    /// are omitted from the result.
    /// The result is sorted in the block order.
    ///
    /// This function also returns the blocks where the phi is defined.
    fn get_phi_of(&self, func: &Function, value: Value) -> Option<ValuePhi> {
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

        if value == self.insn_result {
            return None;
        }

        // If the value is annotated by value phi insn, return it.
        match &self.solver.values[value].value_phi {
            value_phi @ Some(ValuePhi::PhiInsn(..)) => value_phi.clone(),
            _ => None,
        }
    }
}

/// Value phi that described in
/// `Detection of Redundant Expressions: A Complete and Polynomial-Time Algorithm in SSA`.
#[derive(Debug, Clone, PartialEq, Eq)]
enum ValuePhi {
    /// `ValuePhi` may become value itself if the all arguments of the `ValuePhiInsn` is the same
    /// value.
    Value(Value),
    /// Phi instruction which is resolved to a "normal" phi insn in the later pass of `GvnSolver`.
    PhiInsn(ValuePhiInsn),
}

impl ValuePhi {
    /// Returns a value if the value phi is value itself.
    fn value(&self) -> Option<Value> {
        match self {
            Self::Value(value) => Some(*value),
            Self::PhiInsn(..) => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
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
struct RedundantCodeRemover<'a> {
    solver: &'a GvnSolver,

    /// Record available class and available representative value in bottom of blocks.
    /// This is necessary to decide whether the args of inserted phi functions are dominated by its
    /// definitions.
    avail_set: SecondaryMap<Block, FxHashMap<Class, Value>>,
}

impl<'a> RedundantCodeRemover<'a> {
    fn new(solver: &'a GvnSolver) -> Self {
        Self {
            solver,
            avail_set: SecondaryMap::default(),
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

        let mut inserter = InsnInserter::new(func, CursorLocation::BlockTop(block));
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
    fn resolve_value_phi_in_block(&self, func: &mut Function, block: Block) {
        let mut inserter = InsnInserter::new(func, CursorLocation::BlockTop(block));
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
                        if let Some(value_phi) = &self.solver.values[insn_result].value_phi {
                            let ty = inserter.func().dfg.value_ty(insn_result).clone();
                            if let Some(value) =
                                self.try_resolve_value_phi(&mut inserter, value_phi, ty, block)
                            {
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

    fn try_resolve_value_phi(
        &self,
        inserter: &mut InsnInserter,
        value_phi: &ValuePhi,
        ty: Type,
        block: Block,
    ) -> Option<Value> {
        match value_phi {
            ValuePhi::Value(value) => {
                let class = self.solver.value_class(*value);
                self.avail_set[block].get(&class).copied()
            }

            ValuePhi::PhiInsn(phi_insn) => {
                // Memorize current inserter loc to restore later.
                let current_inserter_loc = inserter.loc();

                // Resolve phi value's arguments and append them to the newly `InsnData::Phi`.
                let mut phi = InsnData::phi(ty.clone());
                for (value_phi, phi_block) in &phi_insn.args {
                    let resolved =
                        self.try_resolve_value_phi(inserter, value_phi, ty.clone(), *phi_block)?;
                    phi.append_phi_arg(resolved, *phi_block);
                }

                // Insert new phi insn to top of the phi_insn block.
                inserter.set_loc(CursorLocation::BlockTop(phi_insn.block));
                let insn = inserter.insert_insn_data(phi);
                let result = inserter.make_result(insn).unwrap();
                inserter.attach_result(insn, result);

                // Restore the inserter loc.
                inserter.set_loc(current_inserter_loc);

                // Returns inserted phi insn result.
                Some(result)
            }
        }
    }

    /// Remove unreachable edges and blocks.
    fn remove_unreachable_edges(&self, func: &mut Function) {
        let entry_block = func.layout.entry_block().unwrap();
        let mut inserter = InsnInserter::new(func, CursorLocation::BlockTop(entry_block));

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
                    // If the number of reachable outgoing edge is one, then replace branch
                    // insn to jump insn with appropriate destination.
                    if matches!(inserter.func().dfg.insn_data(insn), InsnData::Branch { .. }) {
                        let block = inserter.block().unwrap();
                        let mut in_edges = self.solver.reachable_out_edges(block);
                        let edge = in_edges.next().unwrap();
                        if in_edges.next().is_none() {
                            inserter.replace(InsnData::jump(self.solver.edge_data(*edge).to));
                        }
                    }
                    inserter.proceed();
                }

                CursorLocation::NoWhere => break,
            }
        }
    }

    /// Rewrite phi insn if there is at least one unreachable incoming edge to the block.
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
