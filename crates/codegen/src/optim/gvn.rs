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
use fxhash::FxHashMap;

use crate::{
    cfg::ControlFlowGraph,
    domtree::DomTree,
    ir::{
        func_cursor::{CursorLocation, FuncCursor, InsnInserter},
        insn::{BinaryOp, InsnData},
        DataFlowGraph, Immediate,
    },
    Block, Function, Insn, Type, Value,
};

use super::{constant_folding, interner::Interner, simplify_impl};

///  An initial class that assigned to all values.
///  If a value still has the initial class after value numbering, then the insn that defines the value is
///  unreachable.
const INITIAL_CLASS: Class = Class(0);

/// The rank for immediates.
const IMMEDIATE_RANK: u32 = 0;

#[derive(Debug, Default)]
pub struct GvnSolver {
    /// Store classes.
    classes: PrimaryMap<Class, ClassData>,

    /// Maps [`Value`] to [`GvnValueData`].
    values: SecondaryMap<Value, GvnValueData>,

    /// An interner that intern [`GvnInsnData`] to `[GvnInsnData]`.
    insns: Interner<GvnInsn, GvnInsnData>,

    /// Maps [`GvnInsnData`] to [`Class`].
    insn_table: FxHashMap<GvnInsn, Class>,

    /// Store edges.
    edges: PrimaryMap<Edge, EdgeData>,

    /// Maps [`Block`] to [`GvnBlockData`]
    blocks: SecondaryMap<Block, GvnBlockData>,
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
            insn: GvnInsn(u32::MAX),
            values: BTreeSet::new(),
        });
        debug_assert!(self.classes.len() == 1);

        // Make the entry block reachable.
        let entry = func.layout.entry_block().unwrap();
        self.blocks[entry].reachable = true;

        // Make classes for immediates.
        for &value in func.dfg.immediates.values() {
            self.assign_class_to_imm_value(value);
        }

        let mut rank = IMMEDIATE_RANK + 1;
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
                        self.add_edge_info(block, dest, None, None);
                    }

                    InsnData::Branch { args, dests } => {
                        let cond = args[0];
                        debug_assert_eq!(func.dfg.value_ty(cond), &Type::I1);

                        let then_block = dests[0];
                        let else_block = dests[1];

                        let then_imm = self.make_imm(&mut func.dfg, true);
                        let else_imm = self.make_imm(&mut func.dfg, false);

                        self.add_edge_info(block, then_block, Some(cond), Some(then_imm));
                        self.add_edge_info(block, else_block, Some(cond), Some(else_imm));
                    }

                    _ => {}
                }
            }
        }

        // Assign rank to function arguments and create class for them.
        for &arg in &func.arg_values {
            self.values[arg].rank = u32::MAX;
            let gvn_insn = self.insns.intern(arg.into());
            self.make_class(arg, gvn_insn);
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
        self.remove_redundant_code(func, cfg, domtree);
    }

    /// Clear all internal data of the solver.
    pub fn clear(&mut self) {
        self.classes.clear();
        self.values.clear();
        self.insns.clear();
        self.insn_table.clear();
        self.edges.clear();
        self.blocks.clear();
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
                if self.infer_edge_reachability(func, then_edge, domtree) {
                    // Mark `then_edge` if its cond is inferred as being always true.
                    self.mark_edge_reachable(then_edge)
                } else if self.infer_edge_reachability(func, else_edge, domtree) {
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
        let gvn_insn_data = self.perform_symbolic_evaluation(func, domtree, insn);
        let gvn_insn = self.insns.intern(gvn_insn_data);

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

        let old_class = self.value_class(insn_result);
        let new_class = if let GvnInsnData::Value(value) = self.insn_data(gvn_insn) {
            // If `gvn_insn` is value itself, then lookup value class of the value.
            self.value_class(*value)
        } else if let Some(class) = self.insn_table.get(&gvn_insn) {
            // If gvn_insn is already inserted, return corresponding class.
            *class
        } else if old_class == INITIAL_CLASS {
            // If the value is not congruent with any known classes, then make new class for the
            // value and its defining insn.
            self.make_class(insn_result, gvn_insn)
        } else {
            old_class
        };

        // If assigned class is not changed, return.
        if old_class == new_class {
            return false;
        }

        // Replace `value` class to `new_class` from `old_class`.
        self.replace_value_class(insn_result, gvn_insn, old_class, new_class);

        true
    }

    fn remove_redundant_code(
        &self,
        func: &mut Function,
        cfg: &mut ControlFlowGraph,
        domtree: &mut DomTree,
    ) {
        let entry_block = func.layout.entry_block().unwrap();
        let mut inserter = InsnInserter::new(func, CursorLocation::BlockTop(entry_block));

        // Remove unreachable blocks and unused edges.
        loop {
            match inserter.loc() {
                CursorLocation::BlockTop(block) => {
                    if !self.blocks[block].reachable {
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
                        let mut in_edges = self.reachable_out_edges(block);
                        let edge = in_edges.next().unwrap();
                        if in_edges.next().is_none() {
                            inserter.replace(InsnData::jump(self.edge_data(*edge).to));
                        }
                    }
                    inserter.proceed();
                }

                CursorLocation::NoWhere => break,
            }
        }

        // Recompute cfg and domtree.
        cfg.compute(inserter.func());
        domtree.compute(cfg);

        inserter.set_loc(CursorLocation::BlockTop(entry_block));
        loop {
            match inserter.loc() {
                CursorLocation::BlockTop(_) | CursorLocation::BlockBottom(..) => {
                    inserter.proceed();
                }

                CursorLocation::At(insn) => {
                    let block = inserter.block().unwrap();
                    if let Some(insn_result) = inserter.func().dfg.insn_result(insn) {
                        let leader = self.leader(insn_result);

                        // If leader dominates the def of insn_result, remove insn and replace the
                        // insn_result with leader.
                        if leader != insn_result
                            && self.dominates(inserter.func(), domtree, leader, insn_result)
                        {
                            inserter.func_mut().dfg.change_to_alias(insn_result, leader);
                            inserter.remove_insn();
                            continue;
                        }

                        // Rewrite phi function if there are the unreachable incoming edge to the block.
                        let insn_data = inserter.func().dfg.insn_data(insn);
                        if matches!(insn_data, InsnData::Phi { .. })
                            && self.blocks[block].in_edges.len()
                                != self.reachable_in_edges(block).count()
                        {
                            let class = self.value_class(insn_result);
                            let gvn_insn = self.classes[class].insn;
                            match self.insns.get(gvn_insn) {
                                GvnInsnData::Insn(insn_data) => inserter.replace(insn_data.clone()),
                                _ => unreachable!(),
                            }
                        }

                        inserter.proceed();
                    } else {
                        inserter.proceed();
                    }
                }

                CursorLocation::NoWhere => break,
            }
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
    fn infer_edge_reachability(&self, func: &Function, edge: Edge, domtree: &DomTree) -> bool {
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
                if let Some(inferred_value) = self.infer_value_by_edge(func, in_edge, cond) {
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
                if let Some(value) = self.infer_value_by_edge(func, dominant_edge, rep_value) {
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

        if let Some(rep_value) = self.infer_value_by_edge(func, edge, rep_value) {
            rep_value
        } else {
            self.infer_value_at_block(func, domtree, rep_value, self.edge_data(edge).from)
        }
    }

    /// Returns inferred `value2` iff
    /// 1. The predicate of dominant incoming edge is represented as `value1 == value2`.
    /// 2. `value` is congruent to value1
    /// 3. `value2`.rank < `value`.rank.
    fn infer_value_by_edge(&self, func: &Function, edge: Edge, value: Value) -> Option<Value> {
        let edge_data = self.edge_data(edge);
        let predicate = edge_data.cond.expand()?;
        if self.is_congruent_value(predicate, value) {
            return Some(edge_data.resolved_cond.unwrap());
        }

        let predicate_insn = match func.dfg.value_insn(predicate) {
            Some(insn) => insn,
            None => return None,
        };

        match func.dfg.insn_data(predicate_insn) {
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
        insn: Insn,
    ) -> GvnInsnData {
        let block = func.layout.insn_block(insn);
        let insn_data = match func.dfg.insn_data(insn) {
            InsnData::Unary { code, args: [arg] } => {
                let arg = self.infer_value_at_block(func, domtree, *arg, block);
                InsnData::unary(*code, arg)
            }

            InsnData::Binary {
                code,
                args: [lhs, rhs],
            } => {
                let mut lhs = self.infer_value_at_block(func, domtree, *lhs, block);
                let mut rhs = self.infer_value_at_block(func, domtree, *rhs, block);
                // Canonicalize argument order if the insn is commutative.
                if code.is_commutative() && self.value_rank(rhs) < self.value_rank(lhs) {
                    std::mem::swap(&mut lhs, &mut rhs);
                }

                InsnData::binary(*code, lhs, rhs)
            }

            InsnData::Cast {
                code,
                args: [arg],
                ty,
            } => {
                let arg = self.infer_value_at_block(func, domtree, *arg, block);
                InsnData::cast(*code, arg, ty.clone())
            }

            data @ InsnData::Store { .. } => data.clone(),

            InsnData::Load { .. }
            | InsnData::Jump { .. }
            | InsnData::Branch { .. }
            | InsnData::Return { .. } => {
                unreachable!()
            }

            InsnData::Phi { values, blocks, ty } => {
                let edges = &self.blocks[block].in_edges;

                let mut phi_args = Vec::with_capacity(values.len());
                for (&value, &from) in (values).iter().zip(blocks.iter()) {
                    let edge = self.find_edge(edges, from, block);
                    if !self.edge_data(edge).reachable {
                        continue;
                    }

                    let inferred_value = self.infer_value_at_edge(func, domtree, value, edge);
                    // In `Self::remove_redundant_code`, we replace the phi insn with the evaluated insn
                    // in case at least one of the incoming edges is unreachable.
                    // So we conservatively evaluate dominant relationship between
                    // `inferred_value` and `value` not to use an incorrect value.
                    if self.dominates(func, domtree, inferred_value, value) {
                        phi_args.push((inferred_value, block));
                    } else {
                        phi_args.push((value, block));
                    }
                }

                // Canonicalize the argument order by block rank.
                phi_args.sort_unstable_by(|(_, block1), (_, block2)| {
                    self.block_rank(*block1).cmp(&self.block_rank(*block2))
                });

                InsnData::Phi {
                    values: phi_args.iter().map(|(value, _)| *value).collect(),
                    blocks: phi_args.iter().map(|(_, block)| *block).collect(),
                    ty: ty.clone(),
                }
            }
        };

        if let Some(result) = self.perform_constant_folding(func, &insn_data) {
            result
        } else if let Some(result) = self.perform_simplification(func, &insn_data) {
            result
        } else {
            GvnInsnData::Insn(insn_data)
        }
    }

    /// Perform constant folding.
    fn perform_constant_folding(
        &mut self,
        func: &mut Function,
        insn_data: &InsnData,
    ) -> Option<GvnInsnData> {
        constant_folding::fold_constant(&func.dfg, insn_data)
            .map(|imm| GvnInsnData::Value(self.make_imm(&mut func.dfg, imm)))
    }

    /// Perform insn simplification.
    fn perform_simplification(
        &mut self,
        func: &mut Function,
        insn_data: &InsnData,
    ) -> Option<GvnInsnData> {
        simplify_impl::simplify_insn_data(&mut func.dfg, insn_data.clone()).map(|res| match res {
            simplify_impl::SimplifyResult::Value(value) => {
                // Need to handle immediate specially.
                if let Some(imm) = func.dfg.value_imm(value) {
                    GvnInsnData::Value(self.make_imm(&mut func.dfg, imm))
                } else {
                    GvnInsnData::Value(value)
                }
            }
            simplify_impl::SimplifyResult::Insn(insn) => GvnInsnData::Insn(insn),
        })
    }

    /// Make edge data and append in and out edges to corresponding blocks.
    fn add_edge_info(
        &mut self,
        from: Block,
        to: Block,
        cond: Option<Value>,
        resolved_cond: Option<Value>,
    ) {
        let edge_data = EdgeData {
            from,
            to,
            cond: cond.into(),
            resolved_cond: resolved_cond.into(),
            reachable: false,
        };

        let edge = self.edges.push(edge_data);
        self.blocks[to].in_edges.push(edge);
        self.blocks[from].out_edges.push(edge);
    }

    /// Replace the class of the `value` from `old` to `new`.
    /// If `old` class becomes empty, then `gvn_insn` is removed from `insn_table`.
    fn replace_value_class(&mut self, value: Value, gvn_insn: GvnInsn, old: Class, new: Class) {
        let value_rank = self.value_rank(value);

        // Remove `value` from `old` class.
        let old_class_data = &mut self.classes[old];
        old_class_data.values.remove(&(value_rank, value));

        // If class becomes empty, then remove the `gvn_insn` from the table.
        if old != INITIAL_CLASS && old_class_data.values.is_empty() {
            self.insn_table.remove(&gvn_insn);
        };

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
        let gvn_insn = self.insns.intern(value.into());

        // If the congruence class for the value already exists, then return.
        if class != INITIAL_CLASS {
            debug_assert_eq!(self.classes[class].insn, gvn_insn);
            debug_assert_eq!(self.values[value].rank, IMMEDIATE_RANK);
            return;
        }

        // Set rank.
        self.values[value].rank = IMMEDIATE_RANK;

        // Create a congruence class for the immediate.
        self.make_class(value, gvn_insn);
    }

    fn is_back_edge(&self, edge: Edge) -> bool {
        let from = self.edge_data(edge).from;
        let to = self.edge_data(edge).to;

        self.blocks[to].rank <= self.blocks[from].rank
    }

    /// Returns leader value of the congruent class to which `value` belongs.
    fn leader(&self, value: Value) -> Value {
        let class = self.values[value].class;
        self.classes[class].values.iter().next().unwrap().1
    }

    /// Returns `GvnInsnData`.
    fn insn_data(&self, gvn_insn: GvnInsn) -> &GvnInsnData {
        self.insns.get(gvn_insn)
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
            insn: gvn_insn,
            values,
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

    /// Returns `true` if def of `value1` strictry dominates def of `value2`.
    fn dominates(&self, func: &Function, domtree: &DomTree, value1: Value, value2: Value) -> bool {
        if func.dfg.is_imm(value1) || func.dfg.is_arg(value1) {
            return true;
        } else if func.dfg.is_imm(value2) || func.dfg.is_arg(value2) {
            return false;
        }

        let insn1 = func.dfg.value_insn(value1).unwrap();
        let insn2 = func.dfg.value_insn(value2).unwrap();

        let block1 = func.layout.insn_block(insn1);
        let block2 = func.layout.insn_block(insn2);

        if block1 == block2 {
            self.value_rank(value1) < self.value_rank(value2)
        } else {
            domtree.dominates(block1, block2)
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash, PartialOrd, Ord)]
struct Class(u32);
entity_impl!(Class);

/// A congruence class.
#[derive(Debug, Clone, PartialEq)]
struct ClassData {
    /// A representative expression for the class.
    insn: GvnInsn,

    /// Values the class includes.
    /// NOTE: We need sort the value by rank.
    values: BTreeSet<(u32, Value)>,
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

#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash, PartialOrd, Ord)]
struct GvnInsn(u32);
entity_impl!(GvnInsn);

/// A insn data which represents canonicalized/simplified/folded insn.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum GvnInsnData {
    /// A value which occurs when insn is simplified/folded to value.
    Value(Value),
    /// An insn data.
    Insn(InsnData),
}

impl From<Value> for GvnInsnData {
    fn from(value: Value) -> Self {
        Self::Value(value)
    }
}

impl From<InsnData> for GvnInsnData {
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

    /// Hold branch's condition if branch is conditional.
    cond: PackedOption<Value>,

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
