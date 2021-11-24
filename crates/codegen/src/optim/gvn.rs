//! This module contains a solver for complete Global Value Numbering.
//! The algorithm here is based on Rekha R. Pai.: Detection of Redundant Expressions: A Complete and Polynomial-Time Algorithm in SSA:
//!
//! Asian Symposium on Programming Languages and Systems 2015 pp49-65:
//! <https://link.springer.com/chapter/10.1007/978-3-319-26529-2_4>

use std::{collections::BTreeSet, hash::Hash};

use cranelift_entity::{
    entity_impl, packed_option::PackedOption, EntityRef, PrimaryMap, SecondaryMap,
};
use fxhash::{FxHashMap, FxHashSet};

use crate::{
    cfg::ControlFlowGraph,
    ir::{
        func_cursor::{CursorLocation, FuncCursor, InsnInserter},
        insn::InsnData,
    },
    Block, Function, Insn, Type, Value,
};

type ValueNumber = u32;

#[derive(Debug, Default)]
pub struct GvnSolver {
    next_vn: ValueNumber,
    partitions: PrimaryMap<Partition, PartitionData>,
    insns: SecondaryMap<Insn, InsnPartition>,
    inserted_phis: SecondaryMap<Block, PartitionData>,
    value_phis: Interner<ValuePhi, ValuePhiData>,
    value_exprs: Interner<ValueExpr, ValueExprData>,
    searched: FxHashSet<Partition>,
    partition_changed: bool,
}

impl GvnSolver {
    pub fn run(&mut self, func: &mut Function, cfg: &ControlFlowGraph) {
        self.clear();

        let mut rpo: Vec<_> = cfg.post_order().collect();
        rpo.reverse();

        if rpo.is_empty() {
            return;
        }

        self.compute_equivalences(func, cfg, &rpo);
        self.remove_redundant_insns(func, &rpo);
    }

    pub fn clear(&mut self) {
        self.next_vn = 0;
        self.partitions.clear();
        self.insns.clear();
        self.inserted_phis.clear();
        self.value_phis.clear();
        self.value_exprs.clear();
        self.searched.clear();
        self.partition_changed = true;
    }

    fn remove_redundant_insns(&mut self, func: &mut Function, rpo: &[Block]) {
        for &block in rpo {
            let mut next_insn = func.layout.first_insn_of(block);
            while let Some(insn) = next_insn {
                let value = match func.dfg.insn_result(insn) {
                    Some(value) => value,
                    None => {
                        next_insn = func.layout.next_insn_of(insn);
                        continue;
                    }
                };

                let (pin, pout) = (
                    self.insns[insn].pin.unwrap(),
                    self.insns[insn].pout.unwrap(),
                );
                let (pin_data, pout_data) = (&self.partitions[pin], &self.partitions[pout]);

                let vn = pout_data.value_vn(value).unwrap();
                let alias = if let Some(alias) = pin_data.representative_value(vn) {
                    alias
                } else if let Some(phi) = pout_data.phi_of_vn(vn) {
                    // No need to resolve phi if insn itself is phi.
                    if func.dfg.is_phi(insn) {
                        next_insn = func.layout.next_insn_of(insn);
                        continue;
                    }
                    let ty = func.dfg.value_ty(value).clone();
                    self.resolve_phi(func, phi, ty)
                } else {
                    next_insn = func.layout.next_insn_of(insn);
                    continue;
                };

                func.dfg.change_to_alias(value, alias);
                next_insn = func.layout.next_insn_of(insn);
                InsnInserter::new(func, CursorLocation::At(insn)).remove_insn();
            }
        }
    }

    fn resolve_phi(&mut self, func: &mut Function, phi: ValuePhi, ty: Type) -> Value {
        let phi_data = self.value_phis.get(phi);
        let block = phi_data.block;
        let vn = self.inserted_phis[block].phi_vn(phi).unwrap();
        if let Some(rep_value) = self.inserted_phis[block].representative_value(vn) {
            return rep_value;
        }

        let phi_args: Vec<_> = phi_data.args().copied().collect();

        let phi_insn = func.dfg.make_insn(InsnData::phi(ty.clone()));
        for phi_arg in phi_args.into_iter() {
            let pout = self.block_pout(func, phi_arg.pred).unwrap();

            let rep_value =
                if let Some(rep_value) = self.partitions[pout].representative_value(phi_arg.vn) {
                    rep_value
                } else {
                    let pred_phi = self.inserted_phis[phi_arg.inserted_block]
                        .phi_of_vn(phi_arg.vn)
                        .unwrap();
                    self.resolve_phi(func, pred_phi, ty.clone())
                };

            func.dfg.append_phi_arg(phi_insn, rep_value, phi_arg.pred);
        }

        let mut inserter = InsnInserter::new(func, CursorLocation::BlockTop(block));
        let result = inserter.make_result(phi_insn).unwrap();
        inserter.attach_result(phi_insn, result);
        inserter.insert_insn(phi_insn);
        self.inserted_phis[block].insert_value(result, vn);

        result
    }

    fn compute_equivalences(&mut self, func: &Function, cfg: &ControlFlowGraph, rpo: &[Block]) {
        debug_assert!(!rpo.is_empty());

        let entry = rpo[0];
        let first_insn = match func.layout.first_insn_of(entry) {
            Some(insn) => insn,
            None => return,
        };

        // Insert function argument to first insn partition.
        let mut first_partition_data = PartitionData::default();
        for &func_arg in &func.arg_values {
            first_partition_data.insert_value(func_arg, self.vn_for_value(func, func_arg));
        }
        self.set_pin(first_insn, first_partition_data);

        self.partition_changed = true;
        while self.partition_changed {
            self.partition_changed = false;

            for &block in rpo {
                for insn in func.layout.iter_insn(block) {
                    if func.dfg.is_phi(insn) {
                        self.transfer_phi(func, cfg, insn);
                    } else {
                        self.transfer_insn(func, cfg, insn);
                    }
                }
            }
        }
    }

    fn transfer_insn(&mut self, func: &Function, cfg: &ControlFlowGraph, insn: Insn) {
        debug_assert!(!func.dfg.is_phi(insn));

        let pin = self.compute_insn_pin(func, cfg, insn);
        self.insns[insn].pin = pin.into();
        let pin_data = &self.partitions[pin].clone();
        let mut pout_data = pin_data.clone();

        // If the insn doesn't have result, do nothing.
        let value = match func.dfg.insn_result(insn) {
            Some(value) => value,
            None => {
                self.insns[insn].pout = pin.into();
                return;
            }
        };

        // If the insn doesn't have value expr format (i.e. the insn has side effect), just insert its
        // result value to the pout.
        let value_expr = match self.value_expr(func, pin, insn) {
            Some(expr) => expr,
            None => {
                pout_data.insert_value(value, self.vn_for_value(func, value));
                self.set_pout(insn, pout_data);
                return;
            }
        };

        // If the insn's value expr is already in its pin data(i.e. the insn is trivially redundant), just
        // insert its result value to the partition cell of the value expr's VN.
        if let Some(vn) = self.partitions[pin].expr_vn(value_expr) {
            pout_data.insert_value(value, vn);
            self.set_pout(insn, pout_data);
            return;
        }

        // Try to find the redundancy beyond the phi function.
        self.searched.clear();
        let vn = self.vn_for_value(func, value);
        pout_data.insert_value(value, vn);
        pout_data.insert_expr(value_expr, vn);
        if let Some(value_phi) = self.compute_value_phi(func, pin, value_expr) {
            pout_data.insert_phi(value_phi, vn);
        }

        self.set_pout(insn, pout_data);
    }

    fn transfer_phi(&mut self, func: &Function, cfg: &ControlFlowGraph, phi: Insn) {
        debug_assert!(func.dfg.is_phi(phi));

        let pin = self.compute_insn_pin(func, cfg, phi);
        self.insns[phi].pin = pin.into();
        let pin_data = &self.partitions[pin];
        let mut pout_data = pin_data.clone();
        let value = func.dfg.insn_result(phi).unwrap();

        let mut value_phi_data = ValuePhiData::new(func.layout.insn_block(phi));
        for (&phi_arg, &pred_block) in func
            .dfg
            .insn_args(phi)
            .iter()
            .zip(func.dfg.phi_blocks(phi).iter())
        {
            let pred_pout = match self.block_pout(func, pred_block) {
                Some(pout) => pout,
                None => {
                    let vn = self.vn_for_value(func, value);
                    pout_data.insert_value(value, vn);
                    self.set_pout(phi, pout_data);
                    return;
                }
            };
            let pred_pout_data = &self.partitions[pred_pout];
            match pred_pout_data.value_vn(phi_arg) {
                Some(vn) => value_phi_data.insert_arg(ValuePhiArg::new(pred_block, pred_block, vn)),
                None => {
                    let vn = self.vn_for_value(func, value);
                    pout_data.insert_value(value, vn);
                    self.set_pout(phi, pout_data);
                    return;
                }
            }
        }

        let value_phi = self.value_phis.intern(value_phi_data);
        if let Some(phi_vn) = pout_data.phi_vn(value_phi) {
            pout_data.insert_value(value, phi_vn);
        } else {
            let vn = self.vn_for_value(func, value);
            pout_data.insert_value(value, vn);
            pout_data.insert_phi(value_phi, vn);
        }

        self.set_pout(phi, pout_data);
    }

    fn compute_insn_pin(
        &mut self,
        func: &Function,
        cfg: &ControlFlowGraph,
        insn: Insn,
    ) -> Partition {
        if func.layout.is_first_insn(insn) {
            self.compute_first_insn_pin(func, cfg, insn)
        } else {
            let prev_insn = func.layout.prev_insn_of(insn).unwrap();
            self.insns[prev_insn].pout.unwrap()
        }
    }

    fn next_vn(&mut self) -> ValueNumber {
        let next_vn = self.next_vn;
        self.next_vn += 1;
        next_vn
    }

    fn vn_for_value(&mut self, func: &Function, value: Value) -> ValueNumber {
        match func.dfg.value_insn(value) {
            Some(insn) => {
                if let Some(pout) = self.insns[insn].pout.expand() {
                    self.partitions[pout]
                        .value_vn(value)
                        .unwrap_or_else(|| self.next_vn())
                } else {
                    self.next_vn()
                }
            }
            None => self.next_vn(),
        }
    }

    fn block_pout(&self, func: &Function, block: Block) -> Option<Partition> {
        let last_insn = func.layout.last_insn_of(block).unwrap();
        self.insns[last_insn].pout.expand()
    }

    fn compute_first_insn_pin(
        &mut self,
        func: &Function,
        cfg: &ControlFlowGraph,
        insn: Insn,
    ) -> Partition {
        let block = func.layout.insn_block(insn);
        let pred_num = cfg.pred_num_of(block);
        if pred_num == 0 {
            // Entry block. Pin for entry block is already set.
            self.insns[insn].pin.unwrap()
        } else if pred_num == 1 {
            // We use reverse post order traversal, so the predecessor is already visited.
            let pred_block = cfg.preds_of(block).next().unwrap();
            let prev_insn = func.layout.last_insn_of(*pred_block).unwrap();
            self.insns[prev_insn].pout.unwrap()
        } else {
            let mut preds = cfg.preds_of(block);
            let first_pred = preds.next().unwrap();
            let first_partition = self.block_pout(func, *first_pred).unwrap();
            let partition_data = preds.fold(
                self.partitions[first_partition].clone(),
                |partition, pred| {
                    if let Some(pout) = self.block_pout(func, *pred) {
                        let pred_partition = &self.partitions[pout];
                        partition.join(pred_partition)
                    } else {
                        partition
                    }
                },
            );

            self.set_pin(insn, partition_data)
        }
    }

    fn compute_value_phi(
        &mut self,
        func: &Function,
        pat: Partition,
        expr: ValueExpr,
    ) -> Option<ValuePhi> {
        let expr_data = self.value_exprs.get(expr);
        if !self.searched.insert(pat) {
            return None;
        }

        let value_phi_data = match expr_data.args.len() {
            0 => None,
            1 => self.value_phi_of_unary(func, pat, expr),
            2 => self.value_phi_of_binary(func, pat, expr),
            _ => unreachable!(),
        }?;

        let block = value_phi_data.block;
        let value_phi = self.value_phis.intern(value_phi_data);
        if self.inserted_phis[block].phi_vn(value_phi).is_none() {
            let vn = self.next_vn();
            self.inserted_phis[block].insert_phi(value_phi, vn);
        }

        Some(value_phi)
    }

    fn value_phi_of_unary(
        &mut self,
        func: &Function,
        pat: Partition,
        expr: ValueExpr,
    ) -> Option<ValuePhiData> {
        let expr_data = self.value_exprs.get(expr);
        debug_assert!(expr_data.args.len() == 1);

        let pat_data = &self.partitions[pat];

        let arg = expr_data.args[0];
        let value_phi = pat_data.phi_of_vn(arg)?;
        let value_phi_data = self.value_phis.get(value_phi);
        let phi_args: Vec<_> = value_phi_data.args().copied().collect();

        let mut new_phi_data = ValuePhiData::new(value_phi_data.block);
        let mut expr = self.value_exprs.get(expr).clone();

        for phi_arg in phi_args.into_iter() {
            expr.set_args(&[phi_arg.vn]);
            let new_arg = self.search_value_phi_arg(func, &expr, phi_arg.pred)?;
            new_phi_data.insert_arg(new_arg);
        }

        Some(new_phi_data)
    }

    fn value_phi_of_binary(
        &mut self,
        func: &Function,
        pat: Partition,
        expr: ValueExpr,
    ) -> Option<ValuePhiData> {
        let expr_data = self.value_exprs.get(expr);
        debug_assert!(expr_data.args.len() == 2);

        let pat_data = &self.partitions[pat];
        let lhs = expr_data.args[0];
        let rhs = expr_data.args[1];

        let lhs_phi = pat_data.phi_of_vn(lhs);
        let rhs_phi = pat_data.phi_of_vn(rhs);
        let mut expr_data = self.value_exprs.get(expr).clone();

        let new_phi_data = match (lhs_phi, rhs_phi) {
            (Some(lhs_phi), Some(rhs_phi)) => {
                let lhs_phi_data = self.value_phis.get(lhs_phi);
                let rhs_phi_data = self.value_phis.get(rhs_phi);
                if lhs_phi_data.block != rhs_phi_data.block {
                    return None;
                }
                let mut new_phi_data = ValuePhiData::new(lhs_phi_data.block);

                let lhs_phi_args: Vec<_> = lhs_phi_data.args().copied().collect();
                let rhs_phi_args: Vec<_> = rhs_phi_data.args().copied().collect();
                for (lhs_arg, rhs_arg) in lhs_phi_args.into_iter().zip(rhs_phi_args.into_iter()) {
                    debug_assert_eq!(lhs_arg.pred, rhs_arg.pred);
                    expr_data.set_args(&[lhs_arg.vn, rhs_arg.vn]);
                    let new_arg = self.search_value_phi_arg(func, &expr_data, lhs_arg.pred)?;
                    new_phi_data.insert_arg(new_arg);
                }
                new_phi_data
            }

            (Some(phi), None) => {
                let phi_data = self.value_phis.get(phi);
                let phi_args: Vec<_> = phi_data.args().copied().collect();
                let mut new_phi_data = ValuePhiData::new(phi_data.block);

                for phi_arg in phi_args.into_iter() {
                    expr_data.set_args(&[phi_arg.vn, rhs]);
                    let new_arg = self.search_value_phi_arg(func, &expr_data, phi_arg.pred)?;
                    new_phi_data.insert_arg(new_arg);
                }
                new_phi_data
            }

            (None, Some(phi)) => {
                let phi_data = self.value_phis.get(phi);
                let phi_args: Vec<_> = phi_data.args().copied().collect();
                let mut new_phi_data = ValuePhiData::new(phi_data.block);

                for phi_arg in phi_args.into_iter() {
                    expr_data.set_args(&[lhs, phi_arg.vn]);
                    let new_arg = self.search_value_phi_arg(func, &expr_data, phi_arg.pred)?;
                    new_phi_data.insert_arg(new_arg);
                }
                new_phi_data
            }
            (None, None) => return None,
        };

        Some(new_phi_data)
    }

    fn search_value_phi_arg(
        &mut self,
        func: &Function,
        expr: &ValueExprData,
        pred: Block,
    ) -> Option<ValuePhiArg> {
        let pred_expr = self.value_exprs.intern(expr.clone());
        let pred_pat = self.block_pout(func, pred)?;

        if let Some(vn) = self.partitions[pred_pat].expr_vn(pred_expr) {
            Some(ValuePhiArg::new(pred, pred, vn))
        } else {
            let pred_phi = self.compute_value_phi(func, pred_pat, pred_expr)?;
            let inserted_block = self.value_phis.get(pred_phi).block;
            let vn = self.inserted_phis[inserted_block].phi_vn(pred_phi).unwrap();
            Some(ValuePhiArg::new(pred, inserted_block, vn))
        }
    }

    fn set_pin(&mut self, insn: Insn, data: PartitionData) -> Partition {
        if let Some(partition) = self.insns[insn].pin.expand() {
            self.partition_changed |= self.partitions[partition] != data;
            self.partitions[partition] = data;
            partition
        } else {
            let partition = self.partitions.push(data);
            self.insns[insn].pin = partition.into();
            self.partition_changed |= true;
            partition
        }
    }

    fn set_pout(&mut self, insn: Insn, data: PartitionData) -> Partition {
        if let Some(partition) = self.insns[insn].pout.expand() {
            self.partition_changed |= self.partitions[partition] != data;
            self.partitions[partition] = data;
            partition
        } else {
            let partition = self.partitions.push(data);
            self.insns[insn].pout = partition.into();
            self.partition_changed |= true;
            partition
        }
    }

    /// Transform insn to `ValueExpr`.
    /// We assume that verifier verifies all definitions of the insn arguments dominates the insn.
    fn value_expr(&mut self, func: &Function, pin: Partition, insn: Insn) -> Option<ValueExpr> {
        use crate::ir::insn::{BinaryOp, CastOp};
        debug_assert!(!func.dfg.is_phi(insn));

        let pin_data = &self.partitions[pin];

        let value_expr_data = match func.dfg.insn_data(insn) {
            InsnData::Binary { code, args } => {
                let lhs = pin_data.value_vn(args[0]).unwrap();
                let rhs = pin_data.value_vn(args[1]).unwrap();
                match code {
                    BinaryOp::Add => ValueExprData::add(lhs, rhs),
                    BinaryOp::Sub => ValueExprData::sub(lhs, rhs),
                    BinaryOp::Mul => ValueExprData::mul(lhs, rhs),
                    BinaryOp::UDiv => ValueExprData::udiv(lhs, rhs),
                    BinaryOp::SDiv => ValueExprData::sdiv(lhs, rhs),
                    BinaryOp::Lt => ValueExprData::lt(lhs, rhs),
                    BinaryOp::Gt => ValueExprData::gt(lhs, rhs),
                    BinaryOp::Slt => ValueExprData::slt(lhs, rhs),
                    BinaryOp::Sgt => ValueExprData::sgt(lhs, rhs),
                    BinaryOp::Eq => ValueExprData::eq(lhs, rhs),
                    BinaryOp::And => ValueExprData::and(lhs, rhs),
                    BinaryOp::Or => ValueExprData::or(lhs, rhs),
                }
            }

            InsnData::Cast { code, args, ty } => {
                let value = pin_data.value_vn(args[0]).unwrap();
                match code {
                    CastOp::Sext => ValueExprData::sext(value, ty.clone()),
                    CastOp::Zext => ValueExprData::zext(value, ty.clone()),
                    CastOp::Trunc => ValueExprData::trunc(value, ty.clone()),
                }
            }
            InsnData::Load { .. }
            | InsnData::Store { .. }
            | InsnData::Jump { .. }
            | InsnData::Branch { .. }
            | InsnData::Return { .. }
            | InsnData::Phi { .. } => return None,
        };

        Some(self.value_exprs.intern(value_expr_data))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash, PartialOrd, Ord)]
struct Partition(pub u32);
entity_impl!(Partition);

#[derive(Debug, Default, Clone)]
struct PartitionData {
    cells: FxHashMap<ValueNumber, PartitionCell>,
    values_map: FxHashMap<Value, ValueNumber>,
    expr_map: FxHashMap<ValueExpr, ValueNumber>,
    phi_map: FxHashMap<ValuePhi, ValueNumber>,
}

impl PartitionData {
    fn join(&self, rhs: &Self) -> Self {
        let mut data = PartitionData::default();

        for (vn, l_cell) in self.cells.iter() {
            if let Some(r_cell) = rhs.cells.get(vn) {
                if let Some(cell) = l_cell.intersection(r_cell) {
                    let vn = cell.vn;
                    let value_expr = cell.value_expr;
                    let value_phi = cell.value_phi;

                    data.values_map.reserve(cell.values.len());
                    for &value in cell.values.iter() {
                        data.values_map.insert(value, vn);
                    }

                    if value_expr.is_some() {
                        data.expr_map.insert(value_expr.unwrap(), vn);
                    }

                    if value_phi.is_some() {
                        data.phi_map.insert(value_phi.unwrap(), vn);
                    }

                    data.cells.insert(cell.vn, cell);
                }
            }
        }

        data
    }

    fn representative_value(&self, vn: ValueNumber) -> Option<Value> {
        self.cells.get(&vn)?.values.iter().next().copied()
    }

    fn value_vn(&self, value: Value) -> Option<ValueNumber> {
        self.values_map.get(&value).copied()
    }

    fn expr_vn(&self, expr: ValueExpr) -> Option<ValueNumber> {
        self.expr_map.get(&expr).copied()
    }

    fn phi_vn(&self, phi: ValuePhi) -> Option<ValueNumber> {
        self.phi_map.get(&phi).copied()
    }

    fn phi_of_vn(&self, vn: ValueNumber) -> Option<ValuePhi> {
        self.cells.get(&vn)?.value_phi.expand()
    }

    fn insert_value(&mut self, value: Value, vn: ValueNumber) {
        self.values_map.insert(value, vn);
        self.cell_mut(vn).values.insert(value);
    }

    fn insert_phi(&mut self, value_phi: ValuePhi, vn: ValueNumber) {
        self.phi_map.insert(value_phi, vn);
        self.cell_mut(vn).value_phi = value_phi.into();
    }

    fn insert_expr(&mut self, value_expr: ValueExpr, vn: ValueNumber) {
        self.expr_map.insert(value_expr, vn);
        self.cell_mut(vn).value_expr = value_expr.into();
    }

    fn cell_mut(&mut self, vn: ValueNumber) -> &mut PartitionCell {
        self.cells
            .entry(vn)
            .or_insert_with(|| PartitionCell::new(vn))
    }
}

impl std::cmp::PartialEq for PartitionData {
    fn eq(&self, rhs: &Self) -> bool {
        self.cells == rhs.cells
    }
}

impl std::cmp::Eq for PartitionData {}

#[derive(Debug, Clone, PartialEq, Eq)]
struct PartitionCell {
    vn: ValueNumber,
    values: FxHashSet<Value>,
    value_expr: PackedOption<ValueExpr>,
    value_phi: PackedOption<ValuePhi>,
}

impl PartitionCell {
    fn new(vn: ValueNumber) -> Self {
        Self {
            vn,
            values: FxHashSet::default(),
            value_expr: None.into(),
            value_phi: None.into(),
        }
    }

    fn intersection(&self, rhs: &Self) -> Option<Self> {
        // Unlike the paper, we add value phi function later in transfer function.
        if self.vn != rhs.vn {
            return None;
        }

        let values: FxHashSet<_> = self.values.intersection(&rhs.values).copied().collect();
        let value_expr = if self.value_expr == rhs.value_expr {
            self.value_expr
        } else {
            None.into()
        };
        let value_phi = if self.value_phi == rhs.value_phi {
            self.value_phi
        } else {
            None.into()
        };

        (!values.is_empty()).then(|| Self {
            vn: self.vn,
            values,
            value_expr,
            value_phi,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash, PartialOrd, Ord)]
struct ValuePhi(u32);
entity_impl!(ValuePhi);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ValuePhiData {
    block: Block,
    args: BTreeSet<ValuePhiArg>,
}

impl ValuePhiData {
    fn new(block: Block) -> Self {
        Self {
            block,
            args: BTreeSet::default(),
        }
    }

    fn insert_arg(&mut self, arg: ValuePhiArg) {
        self.args.insert(arg);
    }

    fn args(&self) -> impl Iterator<Item = &ValuePhiArg> {
        self.args.iter()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash, PartialOrd, Ord)]
struct ValuePhiArg {
    pred: Block,
    inserted_block: Block,
    vn: ValueNumber,
}

impl ValuePhiArg {
    fn new(pred: Block, inserted_block: Block, vn: ValueNumber) -> Self {
        Self {
            pred,
            inserted_block,
            vn,
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Copy, Hash, PartialOrd, Ord)]
struct InsnPartition {
    pin: PackedOption<Partition>,
    pout: PackedOption<Partition>,
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash, PartialOrd, Ord)]
struct ValueExpr(u32);
entity_impl!(ValueExpr);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ValueExprData {
    kind: ValueExprOpKind,
    args: Vec<ValueNumber>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum ValueExprOpKind {
    Add,
    Sub,
    Mul,
    UDiv,
    SDiv,
    Lt,
    Gt,
    Slt,
    Sgt,
    Eq,
    And,
    Or,
    Sext(Type),
    Trunc(Type),
    Zext(Type),
}

macro_rules! binop_ctor{
    (
        $(($name:ident, $variant:ident),)*
    ) => {
        $(
            fn $name(lhs: ValueNumber, rhs: ValueNumber) -> ValueExprData {
                let mut data = ValueExprData {
                    kind: ValueExprOpKind::$variant,
                    args: vec![lhs, rhs],
                };
                data.canonicalize_args();
                data

            }
        )*
    };

}

macro_rules! cast_op_ctor {
    (
        $(($name:ident, $variant:ident),)*
    ) => {
        $(
            fn $name(value: ValueNumber, ty: Type) -> ValueExprData {
                let kind = ValueExprOpKind::$variant(ty);
                ValueExprData {
                    kind,
                    args: vec![value],
                }
            }
        )*
    };
}

impl ValueExprData {
    fn set_args(&mut self, args: &[ValueNumber]) {
        debug_assert_eq!(self.args.len(), args.len());

        self.args = args.to_vec();
        self.canonicalize_args();
    }

    fn is_commutative(&self) -> bool {
        use ValueExprOpKind::*;
        matches!(self.kind, Add | Mul | Eq | And | Or)
    }

    fn canonicalize_args(&mut self) {
        if self.is_commutative() {
            self.args.sort_unstable();
        }
    }

    binop_ctor! {
        (add, Add),
        (sub,Sub),
        (mul, Mul),
        (udiv, UDiv),
        (sdiv, SDiv),
        (lt, Lt),
        (gt, Gt),
        (slt, Slt),
        (sgt, Sgt),
        (eq, Eq),
        (and, And),
        (or, Or),
    }

    cast_op_ctor! {
        (sext, Sext),
        (zext, Zext),
        (trunc, Trunc),
    }
}

#[derive(Debug)]
struct Interner<K, V>
where
    K: EntityRef,
{
    map: FxHashMap<V, K>,
    store: PrimaryMap<K, V>,
}

impl<K, V> Interner<K, V>
where
    K: EntityRef,
    V: Eq + Hash + Clone,
{
    fn intern(&mut self, value: V) -> K {
        if let Some(&key) = self.map.get(&value) {
            key
        } else {
            let key = self.store.push(value.clone());
            self.map.insert(value, key);
            key
        }
    }

    fn get(&self, key: K) -> &V {
        &self.store[key]
    }

    fn clear(&mut self) {
        self.map.clear();
        self.store.clear();
    }
}

impl<K, V> Default for Interner<K, V>
where
    K: EntityRef,
{
    fn default() -> Self {
        Self {
            map: FxHashMap::default(),
            store: PrimaryMap::default(),
        }
    }
}
