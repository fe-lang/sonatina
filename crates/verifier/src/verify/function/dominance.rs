use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    BlockId, InstId, Value,
    inst::{control_flow, downcast},
};

use crate::diagnostic::{Diagnostic, DiagnosticCode, Location};

use super::{
    FunctionVerifier,
    analysis::{compute_idom, compute_reachable, dominates},
    refs::collect_inst_refs,
};

impl FunctionVerifier<'_> {
    pub(super) fn check_dominance_rules(&mut self) {
        if self.block_order.is_empty() {
            return;
        }

        let mut covered = FxHashSet::default();
        let mut components = Vec::new();

        if let Some(entry) = self.func.layout.entry_block()
            && self.block_order.contains(&entry)
        {
            let nodes = compute_reachable(entry, &self.succs);
            covered.extend(nodes.iter().copied());
            components.push((entry, nodes));
        }

        if self.cfg.should_run_deep_sanity() {
            let blocks = self.block_order.clone();
            for block in blocks {
                if covered.contains(&block) {
                    continue;
                }
                let nodes = compute_reachable(block, &self.succs);
                covered.extend(nodes.iter().copied());
                components.push((block, nodes));
            }
        }

        let mut idom = FxHashMap::default();
        let block_order_index = self.block_position_map();
        for (root, nodes) in components {
            let local = compute_idom(root, &nodes, &self.succs, &self.preds, &block_order_index);
            idom.extend(local);
        }

        let blocks = self.block_order.clone();
        for block in blocks {
            if !idom.contains_key(&block) {
                continue;
            }

            let insts = self.block_to_insts.get(&block).cloned().unwrap_or_default();
            for inst in &insts {
                let Some(inst_data) = self.func.dfg.get_inst(*inst) else {
                    continue;
                };

                if downcast::<&control_flow::Phi>(self.ctx.inst_set, inst_data).is_some() {
                    self.check_phi_edge_availability(*inst, &idom, &block_order_index);
                    continue;
                }

                let use_index = self
                    .inst_index_in_block
                    .get(inst)
                    .copied()
                    .unwrap_or(usize::MAX);
                let refs = collect_inst_refs(inst_data);
                for value in refs.values {
                    let Some(Value::Inst { inst: def_inst, .. }) = self.func.dfg.get_value(value)
                    else {
                        continue;
                    };

                    let Some(def_block) = self.inst_to_block.get(def_inst).copied() else {
                        if !self.cfg.allow_detached_entities {
                            self.emit(
                                Diagnostic::error(
                                    DiagnosticCode::DefDoesNotDominateUse,
                                    "value definition is detached from layout",
                                    Location::Inst {
                                        func: self.func_ref,
                                        block: Some(block),
                                        inst: *inst,
                                    },
                                )
                                .with_note(format!(
                                    "value v{} is defined by detached inst {}",
                                    value.as_u32(),
                                    def_inst.as_u32()
                                )),
                            );
                        }
                        continue;
                    };

                    if def_block == block {
                        let Some(def_index) = self.inst_index_in_block.get(def_inst).copied()
                        else {
                            continue;
                        };
                        if def_index >= use_index {
                            self.emit(
                                Diagnostic::error(
                                    DiagnosticCode::UseBeforeDefInBlock,
                                    "instruction uses a value before its local definition",
                                    Location::Inst {
                                        func: self.func_ref,
                                        block: Some(block),
                                        inst: *inst,
                                    },
                                )
                                .with_note(format!(
                                    "def inst {} appears at index {}, use at {}",
                                    def_inst.as_u32(),
                                    def_index,
                                    use_index
                                )),
                            );
                        }
                        continue;
                    }

                    if !dominates(def_block, block, &idom, &block_order_index) {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::DefDoesNotDominateUse,
                                "value definition does not dominate its use",
                                Location::Inst {
                                    func: self.func_ref,
                                    block: Some(block),
                                    inst: *inst,
                                },
                            )
                            .with_note(format!(
                                "value v{} defined in block {}, used in block {}",
                                value.as_u32(),
                                def_block.as_u32(),
                                block.as_u32()
                            )),
                        );
                    }
                }
            }
        }
    }

    fn check_phi_edge_availability(
        &mut self,
        phi_inst: InstId,
        idom: &FxHashMap<BlockId, BlockId>,
        block_order_index: &FxHashMap<BlockId, usize>,
    ) {
        let Some(block) = self.inst_to_block.get(&phi_inst).copied() else {
            return;
        };
        let Some(inst_data) = self.func.dfg.get_inst(phi_inst) else {
            return;
        };
        let Some(phi) = downcast::<&control_flow::Phi>(self.ctx.inst_set, inst_data) else {
            return;
        };

        for (value, pred) in phi.args() {
            let Some(Value::Inst { inst: def_inst, .. }) = self.func.dfg.get_value(*value) else {
                continue;
            };

            let Some(def_block) = self.inst_to_block.get(def_inst).copied() else {
                if !self.cfg.allow_detached_entities {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::PhiIncomingNotAvailableOnEdge,
                            "phi incoming value definition is detached from layout",
                            Location::Inst {
                                func: self.func_ref,
                                block: Some(block),
                                inst: phi_inst,
                            },
                        )
                        .with_note(format!(
                            "value v{} is defined by detached inst {}",
                            value.as_u32(),
                            def_inst.as_u32()
                        )),
                    );
                }
                continue;
            };

            if *def_inst == phi_inst {
                if !dominates(block, *pred, idom, block_order_index) {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::SelfReferentialPhiNotInLoop,
                            "self-referential phi incoming is not dominated by phi block",
                            Location::Inst {
                                func: self.func_ref,
                                block: Some(block),
                                inst: phi_inst,
                            },
                        )
                        .with_note(format!("incoming predecessor block {}", pred.as_u32())),
                    );
                }
                continue;
            }

            if def_block != *pred && !dominates(def_block, *pred, idom, block_order_index) {
                self.emit(
                    Diagnostic::error(
                        DiagnosticCode::PhiIncomingNotAvailableOnEdge,
                        "phi incoming definition is not available on predecessor edge",
                        Location::Inst {
                            func: self.func_ref,
                            block: Some(block),
                            inst: phi_inst,
                        },
                    )
                    .with_note(format!(
                        "value v{} defined in block {}, incoming predecessor {}",
                        value.as_u32(),
                        def_block.as_u32(),
                        pred.as_u32()
                    )),
                );
            }
        }
    }
}
