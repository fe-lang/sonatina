use rustc_hash::FxHashSet;
use sonatina_ir::inst::{control_flow, downcast};

use crate::diagnostic::{Diagnostic, DiagnosticCode, Location};

use super::FunctionVerifier;

impl FunctionVerifier<'_> {
    pub(super) fn check_phi_rules(&mut self) {
        let entry = self.func.layout.entry_block();

        let blocks = self.block_order.clone();
        for block in blocks {
            let insts = self.block_to_insts.get(&block).cloned().unwrap_or_default();
            let preds = self.preds.get(&block).cloned().unwrap_or_default();
            let pred_set: FxHashSet<_> = preds.iter().copied().collect();

            let mut seen_non_phi = false;
            for inst in insts {
                let Some(inst_data) = self.func.dfg.get_inst(inst) else {
                    continue;
                };

                let Some(phi) = downcast::<&control_flow::Phi>(self.ctx.inst_set, inst_data) else {
                    seen_non_phi = true;
                    continue;
                };

                if seen_non_phi {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::PhiNotAtBlockTop,
                            "phi instruction must appear at the beginning of the block",
                            Location::Inst {
                                func: self.func_ref,
                                block: Some(block),
                                inst,
                            },
                        )
                        .with_snippet(self.snippet_for_inst(inst)),
                    );
                }

                if entry == Some(block) {
                    self.emit(Diagnostic::error(
                        DiagnosticCode::PhiInEntryBlock,
                        "entry block must not contain phi instructions",
                        Location::Inst {
                            func: self.func_ref,
                            block: Some(block),
                            inst,
                        },
                    ));
                }

                let mut seen_incomings = FxHashSet::default();
                let result_ty = self.inst_result_ty(inst);

                for (value, pred_block) in phi.args() {
                    if !pred_set.contains(pred_block) {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::PhiHasNonPredIncoming,
                                "phi incoming block is not a CFG predecessor",
                                Location::Inst {
                                    func: self.func_ref,
                                    block: Some(block),
                                    inst,
                                },
                            )
                            .with_note(format!("incoming from block {}", pred_block.as_u32())),
                        );
                    }

                    if !seen_incomings.insert(*pred_block) {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::PhiDuplicateIncomingBlock,
                                "phi contains duplicate incoming block",
                                Location::Inst {
                                    func: self.func_ref,
                                    block: Some(block),
                                    inst,
                                },
                            )
                            .with_note(format!("duplicate predecessor {}", pred_block.as_u32())),
                        );
                    }

                    if let (Some(arg_ty), Some(res_ty)) = (self.value_ty(*value), result_ty)
                        && arg_ty != res_ty
                    {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::PhiIncomingTypeMismatch,
                                "phi incoming value type differs from phi result type",
                                Location::Inst {
                                    func: self.func_ref,
                                    block: Some(block),
                                    inst,
                                },
                            )
                            .with_note(format!("expected {:?}, found {:?}", res_ty, arg_ty)),
                        );
                    }
                }

                if seen_incomings.len() != pred_set.len() {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::PhiArgCountMismatchPreds,
                            "phi incoming blocks do not match predecessor set",
                            Location::Inst {
                                func: self.func_ref,
                                block: Some(block),
                                inst,
                            },
                        )
                        .with_note(format!(
                            "expected {} predecessor(s), found {} incoming block(s)",
                            pred_set.len(),
                            seen_incomings.len()
                        )),
                    );
                }
            }
        }
    }
}
