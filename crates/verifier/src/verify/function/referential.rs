use sonatina_ir::{InstId, Value};

use crate::diagnostic::{Diagnostic, DiagnosticCode, Location};

use super::{FunctionVerifier, refs::collect_inst_refs};

impl FunctionVerifier<'_> {
    pub(super) fn check_referential_integrity(&mut self) {
        let mut insts_to_scan: Vec<InstId> = self
            .block_order
            .iter()
            .flat_map(|block| {
                self.block_to_insts
                    .get(block)
                    .into_iter()
                    .flatten()
                    .copied()
            })
            .collect();

        if !self.cfg.allow_detached_entities {
            for inst in self.func.dfg.insts.keys() {
                if !self.inst_to_block.contains_key(&inst) {
                    insts_to_scan.push(inst);
                }
            }
            insts_to_scan.sort_by_key(|inst| inst.as_u32());
        }

        for inst_id in insts_to_scan {
            let Some(inst) = self.func.dfg.get_inst(inst_id) else {
                self.emit(Diagnostic::error(
                    DiagnosticCode::InvalidInstRef,
                    "instruction id is missing in DFG",
                    Location::Inst {
                        func: self.func_ref,
                        block: self.inst_to_block.get(&inst_id).copied(),
                        inst: inst_id,
                    },
                ));
                continue;
            };

            let refs = collect_inst_refs(inst);
            for value in refs.values {
                if !self.func.dfg.has_value(value) {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::InvalidValueRef,
                            "instruction references value outside DFG value table",
                            Location::Inst {
                                func: self.func_ref,
                                block: self.inst_to_block.get(&inst_id).copied(),
                                inst: inst_id,
                            },
                        )
                        .with_note(format!("invalid value id {}", value.as_u32()))
                        .with_snippet(self.snippet_for_inst(inst_id)),
                    );
                    continue;
                }

                if !self.cfg.allow_detached_entities
                    && let Some(Value::Inst { inst, .. }) = self.func.dfg.get_value(value)
                    && !self.inst_to_block.contains_key(inst)
                {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::InsertedButUnlisted,
                            "instruction uses detached value definition",
                            Location::Inst {
                                func: self.func_ref,
                                block: self.inst_to_block.get(&inst_id).copied(),
                                inst: inst_id,
                            },
                        )
                        .with_note(format!(
                            "value v{} is defined by detached inst {}",
                            value.as_u32(),
                            inst.as_u32()
                        )),
                    );
                }
            }

            for block in refs.blocks {
                if !self.func.dfg.has_block(block) {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::InvalidBlockRef,
                            "instruction references block outside DFG block table",
                            Location::Inst {
                                func: self.func_ref,
                                block: self.inst_to_block.get(&inst_id).copied(),
                                inst: inst_id,
                            },
                        )
                        .with_note(format!("invalid block id {}", block.as_u32())),
                    );
                }
            }

            for func_ref in refs.funcs {
                if self.ctx.get_sig(func_ref).is_none() {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::InvalidFuncRef,
                            "instruction references unknown function",
                            Location::Inst {
                                func: self.func_ref,
                                block: self.inst_to_block.get(&inst_id).copied(),
                                inst: inst_id,
                            },
                        )
                        .with_note(format!("missing function id {}", func_ref.as_u32())),
                    );
                }
            }

            for gv in refs.globals {
                if self.ctx.with_gv_store(|store| store.get(gv).is_none()) {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::InvalidGlobalRef,
                            "instruction references unknown global",
                            Location::Inst {
                                func: self.func_ref,
                                block: self.inst_to_block.get(&inst_id).copied(),
                                inst: inst_id,
                            },
                        )
                        .with_note(format!("missing global id {}", gv.as_u32())),
                    );
                }
            }

            for ty in refs.types {
                if !self.is_type_valid(ty) {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::InvalidTypeRef,
                            "instruction references invalid type",
                            Location::Inst {
                                func: self.func_ref,
                                block: self.inst_to_block.get(&inst_id).copied(),
                                inst: inst_id,
                            },
                        )
                        .with_note(format!("invalid type {ty:?}")),
                    );
                }
            }
        }
    }
}
