use std::collections::BTreeSet;

use rustc_hash::FxHashMap;
use sonatina_ir::{InstId, Value, ValueId};

use crate::diagnostic::{Diagnostic, DiagnosticCode, Location};

use super::FunctionVerifier;

impl FunctionVerifier<'_> {
    pub(super) fn check_metadata_consistency(&mut self) {
        for inst in self.func.dfg.insts.keys() {
            let Some(result) = self.func.dfg.try_inst_result(inst).flatten() else {
                continue;
            };

            let Some(value_data) = self.func.dfg.get_value(result) else {
                self.emit(
                    Diagnostic::error(
                        DiagnosticCode::InstResultMapBroken,
                        "inst_results points to a missing value",
                        Location::Inst {
                            func: self.func_ref,
                            block: self.inst_to_block.get(&inst).copied(),
                            inst,
                        },
                    )
                    .with_note(format!("missing value id {}", result.as_u32())),
                );
                continue;
            };

            if !matches!(value_data, Value::Inst { inst: owner, .. } if *owner == inst) {
                self.emit(
                    Diagnostic::error(
                        DiagnosticCode::InstResultMapBroken,
                        "inst_results and Value::Inst mapping are inconsistent",
                        Location::Inst {
                            func: self.func_ref,
                            block: self.inst_to_block.get(&inst).copied(),
                            inst,
                        },
                    )
                    .with_note(format!("inst_result points to value v{}", result.as_u32())),
                );
            }
        }

        for (value_id, value_data) in self.func.dfg.values.iter() {
            if let Value::Inst { inst, .. } = value_data
                && self.func.dfg.try_inst_result(*inst).flatten() != Some(value_id)
            {
                self.emit(
                    Diagnostic::error(
                        DiagnosticCode::InstResultMapBroken,
                        "Value::Inst does not map back via inst_results",
                        Location::Value {
                            func: self.func_ref,
                            value: value_id,
                        },
                    )
                    .with_note(format!("owner inst {}", inst.as_u32())),
                );
            }
        }

        if self.cfg.should_check_users() {
            let mut expected: FxHashMap<ValueId, BTreeSet<InstId>> = FxHashMap::default();
            let blocks = self.block_order.clone();
            for block in blocks {
                for &inst in self.block_to_insts.get(&block).into_iter().flatten() {
                    let Some(inst_data) = self.func.dfg.get_inst(inst) else {
                        continue;
                    };

                    inst_data.for_each_value(&mut |value| {
                        expected.entry(value).or_default().insert(inst);
                    });
                }
            }

            for value_id in self.func.dfg.values.keys() {
                let expected_users = expected.remove(&value_id).unwrap_or_default();
                let actual_users = self
                    .func
                    .dfg
                    .users_set(value_id)
                    .cloned()
                    .unwrap_or_default();

                if actual_users != expected_users {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::UsersSetMismatch,
                            "dfg.users set does not match scanned instruction uses",
                            Location::Value {
                                func: self.func_ref,
                                value: value_id,
                            },
                        )
                        .with_note(format!(
                            "expected {:?}, found {:?}",
                            expected_users, actual_users
                        )),
                    );
                }
            }
        }

        if self.cfg.should_check_value_caches() {
            let mut immediate_entries: Vec<_> = self
                .func
                .dfg
                .immediates
                .iter()
                .map(|(imm, value_id)| (*imm, *value_id))
                .collect();
            immediate_entries.sort_by(|(lhs_imm, lhs_value), (rhs_imm, rhs_value)| {
                lhs_value
                    .as_u32()
                    .cmp(&rhs_value.as_u32())
                    .then_with(|| format!("{lhs_imm:?}").cmp(&format!("{rhs_imm:?}")))
            });

            for (imm, value_id) in immediate_entries {
                let Some(value_data) = self.func.dfg.get_value(value_id) else {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::ImmediateCacheMismatch,
                            "immediate cache points to missing value",
                            Location::Function(self.func_ref),
                        )
                        .with_note(format!(
                            "immediate {:?} -> v{}",
                            imm,
                            value_id.as_u32()
                        )),
                    );
                    continue;
                };

                match value_data {
                    Value::Immediate { imm: actual, ty } if *actual == imm && *ty == imm.ty() => {}
                    Value::Immediate { imm: actual, ty } => {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::ImmediateCacheMismatch,
                                "immediate cache entry does not match value payload",
                                Location::Value {
                                    func: self.func_ref,
                                    value: value_id,
                                },
                            )
                            .with_note(format!(
                                "cache {:?}, value imm {:?}, value ty {:?}",
                                imm, actual, ty
                            )),
                        );
                    }
                    _ => {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::ImmediateCacheMismatch,
                                "immediate cache entry points to non-immediate value",
                                Location::Value {
                                    func: self.func_ref,
                                    value: value_id,
                                },
                            )
                            .with_note(format!("cache immediate {:?}", imm)),
                        );
                    }
                }
            }

            for (value_id, value_data) in self.func.dfg.values.iter() {
                if let Value::Immediate { imm, .. } = value_data
                    && self.func.dfg.immediates.get(imm) != Some(&value_id)
                {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::ImmediateCacheMismatch,
                            "immediate value does not round-trip through immediate cache",
                            Location::Value {
                                func: self.func_ref,
                                value: value_id,
                            },
                        )
                        .with_note(format!("immediate {:?}", imm)),
                    );
                }
            }

            let mut global_entries: Vec<_> = self
                .func
                .dfg
                .globals
                .iter()
                .map(|(gv, value_id)| (*gv, *value_id))
                .collect();
            global_entries.sort_by(|(lhs_gv, lhs_value), (rhs_gv, rhs_value)| {
                lhs_gv
                    .as_u32()
                    .cmp(&rhs_gv.as_u32())
                    .then_with(|| lhs_value.as_u32().cmp(&rhs_value.as_u32()))
            });

            for (gv, value_id) in global_entries {
                let Some(value_data) = self.func.dfg.get_value(value_id) else {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::GlobalCacheMismatch,
                            "global cache points to missing value",
                            Location::Function(self.func_ref),
                        )
                        .with_note(format!(
                            "global {} -> v{}",
                            gv.as_u32(),
                            value_id.as_u32()
                        )),
                    );
                    continue;
                };

                if !matches!(value_data, Value::Global { gv: actual, .. } if *actual == gv) {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::GlobalCacheMismatch,
                            "global cache entry does not match global value payload",
                            Location::Value {
                                func: self.func_ref,
                                value: value_id,
                            },
                        )
                        .with_note(format!("cache global {}", gv.as_u32())),
                    );
                }
            }

            for (value_id, value_data) in self.func.dfg.values.iter() {
                if let Value::Global { gv, .. } = value_data
                    && self.func.dfg.globals.get(gv) != Some(&value_id)
                {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::GlobalCacheMismatch,
                            "global value does not round-trip through global cache",
                            Location::Value {
                                func: self.func_ref,
                                value: value_id,
                            },
                        )
                        .with_note(format!("global id {}", gv.as_u32())),
                    );
                }
            }
        }
    }
}
