use sonatina_ir::Value;

use crate::{
    diagnostic::{Diagnostic, DiagnosticCode, Location},
    verify::module_invariants::has_by_value_function_type_in_signature,
};

use super::FunctionVerifier;

impl FunctionVerifier<'_> {
    pub(super) fn check_signature_and_values(&mut self) {
        let Some(sig) = self.sig.clone() else {
            self.emit(Diagnostic::error(
                DiagnosticCode::InvalidSignature,
                "function signature is missing in module context",
                Location::Function(self.func_ref),
            ));
            return;
        };

        if self.func.arg_values.len() != sig.args().len() {
            self.emit(
                Diagnostic::error(
                    DiagnosticCode::InvalidSignature,
                    "argument value count does not match function signature",
                    Location::Function(self.func_ref),
                )
                .with_note(format!(
                    "expected {}, found {}",
                    sig.args().len(),
                    self.func.arg_values.len()
                )),
            );
        }

        for (index, value) in self.func.arg_values.iter().enumerate() {
            let Some(value_data) = self.func.dfg.get_value(*value) else {
                self.emit(
                    Diagnostic::error(
                        DiagnosticCode::InvalidValueRef,
                        "function argument references missing value",
                        Location::Function(self.func_ref),
                    )
                    .with_note(format!(
                        "arg index {index} uses missing value {}",
                        value.as_u32()
                    )),
                );
                continue;
            };

            match value_data {
                Value::Arg { ty, idx } => {
                    if !self.is_type_valid(*ty) {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::InvalidTypeRef,
                                "argument value has an invalid type",
                                Location::Value {
                                    func: self.func_ref,
                                    value: *value,
                                },
                            )
                            .with_note(format!("arg index {index}")),
                        );
                    }
                    if has_by_value_function_type_in_signature(self.ctx, *ty) {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::InvalidSignature,
                                "argument value type contains a by-value function type",
                                Location::Value {
                                    func: self.func_ref,
                                    value: *value,
                                },
                            )
                            .with_note(format!("arg index {index}")),
                        );
                    }

                    if *idx != index {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::ValueTypeMismatch,
                                "argument value index does not match its position",
                                Location::Value {
                                    func: self.func_ref,
                                    value: *value,
                                },
                            )
                            .with_note(format!("expected index {index}, found {idx}")),
                        );
                    }

                    if let Some(expected) = sig.args().get(index)
                        && ty != expected
                    {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::ValueTypeMismatch,
                                "argument value type does not match function signature",
                                Location::Value {
                                    func: self.func_ref,
                                    value: *value,
                                },
                            )
                            .with_note(format!("expected {:?}, found {:?}", expected, ty)),
                        );
                    }
                }
                _ => {
                    self.emit(Diagnostic::error(
                        DiagnosticCode::ValueTypeMismatch,
                        "function argument table contains non-argument value",
                        Location::Value {
                            func: self.func_ref,
                            value: *value,
                        },
                    ));
                }
            }
        }

        for (value_id, value_data) in self.func.dfg.values.iter() {
            match value_data {
                Value::Immediate { imm, ty } => {
                    if imm.ty() != *ty {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::ValueTypeMismatch,
                                "immediate value stores mismatched type metadata",
                                Location::Value {
                                    func: self.func_ref,
                                    value: value_id,
                                },
                            )
                            .with_note(format!(
                                "immediate is {:?}, value type is {:?}",
                                imm.ty(),
                                ty
                            )),
                        );
                    }
                }
                Value::Arg { ty, idx } => {
                    if !self.is_type_valid(*ty) {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::InvalidTypeRef,
                                "argument value has an invalid type",
                                Location::Value {
                                    func: self.func_ref,
                                    value: value_id,
                                },
                            )
                            .with_note(format!("arg index {}", idx)),
                        );
                    }
                    if has_by_value_function_type_in_signature(self.ctx, *ty) {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::InvalidSignature,
                                "argument value type contains a by-value function type",
                                Location::Value {
                                    func: self.func_ref,
                                    value: value_id,
                                },
                            )
                            .with_note(format!("arg index {}", idx)),
                        );
                    }

                    let expected = sig.args().get(*idx);
                    if expected.is_none() {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::ValueTypeMismatch,
                                "argument value index is out of signature bounds",
                                Location::Value {
                                    func: self.func_ref,
                                    value: value_id,
                                },
                            )
                            .with_note(format!("arg index {} is out of bounds", idx)),
                        );
                    } else if Some(ty) != expected {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::ValueTypeMismatch,
                                "argument value type does not match signature",
                                Location::Value {
                                    func: self.func_ref,
                                    value: value_id,
                                },
                            )
                            .with_note(format!("expected {:?}, found {:?}", expected, ty)),
                        );
                    }
                }
                Value::Inst { inst, ty } => {
                    if !self.func.dfg.has_inst(*inst) {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::InvalidInstRef,
                                "value points to an instruction that does not exist",
                                Location::Value {
                                    func: self.func_ref,
                                    value: value_id,
                                },
                            )
                            .with_note(format!("missing instruction id {}", inst.as_u32())),
                        );
                    }
                    if !self.is_type_valid(*ty) {
                        self.emit(Diagnostic::error(
                            DiagnosticCode::InvalidTypeRef,
                            "instruction value has invalid type",
                            Location::Value {
                                func: self.func_ref,
                                value: value_id,
                            },
                        ));
                    }
                }
                Value::Global { gv, ty } => {
                    if self.ctx.with_gv_store(|store| store.get(*gv).is_none()) {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::InvalidGlobalRef,
                                "value references a global that does not exist",
                                Location::Value {
                                    func: self.func_ref,
                                    value: value_id,
                                },
                            )
                            .with_note(format!("missing global id {}", gv.as_u32())),
                        );
                    } else {
                        let expected_gv_ty = self.ctx.with_gv_store(|store| store.ty(*gv));
                        let matches = self
                            .pointee_ty(*ty)
                            .is_some_and(|pointee| pointee == expected_gv_ty);
                        if !matches {
                            self.emit(
                                Diagnostic::error(
                                    DiagnosticCode::ValueTypeMismatch,
                                    "global value does not have pointer-to-global type",
                                    Location::Value {
                                        func: self.func_ref,
                                        value: value_id,
                                    },
                                )
                                .with_note(format!(
                                    "global type is {:?}, value type is {:?}",
                                    expected_gv_ty, ty
                                )),
                            );
                        }
                    }
                }
                Value::Undef { ty } => {
                    if !self.is_type_valid(*ty) {
                        self.emit(Diagnostic::error(
                            DiagnosticCode::InvalidTypeRef,
                            "undef value has invalid type",
                            Location::Value {
                                func: self.func_ref,
                                value: value_id,
                            },
                        ));
                    }
                }
            }
        }
    }
}
