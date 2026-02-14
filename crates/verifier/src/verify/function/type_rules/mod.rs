use sonatina_ir::{
    BlockId, GlobalVariableRef, Immediate, Inst, InstArity, InstId, Type, ValueId,
    inst::{data::SymbolRef, downcast},
    module::FuncRef,
    types::CompoundType,
    visitor::Visitor,
};

use crate::diagnostic::{Diagnostic, DiagnosticCode, Location};

use super::FunctionVerifier;
use dispatch::VerifyInst;

mod dispatch;

impl FunctionVerifier<'_> {
    pub(super) fn check_type_rules(&mut self) {
        let mut insts: Vec<_> = self
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
            let mut detached: Vec<_> = self
                .func
                .dfg
                .insts
                .keys()
                .filter(|inst| !self.inst_to_block.contains_key(inst))
                .collect();
            detached.sort_by_key(|inst| inst.as_u32());
            insts.extend(detached);
        }

        for inst_id in insts {
            let Some(inst) = self.func.dfg.get_inst(inst_id) else {
                continue;
            };

            self.verify_inst_type(inst_id, inst);
        }
    }

    fn verify_inst_type(&mut self, inst_id: InstId, inst: &dyn Inst) {
        fn count_arity(inst: &dyn Inst) -> usize {
            struct ArityCounter {
                count: usize,
            }

            impl Visitor for ArityCounter {
                fn visit_ty(&mut self, _item: &Type) {
                    self.count += 1;
                }

                fn visit_value_id(&mut self, _item: ValueId) {
                    self.count += 1;
                }

                fn visit_block_id(&mut self, _item: BlockId) {
                    self.count += 1;
                }

                fn visit_func_ref(&mut self, _item: FuncRef) {
                    self.count += 1;
                }

                fn visit_gv_ref(&mut self, _item: GlobalVariableRef) {
                    self.count += 1;
                }
            }

            let mut counter = ArityCounter { count: 0 };
            inst.accept(&mut counter);
            counter.count
        }

        let expected_arity = inst.arity();
        let rule = downcast::<&dyn VerifyInst>(self.ctx.inst_set, inst);
        let actual_arity = rule.map_or_else(
            || count_arity(inst),
            |rule| rule.actual_arity().unwrap_or_else(|| count_arity(inst)),
        );

        if !expected_arity.accepts(actual_arity) {
            let expected = match expected_arity {
                InstArity::Exact(n) => n.to_string(),
                InstArity::AtLeast(n) => format!("at least {n}"),
                InstArity::AtMost(n) => format!("at most {n}"),
                InstArity::Range { min, max } => format!("{min}..={max}"),
            };
            self.emit(
                Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    "instruction argument count does not match declared arity",
                    self.inst_location(inst_id),
                )
                .with_note(format!("expected {expected}, found {actual_arity}")),
            );
            return;
        }

        if let Some(rule) = rule {
            rule.verify_inst(self, inst_id);
        }
    }

    fn verify_unary_integral_same(&mut self, inst_id: InstId, arg: ValueId, opname: &str) {
        let location = self.inst_location(inst_id);
        let Some(arg_ty) = self.value_ty(arg) else {
            return;
        };

        if !arg_ty.is_integral() {
            self.emit(
                Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    format!("{opname} operand must be integral"),
                    location.clone(),
                )
                .with_note(format!("found operand type {:?}", arg_ty)),
            );
        }

        self.expect_result_ty(inst_id, arg_ty, location);
    }

    fn verify_binary_integral_same(
        &mut self,
        inst_id: InstId,
        lhs: ValueId,
        rhs: ValueId,
        opname: &str,
    ) {
        let location = self.inst_location(inst_id);
        let Some(lhs_ty) = self.value_ty(lhs) else {
            return;
        };
        let Some(rhs_ty) = self.value_ty(rhs) else {
            return;
        };

        if !lhs_ty.is_integral() || !rhs_ty.is_integral() {
            self.emit(
                Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    format!("{opname} operands must be integral"),
                    location.clone(),
                )
                .with_note(format!("lhs {:?}, rhs {:?}", lhs_ty, rhs_ty)),
            );
        }
        if lhs_ty != rhs_ty {
            self.emit(
                Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    format!("{opname} operands must have identical types"),
                    location.clone(),
                )
                .with_note(format!("lhs {:?}, rhs {:?}", lhs_ty, rhs_ty)),
            );
        }

        self.expect_result_ty(inst_id, lhs_ty, location);
    }

    fn verify_shift(&mut self, inst_id: InstId, bits: ValueId, value: ValueId, opname: &str) {
        let location = self.inst_location(inst_id);
        let Some(bits_ty) = self.value_ty(bits) else {
            return;
        };
        let Some(value_ty) = self.value_ty(value) else {
            return;
        };

        if !bits_ty.is_integral() || !value_ty.is_integral() {
            self.emit(
                Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    format!("{opname} operands must be integral"),
                    location.clone(),
                )
                .with_note(format!("bits {:?}, value {:?}", bits_ty, value_ty)),
            );
        }
        if bits_ty != value_ty {
            self.emit(
                Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    format!("{opname} operands must have identical types"),
                    location.clone(),
                )
                .with_note(format!("bits {:?}, value {:?}", bits_ty, value_ty)),
            );
        }

        self.expect_result_ty(inst_id, value_ty, location);
    }

    fn verify_cmp(&mut self, inst_id: InstId, lhs: ValueId, rhs: ValueId, opname: &str) {
        let location = self.inst_location(inst_id);
        let Some(lhs_ty) = self.value_ty(lhs) else {
            return;
        };
        let Some(rhs_ty) = self.value_ty(rhs) else {
            return;
        };

        if !lhs_ty.is_integral() || !rhs_ty.is_integral() {
            self.emit(
                Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    format!("{opname} operands must be integral"),
                    location.clone(),
                )
                .with_note(format!("lhs {:?}, rhs {:?}", lhs_ty, rhs_ty)),
            );
        }
        if lhs_ty != rhs_ty {
            self.emit(
                Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    format!("{opname} operands must have identical types"),
                    location.clone(),
                )
                .with_note(format!("lhs {:?}, rhs {:?}", lhs_ty, rhs_ty)),
            );
        }

        self.expect_result_ty(inst_id, Type::I1, location);
    }

    fn verify_ext_cast(
        &mut self,
        inst_id: InstId,
        from: ValueId,
        to_ty: Type,
        is_ext: bool,
        opname: &str,
    ) {
        let location = self.inst_location(inst_id);
        let Some(from_ty) = self.value_ty(from) else {
            return;
        };

        if !from_ty.is_integral() || !to_ty.is_integral() {
            self.emit(Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                format!("{opname} requires integral source and target types"),
                location.clone(),
            ));
        }

        if is_ext && from_ty >= to_ty {
            self.emit(
                Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    format!("{opname} requires source type narrower than target type"),
                    location.clone(),
                )
                .with_note(format!("from {:?}, to {:?}", from_ty, to_ty)),
            );
        }
        if !is_ext && from_ty <= to_ty {
            self.emit(
                Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    format!("{opname} requires source type wider than target type"),
                    location.clone(),
                )
                .with_note(format!("from {:?}, to {:?}", from_ty, to_ty)),
            );
        }

        self.expect_result_ty(inst_id, to_ty, location);
    }

    fn gep_result_pointee(&mut self, values: &[ValueId], location: Location) -> Option<Type> {
        let base = values.first().copied()?;

        let base_ty = self.value_ty(base)?;
        let Some(_) = self.pointee_ty(base_ty) else {
            self.emit(
                Diagnostic::error(
                    DiagnosticCode::GepTypeComputationFailed,
                    "gep base operand must be a pointer",
                    location,
                )
                .with_note(format!("found base type {:?}", base_ty)),
            );
            return None;
        };
        let mut current_ty = base_ty;

        for &idx_value in values.iter().skip(1) {
            let idx_ty = self.value_ty(idx_value)?;
            if !idx_ty.is_integral() {
                self.emit(
                    Diagnostic::error(
                        DiagnosticCode::GepTypeComputationFailed,
                        "gep index operands must be integral",
                        location.clone(),
                    )
                    .with_note(format!("index type {:?}", idx_ty)),
                );
                return None;
            }

            let Type::Compound(cmpd_ref) = current_ty else {
                self.emit(
                    Diagnostic::error(
                        DiagnosticCode::GepTypeComputationFailed,
                        "gep attempted to index into a non-aggregate scalar type",
                        location.clone(),
                    )
                    .with_note(format!("current type {:?}", current_ty)),
                );
                return None;
            };

            let Some(cmpd) = self
                .ctx
                .with_ty_store(|store| store.get_compound(cmpd_ref).cloned())
            else {
                self.emit(Diagnostic::error(
                    DiagnosticCode::GepTypeComputationFailed,
                    "gep references unknown compound type",
                    location.clone(),
                ));
                return None;
            };

            current_ty = match cmpd {
                CompoundType::Ptr(elem) => elem,
                CompoundType::Array { elem, .. } => elem,
                CompoundType::Struct(s) => {
                    let Some(imm) = self.value_imm(idx_value) else {
                        self.emit(Diagnostic::error(
                            DiagnosticCode::GepTypeComputationFailed,
                            "struct gep indices must be non-negative immediate values",
                            location.clone(),
                        ));
                        return None;
                    };
                    if imm.is_negative() {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::GepTypeComputationFailed,
                                "struct gep indices must be non-negative immediate values",
                                location.clone(),
                            )
                            .with_note(format!("index immediate {:?} is negative", imm)),
                        );
                        return None;
                    }
                    let index = imm.as_usize();
                    let Some(field_ty) = s.fields.get(index).copied() else {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::GepTypeComputationFailed,
                                "struct gep index is out of bounds",
                                location.clone(),
                            )
                            .with_note(format!("index {index}, fields {}", s.fields.len())),
                        );
                        return None;
                    };

                    field_ty
                }
                CompoundType::Func { .. } => {
                    self.emit(Diagnostic::error(
                        DiagnosticCode::GepTypeComputationFailed,
                        "gep cannot index into function type",
                        location.clone(),
                    ));
                    return None;
                }
            };
        }

        Some(current_ty)
    }

    fn aggregate_field_ty(
        &mut self,
        dest_ty: Type,
        idx: ValueId,
        insert_mode: bool,
        location: Location,
    ) -> Option<Type> {
        let Type::Compound(cmpd_ref) = dest_ty else {
            self.emit(Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                "aggregate operation requires struct or array destination",
                location,
            ));
            return None;
        };

        let Some(cmpd) = self
            .ctx
            .with_ty_store(|store| store.get_compound(cmpd_ref).cloned())
        else {
            self.emit(Diagnostic::error(
                DiagnosticCode::InvalidTypeRef,
                "aggregate operation destination references unknown type",
                location,
            ));
            return None;
        };

        let code = if insert_mode {
            DiagnosticCode::InsertIndexOutOfBounds
        } else {
            DiagnosticCode::ExtractIndexOutOfBounds
        };
        let idx_imm = self.value_imm(idx);
        if let Some(imm) = idx_imm
            && imm.is_negative()
        {
            self.emit(
                Diagnostic::error(code, "aggregate index must be non-negative", location)
                    .with_note(format!("index immediate {:?}", imm)),
            );
            return None;
        }
        let idx_imm = idx_imm.map(Immediate::as_usize);

        match cmpd {
            CompoundType::Array { elem, len } => {
                if let Some(index) = idx_imm
                    && index >= len
                {
                    self.emit(
                        Diagnostic::error(code, "aggregate index is out of bounds", location)
                            .with_note(format!("index {index}, length {len}")),
                    );
                    return None;
                }
                Some(elem)
            }
            CompoundType::Struct(s) => {
                let Some(index) = idx_imm else {
                    self.emit(Diagnostic::error(
                        code,
                        "struct aggregate index must be an immediate value",
                        location,
                    ));
                    return None;
                };

                let Some(field_ty) = s.fields.get(index).copied() else {
                    self.emit(
                        Diagnostic::error(code, "aggregate index is out of bounds", location)
                            .with_note(format!("index {index}, fields {}", s.fields.len())),
                    );
                    return None;
                };

                Some(field_ty)
            }
            CompoundType::Ptr(_) | CompoundType::Func { .. } => {
                self.emit(Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    "aggregate operation destination must be struct or array",
                    location,
                ));
                None
            }
        }
    }

    fn verify_symbol_ref(&mut self, sym: &SymbolRef, location: Location) {
        match sym {
            SymbolRef::Func(func) => {
                if self.ctx.get_sig(*func).is_none() {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::InvalidFuncRef,
                            "symbol reference points to unknown function",
                            location,
                        )
                        .with_note(format!("missing function id {}", func.as_u32())),
                    );
                }
            }
            SymbolRef::Global(gv) => {
                if self.ctx.with_gv_store(|store| store.get(*gv).is_none()) {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::InvalidGlobalRef,
                            "symbol reference points to unknown global",
                            location,
                        )
                        .with_note(format!("missing global id {}", gv.as_u32())),
                    );
                }
            }
            SymbolRef::Embed(embed) => {
                if let Some(declared_embed_symbols) = self.declared_embed_symbols
                    && !declared_embed_symbols.contains(embed)
                {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::StructuralInvariantViolation,
                            "symbol reference points to undeclared embed symbol",
                            location,
                        )
                        .with_note(format!("missing embed symbol: &{}", embed.0.as_str())),
                    );
                }
            }
        }
    }
}
