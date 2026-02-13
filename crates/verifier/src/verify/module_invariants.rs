use std::{
    collections::VecDeque,
    panic::{AssertUnwindSafe, catch_unwind},
};

use rustc_hash::FxHashSet;
use sonatina_ir::{
    GlobalVariableRef, Module, Type,
    global_variable::GvInitializer,
    inst::{downcast, data::{self, SymbolRef}},
    isa::TypeLayoutError,
    module::{FuncRef, ModuleCtx},
    object::{Directive, EmbedSymbol, SectionRef},
    types::CompoundType,
};

use crate::{
    VerifierConfig,
    diagnostic::{Diagnostic, DiagnosticCode, Location},
    report::VerificationReport,
};

use super::type_utils::{is_pointer_ty, is_type_valid, iter_nested_types};

pub(super) fn collect_module_invariants(
    module: &Module,
    cfg: &VerifierConfig,
    report: &mut VerificationReport,
) {
    let mut declared_refs: Vec<_> = module
        .ctx
        .declared_funcs
        .iter()
        .map(|entry| *entry.key())
        .collect();
    declared_refs.sort_by_key(|func_ref| func_ref.as_u32());

    for func_ref in &declared_refs {
        if !module.func_store.contains(*func_ref) {
            report.push(
                Diagnostic::error(
                    DiagnosticCode::InvalidFuncRef,
                    "declared function is missing from function store",
                    Location::Function(*func_ref),
                ),
                cfg.max_diagnostics,
            );
        }

        let Some(sig) = module.ctx.get_sig(*func_ref) else {
            continue;
        };

        for (index, arg_ty) in sig.args().iter().enumerate() {
            verify_signature_type(
                &module.ctx,
                *func_ref,
                *arg_ty,
                format!("signature arg {index}"),
                cfg,
                report,
            );
        }

        verify_signature_type(
            &module.ctx,
            *func_ref,
            sig.ret_ty(),
            "signature return".to_string(),
            cfg,
            report,
        );
    }

    let mut store_refs = module.func_store.funcs();
    store_refs.sort_by_key(|func_ref| func_ref.as_u32());
    for func_ref in store_refs {
        if module.ctx.get_sig(func_ref).is_none() {
            report.push(
                Diagnostic::error(
                    DiagnosticCode::InvalidSignature,
                    "function has no declared signature",
                    Location::Function(func_ref),
                ),
                cfg.max_diagnostics,
            );
        }
    }

    module.ctx.with_ty_store(|type_store| {
        for (cmpd_ref, cmpd) in type_store.all_compounds() {
            let ty = Type::Compound(cmpd_ref);
            let location = Location::Type { func: None, ty };
            if matches!(cmpd, CompoundType::Struct(s) if s.packed)
                && matches!(
                    module.ctx.triple.architecture,
                    sonatina_triple::Architecture::Evm
                )
            {
                report.push(
                    Diagnostic::error(
                        DiagnosticCode::InvalidTypeRef,
                        "packed struct is unsupported by the active target layout",
                        location.clone(),
                    ),
                    cfg.max_diagnostics,
                );
            }

            for nested in iter_nested_types(cmpd) {
                if let Type::Compound(nested_ref) = nested
                    && type_store.get_compound(nested_ref).is_none()
                {
                    report.push(
                        Diagnostic::error(
                            DiagnosticCode::InvalidTypeRef,
                            "compound type references a missing nested type",
                            location.clone(),
                        )
                        .with_note(format!("missing type ref: {}", nested_ref.as_u32())),
                        cfg.max_diagnostics,
                    );
                }
            }

            if !is_type_valid(&module.ctx, ty) {
                report.push(
                    Diagnostic::error(
                        DiagnosticCode::InvalidTypeRef,
                        "type is not representable (contains a by-value recursive cycle)",
                        location.clone(),
                    ),
                    cfg.max_diagnostics,
                );
                continue;
            }

            let size_res = catch_unwind(AssertUnwindSafe(|| module.ctx.size_of(ty)));
            if !matches!(
                size_res,
                Ok(Ok(_)) | Ok(Err(TypeLayoutError::UnrepresentableType(_)))
            ) {
                report.push(
                    Diagnostic::error(
                        DiagnosticCode::InvalidTypeRef,
                        "type layout computation failed",
                        location.clone(),
                    ),
                    cfg.max_diagnostics,
                );
            }

            let align_res = catch_unwind(AssertUnwindSafe(|| module.ctx.align_of(ty)));
            if !matches!(
                align_res,
                Ok(Ok(_)) | Ok(Err(TypeLayoutError::UnrepresentableType(_)))
            ) {
                report.push(
                    Diagnostic::error(
                        DiagnosticCode::InvalidTypeRef,
                        "type alignment computation failed",
                        location,
                    ),
                    cfg.max_diagnostics,
                );
            }
        }
    });

    module.ctx.with_gv_store(|gv_store| {
        for gv_ref in gv_store.all_gv_refs() {
            let Some(gv_data) = gv_store.get(gv_ref) else {
                report.push(
                    Diagnostic::error(
                        DiagnosticCode::InvalidGlobalRef,
                        "global reference points to missing global data",
                        Location::Global(gv_ref),
                    ),
                    cfg.max_diagnostics,
                );
                continue;
            };

            if let Type::Compound(cmpd_ref) = gv_data.ty
                && module
                    .ctx
                    .with_ty_store(|store| store.get_compound(cmpd_ref).is_none())
            {
                report.push(
                    Diagnostic::error(
                        DiagnosticCode::InvalidTypeRef,
                        "global type references a missing compound type",
                        Location::Global(gv_ref),
                    ),
                    cfg.max_diagnostics,
                );
            }

            if gv_data.linkage.is_external() && gv_data.initializer.is_some() {
                report.push(
                    Diagnostic::error(
                        DiagnosticCode::StructuralInvariantViolation,
                        "external global must not define an initializer",
                        Location::Global(gv_ref),
                    ),
                    cfg.max_diagnostics,
                );
            }

            if let Some(initializer) = &gv_data.initializer {
                verify_gv_initializer(module, gv_ref, initializer, gv_data.ty, cfg, report);
            }
        }
    });

    let mut object_names: Vec<_> = module.objects.keys().cloned().collect();
    object_names.sort();

    for object_name in object_names {
        let Some(object) = module.objects.get(&object_name) else {
            continue;
        };

        let mut section_names = FxHashSet::default();
        for section in &object.sections {
            let section_name = section.name.0.to_string();
            if !section_names.insert(section_name.clone()) {
                report.push(
                    Diagnostic::error(
                        DiagnosticCode::StructuralInvariantViolation,
                        "object contains duplicate section name",
                        Location::Object {
                            name: object_name.clone(),
                            section: Some(section_name.clone()),
                        },
                    ),
                    cfg.max_diagnostics,
                );
            }

            let mut entry_count = 0usize;
            let mut entry = None;
            let mut include_funcs = Vec::new();
            let mut include_set = FxHashSet::default();
            let mut local_embed_symbols = FxHashSet::default();
            for directive in &section.directives {
                match directive {
                    Directive::Entry(func) => {
                        entry_count += 1;
                        if module.ctx.get_sig(*func).is_none() {
                            report.push(
                                Diagnostic::error(
                                    DiagnosticCode::InvalidFuncRef,
                                    "object entry directive references unknown function",
                                    Location::Object {
                                        name: object_name.clone(),
                                        section: Some(section_name.clone()),
                                    },
                                )
                                .with_note(format!("missing function ref: {}", func.as_u32())),
                                cfg.max_diagnostics,
                            );
                        } else if entry.is_none() {
                            entry = Some(*func);
                        }
                    }
                    Directive::Include(func) => {
                        if module.ctx.get_sig(*func).is_none() {
                            report.push(
                                Diagnostic::error(
                                    DiagnosticCode::InvalidFuncRef,
                                    "object include directive references unknown function",
                                    Location::Object {
                                        name: object_name.clone(),
                                        section: Some(section_name.clone()),
                                    },
                                )
                                .with_note(format!("missing function ref: {}", func.as_u32())),
                                cfg.max_diagnostics,
                            );
                        } else if include_set.insert(*func) {
                            include_funcs.push(*func);
                        }
                    }
                    Directive::Data(gv) => {
                        let Some(gv_data) =
                            module.ctx.with_gv_store(|store| store.get(*gv).cloned())
                        else {
                            report.push(
                                Diagnostic::error(
                                    DiagnosticCode::InvalidGlobalRef,
                                    "object data directive references unknown global",
                                    Location::Object {
                                        name: object_name.clone(),
                                        section: Some(section_name.clone()),
                                    },
                                )
                                .with_note(format!("missing global ref: {}", gv.as_u32())),
                                cfg.max_diagnostics,
                            );
                            continue;
                        };

                        if let Err(reason) = validate_global_for_object_data(
                            &module.ctx,
                            gv_data.ty,
                            gv_data.is_const,
                            gv_data.initializer.as_ref(),
                        ) {
                            report.push(
                                Diagnostic::error(
                                    DiagnosticCode::StructuralInvariantViolation,
                                    "object data directive references non-encodable global data",
                                    Location::Object {
                                        name: object_name.clone(),
                                        section: Some(section_name.clone()),
                                    },
                                )
                                .with_note(format!("global ref: {}", gv.as_u32()))
                                .with_note(reason),
                                cfg.max_diagnostics,
                            );
                        }
                    }
                    Directive::Embed(embed) => {
                        let symbol = embed.as_symbol.0.to_string();
                        if !local_embed_symbols.insert(symbol.clone()) {
                            report.push(
                                Diagnostic::error(
                                    DiagnosticCode::StructuralInvariantViolation,
                                    "duplicate embed symbol in section",
                                    Location::Object {
                                        name: object_name.clone(),
                                        section: Some(section_name.clone()),
                                    },
                                )
                                .with_note(format!("duplicate embed symbol: &{symbol}")),
                                cfg.max_diagnostics,
                            );
                        }

                        match &embed.source {
                            SectionRef::Local(local) => {
                                let exists = object
                                    .sections
                                    .iter()
                                    .any(|candidate| candidate.name.0 == local.0);
                                if !exists {
                                    report.push(
                                        Diagnostic::error(
                                            DiagnosticCode::InvalidBlockRef,
                                            "embed source section does not exist in object",
                                            Location::Object {
                                                name: object_name.clone(),
                                                section: Some(section_name.clone()),
                                            },
                                        )
                                        .with_note(
                                            format!("missing local section: {}", local.0.as_str()),
                                        ),
                                        cfg.max_diagnostics,
                                    );
                                }
                            }
                            SectionRef::External {
                                object: ext_obj,
                                section: ext_section,
                            } => {
                                let exists = module.objects.get(ext_obj.0.as_str()).is_some_and(
                                    |target_obj| {
                                        target_obj
                                            .sections
                                            .iter()
                                            .any(|candidate| candidate.name.0 == ext_section.0)
                                    },
                                );
                                if !exists {
                                    report.push(
                                        Diagnostic::error(
                                            DiagnosticCode::InvalidBlockRef,
                                            "embed source external section does not exist",
                                            Location::Object {
                                                name: object_name.clone(),
                                                section: Some(section_name.clone()),
                                            },
                                        )
                                        .with_note(
                                            format!(
                                                "missing external section: @{}.{}",
                                                ext_obj.0.as_str(),
                                                ext_section.0.as_str()
                                            ),
                                        ),
                                        cfg.max_diagnostics,
                                    );
                                }
                            }
                        }
                    }
                }
            }

            if entry_count == 0 {
                report.push(
                    Diagnostic::error(
                        DiagnosticCode::StructuralInvariantViolation,
                        "section is missing an entry directive",
                        Location::Object {
                            name: object_name.clone(),
                            section: Some(section_name.clone()),
                        },
                    ),
                    cfg.max_diagnostics,
                );
            }
            if entry_count > 1 {
                report.push(
                    Diagnostic::error(
                        DiagnosticCode::StructuralInvariantViolation,
                        "section has multiple entry directives",
                        Location::Object {
                            name: object_name.clone(),
                            section: Some(section_name.clone()),
                        },
                    ),
                    cfg.max_diagnostics,
                );
            }

            if let Some(entry_func) = entry {
                let used_embed_symbols =
                    collect_section_used_embed_symbols(module, entry_func, &include_funcs);
                let mut missing_symbols: Vec<_> = used_embed_symbols
                    .into_iter()
                    .filter(|symbol| !local_embed_symbols.contains(symbol))
                    .collect();
                missing_symbols.sort();

                for symbol in missing_symbols {
                    report.push(
                        Diagnostic::error(
                            DiagnosticCode::StructuralInvariantViolation,
                            "section uses an embed symbol that is not declared in that section",
                            Location::Object {
                                name: object_name.clone(),
                                section: Some(section_name.clone()),
                            },
                        )
                        .with_note(format!("missing embed symbol: &{symbol}")),
                        cfg.max_diagnostics,
                    );
                }
            }
        }
    }
}

pub(super) fn collect_declared_embed_symbols(module: &Module) -> FxHashSet<EmbedSymbol> {
    let mut symbols = FxHashSet::default();

    for object in module.objects.values() {
        for section in &object.sections {
            for directive in &section.directives {
                if let Directive::Embed(embed) = directive {
                    symbols.insert(embed.as_symbol.clone());
                }
            }
        }
    }

    symbols
}

fn verify_signature_type(
    ctx: &ModuleCtx,
    func_ref: FuncRef,
    ty: Type,
    usage: String,
    cfg: &VerifierConfig,
    report: &mut VerificationReport,
) {
    let location = Location::Type {
        func: Some(func_ref),
        ty,
    };

    if !is_type_valid(ctx, ty) {
        report.push(
            Diagnostic::error(
                DiagnosticCode::InvalidTypeRef,
                "function signature contains an invalid type",
                location,
            )
            .with_note(usage),
            cfg.max_diagnostics,
        );
        return;
    }

    if has_by_value_function_type_in_signature(ctx, ty) {
        report.push(
            Diagnostic::error(
                DiagnosticCode::InvalidSignature,
                "function signature contains a by-value function type",
                location,
            )
            .with_note(usage),
            cfg.max_diagnostics,
        );
    }
}

pub(crate) fn has_by_value_function_type_in_signature(ctx: &ModuleCtx, ty: Type) -> bool {
    let mut visited = FxHashSet::default();
    let mut stack = vec![(ty, false)];

    while let Some((current_ty, behind_pointer)) = stack.pop() {
        let Type::Compound(cmpd_ref) = current_ty else {
            continue;
        };
        if !visited.insert((cmpd_ref, behind_pointer)) {
            continue;
        }

        let Some(cmpd) = ctx.with_ty_store(|store| store.get_compound(cmpd_ref).cloned()) else {
            continue;
        };

        match cmpd {
            CompoundType::Array { elem, .. } => {
                stack.push((elem, behind_pointer));
            }
            CompoundType::Ptr(elem) => {
                stack.push((elem, true));
            }
            CompoundType::Struct(s) => {
                for field in s.fields {
                    stack.push((field, behind_pointer));
                }
            }
            CompoundType::Func { args, ret_ty } => {
                if !behind_pointer {
                    return true;
                }
                for arg in args {
                    stack.push((arg, false));
                }
                stack.push((ret_ty, false));
            }
        }
    }

    false
}

fn validate_global_for_object_data(
    ctx: &ModuleCtx,
    ty: Type,
    is_const: bool,
    initializer: Option<&GvInitializer>,
) -> Result<(), String> {
    if !is_const {
        return Err("global must be declared const for object data emission".to_string());
    }
    let Some(initializer) = initializer else {
        return Err("global must define an initializer for object data emission".to_string());
    };

    validate_data_initializer_shape(ctx, ty, initializer)
}

fn validate_data_initializer_shape(
    ctx: &ModuleCtx,
    ty: Type,
    initializer: &GvInitializer,
) -> Result<(), String> {
    if ty.is_pointer(ctx) {
        return Err(format!(
            "type {ty:?} is unsupported for object data (pointer type)"
        ));
    }

    if ty.is_integral() {
        return match initializer {
            GvInitializer::Immediate(imm) if imm.ty() == ty => Ok(()),
            GvInitializer::Immediate(imm) => Err(format!(
                "integral initializer type mismatch: expected {ty:?}, found {:?}",
                imm.ty()
            )),
            _ => Err(format!(
                "integral type {ty:?} requires an immediate initializer"
            )),
        };
    }

    let Type::Compound(cmpd_ref) = ty else {
        return Err(format!("type {ty:?} is unsupported for object data"));
    };
    let Some(cmpd) = ctx.with_ty_store(|store| store.get_compound(cmpd_ref).cloned()) else {
        return Err(format!("type ref {} does not exist", cmpd_ref.as_u32()));
    };

    match cmpd {
        CompoundType::Array { elem, len } => {
            let GvInitializer::Array(items) = initializer else {
                return Err("array type requires array initializer".to_string());
            };
            if items.len() != len {
                return Err(format!(
                    "array initializer length mismatch: expected {len}, found {}",
                    items.len()
                ));
            }

            for item in items {
                validate_data_initializer_shape(ctx, elem, item)?;
            }
            Ok(())
        }
        CompoundType::Struct(s) => {
            if s.packed {
                return Err(format!(
                    "type {ty:?} is unsupported for object data (packed struct)"
                ));
            }

            let GvInitializer::Struct(fields) = initializer else {
                return Err("struct type requires struct initializer".to_string());
            };
            if fields.len() != s.fields.len() {
                return Err(format!(
                    "struct initializer field count mismatch: expected {}, found {}",
                    s.fields.len(),
                    fields.len()
                ));
            }

            for (field, field_ty) in fields.iter().zip(s.fields) {
                validate_data_initializer_shape(ctx, field_ty, field)?;
            }
            Ok(())
        }
        CompoundType::Ptr(_) => Err(format!(
            "type {ty:?} is unsupported for object data (pointer type)"
        )),
        CompoundType::Func { .. } => Err(format!(
            "type {ty:?} is unsupported for object data (function type)"
        )),
    }
}

fn collect_section_used_embed_symbols(
    module: &Module,
    entry: FuncRef,
    includes: &[FuncRef],
) -> FxHashSet<String> {
    let mut seen_funcs = FxHashSet::default();
    let mut worklist = VecDeque::new();
    let mut used_embed_symbols = FxHashSet::default();

    for func in std::iter::once(entry).chain(includes.iter().copied()) {
        if seen_funcs.insert(func) {
            worklist.push_back(func);
        }
    }

    while let Some(func_ref) = worklist.pop_front() {
        let _ = module.func_store.try_view(func_ref, |func| {
            let inst_set = func.inst_set();
            for block in func.layout.iter_block() {
                for inst_id in func.layout.iter_inst(block) {
                    if let Some(call) = func.dfg.call_info(inst_id) {
                        let callee = call.callee();
                        if module.ctx.get_sig(callee).is_some() && seen_funcs.insert(callee) {
                            worklist.push_back(callee);
                        }
                    }

                    let inst = func.dfg.inst(inst_id);
                    if let Some(ptr) =
                        downcast::<&data::GetFunctionPtr>(inst_set, inst)
                    {
                        let callee = *ptr.func();
                        if module.ctx.get_sig(callee).is_some() && seen_funcs.insert(callee) {
                            worklist.push_back(callee);
                        }
                    }
                    if let Some(sym) = downcast::<&data::SymAddr>(inst_set, inst) {
                        record_symbol_membership(
                            &module.ctx,
                            sym.sym(),
                            &mut seen_funcs,
                            &mut worklist,
                            &mut used_embed_symbols,
                        );
                    }
                    if let Some(sym) = downcast::<&data::SymSize>(inst_set, inst) {
                        record_symbol_membership(
                            &module.ctx,
                            sym.sym(),
                            &mut seen_funcs,
                            &mut worklist,
                            &mut used_embed_symbols,
                        );
                    }
                }
            }
        });
    }

    used_embed_symbols
}

fn record_symbol_membership(
    ctx: &ModuleCtx,
    sym: &SymbolRef,
    seen_funcs: &mut FxHashSet<FuncRef>,
    worklist: &mut VecDeque<FuncRef>,
    used_embed_symbols: &mut FxHashSet<String>,
) {
    match sym {
        SymbolRef::Func(func) => {
            if ctx.get_sig(*func).is_some() && seen_funcs.insert(*func) {
                worklist.push_back(*func);
            }
        }
        SymbolRef::Global(_) => {}
        SymbolRef::Embed(embed) => {
            used_embed_symbols.insert(embed.0.to_string());
        }
    }
}

fn verify_gv_initializer(
    module: &Module,
    gv_ref: GlobalVariableRef,
    init: &GvInitializer,
    expected_ty: Type,
    cfg: &VerifierConfig,
    report: &mut VerificationReport,
) {
    match init {
        GvInitializer::Immediate(imm) => {
            let expected = expected_ty;
            let pointer_repl = module.ctx.type_layout.pointer_repl();
            if imm.ty() != expected
                && !(is_pointer_ty(&module.ctx, expected) && imm.ty() == pointer_repl)
            {
                report.push(
                    Diagnostic::error(
                        DiagnosticCode::ValueTypeMismatch,
                        "global initializer immediate type does not match global type",
                        Location::Global(gv_ref),
                    )
                    .with_note(format!(
                        "expected {:?}, found {:?}",
                        expected,
                        imm.ty()
                    )),
                    cfg.max_diagnostics,
                );
            }
        }
        GvInitializer::Array(items) => {
            let Some((elem_ty, len)) = module.ctx.with_ty_store(|store| {
                let Type::Compound(cmpd_ref) = expected_ty else {
                    return None;
                };
                match store.get_compound(cmpd_ref) {
                    Some(CompoundType::Array { elem, len }) => Some((*elem, *len)),
                    _ => None,
                }
            }) else {
                report.push(
                    Diagnostic::error(
                        DiagnosticCode::ValueTypeMismatch,
                        "array initializer used for non-array global type",
                        Location::Global(gv_ref),
                    ),
                    cfg.max_diagnostics,
                );
                return;
            };

            if items.len() != len {
                report.push(
                    Diagnostic::error(
                        DiagnosticCode::ValueTypeMismatch,
                        "array initializer length does not match declared array length",
                        Location::Global(gv_ref),
                    )
                    .with_note(format!("expected {len}, found {}", items.len())),
                    cfg.max_diagnostics,
                );
            }

            for item in items {
                verify_gv_initializer(module, gv_ref, item, elem_ty, cfg, report);
            }
        }
        GvInitializer::Struct(fields) => {
            let Some(struct_data) = module.ctx.with_ty_store(|store| {
                let Type::Compound(cmpd_ref) = expected_ty else {
                    return None;
                };
                match store.get_compound(cmpd_ref) {
                    Some(CompoundType::Struct(s)) => Some(s.clone()),
                    _ => None,
                }
            }) else {
                report.push(
                    Diagnostic::error(
                        DiagnosticCode::ValueTypeMismatch,
                        "struct initializer used for non-struct global type",
                        Location::Global(gv_ref),
                    ),
                    cfg.max_diagnostics,
                );
                return;
            };

            if fields.len() != struct_data.fields.len() {
                report.push(
                    Diagnostic::error(
                        DiagnosticCode::ValueTypeMismatch,
                        "struct initializer field count does not match struct type",
                        Location::Global(gv_ref),
                    )
                    .with_note(format!(
                        "expected {}, found {}",
                        struct_data.fields.len(),
                        fields.len()
                    )),
                    cfg.max_diagnostics,
                );
            }

            for (field, ty) in fields.iter().zip(struct_data.fields) {
                verify_gv_initializer(module, gv_ref, field, ty, cfg, report);
            }
        }
    }
}
