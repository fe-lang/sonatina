use indexmap::IndexMap;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    GlobalVariableRef, Module,
    inst::equiv::{BinaryInstKind, InstClassKind, UnaryInstKind},
    module::FuncRef,
    object::EmbedSymbol,
};
use sonatina_triple::Architecture;
use sonatina_verifier::{
    Location, VerificationLevel, VerifierConfig, verify_module, verify_module_invariants,
};
use tracing::{debug_span, info_span, trace_span};

use super::{
    CompileOptions,
    artifact::ObjectArtifact,
    error::ObjectCompileError,
    link::{LinkSectionError, link_section},
    resolve::{ObjectId, ResolvedProgram, SectionId},
};
use crate::{
    isa::evm::{EvmBackend, collect_unsupported_evm_multi_return},
    machinst::lower::{
        SectionWorkModule, build_section_membership, compute_section_function_emission_order,
    },
};

fn compile_required_sections_into_cache(
    program: &ResolvedProgram<'_>,
    backend: &EvmBackend,
    required: Option<&FxHashSet<SectionId>>,
    opts: &CompileOptions,
) -> Result<FxHashMap<SectionId, super::artifact::SectionArtifact>, Vec<ObjectCompileError>> {
    let _span = debug_span!(
        "sonatina.codegen.object.compile_required_sections_into_cache",
        required_len = ?required.map(|required| required.len())
    )
    .entered();
    let order = {
        let _span = trace_span!("sonatina.codegen.object.topo_sort_sections").entered();
        topo_sort_sections(program)
    };

    let mut cache: FxHashMap<SectionId, super::artifact::SectionArtifact> = FxHashMap::default();
    for section_id in order {
        if required.is_none_or(|required| required.contains(&section_id)) {
            let _span = trace_span!(
                "sonatina.codegen.object.compile_section_if_required",
                section_object = section_id.object.0,
                section = section_id.section
            )
            .entered();
            compile_section(program, backend, section_id, &mut cache, opts)?;
        }
    }

    Ok(cache)
}

fn verify_module_for_codegen(
    module: &Module,
    cfg: &VerifierConfig,
) -> Result<(), Vec<ObjectCompileError>> {
    let _span = debug_span!(
        "sonatina.codegen.object.verify_module_for_codegen",
        verification_level = ?cfg.level
    )
    .entered();
    let fast_invariants_only = matches!(cfg.level, VerificationLevel::Fast)
        && !cfg.should_check_dominance()
        && !cfg.should_check_users()
        && !cfg.should_check_value_caches();
    let report = if fast_invariants_only {
        verify_module_invariants(module, cfg)
    } else {
        verify_module(module, cfg)
    };
    if report.has_errors() {
        return Err(vec![ObjectCompileError::VerifierFailed { report }]);
    }

    if !cfg.should_check_types() {
        let mut type_cfg = cfg.clone();
        type_cfg.level = VerificationLevel::Standard;
        let mut report = verify_module(module, &type_cfg);
        report
            .diagnostics
            .retain(|diagnostic| diagnostic_targets_multi_result_inst(module, &diagnostic.primary));
        if report.has_errors() {
            return Err(vec![ObjectCompileError::VerifierFailed { report }]);
        }
    }

    Ok(())
}

fn diagnostic_targets_multi_result_inst(module: &Module, location: &Location) -> bool {
    let Location::Inst { func, inst, .. } = *location else {
        return false;
    };

    module.func_store.view(func, |function| {
        let inst_data = function.dfg.inst(inst);
        function.dfg.inst_results(inst).len() != 1 || is_checked_multi_result_inst(inst_data.kind())
    })
}

fn is_checked_multi_result_inst(kind: InstClassKind) -> bool {
    matches!(
        kind,
        InstClassKind::Unary(UnaryInstKind::Snego)
            | InstClassKind::Binary(
                BinaryInstKind::Uaddo
                    | BinaryInstKind::Saddo
                    | BinaryInstKind::Usubo
                    | BinaryInstKind::Ssubo
                    | BinaryInstKind::Umulo
                    | BinaryInstKind::Smulo
                    | BinaryInstKind::EvmUdivo
                    | BinaryInstKind::EvmSdivo
                    | BinaryInstKind::EvmUmodo
                    | BinaryInstKind::EvmSmodo
            )
    )
}

fn reject_unsupported_evm_multi_return(
    module: &Module,
    funcs: &[FuncRef],
    entry: FuncRef,
    object: &sonatina_ir::object::ObjectName,
    section: &sonatina_ir::object::SectionName,
) -> Vec<ObjectCompileError> {
    if !matches!(module.ctx.triple.architecture, Architecture::Evm) {
        return vec![];
    }

    collect_unsupported_evm_multi_return(module, funcs, Some(entry))
        .into_iter()
        .map(|(func, message)| ObjectCompileError::BackendError {
            object: object.clone(),
            section: section.clone(),
            func,
            message,
        })
        .collect()
}

pub fn compile_all_objects(
    module: &Module,
    backend: &EvmBackend,
    opts: &CompileOptions,
) -> Result<Vec<ObjectArtifact>, Vec<ObjectCompileError>> {
    let _span = info_span!("sonatina.codegen.object.compile_all_objects").entered();
    {
        let _span = debug_span!("sonatina.codegen.object.verify").entered();
        verify_module_for_codegen(module, &opts.verifier_cfg)?;
    }
    let program = {
        let _span = debug_span!("sonatina.codegen.object.resolve_program").entered();
        ResolvedProgram::resolve(module)?
    };
    let mut cache = {
        let _span = debug_span!(
            "sonatina.codegen.object.compile_required_sections",
            object_count = program.objects.len()
        )
        .entered();
        compile_required_sections_into_cache(&program, backend, None, opts)?
    };

    let _span = debug_span!(
        "sonatina.codegen.object.materialize_object_artifacts",
        object_count = program.objects.len()
    )
    .entered();
    let mut artifacts = Vec::new();
    for (idx, obj) in program.objects.iter().enumerate() {
        let object_id = ObjectId(idx as u32);
        let mut sections = IndexMap::new();
        for (section_idx, section) in obj.sections.iter().enumerate() {
            let id = SectionId {
                object: object_id,
                section: section_idx as u32,
            };
            let artifact = cache.remove(&id).ok_or_else(|| {
                vec![ObjectCompileError::LinkError {
                    object: obj.name.clone(),
                    section: section.name.clone(),
                    message: "missing compiled section".to_string(),
                }]
            })?;
            sections.insert(section.name.clone(), artifact);
        }
        artifacts.push(ObjectArtifact {
            object: obj.name.clone(),
            sections,
        });
    }

    Ok(artifacts)
}

pub fn compile_object(
    module: &Module,
    backend: &EvmBackend,
    object: &str,
    opts: &CompileOptions,
) -> Result<ObjectArtifact, Vec<ObjectCompileError>> {
    let _span = info_span!("sonatina.codegen.object.compile_object", object).entered();
    {
        let _span = debug_span!("sonatina.codegen.object.verify").entered();
        verify_module_for_codegen(module, &opts.verifier_cfg)?;
    }
    let program = {
        let _span = debug_span!("sonatina.codegen.object.resolve_program").entered();
        ResolvedProgram::resolve(module)?
    };

    let Some((object_idx, obj)) = program
        .objects
        .iter()
        .enumerate()
        .find(|(_, obj)| obj.name.0.as_str() == object)
    else {
        return Err(vec![ObjectCompileError::ObjectNotFound {
            object: object.to_string(),
        }]);
    };

    let object_id = ObjectId(object_idx as u32);
    let mut required: FxHashSet<SectionId> = FxHashSet::default();
    {
        let _span = debug_span!("sonatina.codegen.object.collect_embed_deps").entered();
        for (section_idx, _) in obj.sections.iter().enumerate() {
            let id = SectionId {
                object: object_id,
                section: section_idx as u32,
            };
            collect_embed_deps(&program, id, &mut required);
        }
    }

    let mut cache = {
        let _span = debug_span!(
            "sonatina.codegen.object.compile_required_sections",
            required_len = required.len()
        )
        .entered();
        compile_required_sections_into_cache(&program, backend, Some(&required), opts)?
    };

    let _span = debug_span!("sonatina.codegen.object.materialize_object").entered();
    let mut sections = IndexMap::new();
    for (section_idx, section) in obj.sections.iter().enumerate() {
        let id = SectionId {
            object: object_id,
            section: section_idx as u32,
        };
        let artifact = cache.remove(&id).ok_or_else(|| {
            vec![ObjectCompileError::LinkError {
                object: obj.name.clone(),
                section: section.name.clone(),
                message: "missing compiled section".to_string(),
            }]
        })?;
        sections.insert(section.name.clone(), artifact);
    }

    Ok(ObjectArtifact {
        object: obj.name.clone(),
        sections,
    })
}

fn compile_section(
    program: &ResolvedProgram<'_>,
    backend: &EvmBackend,
    section_id: SectionId,
    cache: &mut FxHashMap<SectionId, super::artifact::SectionArtifact>,
    opts: &CompileOptions,
) -> Result<(), Vec<ObjectCompileError>> {
    let _span = trace_span!(
        "sonatina.codegen.object.compile_section",
        section_object = section_id.object.0,
        section = section_id.section
    )
    .entered();
    if cache.contains_key(&section_id) {
        return Ok(());
    }

    let section = program.section(section_id);
    let (object_name, section_name) = program.section_name(section_id);

    let defined_embed_symbols: Vec<EmbedSymbol> =
        section.embeds.iter().map(|e| e.as_symbol.clone()).collect();
    let defined_embed_symbol_set: FxHashSet<EmbedSymbol> =
        defined_embed_symbols.iter().cloned().collect();
    let mut section_data: Vec<GlobalVariableRef> = section.data.iter().copied().collect();
    section_data.sort_unstable();

    let membership = {
        let _span = trace_span!("sonatina.codegen.object.build_membership").entered();
        build_section_membership(
            program.module,
            section.entry,
            &section.includes,
            &section_data,
        )
    };

    let funcs = {
        let _span =
            trace_span!("sonatina.codegen.object.compute_function_emission_order").entered();
        compute_section_function_emission_order(
            program.module,
            section.entry,
            &section.includes,
            &membership,
        )
    };
    let backend_errors = reject_unsupported_evm_multi_return(
        program.module,
        &funcs,
        section.entry,
        object_name,
        section_name,
    );
    if !backend_errors.is_empty() {
        return Err(backend_errors);
    }

    let prepare_error = |message: String, func: FuncRef| {
        vec![ObjectCompileError::BackendError {
            object: object_name.clone(),
            section: section_name.clone(),
            func,
            message,
        }]
    };

    let prepared = {
        let _span = trace_span!("sonatina.codegen.object.prepare_section_work_module").entered();
        let fallback_func = funcs.first().copied().unwrap_or(section.entry);
        let work = SectionWorkModule::from_module_subset(
            program.module,
            &funcs,
            section.entry,
            &section.includes,
            &section_data,
        );
        backend
            .prepare_section(work)
            .map_err(|message| prepare_error(message, fallback_func))?
    };

    for used in prepared.used_embed_symbols() {
        if !defined_embed_symbol_set.contains(used) {
            return Err(vec![ObjectCompileError::UndefinedEmbedSymbol {
                object: object_name.clone(),
                section: section_name.clone(),
                symbol: used.clone(),
            }]);
        }
    }
    let mut data: Vec<(GlobalVariableRef, Vec<u8>)> = Vec::new();
    {
        let _span = trace_span!(
            "sonatina.codegen.object.encode_global_initializers",
            global_count = prepared.globals().len()
        )
        .entered();
        for &gv in prepared.globals() {
            let bytes = super::data::encode_gv_initializer_to_bytes(&prepared.module().ctx, gv)
                .map_err(|e| {
                    vec![ObjectCompileError::InvalidGlobalForData {
                        object: object_name.clone(),
                        section: section_name.clone(),
                        gv,
                        reason: format!("{e:?}"),
                    }]
                })?;
            data.push((gv, bytes));
        }
    }

    let mut embeds: Vec<(EmbedSymbol, Vec<u8>)> = Vec::new();
    {
        let _span = trace_span!(
            "sonatina.codegen.object.collect_embeds",
            embed_count = section.embeds.len()
        )
        .entered();
        for embed in &section.embeds {
            let source = cache.get(&embed.source).ok_or_else(|| {
                vec![ObjectCompileError::LinkError {
                    object: object_name.clone(),
                    section: section_name.clone(),
                    message: "missing embedded section artifact".to_string(),
                }]
            })?;
            embeds.push((embed.as_symbol.clone(), source.bytes.clone()));
        }
    }

    let artifact = {
        let _span = trace_span!(
            "sonatina.codegen.object.link_section",
            object = %object_name.0,
            section = %section_name.0
        )
        .entered();
        link_section(backend, &prepared, &data, &embeds, section_name, opts).map_err(
            |e| match e {
                LinkSectionError::Backend { func, error } => {
                    vec![ObjectCompileError::BackendError {
                        object: object_name.clone(),
                        section: section_name.clone(),
                        func,
                        message: error,
                    }]
                }
                LinkSectionError::Link(message) => vec![ObjectCompileError::LinkError {
                    object: object_name.clone(),
                    section: section_name.clone(),
                    message,
                }],
            },
        )?
    };

    cache.insert(section_id, artifact);
    Ok(())
}

fn collect_embed_deps(
    program: &ResolvedProgram<'_>,
    id: SectionId,
    out: &mut FxHashSet<SectionId>,
) {
    if !out.insert(id) {
        return;
    }
    for embed in &program.section(id).embeds {
        collect_embed_deps(program, embed.source, out);
    }
}

fn topo_sort_sections(program: &ResolvedProgram<'_>) -> Vec<SectionId> {
    let roots = program.all_sections();

    let mut visited: FxHashSet<SectionId> = FxHashSet::default();
    let mut order = Vec::new();

    fn dfs(
        program: &ResolvedProgram<'_>,
        node: SectionId,
        visited: &mut FxHashSet<SectionId>,
        order: &mut Vec<SectionId>,
    ) {
        if !visited.insert(node) {
            return;
        }

        for embed in &program.section(node).embeds {
            dfs(program, embed.source, visited, order);
        }
        order.push(node);
    }

    for root in roots {
        dfs(program, root, &mut visited, &mut order);
    }

    order
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        isa::evm::{EvmBackend, PushWidthPolicy},
        object::{
            CompileOptions, FrontendProvenanceMap, OBSERVABILITY_SCHEMA_VERSION, artifact::SymbolId,
        },
    };
    use sonatina_ir::{
        InstDowncastMut, Type, inst::arith::Add, ir_writer::ModuleWriter, isa::evm::Evm,
    };
    use sonatina_parser::parse_module;
    use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};
    use sonatina_verifier::{VerificationLevel, VerifierConfig};

    fn test_backend() -> EvmBackend {
        EvmBackend::new(Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        }))
    }

    fn compile_opts(
        fixup_policy: PushWidthPolicy,
        emit_symtab: bool,
        emit_observability: bool,
        verifier_cfg: VerifierConfig,
    ) -> CompileOptions {
        CompileOptions {
            fixup_policy,
            emit_symtab,
            emit_observability,
            verifier_cfg,
        }
    }

    fn compile_fixture(
        source: &str,
        object: &str,
        opts: &CompileOptions,
    ) -> crate::object::artifact::ObjectArtifact {
        let parsed = parse_module(source).unwrap();
        compile_object(&parsed.module, &test_backend(), object, opts).unwrap()
    }

    fn section<'a>(
        artifact: &'a crate::object::artifact::ObjectArtifact,
        name: &str,
    ) -> &'a crate::object::artifact::SectionArtifact {
        artifact
            .sections
            .iter()
            .find(|(section_name, _)| section_name.0.as_str() == name)
            .expect("section missing")
            .1
    }

    fn expect_contains_u32(bytes: &[u8], value: u32) {
        let needle = value.to_be_bytes();
        assert!(
            bytes.windows(needle.len()).any(|window| window == needle),
            "expected {value} in {bytes:?}"
        );
    }

    #[test]
    fn compile_object_embeds_sections_and_patches_fixups() {
        let artifact = compile_fixture(
            r#"
target = "evm-ethereum-osaka"

global public const [i8; 3] $blob = [1, 2, 3];

func public %runtime() {
    block0:
        v0.i256 = sym_addr $blob;
        v1.i256 = sym_size $blob;
        mstore 0.i256 v0 i256;
        mstore 32.i256 v1 i256;
        evm_return 0.i256 64.i256;
}

func public %init() {
    block0:
        v0.i256 = sym_addr &runtime;
        v1.i256 = sym_size &runtime;
        mstore 0.i256 v0 i256;
        mstore 32.i256 v1 i256;
        evm_return 0.i256 64.i256;
}

object @Contract {
  section init {
    entry %init;
    embed .runtime as &runtime;
  }
  section runtime {
    entry %runtime;
    data $blob;
  }
}
"#,
            "Contract",
            &compile_opts(
                PushWidthPolicy::Push4,
                true,
                false,
                VerifierConfig::for_level(VerificationLevel::Standard),
            ),
        );

        let init = section(&artifact, "init");
        let runtime = section(&artifact, "runtime");
        let blob = runtime
            .symtab
            .iter()
            .find_map(|(sym, def)| matches!(sym, SymbolId::Global(_)).then_some(def))
            .expect("blob symbol missing");
        let embed = init
            .symtab
            .iter()
            .find_map(|(sym, def)| matches!(sym, SymbolId::Embed(_)).then_some(def))
            .expect("embed symbol missing");

        assert!(init.bytes.ends_with(runtime.bytes.as_slice()));
        expect_contains_u32(&runtime.bytes, blob.offset);
        expect_contains_u32(&runtime.bytes, blob.size);
        expect_contains_u32(&init.bytes, embed.offset);
        expect_contains_u32(&init.bytes, embed.size);
    }

    #[test]
    fn compile_object_resolves_current_section_symbols() {
        let artifact = compile_fixture(
            r#"
target = "evm-ethereum-osaka"

global public const [i8; 3] $blob = [1, 2, 3];

func public %runtime() {
    block0:
        v0.i256 = sym_addr $blob;
        v1.i256 = sym_size $blob;
        mstore 0.i256 v0 i256;
        mstore 32.i256 v1 i256;
        evm_return 0.i256 64.i256;
}

func public %init() {
    block0:
        v0.i256 = sym_addr .;
        v1.i256 = sym_size .;
        v2.i256 = sym_addr &runtime;
        v3.i256 = sym_size &runtime;
        mstore 0.i256 v0 i256;
        mstore 32.i256 v1 i256;
        mstore 64.i256 v2 i256;
        mstore 96.i256 v3 i256;
        evm_return 0.i256 128.i256;
}

object @Contract {
  section init {
    entry %init;
    embed .runtime as &runtime;
  }
  section runtime {
    entry %runtime;
    data $blob;
  }
}
"#,
            "Contract",
            &compile_opts(
                PushWidthPolicy::Push4,
                true,
                false,
                VerifierConfig::for_level(VerificationLevel::Standard),
            ),
        );

        let init = section(&artifact, "init");
        let init_current = init
            .symtab
            .get(&SymbolId::CurrentSection)
            .expect("current-section symbol missing");
        let runtime_embed = init
            .symtab
            .iter()
            .find_map(|(sym, def)| matches!(sym, SymbolId::Embed(_)).then_some(def))
            .expect("runtime embed symbol missing");

        expect_contains_u32(&init.bytes, init_current.offset);
        expect_contains_u32(&init.bytes, init_current.size);
        expect_contains_u32(&init.bytes, runtime_embed.offset);
        expect_contains_u32(&init.bytes, runtime_embed.size);
    }

    #[test]
    fn compile_object_emits_observability_when_enabled() {
        let artifact = compile_fixture(
            r#"
target = "evm-ethereum-osaka"

func public %runtime() {
    block0:
        v0.i256 = add 1.i256 2.i256;
        mstore 0.i256 v0 i256;
        evm_return 0.i256 32.i256;
}

func public %init() {
    block0:
        call %runtime;
        evm_return 0.i256 0.i256;
}

object @Contract {
  section init {
    entry %init;
  }
  section runtime {
    entry %runtime;
  }
}
"#,
            "Contract",
            &compile_opts(
                PushWidthPolicy::Push4,
                false,
                true,
                VerifierConfig::for_level(VerificationLevel::Standard),
            ),
        );

        let init = section(&artifact, "init");
        let runtime = section(&artifact, "runtime");
        let init_obs = init.observability.as_ref().expect("init observability");
        let runtime_obs = runtime
            .observability
            .as_ref()
            .expect("runtime observability");

        assert_eq!(init_obs.schema_version, OBSERVABILITY_SCHEMA_VERSION);
        assert_eq!(runtime_obs.schema_version, OBSERVABILITY_SCHEMA_VERSION);
        assert_eq!(init_obs.section_bytes, init.bytes.len() as u32);
        assert_eq!(runtime_obs.section_bytes, runtime.bytes.len() as u32);
        assert_eq!(
            init_obs.mapped_code_bytes + init_obs.unmapped_code_bytes,
            init_obs.code_bytes
        );
        assert_eq!(
            runtime_obs.mapped_code_bytes + runtime_obs.unmapped_code_bytes,
            runtime_obs.code_bytes
        );

        let mut enriched = artifact.observability().expect("object observability");
        let target = enriched
            .sections
            .values()
            .flat_map(|section| section.pc_map.iter())
            .find_map(|entry| entry.ir_inst.map(|ir_inst| (entry.func, ir_inst)))
            .expect("expected ir-backed pc-map entry");
        let mut map = FrontendProvenanceMap::default();
        map.insert(target, "mir_stmt:1".to_string());
        enriched.apply_frontend_provenance(&map);
        assert!(
            enriched
                .to_json()
                .contains("\"frontend_provenance\":\"mir_stmt:1\"")
        );
    }

    #[test]
    fn compile_object_omits_observability_when_disabled() {
        let artifact = compile_fixture(
            r#"
target = "evm-ethereum-osaka"

func public %runtime() {
    block0:
        evm_return 0.i256 0.i256;
}

object @Contract {
  section runtime {
    entry %runtime;
  }
}
"#,
            "Contract",
            &compile_opts(
                PushWidthPolicy::Push4,
                false,
                false,
                VerifierConfig::for_level(VerificationLevel::Standard),
            ),
        );

        assert!(artifact.observability().is_none());
        assert!(
            artifact
                .sections
                .values()
                .all(|section| section.observability.is_none())
        );
    }

    #[test]
    fn observability_serialization_is_deterministic_across_repeated_builds() {
        let source = r#"
target = "evm-ethereum-osaka"

func public %runtime() {
    block0:
        v0.i256 = add 1.i256 2.i256;
        mstore 0.i256 v0 i256;
        evm_return 0.i256 32.i256;
}

object @Contract {
  section runtime {
    entry %runtime;
  }
}
"#;
        let opts = compile_opts(
            PushWidthPolicy::Push4,
            false,
            true,
            VerifierConfig::for_level(VerificationLevel::Standard),
        );

        let a = compile_fixture(source, "Contract", &opts);
        let b = compile_fixture(source, "Contract", &opts);

        let a_obs = a.observability().expect("observability expected");
        let b_obs = b.observability().expect("observability expected");
        assert_eq!(a_obs.to_text(), b_obs.to_text());
        assert_eq!(a_obs.to_json(), b_obs.to_json());
    }

    #[test]
    fn compile_object_reports_verifier_failures_before_codegen() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func public %main() {
    block0:
        v0.i32 = add 1.i32 2.i32;
}

object @O {
  section runtime {
    entry %main;
  }
}
"#,
        )
        .unwrap();
        let errs = compile_object(
            &parsed.module,
            &test_backend(),
            "O",
            &compile_opts(
                PushWidthPolicy::Push4,
                false,
                false,
                VerifierConfig::for_level(VerificationLevel::Standard),
            ),
        )
        .expect_err("invalid IR should fail verifier preflight");
        assert!(matches!(
            errs.as_slice(),
            [ObjectCompileError::VerifierFailed { .. }]
        ));
    }

    #[test]
    fn compile_object_fast_respects_custom_users_check() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func public %main() {
    block0:
        v0.i32 = add 1.i32 2.i32;
        return;
}

object @O {
  section runtime {
    entry %main;
  }
}
"#,
        )
        .unwrap();
        let module = parsed.module;
        let func_ref = module.funcs()[0];
        module.func_store.modify(func_ref, |func| {
            let block = func.layout.entry_block().expect("entry block must exist");
            let inst = func
                .layout
                .first_inst_of(block)
                .expect("first instruction must exist");
            let replacement = func.dfg.make_imm_value(99i32);
            let inst_set = func.inst_set();
            let inst_data = func.dfg.inst_mut(inst);
            let add =
                <&mut Add as InstDowncastMut>::downcast_mut(inst_set, inst_data).expect("add");
            *add.lhs_mut() = replacement;
        });

        let mut verifier_cfg = VerifierConfig::for_level(VerificationLevel::Fast);
        verifier_cfg.check_users = true;
        let errs = compile_object(
            &module,
            &test_backend(),
            "O",
            &compile_opts(PushWidthPolicy::Push4, false, false, verifier_cfg),
        )
        .expect_err("fast preflight should run requested users check");
        let [ObjectCompileError::VerifierFailed { report }] = errs.as_slice() else {
            panic!("expected verifier failure, got {errs:?}");
        };
        assert!(
            report
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code.as_str() == "IR0700")
        );
    }

    #[test]
    fn compile_object_fast_rejects_bad_uaddo_result_shape() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func public %main(v0.i32, v1.i32) -> i32 {
    block0:
        v2.i32 = uaddo v0 v1;
        return v2;
}

object @O {
  section runtime {
    entry %main;
  }
}
"#,
        )
        .unwrap();
        let errs = compile_object(
            &parsed.module,
            &test_backend(),
            "O",
            &compile_opts(
                PushWidthPolicy::Push4,
                false,
                false,
                VerifierConfig::for_level(VerificationLevel::Fast),
            ),
        )
        .expect_err("bad multi-result IR should fail verifier preflight");
        let [ObjectCompileError::VerifierFailed { report }] = errs.as_slice() else {
            panic!("expected verifier failure, got {errs:?}");
        };
        assert!(
            report
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code.as_str() == "IR0601")
        );
    }

    #[test]
    fn compile_object_fast_rejects_bad_snego_result_shape() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func public %main(v0.i32) -> i32 {
    block0:
        v1.i32 = snego v0;
        return v1;
}

object @O {
  section runtime {
    entry %main;
  }
}
"#,
        )
        .unwrap();
        let errs = compile_object(
            &parsed.module,
            &test_backend(),
            "O",
            &compile_opts(
                PushWidthPolicy::Push4,
                false,
                false,
                VerifierConfig::for_level(VerificationLevel::Fast),
            ),
        )
        .expect_err("bad checked-overflow IR should fail verifier preflight");
        let [ObjectCompileError::VerifierFailed { report }] = errs.as_slice() else {
            panic!("expected verifier failure, got {errs:?}");
        };
        assert!(
            report
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code.as_str() == "IR0601")
        );
    }

    #[test]
    fn compile_object_rejects_multi_return_section_entry_for_evm() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func public %main(v0.i32, v1.i32) -> (i32, i1) {
    block0:
        (v2.i32, v3.i1) = uaddo v0 v1;
        return (v2, v3);
}

object @O {
  section runtime {
    entry %main;
  }
}
"#,
        )
        .unwrap();
        let errs = compile_object(
            &parsed.module,
            &test_backend(),
            "O",
            &compile_opts(
                PushWidthPolicy::Push4,
                false,
                false,
                VerifierConfig::for_level(VerificationLevel::Standard),
            ),
        )
        .expect_err("must reject multi-return");
        assert!(errs.iter().any(|err| matches!(
            err,
            ObjectCompileError::BackendError { message, .. }
                if message.contains("does not support section entry %main with 2 return values")
        )));
    }

    #[test]
    fn compile_object_rejects_declaration_only_section_entry() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

declare external %main();

object @O {
  section runtime {
    entry %main;
  }
}
"#,
        )
        .unwrap();
        let errs = compile_object(
            &parsed.module,
            &test_backend(),
            "O",
            &compile_opts(
                PushWidthPolicy::Push4,
                false,
                false,
                VerifierConfig::for_level(VerificationLevel::Fast),
            ),
        )
        .expect_err("declaration-only section entry must fail verifier preflight");
        let [ObjectCompileError::VerifierFailed { report }] = errs.as_slice() else {
            panic!("expected verifier failure, got {errs:?}");
        };
        assert!(report.diagnostics.iter().any(|diagnostic| {
            diagnostic
                .message
                .contains("section entry must reference a defined function body")
        }));
    }

    #[test]
    fn compile_object_allows_internal_multi_return_helpers_for_evm() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func public %pair_add(v0.i32, v1.i32) -> (i32, i1) {
    block0:
        v2.i32 = add v0 v1;
        v3.i1 = lt v2 v0;
        return (v2, v3);
}

func public %main() -> i32 {
    block0:
        (v0.i32, v1.i1) = call %pair_add 1.i32 2.i32;
        br v1 block1 block2;

    block1:
        return 0.i32;

    block2:
        return v0;
}

object @O {
  section runtime {
    entry %main;
  }
}
"#,
        )
        .unwrap();
        compile_object(
            &parsed.module,
            &test_backend(),
            "O",
            &compile_opts(
                PushWidthPolicy::Push4,
                false,
                false,
                VerifierConfig::for_level(VerificationLevel::Standard),
            ),
        )
        .expect("internal multi-return helper should be allowed");
    }

    #[test]
    fn compile_object_rejects_external_multi_return_calls_for_evm() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

declare external %pair_add(i32, i32) -> (i32, i1);

func public %main() {
    block0:
        (v0.i32, v1.i1) = call %pair_add 1.i32 2.i32;
        return;
}

object @O {
  section runtime {
    entry %main;
  }
}
"#,
        )
        .unwrap();
        let errs = compile_object(
            &parsed.module,
            &test_backend(),
            "O",
            &compile_opts(
                PushWidthPolicy::Push4,
                false,
                false,
                VerifierConfig::for_level(VerificationLevel::Standard),
            ),
        )
        .expect_err("must reject multi-return call");
        assert!(errs.iter().any(|err| matches!(
            err,
            ObjectCompileError::BackendError { message, .. }
                if message.contains("external or declaration-only multi-return calls")
        )));
    }

    #[test]
    fn compile_object_keeps_input_module_immutable() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func private %swap(v0.@pair) -> @pair {
    block0:
        v1.i256 = extract_value v0 0.i8;
        v2.i256 = extract_value v0 1.i8;
        v3.@pair = insert_value undef.@pair 0.i8 v2;
        v4.@pair = insert_value v3 1.i8 v1;
        return v4;
}

func public %main(v0.i256, v1.i256) -> i256 {
    block0:
        v2.@pair = insert_value undef.@pair 0.i8 v0;
        v3.@pair = insert_value v2 1.i8 v1;
        v4.@pair = call %swap v3;
        v5.i256 = extract_value v4 0.i8;
        return v5;
}

object @O {
  section runtime {
    entry %main;
  }
}
"#,
        )
        .unwrap();
        let original = ModuleWriter::new(&parsed.module).dump_string();
        compile_object(
            &parsed.module,
            &test_backend(),
            "O",
            &compile_opts(
                PushWidthPolicy::Push4,
                false,
                false,
                VerifierConfig::for_level(VerificationLevel::Standard),
            ),
        )
        .expect("compile should succeed");

        let swap = parsed
            .module
            .ctx
            .declared_funcs
            .iter()
            .find_map(|entry| (entry.value().name() == "swap").then_some(*entry.key()))
            .expect("swap should exist");
        let sig = parsed
            .module
            .ctx
            .get_sig(swap)
            .expect("signature should exist");
        assert!(matches!(sig.args(), [Type::Compound(_)]));
        assert!(matches!(sig.ret_tys(), [Type::Compound(_)]));
        assert_eq!(ModuleWriter::new(&parsed.module).dump_string(), original);
    }

    #[test]
    fn compile_object_rejects_internal_multi_return_arity_above_16_for_evm() {
        let ret_tys = std::iter::repeat_n("i32", 17)
            .collect::<Vec<_>>()
            .join(", ");
        let ret_values = (0..17)
            .map(|idx| format!("{idx}.i32"))
            .collect::<Vec<_>>()
            .join(", ");
        let call_results = (0..17)
            .map(|idx| format!("v{idx}.i32"))
            .collect::<Vec<_>>()
            .join(", ");
        let source = format!(
            r#"
target = "evm-ethereum-osaka"

func public %pair_many() -> ({ret_tys}) {{
    block0:
        return ({ret_values});
}}

func public %main() -> i32 {{
    block0:
        ({call_results}) = call %pair_many;
        return v0;
}}

object @O {{
  section runtime {{
    entry %main;
  }}
}}
"#
        );
        let parsed = parse_module(&source).unwrap();
        let errs = compile_object(
            &parsed.module,
            &test_backend(),
            "O",
            &compile_opts(
                PushWidthPolicy::Push4,
                false,
                false,
                VerifierConfig::for_level(VerificationLevel::Standard),
            ),
        )
        .expect_err("must reject >16 internal multi-return arity");
        assert!(errs.iter().any(|err| matches!(
            err,
            ObjectCompileError::BackendError { message, .. }
                if message.contains("supports at most 16 internal return values")
        )));
    }

    #[test]
    fn emits_functions_in_call_graph_dfs_order() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func public %main() {
    block0:
        call %b;
        call %c;
        return;
}

func public %b() {
    block0:
        return;
}

func public %c() {
    block0:
        return;
}

func public %d() {
    block0:
        call %e;
        return;
}

func public %e() {
    block0:
        return;
}

object @O {
  section runtime {
    entry %main;
    include %c;
    include %d;
  }
}
"#,
        )
        .unwrap();
        let program = ResolvedProgram::resolve(&parsed.module).unwrap();
        let section_id = SectionId {
            object: ObjectId(0),
            section: 0,
        };
        let section = program.section(section_id);
        let mut section_data: Vec<GlobalVariableRef> = section.data.iter().copied().collect();
        section_data.sort_unstable();
        let membership = build_section_membership(
            &parsed.module,
            section.entry,
            &section.includes,
            &section_data,
        );
        let order = compute_section_function_emission_order(
            &parsed.module,
            section.entry,
            &section.includes,
            &membership,
        );
        let names: Vec<_> = order
            .into_iter()
            .map(|func| {
                parsed
                    .module
                    .ctx
                    .func_sig(func, |sig| sig.name().to_string())
            })
            .collect();
        assert_eq!(names, vec!["main", "c", "b", "d", "e"]);
    }
}
