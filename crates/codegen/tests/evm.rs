mod evm_directives;

use dir_test::{Fixture, dir_test};

use hex::ToHex;
use revm::{
    Context, EvmContext, Handler, inspector_handle_register,
    interpreter::Interpreter,
    primitives::{
        AccountInfo, Address, Bytecode, Bytes, Env, ExecutionResult, OsakaSpec, Output, TransactTo,
        U256,
    },
};

use sonatina_codegen::{
    domtree::DomTree,
    isa::evm::{EvmBackend, LateCleanupProfile, PushWidthPolicy, canonicalize_alias_value},
    liveness::Liveness,
    machinst::{
        lower::{LoweredFunction, SectionCodeUnit, SectionWorkModule},
        vcode::{Label, VCodeFixup},
    },
    object::{CompileOptions, compile_all_objects},
    optim::{
        dead_func::{collect_object_roots, run_dead_func_elim},
        pipeline::Pipeline,
    },
    stackalloc::StackifyBuilder,
    stackify_edge::StackifyEdgeSplitter,
};
use sonatina_ir::{
    BlockId, Function, U256 as IrU256,
    cfg::ControlFlowGraph,
    ir_writer::{FuncWriteCtx, FunctionSignature, IrWrite, ModuleWriter},
    isa::evm::Evm,
    module::{Module, ModuleCtx},
};
use sonatina_parser::{ParsedModule, parse_module};
use sonatina_triple::{Architecture, OperatingSystem, Vendor};
use sonatina_verifier::{VerificationLevel, VerifierConfig};
use std::{
    collections::HashMap,
    fmt,
    io::{Write, stderr},
};

use evm_directives::{EvmCase, EvmExpect, EvmOptPipeline};

fn fmt_stackify_trace(trace: &str) -> String {
    let mut out = String::new();
    for line in trace.lines() {
        if line == "STACKIFY" || line == "trace:" {
            continue;
        }
        out.push_str(line);
        out.push('\n');
    }
    out
}

// XXX copied from fe test-utils
#[macro_export]
macro_rules! snap_test {
    ($value:expr, $fixture_path: expr) => {
        let mut settings = insta::Settings::new();
        let fixture_path = ::std::path::Path::new($fixture_path);
        let fixture_dir = fixture_path.parent().unwrap();
        let fixture_name = fixture_path.file_stem().unwrap().to_str().unwrap();

        settings.set_snapshot_path(fixture_dir);
        settings.set_input_file($fixture_path);
        settings.set_prepend_module_to_snapshot(false);
        settings.bind(|| {
            insta::_macro_support::assert_snapshot(
                (insta::_macro_support::AutoName, $value.as_str()).into(),
                std::path::Path::new(env!("CARGO_MANIFEST_DIR")),
                fixture_name,
                module_path!(),
                file!(),
                line!(),
                stringify!($value),
            )
            .unwrap()
        })
    };

    ($value:expr, $fixture_path: expr, $suffix:expr) => {
        let mut settings = insta::Settings::new();
        let fixture_path = ::std::path::Path::new($fixture_path);
        let fixture_dir = fixture_path.parent().unwrap();
        let fixture_name = fixture_path.file_stem().unwrap().to_str().unwrap();
        let suffix: &str = $suffix;
        let name = format!("{fixture_name}.{suffix}");

        settings.set_snapshot_path(fixture_dir);
        settings.set_input_file($fixture_path);
        settings.set_prepend_module_to_snapshot(false);
        settings.bind(|| {
            insta::_macro_support::assert_snapshot(
                (name, $value.as_str()).into(),
                std::path::Path::new(env!("CARGO_MANIFEST_DIR")),
                fixture_name,
                module_path!(),
                file!(),
                line!(),
                stringify!($value),
            )
            .unwrap()
        })
    };
}

fn parse_sona(content: &str) -> ParsedModule {
    match parse_module(content) {
        Ok(module) => module,
        Err(errs) => {
            let mut w = stderr();
            for err in errs {
                err.print(&mut w, "[test]", content, true).unwrap();
            }
            panic!("Failed to parse test file. See errors above.")
        }
    }
}

fn run_opt_pipeline(module: &mut Module, opt_pipeline: EvmOptPipeline) {
    match opt_pipeline {
        EvmOptPipeline::None => {}
        EvmOptPipeline::Size => Pipeline::size().run(module),
        EvmOptPipeline::Speed => Pipeline::speed().run(module),
    }
}

fn prune_unreachable_funcs_for_optimized_evm_snapshots(
    module: &mut Module,
    opt_pipeline: EvmOptPipeline,
) {
    if opt_pipeline != EvmOptPipeline::None {
        let roots = collect_object_roots(module);
        run_dead_func_elim(module, &roots, Default::default());
    }
}

#[dir_test(
    dir: "$CARGO_MANIFEST_DIR/test_files/evm",
    glob: "*.sntn"
)]
fn test_evm(fixture: Fixture<&str>) {
    let mut parsed = parse_sona(fixture.content());
    let cfg = evm_directives::parse_evm_config(&parsed.debug.module_comments)
        .unwrap_or_else(|e| panic!("{}: {e}", fixture.path()));
    let stackify_reach_depth = cfg.stack_reach.unwrap_or(16);
    let emit_vcode = cfg.vcode.unwrap_or(false);
    let emit_bytecode_hex = cfg.bytecode_hex.unwrap_or(false);
    let emit_stackify_trace = cfg.stackify_trace.unwrap_or(false);
    let emit_evm_trace = cfg.evm_trace.unwrap_or(false);
    let emit_observability = cfg.emit_observability.unwrap_or(false);
    let opt_pipeline = cfg.opt.unwrap_or(EvmOptPipeline::None);

    let cases = evm_directives::parse_evm_cases(&parsed.debug.module_comments)
        .unwrap_or_else(|e| panic!("{}: {e}", fixture.path()));

    run_opt_pipeline(&mut parsed.module, opt_pipeline);
    prune_unreachable_funcs_for_optimized_evm_snapshots(&mut parsed.module, opt_pipeline);
    let opt_ir_snapshot = (opt_pipeline != EvmOptPipeline::None).then(|| {
        let mut writer = ModuleWriter::with_debug_provider(&parsed.module, &parsed.debug);
        writer.dump_string()
    });

    let func_order: Vec<_> = parsed
        .debug
        .func_order
        .iter()
        .copied()
        .filter(|func_ref| {
            parsed.module.ctx.declared_funcs.contains_key(func_ref)
                && parsed
                    .module
                    .ctx
                    .func_sig(*func_ref, |sig| sig.linkage().has_definition())
        })
        .collect();

    let backend = EvmBackend::new(Evm::new(sonatina_triple::TargetTriple {
        architecture: Architecture::Evm,
        vendor: Vendor::Ethereum,
        operating_system: OperatingSystem::Evm(sonatina_triple::EvmVersion::Osaka),
    }))
    .with_stackify_reach_depth(stackify_reach_depth)
    .with_late_cleanup_profile(match opt_pipeline {
        EvmOptPipeline::None => LateCleanupProfile::Off,
        EvmOptPipeline::Size => LateCleanupProfile::Size,
        EvmOptPipeline::Speed => LateCleanupProfile::Speed,
    });

    let prepared = backend
        .prepare_section(SectionWorkModule::from_roots(
            &parsed.module,
            func_order[0],
            &func_order[1..],
            &[],
        ))
        .unwrap();

    let mem_plan = backend.snapshot_mem_plan(&prepared);
    let (mem_plan_header, mem_plan_funcs) = parse_mem_plan_summary(&mem_plan);

    let mut lowered_funcs: Vec<_> = prepared
        .funcs()
        .iter()
        .copied()
        .map(|func| {
            backend
                .lower_function(&prepared, func)
                .map(|lowered| (func, lowered))
                .unwrap()
        })
        .collect();
    let synthetic_units = backend
        .post_lower_section(&prepared, &mut lowered_funcs)
        .unwrap();

    let mut func_stats: Vec<FuncStats> = Vec::new();
    let mut stackify_out = Vec::new();
    let mut lowered_out = Vec::new();

    for (fref, lowered) in &lowered_funcs {
        let vcode_ops = lowered.vcode.insts.len();
        let vcode_fixups = lowered.vcode.fixups.len();
        let vcode_imm_bytes = lowered.vcode.inst_imm_bytes.len();

        let name = prepared
            .module()
            .ctx
            .func_sig(*fref, |sig| sig.name().to_string());

        let mem = mem_plan_funcs
            .get(&name)
            .cloned()
            .unwrap_or_else(|| format!("<missing mem plan entry for {name}>"));

        let (ir_blocks, ir_insts) = prepared.module().func_store.view(*fref, |function| {
            if emit_stackify_trace || emit_vcode {
                let ctx = FuncWriteCtx::with_debug_provider(function, *fref, &parsed.debug);

                if emit_stackify_trace {
                    let stackify = stackify_trace_for_fn(
                        function,
                        &prepared.module().ctx,
                        &backend,
                        stackify_reach_depth,
                    );
                    write!(&mut stackify_out, "// ").unwrap();
                    FunctionSignature.write(&mut stackify_out, &ctx).unwrap();
                    writeln!(&mut stackify_out).unwrap();
                    write!(&mut stackify_out, "{}", fmt_stackify_trace(&stackify)).unwrap();
                    writeln!(&mut stackify_out).unwrap();
                }

                if emit_vcode {
                    write_vcode_in_emitted_order(lowered, &mut lowered_out, &ctx);
                    writeln!(&mut lowered_out).unwrap();
                }
            }

            let ir_blocks = function.layout.iter_block().count();
            let mut ir_insts: usize = 0;
            for block in function.layout.iter_block() {
                ir_insts += function.layout.iter_inst(block).count();
            }
            (ir_blocks, ir_insts)
        });

        func_stats.push(FuncStats {
            name,
            mem,
            ir_blocks,
            ir_insts,
            vcode_ops,
            vcode_fixups,
            vcode_imm_bytes,
        });
    }

    let opts = CompileOptions {
        fixup_policy: PushWidthPolicy::MinimalRelax,
        emit_symtab: false,
        emit_observability,
        verifier_cfg: VerifierConfig::for_level(VerificationLevel::Fast),
    };

    let artifacts = compile_all_objects(&parsed.module, &backend, &opts)
        .unwrap_or_else(|errs| panic!("{}: object compile failed: {errs:?}", fixture.path()));

    let mut out = Vec::new();
    let opt_pipeline_suffix = if opt_pipeline == EvmOptPipeline::None {
        String::new()
    } else {
        format!(" opt={}", opt_pipeline.as_u8())
    };
    writeln!(
        &mut out,
        "evm.config: stack_reach={stackify_reach_depth} vcode={emit_vcode} bytecode_hex={emit_bytecode_hex} stackify_trace={emit_stackify_trace} evm_trace={emit_evm_trace} emit_observability={emit_observability}{opt_pipeline_suffix}",
    )
    .unwrap();
    writeln!(&mut out).unwrap();

    for artifact in &artifacts {
        writeln!(&mut out, "object: {}", artifact.object.0.as_str()).unwrap();
        let mut total_bytes: usize = 0;
        for (name, section) in &artifact.sections {
            let size = section.bytes.len();
            total_bytes += size;
            writeln!(&mut out, "  section {}: {} bytes", name.0.as_str(), size).unwrap();
        }
        writeln!(&mut out, "  total: {total_bytes} bytes").unwrap();
        writeln!(&mut out).unwrap();
    }

    let artifact = artifacts
        .iter()
        .find(|artifact| artifact.object.0.as_str() == "Contract")
        .unwrap_or_else(|| panic!("{}: missing `Contract` object", fixture.path()));

    writeln!(&mut out, "functions:").unwrap();
    if let Some(header) = mem_plan_header {
        writeln!(&mut out, "  mem: {header}").unwrap();
    }
    for stat in &func_stats {
        writeln!(
            &mut out,
            "  {}: ir_blocks={} ir_insts={} vcode_ops={} fixups={} imm_bytes={}",
            stat.name,
            stat.ir_blocks,
            stat.ir_insts,
            stat.vcode_ops,
            stat.vcode_fixups,
            stat.vcode_imm_bytes
        )
        .unwrap();
        writeln!(&mut out, "    mem: {}", stat.mem).unwrap();
    }
    writeln!(&mut out).unwrap();

    if emit_observability && let Some(observability) = artifact.observability() {
        writeln!(&mut out, "--------------- OBSERVABILITY ---------------\n").unwrap();
        writeln!(&mut out, "{}", observability.to_text()).unwrap();
    }

    let init = artifact
        .sections
        .iter()
        .find(|(name, _)| name.0.as_str() == "init")
        .map(|(_, s)| s.bytes.clone());
    let runtime = artifact
        .sections
        .iter()
        .find(|(name, _)| name.0.as_str() == "runtime")
        .map(|(_, s)| s.bytes.clone())
        .unwrap_or_else(|| panic!("{}: missing `runtime` section", fixture.path()));

    let mut deploy_res_dbg: Option<String> = None;
    let mut deploy_trace: Option<String> = None;
    let mut first_call_res_dbg: Option<String> = None;
    let mut first_call_trace: Option<String> = None;

    let mut harness = if let Some(init) = init {
        let (res, trace, harness) = EvmHarness::deploy_with_optional_trace(&init, emit_evm_trace);
        if let Some(trace) = trace {
            deploy_res_dbg = Some(format!("{res:?}"));
            deploy_trace = Some(trace);
        }
        writeln!(&mut out, "evm:").unwrap();
        writeln!(&mut out, "  deploy: {}", summarize_execution_result(&res)).unwrap();
        match res {
            ExecutionResult::Success { .. } => {}
            _ => panic!("{}: deployment failed: {res:?}", fixture.path()),
        }
        harness
    } else {
        writeln!(&mut out, "evm:").unwrap();
        EvmHarness::from_runtime(&runtime)
    };

    if cases.is_empty() {
        writeln!(&mut out, "  <no evm.case directives>").unwrap();
    }

    for (idx, case) in cases.iter().enumerate() {
        let (res, trace) =
            harness.call_with_optional_trace(&case.calldata, emit_evm_trace && idx == 0);
        if let Some(trace) = trace {
            first_call_res_dbg = Some(format!("{res:?}"));
            first_call_trace = Some(trace);
        }
        assert_case(case, &res, fixture.path());
        let tx_gas = initial_tx_gas_for_call(&case.calldata);
        let runtime_gas = execution_gas_used(&res).saturating_sub(tx_gas);
        writeln!(
            &mut out,
            "  case {}: calldata_len={} {} tx_gas={} runtime_gas={}",
            case.name,
            case.calldata.len(),
            summarize_execution_result(&res),
            tx_gas,
            runtime_gas,
        )
        .unwrap();
    }

    if emit_stackify_trace || emit_vcode || emit_bytecode_hex {
        writeln!(&mut out, "\n\n--------------- DEBUG ---------------\n").unwrap();

        out.append(&mut stackify_out);
        out.append(&mut lowered_out);
        if emit_vcode {
            for unit in &synthetic_units {
                write_synthetic_section_unit(unit, &mut out);
                writeln!(&mut out).unwrap();
            }
        }

        if emit_bytecode_hex {
            writeln!(&mut out, "\n\n--------------- BYTECODE ---------------\n").unwrap();
            for (name, section) in &artifact.sections {
                writeln!(&mut out, "// section {}", name.0.as_str()).unwrap();
                let hex = section.bytes.encode_hex::<String>();
                writeln!(&mut out, "0x{hex}\n").unwrap();
            }
        }
    }

    if emit_evm_trace {
        writeln!(&mut out, "\n\n--------------- EVM TRACE ---------------\n").unwrap();
        if let Some(res) = deploy_res_dbg {
            writeln!(&mut out, "\n{res}").unwrap();
        }
        if let Some(trace) = deploy_trace {
            writeln!(&mut out, "\n{trace}").unwrap();
        }
        if let Some(res) = first_call_res_dbg {
            writeln!(&mut out, "\n{res}").unwrap();
        }
        if let Some(trace) = first_call_trace {
            writeln!(&mut out, "\n{trace}").unwrap();
        }
    }

    snap_test!(String::from_utf8(out).unwrap(), fixture.path());
    if let Some(opt_ir_snapshot) = opt_ir_snapshot {
        snap_test!(opt_ir_snapshot, fixture.path(), "opt_ir");
    }
}

fn write_vcode_in_emitted_order<Op: std::fmt::Debug>(
    lowered: &LoweredFunction<Op>,
    out: &mut Vec<u8>,
    ctx: &FuncWriteCtx<'_>,
) {
    lowered
        .vcode
        .write_with_block_order(out, ctx, &lowered.block_order)
        .unwrap();
}

fn write_synthetic_section_unit<Op: fmt::Debug>(unit: &SectionCodeUnit<Op>, out: &mut Vec<u8>) {
    writeln!(out, "// synthetic section unit").unwrap();
    writeln!(out, "{}:", unit.name).unwrap();
    for &block in &unit.block_order {
        let block_insts: Vec<_> = unit.vcode.block_insns(block).collect();
        if block_insts.is_empty() {
            continue;
        }
        writeln!(out, "  block{}:", block.0).unwrap();
        for (idx, insn) in block_insts.iter().copied().enumerate() {
            write!(out, "    {:?}", unit.vcode.insts[insn]).unwrap();
            if let Some((_, bytes)) = unit.vcode.inst_imm_bytes.get(insn) {
                let mut be = [0; 32];
                be[32 - bytes.len()..].copy_from_slice(bytes);
                let imm = IrU256::from_big_endian(&be);
                write!(out, " 0x{imm:x} ({imm})").unwrap();
            } else if let Some((_, fixup)) = unit.vcode.fixups.get(insn)
                && let VCodeFixup::Label(label) = fixup
            {
                match unit.vcode.labels[*label] {
                    Label::Block(BlockId(n)) => write!(out, " block{n}").unwrap(),
                    Label::Insn(target_insn) => {
                        let pos = block_insts
                            .iter()
                            .position(|i| *i == target_insn)
                            .expect("Label::Insn must be in same synthetic block");
                        let offset = pos as i32 - idx as i32;
                        write!(out, " `pc + ({offset})`").unwrap();
                    }
                    Label::Function(func) => write!(out, " {func:?}").unwrap(),
                    Label::SectionCodeUnit(unit) => write!(out, " section_unit{}", unit.0).unwrap(),
                }
            }
            writeln!(out).unwrap();
        }
    }
}

fn assert_case(case: &EvmCase, res: &ExecutionResult, fixture_path: &str) {
    match (&case.expect, res) {
        (EvmExpect::Return(expected), ExecutionResult::Success { output, .. }) => {
            let Output::Call(actual) = output else {
                panic!(
                    "{fixture_path}: evm.case `{}` expected call return, got {res:?}",
                    case.name
                );
            };

            if actual.as_ref() != expected.as_slice() {
                let expected_hex = hex::encode(expected);
                let actual_hex = hex::encode(actual.as_ref());
                panic!(
                    "{fixture_path}: evm.case `{}` return mismatch: expected 0x{expected_hex}, got 0x{actual_hex} ({res:?})",
                    case.name
                );
            }
        }
        (EvmExpect::Revert(expected), ExecutionResult::Revert { output, .. }) => {
            if output.as_ref() != expected.as_slice() {
                let expected_hex = hex::encode(expected);
                let actual_hex = hex::encode(output.as_ref());
                panic!(
                    "{fixture_path}: evm.case `{}` revert mismatch: expected 0x{expected_hex}, got 0x{actual_hex} ({res:?})",
                    case.name
                );
            }
        }
        _ => {
            panic!(
                "{fixture_path}: evm.case `{}` unexpected result: expected {:?}, got {res:?}",
                case.name, case.expect
            );
        }
    }
}

struct EvmHarness {
    db: revm::InMemoryDB,
    contract: Address,
}

impl EvmHarness {
    fn from_runtime(bytecode: &[u8]) -> Self {
        let mut db = revm::InMemoryDB::default();
        let revm_bytecode = Bytecode::new_raw(Bytes::copy_from_slice(bytecode));
        let contract = Address::repeat_byte(0x12);
        db.insert_account_info(
            contract,
            AccountInfo {
                balance: U256::ZERO,
                nonce: 0,
                code_hash: revm_bytecode.hash_slow(),
                code: Some(revm_bytecode),
            },
        );

        Self { db, contract }
    }

    fn deploy(init_code: &[u8]) -> (ExecutionResult, Self) {
        let mut env = Env::default();
        env.tx.clear();
        env.tx.transact_to = TransactTo::Create;
        env.tx.data = Bytes::copy_from_slice(init_code);

        let (res, db) = Self::run_tx(revm::InMemoryDB::default(), env);
        let deployed = match &res {
            ExecutionResult::Success {
                output: Output::Create(_, Some(addr)),
                ..
            } => *addr,
            _ => panic!("unexpected deployment result: {res:?}"),
        };

        (
            res,
            Self {
                db,
                contract: deployed,
            },
        )
    }

    fn deploy_with_trace(init_code: &[u8]) -> (ExecutionResult, String, Self) {
        let mut env = Env::default();
        env.tx.clear();
        env.tx.transact_to = TransactTo::Create;
        env.tx.data = Bytes::copy_from_slice(init_code);

        let (res, trace, db) = Self::run_tx_with_trace(revm::InMemoryDB::default(), env);
        let deployed = match &res {
            ExecutionResult::Success {
                output: Output::Create(_, Some(addr)),
                ..
            } => *addr,
            _ => panic!("unexpected deployment result: {res:?}"),
        };

        (
            res,
            trace,
            Self {
                db,
                contract: deployed,
            },
        )
    }

    fn deploy_with_optional_trace(
        init_code: &[u8],
        emit_trace: bool,
    ) -> (ExecutionResult, Option<String>, Self) {
        if emit_trace {
            let (res, trace, harness) = Self::deploy_with_trace(init_code);
            (res, Some(trace), harness)
        } else {
            let (res, harness) = Self::deploy(init_code);
            (res, None, harness)
        }
    }

    fn call(&mut self, calldata: &[u8]) -> ExecutionResult {
        let mut env = Env::default();
        env.tx.clear();
        env.tx.transact_to = TransactTo::Call(self.contract);
        env.tx.data = Bytes::copy_from_slice(calldata);

        let db = std::mem::take(&mut self.db);
        let (res, db) = Self::run_tx(db, env);
        self.db = db;
        res
    }

    fn call_with_trace(&mut self, calldata: &[u8]) -> (ExecutionResult, String) {
        let mut env = Env::default();
        env.tx.clear();
        env.tx.transact_to = TransactTo::Call(self.contract);
        env.tx.data = Bytes::copy_from_slice(calldata);

        let db = std::mem::take(&mut self.db);
        let (res, trace, db) = Self::run_tx_with_trace(db, env);
        self.db = db;
        (res, trace)
    }

    fn call_with_optional_trace(
        &mut self,
        calldata: &[u8],
        emit_trace: bool,
    ) -> (ExecutionResult, Option<String>) {
        if emit_trace {
            let (res, trace) = self.call_with_trace(calldata);
            (res, Some(trace))
        } else {
            (self.call(calldata), None)
        }
    }

    fn run_tx(mut db: revm::InMemoryDB, env: Env) -> (ExecutionResult, revm::InMemoryDB) {
        struct NoopInspector;
        impl<DB: revm::Database> revm::Inspector<DB> for NoopInspector {}

        let context = Context::new(EvmContext::new_with_env(db, Box::new(env)), NoopInspector);
        let mut evm = revm::Evm::new(context, Handler::mainnet::<OsakaSpec>());

        let res = evm.transact_commit();
        db = std::mem::take(&mut evm.context.evm.inner.db);

        match res {
            Ok(r) => (r, db),
            Err(e) => panic!("evm failure: {e}"),
        }
    }

    fn run_tx_with_trace(
        mut db: revm::InMemoryDB,
        env: Env,
    ) -> (ExecutionResult, String, revm::InMemoryDB) {
        let context = Context::new(
            EvmContext::new_with_env(db, Box::new(env)),
            TestInspector::new(vec![]),
        );

        let mut evm = revm::Evm::new(context, Handler::mainnet::<OsakaSpec>());
        evm = evm
            .modify()
            .append_handler_register(inspector_handle_register)
            .build();

        let res = evm.transact_commit();
        let trace = String::from_utf8(evm.context.external.w).unwrap();
        db = std::mem::take(&mut evm.context.evm.inner.db);

        match res {
            Ok(r) => (r, trace, db),
            Err(e) => panic!("evm failure: {e}"),
        }
    }
}

struct TestInspector<W: Write> {
    w: W,
}

impl<W: Write> TestInspector<W> {
    fn new(w: W) -> TestInspector<W> {
        Self { w }
    }
}

impl<W: Write, DB: revm::Database> revm::Inspector<DB> for TestInspector<W> {
    fn initialize_interp(&mut self, _interp: &mut Interpreter, _context: &mut EvmContext<DB>) {
        writeln!(
            self.w,
            "{:>6}  {:<17} input (stack grows to the right)",
            "pc", "opcode"
        )
        .unwrap();
    }

    fn step(&mut self, interp: &mut Interpreter, _context: &mut EvmContext<DB>) {
        // xxx tentatively writing input stack; clean up
        let pc = interp.program_counter();

        let op = interp.current_opcode();
        let code = unsafe { std::mem::transmute::<u8, revm::interpreter::OpCode>(op) };

        let stack = interp.stack().data();

        write!(
            self.w,
            "{:>6}  {:0>2}  {:<12}  ",
            pc,
            format!("{op:x}"),
            code.info().name(),
        )
        .unwrap();
        let imm_size = code.info().immediate_size() as usize;
        if imm_size > 0 {
            let imm_bytes = interp.bytecode.slice((pc + 1)..(pc + 1 + imm_size));
            writeln!(self.w, "{}  {}", imm_bytes, fmt_evm_stack(stack)).unwrap();
        } else {
            writeln!(self.w, "{}", fmt_evm_stack(stack)).unwrap();
        }
    }

    fn step_end(&mut self, _interp: &mut Interpreter, _context: &mut EvmContext<DB>) {
        // NOTE: annoying revm behavior: `interp.current_opcode()` now returns the next opcode.
    }
}

fn stackify_trace_for_fn(
    function: &Function,
    module_ctx: &ModuleCtx,
    backend: &EvmBackend,
    stackify_reach_depth: u8,
) -> String {
    let mut function = function.clone();
    let mut cfg = ControlFlowGraph::new();
    cfg.compute(&function);

    let mut splitter = StackifyEdgeSplitter::new();
    splitter.run(&mut function, &mut cfg);

    let value_aliases = backend.compute_stackify_value_aliases(&function, module_ctx);

    let mut liveness = Liveness::new();
    liveness.compute_with_value_normalizer(&function, &cfg, |v| {
        canonicalize_alias_value(&value_aliases, v)
    });
    let mut dom = DomTree::new();
    dom.compute(&cfg);

    let (_alloc, stackify) =
        StackifyBuilder::new(&function, &cfg, &dom, &liveness, stackify_reach_depth)
            .with_value_aliases(&value_aliases)
            .compute_with_trace();
    stackify
}

fn fmt_evm_stack(stack: &[U256]) -> String {
    const SHOW: usize = 6;

    fn fmt_u256(v: &U256) -> String {
        format!("{v:#x}")
    }

    let len = stack.len();
    if len == 0 {
        return "[]".to_string();
    }

    if len <= SHOW {
        let elems: Vec<String> = stack.iter().map(fmt_u256).collect();
        return format!("[{}]", elems.join(", "));
    }

    let head: Vec<String> = stack.iter().take(2).map(fmt_u256).collect();
    let tail: Vec<String> = stack.iter().skip(len - 3).map(fmt_u256).collect();
    format!("[{}, …, {}] (len={len})", head.join(", "), tail.join(", "))
}

struct FuncStats {
    name: String,
    mem: String,
    ir_blocks: usize,
    ir_insts: usize,
    vcode_ops: usize,
    vcode_fixups: usize,
    vcode_imm_bytes: usize,
}

fn parse_mem_plan_summary(mem_plan: &str) -> (Option<String>, HashMap<String, String>) {
    let mut header: Option<String> = None;
    let mut funcs: HashMap<String, String> = HashMap::new();

    for line in mem_plan.lines() {
        let Some(rest) = line.strip_prefix("evm mem plan: ") else {
            continue;
        };
        if rest.starts_with("dyn_base=") {
            header = Some(rest.to_string());
            continue;
        }

        let Some((name, details)) = rest.split_once(' ') else {
            continue;
        };
        funcs.insert(name.to_string(), details.to_string());
    }

    (header, funcs)
}

fn summarize_execution_result(res: &ExecutionResult) -> String {
    match res {
        ExecutionResult::Success {
            reason,
            gas_used,
            gas_refunded,
            logs,
            output,
        } => format!(
            "success reason={reason:?} gas_used={gas_used} gas_refunded={gas_refunded} logs={} output={}",
            logs.len(),
            summarize_output(output),
        ),
        ExecutionResult::Revert { gas_used, output } => {
            format!("revert gas_used={gas_used} output_len={}", output.len())
        }
        ExecutionResult::Halt { reason, gas_used } => {
            format!("halt reason={reason:?} gas_used={gas_used}")
        }
    }
}

fn execution_gas_used(res: &ExecutionResult) -> u64 {
    match res {
        ExecutionResult::Success { gas_used, .. }
        | ExecutionResult::Revert { gas_used, .. }
        | ExecutionResult::Halt { gas_used, .. } => *gas_used,
    }
}

fn initial_tx_gas_for_call(calldata: &[u8]) -> u64 {
    let mut env = Env::default();
    env.tx.clear();
    env.tx.transact_to = TransactTo::Call(Address::ZERO);
    env.tx.data = Bytes::copy_from_slice(calldata);

    revm::handler::mainnet::validate_initial_tx_gas::<OsakaSpec, revm::InMemoryDB>(&env)
        .unwrap_or_else(|err| {
            panic!("failed to compute initial tx gas for evm.case calldata: {err}")
        })
}

fn summarize_output(output: &Output) -> String {
    match output {
        Output::Call(bytes) => format!("call len={}", bytes.len()),
        Output::Create(bytes, addr) => match addr {
            Some(addr) => format!("create len={} addr={addr:?}", bytes.len()),
            None => format!("create len={} addr=<none>", bytes.len()),
        },
    }
}
