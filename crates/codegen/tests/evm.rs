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
    isa::evm::{EvmBackend, PushWidthPolicy},
    liveness::Liveness,
    machinst::lower::{LowerBackend, SectionLoweringCtx},
    object::{CompileOptions, compile_object},
    stackalloc::StackifyAlloc,
};
use sonatina_ir::{
    Function,
    cfg::ControlFlowGraph,
    ir_writer::{FuncWriteCtx, FunctionSignature, IrWrite},
    isa::evm::Evm,
    object::{EmbedSymbol, ObjectName, SectionName},
};
use sonatina_parser::{ParsedModule, parse_module};
use sonatina_triple::{Architecture, OperatingSystem, Vendor};
use std::{
    collections::HashMap,
    io::{Write, stderr},
};

use evm_directives::{EvmCase, EvmExpect};

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

#[dir_test(
    dir: "$CARGO_MANIFEST_DIR/test_files/evm",
    glob: "*.sntn"
)]
fn test_evm(fixture: Fixture<&str>) {
    let parsed = parse_sona(fixture.content());
    let stackify_reach_depth = stackify_reach_depth_for_fixture(fixture.path(), &parsed);
    let emit_debug_trace = emit_debug_trace_for_fixture(fixture.path(), &parsed);
    let emit_mem_plan = emit_mem_plan_for_fixture(fixture.path(), &parsed);

    let cases = evm_directives::parse_evm_cases(&parsed.debug.module_comments)
        .unwrap_or_else(|e| panic!("{}: {e}", fixture.path()));

    let backend = EvmBackend::new(Evm::new(sonatina_triple::TargetTriple {
        architecture: Architecture::Evm,
        vendor: Vendor::Ethereum,
        operating_system: OperatingSystem::Evm(sonatina_triple::EvmVersion::Osaka),
    }))
    .with_stackify_reach_depth(stackify_reach_depth);

    let object_name = ObjectName::from("Contract");
    let section_name = SectionName::from("snapshot");
    let embed_symbols: Vec<EmbedSymbol> = Vec::new();
    let section_ctx = SectionLoweringCtx {
        object: &object_name,
        section: &section_name,
        embed_symbols: &embed_symbols,
    };

    backend.prepare_section(&parsed.module, &parsed.debug.func_order, &section_ctx);

    let mem_plan = backend.snapshot_mem_plan(&parsed.module, &parsed.debug.func_order);
    let mem_plan_detail = emit_mem_plan
        .then(|| backend.snapshot_mem_plan_detail(&parsed.module, &parsed.debug.func_order));
    let (mem_plan_header, mem_plan_funcs) = parse_mem_plan_summary(&mem_plan);

    let mut func_stats: Vec<FuncStats> = Vec::new();
    let mut stackify_out = Vec::new();
    let mut lowered_out = Vec::new();

    for fref in parsed.debug.func_order.iter() {
        let lowered = backend
            .lower_function(&parsed.module, *fref, &section_ctx)
            .unwrap();

        let vcode_ops = lowered.vcode.insts.len();
        let vcode_fixups = lowered.vcode.fixups.len();
        let vcode_imm_bytes = lowered.vcode.inst_imm_bytes.len();

        let name = parsed
            .module
            .ctx
            .func_sig(*fref, |sig| sig.name().to_string());

        let mem = mem_plan_funcs
            .get(&name)
            .cloned()
            .unwrap_or_else(|| format!("<missing mem plan entry for {name}>"));

        let (ir_blocks, ir_insts) = parsed.module.func_store.view(*fref, |function| {
            if emit_debug_trace {
                let stackify = stackify_trace_for_fn(function, stackify_reach_depth);
                let ctx = FuncWriteCtx::with_debug_provider(function, *fref, &parsed.debug);

                write!(&mut stackify_out, "// ").unwrap();
                FunctionSignature.write(&mut stackify_out, &ctx).unwrap();
                writeln!(&mut stackify_out).unwrap();
                write!(&mut stackify_out, "{}", fmt_stackify_trace(&stackify)).unwrap();
                writeln!(&mut stackify_out).unwrap();

                lowered.vcode.write(&mut lowered_out, &ctx).unwrap();
                writeln!(&mut lowered_out).unwrap();
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
    };

    let artifact = compile_object(&parsed.module, &backend, "Contract", &opts)
        .unwrap_or_else(|errs| panic!("{}: object compile failed: {errs:?}", fixture.path()));

    let mut out = Vec::new();
    if emit_mem_plan {
        writeln!(
            &mut out,
            "evm.config: stack_reach={stackify_reach_depth} emit_debug_trace={emit_debug_trace} emit_mem_plan=true"
        )
        .unwrap();
    } else {
        writeln!(
            &mut out,
            "evm.config: stack_reach={stackify_reach_depth} emit_debug_trace={emit_debug_trace}"
        )
        .unwrap();
    }
    writeln!(&mut out).unwrap();

    writeln!(&mut out, "object: {}", artifact.object.0.as_str()).unwrap();
    let mut total_bytes: usize = 0;
    for (name, section) in &artifact.sections {
        let size = section.bytes.len();
        total_bytes += size;
        writeln!(&mut out, "  section {}: {} bytes", name.0.as_str(), size).unwrap();
    }
    writeln!(&mut out, "  total: {total_bytes} bytes").unwrap();
    writeln!(&mut out).unwrap();

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

    if let Some(mem_plan_detail) = mem_plan_detail
        && !mem_plan_detail.is_empty()
    {
        writeln!(&mut out, "--------------- MEM PLAN ---------------\n").unwrap();
        writeln!(&mut out, "{mem_plan_detail}").unwrap();
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
        if emit_debug_trace {
            let (res, trace, harness) = EvmHarness::deploy_with_trace(&init);
            deploy_res_dbg = Some(format!("{res:?}"));
            deploy_trace = Some(trace);
            writeln!(&mut out, "evm:").unwrap();
            writeln!(&mut out, "  deploy: {}", summarize_execution_result(&res)).unwrap();
            match res {
                ExecutionResult::Success { .. } => {}
                _ => panic!("{}: deployment failed: {res:?}", fixture.path()),
            }
            harness
        } else {
            let (res, harness) = EvmHarness::deploy(&init);
            writeln!(&mut out, "evm:").unwrap();
            writeln!(&mut out, "  deploy: {}", summarize_execution_result(&res)).unwrap();
            match res {
                ExecutionResult::Success { .. } => {}
                _ => panic!("{}: deployment failed: {res:?}", fixture.path()),
            }
            harness
        }
    } else {
        writeln!(&mut out, "evm:").unwrap();
        EvmHarness::from_runtime(&runtime)
    };

    if cases.is_empty() {
        writeln!(&mut out, "  <no evm.case directives>").unwrap();
    }

    for (idx, case) in cases.iter().enumerate() {
        let (res, trace) = if emit_debug_trace && idx == 0 {
            let (res, trace) = harness.call_with_trace(&case.calldata);
            (res, Some(trace))
        } else {
            (harness.call(&case.calldata), None)
        };

        if emit_debug_trace && idx == 0 {
            first_call_res_dbg = Some(format!("{res:?}"));
        }
        if let Some(trace) = trace {
            first_call_trace = Some(trace);
        }

        assert_case(case, &res, fixture.path());
        writeln!(
            &mut out,
            "  case {}: calldata_len={} {}",
            case.name,
            case.calldata.len(),
            summarize_execution_result(&res)
        )
        .unwrap();
    }

    if emit_debug_trace {
        writeln!(&mut out, "\n\n--------------- DEBUG ---------------\n").unwrap();

        if !mem_plan.is_empty() {
            writeln!(&mut out, "{mem_plan}").unwrap();
        }

        out.append(&mut stackify_out);
        out.append(&mut lowered_out);

        writeln!(&mut out, "\n\n--------------- BYTECODE ---------------\n").unwrap();
        for (name, section) in &artifact.sections {
            writeln!(&mut out, "// section {}", name.0.as_str()).unwrap();
            let hex = section.bytes.encode_hex::<String>();
            writeln!(&mut out, "0x{hex}\n").unwrap();
        }

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

fn stackify_trace_for_fn(function: &Function, stackify_reach_depth: u8) -> String {
    let mut cfg = ControlFlowGraph::new();
    cfg.compute(function);

    let mut liveness = Liveness::new();
    liveness.compute(function, &cfg);
    let mut dom = DomTree::new();
    dom.compute(&cfg);
    let (_alloc, stackify) = StackifyAlloc::for_function_with_trace(
        function,
        &cfg,
        &dom,
        &liveness,
        stackify_reach_depth,
    );
    stackify
}

fn stackify_reach_depth_for_fixture(path: &str, parsed: &ParsedModule) -> u8 {
    match evm_directives::stack_reach_depth(&parsed.debug.module_comments) {
        Ok(depth) => depth,
        Err(e) => panic!("{path}: {e}"),
    }
}

fn emit_debug_trace_for_fixture(path: &str, parsed: &ParsedModule) -> bool {
    match evm_directives::emit_debug_trace(&parsed.debug.module_comments) {
        Ok(v) => v,
        Err(e) => panic!("{path}: {e}"),
    }
}

fn emit_mem_plan_for_fixture(path: &str, parsed: &ParsedModule) -> bool {
    match evm_directives::emit_mem_plan(&parsed.debug.module_comments) {
        Ok(v) => v,
        Err(e) => panic!("{path}: {e}"),
    }
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

fn summarize_output(output: &Output) -> String {
    match output {
        Output::Call(bytes) => format!("call len={}", bytes.len()),
        Output::Create(bytes, addr) => match addr {
            Some(addr) => format!("create len={} addr={addr:?}", bytes.len()),
            None => format!("create len={} addr=<none>", bytes.len()),
        },
    }
}
