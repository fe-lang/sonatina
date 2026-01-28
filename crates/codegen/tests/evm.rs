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
use std::io::{Write, stderr};

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
    let stackify_reach_depth = stackify_reach_depth_for_fixture(fixture.path());
    let calldata = calldata_for_fixture(fixture.path());

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

    let mut stackify_out = Vec::new();
    let mut lowered_out = Vec::new();
    for fref in parsed.debug.func_order.iter() {
        let lowered = backend
            .lower_function(&parsed.module, *fref, &section_ctx)
            .unwrap();

        parsed.module.func_store.view(*fref, |function| {
            let stackify = stackify_trace_for_fn(function, stackify_reach_depth);
            let ctx = FuncWriteCtx::with_debug_provider(function, *fref, &parsed.debug);

            // Snapshot format:
            // - all stackify traces first
            // - then lowered functions/blocks
            // - then the runtime EVM trace at the bottom
            write!(&mut stackify_out, "// ").unwrap();
            FunctionSignature.write(&mut stackify_out, &ctx).unwrap();
            writeln!(&mut stackify_out).unwrap();
            write!(&mut stackify_out, "{}", fmt_stackify_trace(&stackify)).unwrap();
            writeln!(&mut stackify_out).unwrap();

            lowered.vcode.write(&mut lowered_out, &ctx).unwrap();
            writeln!(&mut lowered_out).unwrap();
        });
    }

    let mut v = Vec::new();
    if !mem_plan.is_empty() {
        writeln!(&mut v, "{mem_plan}").unwrap();
    }
    v.append(&mut stackify_out);
    v.append(&mut lowered_out);

    write!(&mut v, "\n\n---------------\n\n").unwrap();
    let opts = CompileOptions {
        fixup_policy: PushWidthPolicy::MinimalRelax,
        emit_symtab: false,
    };

    let artifact = compile_object(&parsed.module, &backend, "Contract", &opts).unwrap();
    for (name, section) in &artifact.sections {
        writeln!(&mut v, "// section {}", name.0.as_str()).unwrap();
        let hex = section.bytes.encode_hex::<String>();
        writeln!(&mut v, "0x{hex}\n").unwrap();
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
        .unwrap();

    if let Some(init) = init {
        let (create_res, create_trace, db, deployed) = deploy_on_evm(&init);
        writeln!(&mut v, "\n{create_res:?}").unwrap();
        writeln!(&mut v, "\n{create_trace}").unwrap();

        let (call_res, call_trace) = call_on_evm(db, deployed, &calldata);
        writeln!(&mut v, "\n{call_res:?}").unwrap();
        writeln!(&mut v, "\n{call_trace}").unwrap();
    } else {
        let (res, trace) = run_on_evm(&runtime, &calldata);
        writeln!(&mut v, "\n{res:?}").unwrap();
        writeln!(&mut v, "\n{trace}").unwrap();
    }

    snap_test!(String::from_utf8(v).unwrap(), fixture.path());
}

fn run_on_evm(bytecode: &[u8], calldata: &[u8]) -> (ExecutionResult, String) {
    let mut db = revm::InMemoryDB::default();
    let revm_bytecode = Bytecode::new_raw(Bytes::copy_from_slice(bytecode));
    let test_address = Address::repeat_byte(0x12);
    db.insert_account_info(
        test_address,
        AccountInfo {
            balance: U256::ZERO,
            nonce: 0,
            code_hash: revm_bytecode.hash_slow(),
            code: Some(revm_bytecode),
        },
    );

    let mut env = Env::default();
    env.tx.clear();
    env.tx.transact_to = TransactTo::Call(test_address);
    env.tx.data = Bytes::copy_from_slice(calldata);

    let (res, trace, _db) = run_revm_tx(db, env);
    (res, trace)
}

fn deploy_on_evm(init_code: &[u8]) -> (ExecutionResult, String, revm::InMemoryDB, Address) {
    let db = revm::InMemoryDB::default();
    let mut env = Env::default();
    env.tx.clear();
    env.tx.transact_to = TransactTo::Create;
    env.tx.data = Bytes::copy_from_slice(init_code);

    let (res, trace, db) = run_revm_tx(db, env);
    let deployed = match &res {
        ExecutionResult::Success {
            output: Output::Create(_, Some(addr)),
            ..
        } => *addr,
        _ => panic!("unexpected deployment result: {res:?}"),
    };
    (res, trace, db, deployed)
}

fn call_on_evm(db: revm::InMemoryDB, addr: Address, calldata: &[u8]) -> (ExecutionResult, String) {
    let mut env = Env::default();
    env.tx.clear();
    env.tx.transact_to = TransactTo::Call(addr);
    env.tx.data = Bytes::copy_from_slice(calldata);

    let (res, trace, _db) = run_revm_tx(db, env);
    (res, trace)
}

fn run_revm_tx(mut db: revm::InMemoryDB, env: Env) -> (ExecutionResult, String, revm::InMemoryDB) {
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

fn stackify_reach_depth_for_fixture(path: &str) -> u8 {
    let Some(stem) = std::path::Path::new(path)
        .file_stem()
        .and_then(|s| s.to_str())
    else {
        return 16;
    };

    let Some(pos) = stem.find("reach") else {
        return 16;
    };

    let digits: String = stem[pos + "reach".len()..]
        .chars()
        .take_while(|c| c.is_ascii_digit())
        .collect();
    if digits.is_empty() {
        return 16;
    }

    digits.parse().unwrap_or(16)
}

fn calldata_for_fixture(path: &str) -> Vec<u8> {
    let Some(stem) = std::path::Path::new(path)
        .file_stem()
        .and_then(|s| s.to_str())
    else {
        return vec![0, 0, 0, 11, 0, 0, 0, 22];
    };

    // TODO: better test case specification :)
    match stem {
        // `fe_enum.sntn` expects:
        // - 4 bytes: selector `1817627404` (big-endian u32)
        // - 32 bytes: ABI-encoded `u256=42` (big-endian 32 bytes)
        "fe_enum" => {
            let mut bytes = Vec::with_capacity(36);
            bytes.extend_from_slice(&1817627404u32.to_be_bytes());
            let mut arg = [0u8; 32];
            arg[31] = 42;
            bytes.extend_from_slice(&arg);
            bytes
        }
        _ => vec![0, 0, 0, 11, 0, 0, 0, 22],
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
