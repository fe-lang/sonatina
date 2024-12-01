use dir_test::{dir_test, Fixture};

use hex::ToHex;
use revm::{
    inspector_handle_register,
    interpreter::Interpreter,
    primitives::{
        AccountInfo, Address, Bytecode, Bytes, CancunSpec, Env, ExecutionResult, TransactTo, U256,
    },
    Context, EvmContext, Handler,
};

use sonatina_codegen::{
    critical_edge::CriticalEdgeSplitter,
    domtree::DomTree,
    isa::evm::{opcode::OpCode, EvmBackend},
    liveness::Liveness,
    machinst::{assemble::ObjectLayout, lower::Lower, vcode::VCode},
    stackalloc::SimpleAlloc,
};
use sonatina_ir::{
    cfg::ControlFlowGraph,
    ir_writer::{FuncWriteCtx, IrWrite},
    isa::evm::Evm,
    module::ModuleCtx,
    BlockId, Function,
};
use sonatina_parser::{parse_module, ParsedModule};
use sonatina_triple::{Architecture, OperatingSystem, Vendor};
use std::io::{stderr, Write};

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

    let backend = EvmBackend::new(Evm::new(sonatina_triple::TargetTriple {
        architecture: Architecture::Evm,
        vendor: Vendor::Ethereum,
        operating_system: OperatingSystem::Evm(sonatina_triple::EvmVersion::Cancun),
    }));

    let mut v = Vec::new();
    let funcs = parsed
        .debug
        .func_order
        .iter()
        .map(|fref| {
            let (vcode, block_order) = parsed.module.func_store.modify(*fref, |function| {
                let (vcode, block_order) = vcode_for_fn(function, &parsed.module.ctx, &backend);
                let ctx = FuncWriteCtx::with_debug_provider(function, *fref, &parsed.debug);
                vcode.write(&mut v, &ctx).unwrap();
                (vcode, block_order)
            });

            writeln!(v).unwrap();
            (*fref, vcode, block_order)
        })
        .collect();

    write!(&mut v, "\n\n---------------\n\n").unwrap();

    let mut layout = ObjectLayout::new(funcs, 0);
    let mut i = 0;
    while layout.resize(&backend, 0) {
        i += 1;
        println!("resize iteration {i}");
    }
    layout.print(&mut v, &parsed.module, &parsed.debug).unwrap();

    let mut bytecode = Vec::new();
    layout.emit(&backend, &mut bytecode);
    let hex = bytecode.encode_hex::<String>();

    writeln!(&mut v, "\n0x{hex}").unwrap();

    let (res, trace) = run_on_evm(&bytecode);

    writeln!(&mut v, "\n{trace}").unwrap();
    writeln!(&mut v, "\n{res:?}").unwrap();

    snap_test!(String::from_utf8(v).unwrap(), fixture.path());
}

fn run_on_evm(bytecode: &[u8]) -> (ExecutionResult, String) {
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
    env.tx.data = Bytes::copy_from_slice(&[0, 0, 0, 11, 0, 0, 0, 22]);

    let context = Context::new(
        EvmContext::new_with_env(db, Box::new(env)),
        // TracingInspector::new(TracingInspectorConfig::all());
        TestInspector::new(vec![]),
    );

    let mut evm = revm::Evm::new(context, Handler::mainnet::<CancunSpec>());
    evm = evm
        .modify()
        .append_handler_register(inspector_handle_register)
        .build();

    let res = evm.transact_commit();

    // let mut w = TraceWriter::new(&mut v).use_colors(ColorChoice::Never);
    // w.write_arena(evm.context.external.traces()).unwrap();

    match res.clone() {
        Ok(r) => (r, String::from_utf8(evm.context.external.w).unwrap()),
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
            writeln!(self.w, "{}", imm_bytes).unwrap();
        } else {
            writeln!(self.w, "{stack:?}").unwrap();
        }
    }

    fn step_end(&mut self, _interp: &mut Interpreter, _context: &mut EvmContext<DB>) {
        // NOTE: annoying revm behavior: `interp.current_opcode()` now returns the next opcode.
    }
}

fn vcode_for_fn(
    function: &mut Function,
    module: &ModuleCtx,
    backend: &EvmBackend,
) -> (VCode<OpCode>, Vec<BlockId>) {
    let mut cfg = ControlFlowGraph::new();
    cfg.compute(function);
    let mut splitter = CriticalEdgeSplitter::new();
    splitter.run(function, &mut cfg);

    let mut liveness = Liveness::new();
    liveness.compute(function, &cfg);
    let mut dom = DomTree::new();
    dom.compute(&cfg);
    let mut alloc = SimpleAlloc::for_function(function, &cfg, &dom, &liveness, 16);
    let lower = Lower::new(module, function);

    match lower.lower(backend, &mut alloc) {
        Ok(vcode) => (vcode, dom.rpo().to_owned()),
        Err(err) => panic!("{:?}", err),
    }
}
