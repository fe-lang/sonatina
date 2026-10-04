mod alias_execution;
mod evm_directives;

use dir_test::{Fixture, dir_test};

use hex::ToHex;
use revm::{
    Context, EvmContext, Handler, inspector_handle_register,
    interpreter::Interpreter,
    primitives::{
        AccountInfo, Address, Bytecode, Bytes, Env, ExecutionResult, HaltReason, OsakaSpec, Output,
        TransactTo, U256,
    },
};

use sonatina_codegen::{
    Compile,
    compile::{EvmCompiler, OptLevel},
    isa::evm::{
        EvmBackend, ImmediateMaterializationMode, LateCleanupProfile, PushWidthPolicy,
        opcode::OpCode,
    },
    machinst::{
        lower::{LoweredFunction, SectionCodeUnit, SectionWorkModule},
        vcode::{Label, VCodeFixup, section_code_unit_label_name},
    },
    object::{CompileOptions, compile_all_objects, compile_object},
    optim::{
        dead_func::{collect_object_roots, run_dead_func_elim},
        pipeline::Pipeline,
    },
    stackalloc::StackifySearchProfile,
    transform::aggregate::ObjectArgPromotion,
};
use sonatina_ir::{
    BlockId, U256 as IrU256,
    ir_writer::{FuncWriteCtx, FunctionSignature, IrWrite, ModuleWriter},
    isa::evm::Evm,
    module::{InlineHint, Module},
};
use sonatina_parser::{ParsedModule, parse_module};
use sonatina_triple::{Architecture, OperatingSystem, Vendor};
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module, verify_module_or_panic};
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

#[test]
fn object_alias_execution_matrix_at_all_optimization_levels() {
    for (body, cases, expected_calls, expect_promotion) in [
        (alias_execution::SOURCE, alias_execution::CASES, 3, false),
        (
            alias_execution::CAPTURE_SOURCE,
            &[
                ("captured_alias", 22),
                ("recovered_holder", 22),
                ("copied_holder", 22),
                ("picked_write", 22),
                ("picked_read", 33),
                ("wrapped", 22),
                ("picked_snapshot", 7),
                ("recovered_slot", 14),
                ("stored_into_result", 12),
                ("stashed_payload", 22),
                ("wrapped_pair", 8),
                ("published_result", 22),
                ("linked_result", 22),
                ("forwarded_result", 22),
                ("stack_leaked_result", 22),
                ("heap_leaked_result", 22),
                ("linked_then_filled", 22),
                ("returned_then_filled", 22),
                ("copied_then_cleared", 22),
                ("copied_arg_then_cleared", 22),
                ("copied_empty_then_filled", 22),
                ("copied_picked_then_cleared", 22),
                ("indexed_result", 22),
                ("borrowed_indexed_result", 22),
            ][..],
            0,
            false,
        ),
        (
            alias_execution::DISJOINT_SOURCE,
            &[("disjoint_only", 11)][..],
            1,
            true,
        ),
    ] {
        let mut source =
            format!("target = \"evm-ethereum-osaka\"\n{body}\nfunc public %entry() {{\nblock0:\n");
        let mut stores = String::new();
        for (index, &(name, _)) in cases.iter().enumerate() {
            let result = index * 2;
            let extended = result + 1;
            let offset = index * 32;
            source.push_str(&format!(
                "v{result}.i64 = call %{name};\nv{extended}.i256 = zext v{result} i256;\n"
            ));
            stores.push_str(&format!("mstore {offset}.i256 v{extended} i256;\n"));
        }
        // Store after the last call: the backend reserves low memory for
        // spills and the free and dynamic stack pointers.
        source.push_str(&stores);
        let size = cases.len() * 32;
        source.push_str(&format!("evm_return 0.i256 {size}.i256;\n}}\nobject @Contract {{ section runtime {{ entry %entry; }} }}\n"));
        let config = VerifierConfig::for_level(VerificationLevel::Full);
        for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2] {
            let module = parse_sona(&source).module;
            let report = verify_module(&module, &config);
            assert!(report.is_ok(), "{report}");
            let mut compiler = Compile::new(module, EvmCompiler::default()).with_opt_level(level);
            let module = compiler.optimize();
            let report = verify_module(module, &config);
            assert!(report.is_ok(), "{level:?}: {report}");
            let text = ModuleWriter::new(module).dump_string();
            assert_eq!(
                text.matches("call %read_after_write").count(),
                expected_calls,
                "{text}"
            );
            if expect_promotion && level != OptLevel::O0 {
                assert!(
                    text.find("obj.load").unwrap() < text.find("obj.store").unwrap(),
                    "{text}"
                );
            }
            let artifacts = compiler.compile().expect("alias matrix should compile");
            let runtime = artifacts[0]
                .sections
                .iter()
                .find(|(name, _)| name.0 == "runtime")
                .unwrap();
            let mut harness = EvmHarness::from_runtime(&runtime.1.bytes);
            let result = harness.call(&[]);
            let ExecutionResult::Success {
                output: Output::Call(actual),
                ..
            } = result
            else {
                panic!("{level:?}: {result:?}");
            };
            assert_eq!(actual.len(), size);
            for (bytes, &(name, expected)) in actual.as_chunks::<32>().0.iter().zip(cases) {
                assert_eq!(
                    *bytes,
                    IrU256::from(expected as u64).to_big_endian(),
                    "{level:?}: {name}"
                );
            }
        }
    }
}

#[test]
fn code_word_loads_preserve_memory_and_zero_pad_code_tails() {
    let source = r#"
target = "evm-ethereum-osaka"
global private const [i8; 3] $payload = [17, 34, 51];

func private %read(v0.i256) -> i256 {
block0:
    v1.i256 = evm_code_load v0;
    return v1;
}

func public %entry() {
block0:
    mstore 128.i256 99.i256 i256;
    v0.i256 = evm_calldata_load 0.i256;
    v1.i256 = sym_addr $payload;
    v2.i256 = add v0 v1;
    v3.i256 = call %read v2;
    v4.i256 = evm_code_load -1.i256;
    v5.i256 = mload 128.i256 i256;
    mstore 0.i256 v3 i256;
    mstore 32.i256 v5 i256;
    mstore 64.i256 v4 i256;
    evm_return 0.i256 96.i256;
}

object @Contract {
    section runtime {
        entry %entry;
        data $payload;
    }
}
"#;
    let config = VerifierConfig::for_level(VerificationLevel::Full);
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::Os] {
        let module = parse_sona(source).module;
        verify_module_or_panic(&module, &config);
        let mut compiler = Compile::new(module, EvmCompiler::default()).with_opt_level(level);
        verify_module_or_panic(compiler.optimize(), &config);
        let artifacts = compiler.compile().expect("code loads should compile");
        let runtime = artifacts[0]
            .sections
            .iter()
            .find(|(name, _)| name.0 == "runtime")
            .unwrap();
        let mut harness = EvmHarness::from_runtime(&runtime.1.bytes);
        for offset in [0, 1, 2, 3, 32] {
            let result = harness.call(&IrU256::from(offset as u64).to_big_endian());
            let ExecutionResult::Success {
                output: Output::Call(actual),
                ..
            } = result
            else {
                panic!("{level:?}, offset={offset}: {result:?}");
            };
            let mut expected = [0; 96];
            let tail = [17, 34, 51].get(offset..).unwrap_or_default();
            expected[..tail.len()].copy_from_slice(tail);
            expected[63] = 99;
            assert_eq!(actual.as_ref(), expected, "{level:?}, offset={offset}");
        }
    }
}

#[test]
fn callee_heap_returns_preserve_heap_and_borrowed_values_across_calls() {
    let source = r#"
target = "evm-ethereum-osaka"
func inline(never) private %allocate(v0.i256) -> i256 {
block0:
    v1.*i256 = evm_malloc 32.i256;
    mstore v1 v0 i256;
    v2.i256 = ptr_to_int v1 i256;
    return v2;
}
func inline(never) private %forward(v0.i256) -> i256 {
block0:
    v1.i256 = call %allocate v0;
    return v1;
}
func inline(never) private %choose(v0.*i256, v1.i256, v2.i1) -> i256 {
block0:
    br v2 block1 block2;
block1:
    v3.i256 = call %forward v1;
    return v3;
block2:
    v4.i256 = ptr_to_int v0 i256;
    return v4;
}
func inline(never) private %touch(v0.*i256) -> i256 {
block0:
    v1.i256 = mload v0 i256;
    return v1;
}
func inline(never) private %clobber(v0.i256) -> i256 {
block0:
    v1.*[i256; 8] = alloca [i256; 8];
    v2.*i256 = bitcast v1 *i256;
    mstore v2 v0 i256;
    v3.i256 = call %touch v2;
    v4.i256 = call %allocate v3;
    v5.i256 = mload v4 i256;
    return v5;
}
func public %entry() {
block0:
    v0.i256 = evm_calldata_load 0.i256;
    v1.i256 = evm_calldata_load 32.i256;
    v2.i1 = eq v1 1.i256;
    v3.*[i256; 4] = alloca [i256; 4];
    v4.*i256 = bitcast v3 *i256;
    mstore v4 17.i256 i256;
    v5.i256 = call %touch v4;
    v6.*i256 = alloca i256;
    v7.i256 = xor v0 255.i256;
    mstore v6 v7 i256;
    v8.i256 = call %choose v6 v0 v2;
    v9.*i256 = alloca i256;
    mstore v9 v8 i256;
    v10.i256 = call %clobber 99.i256;
    v11.i256 = call %touch v9;
    v12.i256 = mload v11 i256;
    v13.i256 = call %forward 101.i256;
    v14.i256 = mload v13 i256;
    v15.i256 = mload v11 i256;
    mstore 0.i256 v5 i256;
    mstore 32.i256 v10 i256;
    mstore 64.i256 v12 i256;
    mstore 96.i256 v14 i256;
    mstore 128.i256 v15 i256;
    evm_return 0.i256 160.i256;
}
object @Contract { section runtime { entry %entry; } }
"#;
    let config = VerifierConfig::for_level(VerificationLevel::Full);
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::Os] {
        let module = parse_sona(source).module;
        verify_module_or_panic(&module, &config);
        let mut compiler = Compile::new(module, EvmCompiler::default()).with_opt_level(level);
        verify_module_or_panic(compiler.optimize(), &config);
        let artifacts = compiler.compile().expect("heap-return program compiles");
        let runtime = artifacts[0]
            .sections
            .iter()
            .find(|(name, _)| name.0 == "runtime")
            .unwrap();
        let mut harness = EvmHarness::from_runtime(&runtime.1.bytes);
        for seed in [
            IrU256::zero(),
            IrU256::from(19),
            IrU256::one() << 255,
            IrU256::MAX,
        ] {
            for flag in [0u64, 1] {
                let mut input = seed.to_big_endian().to_vec();
                input.extend_from_slice(&IrU256::from(flag).to_big_endian());
                let result = harness.call(&input);
                let ExecutionResult::Success {
                    output: Output::Call(actual),
                    ..
                } = result
                else {
                    panic!("{level:?}, {seed}, {flag}: {result:?}");
                };
                let value = if flag == 1 {
                    seed
                } else {
                    seed ^ IrU256::from(255)
                };
                let expected = [
                    IrU256::from(17),
                    IrU256::from(99),
                    value,
                    IrU256::from(101),
                    value,
                ]
                .into_iter()
                .flat_map(|value| value.to_big_endian())
                .collect::<Vec<_>>();
                assert_eq!(actual.as_ref(), expected, "{level:?}, {seed}, {flag}");
            }
        }
    }
}

#[test]
fn terminal_payload_bases_preserve_overlaps_values_and_halts() {
    let bases = [
        IrU256::from(64),
        IrU256::from(257),
        IrU256::from(1024),
        IrU256::from(8192),
        IrU256::zero(),
        IrU256::MAX - IrU256::from(16),
    ];
    let offsets = [-4i64, 0, 4, 36, 32, 64, 96, 128];
    let patterns = [0x31u8, 0x42, 0x53, 0x64, 0x75, 0x86, 0x97, 0xa8];
    for terminal in ["evm_return", "evm_revert"] {
        let mut functions = String::new();
        let mut expected = Vec::new();
        for (idx, base) in bases.iter().enumerate() {
            let mut body = String::new();
            let mut output = vec![0u8; 160];
            for (store, (&offset, &pattern)) in offsets.iter().zip(&patterns).enumerate() {
                let address = if offset < 0 {
                    base.overflowing_sub(IrU256::from(offset.unsigned_abs())).0
                } else {
                    base.overflowing_add(IrU256::from(offset as u64)).0
                };
                // Three independently varying words plus the address exercise
                // the complete four-parameter budget, interspersed with literals.
                let byte = if [1, 3, 5].contains(&store) {
                    pattern.wrapping_add(idx as u8)
                } else {
                    pattern
                };
                let word = IrU256::from_big_endian(&[byte; 32]);
                body.push_str(&format!("evm_mstore {address}.i256 {word}.i256;\n"));
                for (at, value) in output.iter_mut().enumerate() {
                    if (offset..offset + 32).contains(&(at as i64)) {
                        *value = byte;
                    }
                }
            }
            body.push_str(&format!("{terminal} {base}.i256 160.i256;"));
            for function in [idx, idx + bases.len()] {
                functions.push_str(&format!(
                    "func inline(never) private %payload{function}() {{\nblock0:\n{body}\n}}\n"
                ));
            }
            expected.push(output);
        }
        // Duplicate each payload in separate functions so exact outlining first
        // creates helpers, and the base-sharing path must rewrite those helpers.
        expected.extend_from_within(..);
        let arms = expected.iter().enumerate().map(|(idx, _)| {
            let next = idx + 1;
            format!("block{idx}:\nv{next}.i1 = eq v0 {idx}.i256;\nbr v{next} block{} block{next};\n", idx + expected.len() + 1)
        }).collect::<String>();
        let dispatch = expected
            .iter()
            .enumerate()
            .map(|(idx, _)| {
                let block = idx + expected.len() + 1;
                format!("block{block}:\ncall %payload{idx};\nevm_revert 0.i256 0.i256;\n")
            })
            .collect::<String>();
        let source = format!(
            r#"target = "evm-ethereum-osaka"
{functions}
func public %entry() {{
block100:
v0.i256 = evm_calldata_load 0.i256;
jump block0;
{arms}
block{}:
evm_revert 0.i256 0.i256;
{dispatch}
}}
object @Contract {{ section runtime {{ entry %entry; }} }}
"#,
            expected.len()
        );
        for profile in [
            LateCleanupProfile::Off,
            LateCleanupProfile::Speed,
            LateCleanupProfile::Size,
        ] {
            let parsed = parse_sona(&source);
            let backend = EvmBackend::new(Evm::new(parsed.module.ctx.triple))
                .with_late_cleanup_profile(profile);
            let entry = *parsed.debug.func_order.last().unwrap();
            let prepared = backend
                .prepare_section(SectionWorkModule::from_roots(
                    &parsed.module,
                    entry,
                    &[],
                    &[],
                ))
                .unwrap();
            let mut lowered = prepared
                .funcs()
                .iter()
                .map(|&func| (func, backend.lower_function(&prepared, func).unwrap()))
                .collect();
            let units = backend.post_lower_section(&prepared, &mut lowered).unwrap();
            let shared_payload = units.iter().any(|unit| {
                unit.block_order.iter().any(|&block| {
                    let ops = unit
                        .vcode
                        .block_insns(block)
                        .map(|inst| unit.vcode.insts[inst] as u8)
                        .collect::<Vec<_>>();
                    ops.len() >= 2
                        && ops[ops.len() - 2] == OpCode::SWAP1 as u8
                        && ops.contains(&(OpCode::MSTORE as u8))
                })
            });
            assert_eq!(
                shared_payload,
                profile == LateCleanupProfile::Size
                    || profile == LateCleanupProfile::Speed && terminal == "evm_revert",
                "sharing must actually fire under the intended {profile:?} {terminal} policy"
            );
            let artifact = compile_object(
                &parsed.module,
                &backend,
                "Contract",
                &CompileOptions::default(),
            )
            .unwrap();
            let runtime = artifact
                .sections
                .iter()
                .find(|(name, _)| name.0 == "runtime")
                .unwrap();
            let mut harness = EvmHarness::from_runtime(&runtime.1.bytes);
            for (idx, output) in expected.iter().enumerate() {
                let result = harness.call(&IrU256::from(idx).to_big_endian());
                if idx % bases.len() >= 4 {
                    assert!(
                        matches!(result, ExecutionResult::Halt { .. }),
                        "{profile:?} {terminal} case {idx}: {result:?}"
                    );
                    continue;
                }
                let actual = match result {
                    ExecutionResult::Success {
                        output: Output::Call(actual),
                        ..
                    } if terminal == "evm_return" => actual,
                    ExecutionResult::Revert { output: actual, .. } if terminal == "evm_revert" => {
                        actual
                    }
                    _ => panic!("{profile:?} {terminal} case {idx}: {result:?}"),
                };
                assert_eq!(actual.as_ref(), output, "{profile:?} {terminal} case {idx}");
            }
        }
    }
}

#[test]
fn machine_snapshot_copies_preserve_dynamic_aliases_and_wrapping_failures() {
    for (words, interleaved) in [(2, false), (6, false), (18, false), (6, true)] {
        let offsets: Vec<_> = (0..words * 32).step_by(32).collect();
        let mut body = String::new();
        let mut stores = String::new();
        for (word, offset) in offsets.iter().enumerate() {
            let addr = word * 3 + 3;
            let value = addr + 1;
            let dest = addr + 2;
            body.push_str(&format!(
                "v{addr}.i256 = add v2 {offset}.i256;\nv{value}.i256 = evm_mload v{addr};\n"
            ));
            let store =
                format!("v{dest}.i256 = add v1 {offset}.i256;\nevm_mstore v{dest} v{value};\n");
            if interleaved {
                body.push_str(&store);
            } else {
                stores.push_str(&store);
            }
        }
        body.push_str(&stores);
        let source = format!(
            r#"target = "evm-ethereum-osaka"
func public %entry() {{
block0:
    evm_calldata_copy 256.i256 64.i256 2048.i256;
    v0.i256 = evm_calldata_load 0.i256;
    v1.i256 = evm_calldata_load 32.i256;
    v2.i256 = sub v0 64.i256;
    {body}
    evm_return 256.i256 2048.i256;
}}
object @Contract {{ section runtime {{ entry %entry; }} }}
"#
        );
        for profile in [
            LateCleanupProfile::Off,
            LateCleanupProfile::Speed,
            LateCleanupProfile::Size,
        ] {
            let parsed = parse_sona(&source);
            let backend = EvmBackend::new(Evm::new(parsed.module.ctx.triple))
                .with_late_cleanup_profile(profile);
            let artifact = compile_object(
                &parsed.module,
                &backend,
                "Contract",
                &CompileOptions::default(),
            )
            .expect("dynamic word copies should compile");
            let runtime = artifact
                .sections
                .iter()
                .find(|(name, _)| name.0 == "runtime")
                .unwrap();
            let mut harness = EvmHarness::from_runtime(&runtime.1.bytes);
            for (src, dst) in [
                (256, 1536),
                (1024, 256),
                (512, 512),
                (512, 513),
                (513, 512),
                (512, 544),
                (544, 512),
            ] {
                for seed in [0u8, 1, 127, 255] {
                    let data: Vec<_> = (0..2048)
                        .map(|i| seed.wrapping_add((i * 37) as u8))
                        .collect();
                    let mut expected = data.clone();
                    let (src, dst) = (src - 256, dst - 256);
                    if interleaved {
                        for &offset in &offsets {
                            let loaded = expected[src + offset..src + offset + 32].to_vec();
                            expected[dst + offset..dst + offset + 32].copy_from_slice(&loaded);
                        }
                    } else {
                        let loaded = expected[src..src + words * 32].to_vec();
                        expected[dst..dst + words * 32].copy_from_slice(&loaded);
                    }
                    let mut calldata = IrU256::from(src + 256 + 64).to_big_endian().to_vec();
                    calldata.extend_from_slice(&IrU256::from(dst + 256).to_big_endian());
                    calldata.extend_from_slice(&data);
                    let result = harness.call(&calldata);
                    let ExecutionResult::Success {
                        output: Output::Call(actual),
                        ..
                    } = result
                    else {
                        panic!(
                            "src={src}, dst={dst}, words={words}, interleaved={interleaved}, profile={profile:?}: {result:?}"
                        );
                    };
                    assert_eq!(
                        actual.as_ref(),
                        expected,
                        "src={src}, dst={dst}, words={words}, interleaved={interleaved}, profile={profile:?}"
                    );
                }
            }
            for (src, dst) in [
                (IrU256::zero(), IrU256::from(512)),
                (IrU256::from(63), IrU256::from(512)),
                (IrU256::from(576), IrU256::MAX - IrU256::from(31)),
                (IrU256::from(576), IrU256::one() << 255),
            ] {
                let calldata = [src.to_big_endian(), dst.to_big_endian()].concat();
                assert!(
                    matches!(harness.call(&calldata), ExecutionResult::Halt { .. }),
                    "wrapping or unpayable memory range must halt"
                );
            }
        }
    }
}

#[test]
fn machine_copies_preserve_words_guards_and_overlap_semantics() {
    for (src, dst, words, interleaved) in [
        (256, 1024, 18, false),
        (257, 1025, 6, true),
        (256, 288, 6, true),
        (288, 256, 6, false),
    ] {
        let len = words * 32;
        let offsets: Vec<_> = (0..len).step_by(32).collect();
        let mut body = String::new();
        let mut stores = String::new();
        for (word, offset) in offsets.iter().enumerate() {
            let source = src + offset;
            let dest = dst + offset;
            body.push_str(&format!("v{word}.i256 = evm_mload {source}.i256;\n"));
            let store = format!("evm_mstore {dest}.i256 v{word};\n");
            if interleaved {
                body.push_str(&store);
            } else {
                stores.push_str(&store);
            }
        }
        body.push_str(&stores);
        let before = dst - 32;
        let after = dst + len;
        let return_len = len + 64;
        let source = format!(
            r#"target = "evm-ethereum-osaka"
func public %entry() {{
block0:
    evm_calldata_copy {src}.i256 0.i256 {len}.i256;
    evm_mstore {before}.i256 123.i256;
    evm_mstore {after}.i256 456.i256;
    {body}
    evm_return {before}.i256 {return_len}.i256;
}}
object @Contract {{ section runtime {{ entry %entry; }} }}
"#
        );
        for profile in [
            LateCleanupProfile::Off,
            LateCleanupProfile::Speed,
            LateCleanupProfile::Size,
        ] {
            let parsed = parse_sona(&source);
            let backend = EvmBackend::new(Evm::new(parsed.module.ctx.triple))
                .with_late_cleanup_profile(profile);
            let artifact = compile_object(
                &parsed.module,
                &backend,
                "Contract",
                &CompileOptions::default(),
            )
            .expect("word copies should compile");
            let runtime = artifact
                .sections
                .iter()
                .find(|(name, _)| name.0 == "runtime")
                .unwrap();
            let mut harness = EvmHarness::from_runtime(&runtime.1.bytes);
            for seed in [0u8, 1, 127, 255] {
                let calldata: Vec<_> = (0..len)
                    .map(|i| seed.wrapping_add((i * 37) as u8))
                    .collect();
                let mut memory = vec![0; (src + len).max(after + 32)];
                memory[src..src + len].copy_from_slice(&calldata);
                memory[before..dst].copy_from_slice(&IrU256::from(123).to_big_endian());
                memory[after..after + 32].copy_from_slice(&IrU256::from(456).to_big_endian());
                if interleaved {
                    for offset in &offsets {
                        let loaded = memory[src + offset..src + offset + 32].to_vec();
                        memory[dst + offset..dst + offset + 32].copy_from_slice(&loaded);
                    }
                } else {
                    let loaded = memory[src..src + len].to_vec();
                    memory[dst..after].copy_from_slice(&loaded);
                }
                let result = harness.call(&calldata);
                let ExecutionResult::Success {
                    output: Output::Call(actual),
                    ..
                } = result
                else {
                    panic!("src={src}, dst={dst}, words={words}, profile={profile:?}: {result:?}");
                };
                assert_eq!(
                    actual.as_ref(),
                    &memory[before..after + 32],
                    "src={src}, dst={dst}, words={words}, profile={profile:?}"
                );
            }
        }
    }
}

#[test]
fn private_return_lanes_preserve_values_storage_and_reverts() {
    let source = r#"
target = "evm-ethereum-osaka"
func private %mixed(v0.i256, v1.i256) -> (i256, i256, i256, i256) {
block0:
    evm_sstore 0.i256 v0;
    v2.i256 = xor v0 v1;
    v3.i256 = add v0 v1;
    return (v1, v2, v3, v0);
}
func private %effects_only(v0.i256, v1.i256) -> i256 {
block0:
    v2.i1 = is_zero v1;
    br v2 block1 block2;
block1:
    evm_mstore 0.i256 v0;
    evm_revert 0.i256 32.i256;
block2:
    evm_sstore 1.i256 v1;
    return v0;
}
func public %entry() {
block0:
    v0.i256 = evm_calldata_load 0.i256;
    v1.i256 = evm_calldata_load 32.i256;
    (v2.i256, v3.i256, v4.i256, v5.i256) = call %mixed v0 v1;
    v6.i256 = call %effects_only v0 v1;
    v7.i256 = evm_sload 0.i256;
    v8.i256 = evm_sload 1.i256;
    evm_mstore 0.i256 v2;
    evm_mstore 32.i256 v3;
    evm_mstore 64.i256 v5;
    evm_mstore 96.i256 v7;
    evm_mstore 128.i256 v8;
    evm_return 0.i256 160.i256;
}
object @Contract { section runtime { entry %entry; } }
"#;
    let pairs = [
        (IrU256::zero(), IrU256::one()),
        (IrU256::one(), IrU256::zero()),
        (IrU256::MAX, IrU256::one()),
        (IrU256::one() << 255, IrU256::MAX),
        (IrU256::MAX, IrU256::MAX),
        (IrU256::zero(), IrU256::zero()),
        (IrU256::MAX, IrU256::zero()),
        (IrU256::one(), IrU256::one() << 128),
    ];
    let config = VerifierConfig::for_level(VerificationLevel::Full);
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::Os] {
        let module = parse_sona(source).module;
        verify_module_or_panic(&module, &config);
        for func in module.funcs() {
            if module.ctx.func_sig(func, |sig| sig.linkage().is_private()) {
                module.ctx.set_inline_hint(func, InlineHint::Never);
            }
        }
        let mut compiler = Compile::new(module, EvmCompiler::default()).with_opt_level(level);
        verify_module_or_panic(compiler.optimize(), &config);
        let artifacts = compiler
            .compile()
            .expect("private return lanes should compile");
        let runtime = artifacts[0]
            .sections
            .iter()
            .find(|(name, _)| name.0 == "runtime")
            .unwrap();
        let mut harness = EvmHarness::from_runtime(&runtime.1.bytes);
        for (lhs, rhs) in pairs {
            let calldata = [lhs.to_big_endian(), rhs.to_big_endian()].concat();
            let result = harness.call(&calldata);
            if rhs.is_zero() {
                let ExecutionResult::Revert { output, .. } = result else {
                    panic!("{level:?}, lhs={lhs}, rhs={rhs}: {result:?}");
                };
                assert_eq!(output.as_ref(), lhs.to_big_endian());
            } else {
                let ExecutionResult::Success {
                    output: Output::Call(output),
                    ..
                } = result
                else {
                    panic!("{level:?}, lhs={lhs}, rhs={rhs}: {result:?}");
                };
                let expected = [rhs, lhs ^ rhs, lhs, lhs, rhs]
                    .into_iter()
                    .flat_map(|word| word.to_big_endian())
                    .collect::<Vec<_>>();
                assert_eq!(output.as_ref(), expected, "{level:?}, lhs={lhs}, rhs={rhs}");
            }
        }
    }
}

#[test]
fn guarded_subtraction_preserves_values_and_overflow_at_all_optimization_levels() {
    let source = r#"
target = "evm-ethereum-osaka"
func private %subtract(v0.i256, v1.i256) -> (i256, i1) {
block0:
    v2.i1 = lt v0 v1;
    br v2 block1 block2;
block1:
    (v3.i256, v4.i1) = usubo v0 v1;
    return (v3, v4);
block2:
    (v5.i256, v6.i1) = usubo v0 v1;
    return (v5, v6);
}
func public %entry() {
block0:
    v0.i256 = evm_calldata_load 0.i256;
    v1.i256 = evm_calldata_load 32.i256;
    (v2.i256, v3.i1) = call %subtract v0 v1;
    v4.i256 = zext v3 i256;
    evm_mstore 0.i256 v2;
    evm_mstore 32.i256 v4;
    evm_return 0.i256 64.i256;
}
object @Contract { section runtime { entry %entry; } }
"#;
    let words = [
        IrU256::zero(),
        IrU256::one(),
        IrU256::from(255),
        IrU256::one() << 128,
        (IrU256::one() << 255) - IrU256::one(),
        IrU256::one() << 255,
        IrU256::MAX - IrU256::one(),
        IrU256::MAX,
    ];
    let config = VerifierConfig::for_level(VerificationLevel::Full);
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::Os] {
        let module = parse_sona(source).module;
        verify_module_or_panic(&module, &config);
        let subtract = module
            .funcs()
            .into_iter()
            .find(|&func| module.ctx.func_sig(func, |sig| sig.name() == "subtract"))
            .unwrap();
        module.ctx.set_inline_hint(subtract, InlineHint::Never);
        let mut compiler = Compile::new(module, EvmCompiler::default()).with_opt_level(level);
        verify_module_or_panic(compiler.optimize(), &config);
        let artifacts = compiler
            .compile()
            .expect("guarded subtraction should compile");
        let runtime = artifacts[0]
            .sections
            .iter()
            .find(|(name, _)| name.0 == "runtime")
            .unwrap();
        let mut harness = EvmHarness::from_runtime(&runtime.1.bytes);
        for lhs in words {
            for rhs in words {
                let calldata = [lhs.to_big_endian(), rhs.to_big_endian()].concat();
                let (difference, overflow) = lhs.overflowing_sub(rhs);
                let expected = [
                    difference.to_big_endian(),
                    IrU256::from(u8::from(overflow)).to_big_endian(),
                ]
                .concat();
                let result = harness.call(&calldata);
                let ExecutionResult::Success {
                    output: Output::Call(actual),
                    ..
                } = result
                else {
                    panic!("{level:?}, lhs={lhs}, rhs={rhs}: {result:?}");
                };
                assert_eq!(actual.as_ref(), expected, "{level:?}, lhs={lhs}, rhs={rhs}");
            }
        }
    }
}

#[test]
fn empty_mcopy_preserves_operand_effects_without_touching_memory() {
    let source = r#"
target = "evm-ethereum-osaka"
func private %address(v0.i256) -> i256 {
block0:
    evm_sstore 7.i256 99.i256;
    return v0;
}
func public %entry() {
block0:
    v0.i256 = evm_calldata_load 0.i256;
    v1.i256 = evm_calldata_load 32.i256;
    v2.i256 = call %address v0;
    evm_mcopy v2 v1 0.i256;
    v3.i256 = evm_sload 7.i256;
    evm_mstore 0.i256 v3;
    evm_return 0.i256 32.i256;
}
object @Contract { section runtime { entry %entry; } }
"#;
    let config = VerifierConfig::for_level(VerificationLevel::Full);
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::Os] {
        let module = parse_sona(source).module;
        verify_module_or_panic(&module, &config);
        let mut compiler = Compile::new(module, EvmCompiler::default()).with_opt_level(level);
        verify_module_or_panic(compiler.optimize(), &config);
        let artifacts = compiler.compile().expect("empty copies should compile");
        let runtime = artifacts[0]
            .sections
            .iter()
            .find(|(name, _)| name.0 == "runtime")
            .unwrap();
        for dest in [IrU256::zero(), IrU256::one() << 255, IrU256::MAX] {
            for addr in [IrU256::zero(), IrU256::one() << 255, IrU256::MAX] {
                // Each call starts with fresh storage, so a prior case cannot
                // hide removal of the operand-producing call's storage write.
                let mut harness = EvmHarness::from_runtime(&runtime.1.bytes);
                let calldata = [dest.to_big_endian(), addr.to_big_endian()].concat();
                let result = harness.call(&calldata);
                let ExecutionResult::Success {
                    output: Output::Call(actual),
                    ..
                } = result
                else {
                    panic!("{level:?}, dest={dest}, addr={addr}: {result:?}");
                };
                assert_eq!(actual.as_ref(), IrU256::from(99).to_big_endian());
            }
        }
    }
}

#[test]
fn terminal_word_buffers_preserve_return_and_revert_payloads() {
    let source = r#"
target = "evm-ethereum-osaka"

func private %read(v0.*i256) -> i256 {
block0:
    v1.i256 = mload v0 i256;
    return v1;
}

func public %entry() {
block0:
    v0.i256 = evm_calldata_load 0.i256;
    v1.i256 = evm_calldata_load 32.i256;
    mstore 0.i256 v1 i256;
    v2.*i256 = alloca i256;
    mstore v2 v0 i256;
    v3.i256 = call %read v2;
    v4.*i8 = evm_malloc 32.i256;
    v5.i256 = ptr_to_int v4 i256;
    v6.i256 = mload 0.i256 i256;
    v7.i256 = xor v6 v3;
    v8.i1 = eq v0 0.i256;
    br v8 block1 block2;
block1:
    mstore v5 v7 i256;
    evm_return v5 32.i256;
block2:
    mstore v5 v7 i256;
    evm_revert v5 32.i256;
}

object @Contract { section runtime { entry %entry; } }
"#;
    let config = VerifierConfig::for_level(VerificationLevel::Full);
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::Os] {
        let module = parse_sona(source).module;
        verify_module_or_panic(&module, &config);
        let read = module
            .funcs()
            .into_iter()
            .find(|&func| module.ctx.func_sig(func, |sig| sig.name() == "read"))
            .unwrap();
        module.ctx.set_inline_hint(read, InlineHint::Never);
        let compiler = Compile::new(module, EvmCompiler::default()).with_opt_level(level);
        let artifacts = compiler.compile().expect("terminal buffers should compile");
        let runtime = artifacts[0]
            .sections
            .iter()
            .find(|(name, _)| name.0 == "runtime")
            .unwrap();
        let mut harness = EvmHarness::from_runtime(&runtime.1.bytes);
        for mode in [0u64, 1] {
            for word in [
                IrU256::zero(),
                IrU256::one(),
                IrU256::MAX,
                IrU256::one() << 255,
            ] {
                let mut calldata = IrU256::from(mode).to_big_endian().to_vec();
                calldata.extend_from_slice(&word.to_big_endian());
                let result = harness.call(&calldata);
                let actual = match result {
                    ExecutionResult::Success {
                        output: Output::Call(bytes),
                        ..
                    } if mode == 0 => bytes,
                    ExecutionResult::Revert { output, .. } if mode == 1 => output,
                    _ => panic!("{level:?}, mode={mode}: {result:?}"),
                };
                assert_eq!(actual.as_ref(), (word ^ IrU256::from(mode)).to_big_endian());
            }
        }
    }
}

#[test]
fn nested_const_indices_execute_at_all_optimization_levels() {
    let mut source = include_str!("../test_files/const_data/nested_indices.sntn").to_string();
    source.push_str("\nfunc public %entry() {\nblock0:\nv0.i256 = evm_calldata_load 0.i256;\n");
    let cases = [
        ("static_index", false, [11, 11]),
        ("dynamic_index", true, [42, 11]),
        ("affine_index", true, [42, 11]),
        ("reordered_blocks", true, [42, 11]),
        ("nested_rows", true, [162, 161]),
        ("init_pair", true, [99, 42]),
        ("static_init_pair", false, [99, 99]),
        ("load_escaped_index", true, [42, 11]),
    ];
    for (index, (name, takes_index, _)) in cases.iter().enumerate() {
        let result = index + 1;
        let offset = index * 32;
        let args = if *takes_index { " v0" } else { "" };
        source.push_str(&format!(
            "v{result}.i256 = call %{name}{args};\nmstore {offset}.i256 v{result} i256;\n"
        ));
    }
    let size = cases.len() * 32;
    source.push_str(&format!("evm_return 0.i256 {size}.i256;\n}}\nobject @Contract {{ section runtime {{ entry %entry; }} }}\n"));
    let config = VerifierConfig::for_level(VerificationLevel::Full);
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2] {
        let module = parse_sona(&source).module;
        verify_module_or_panic(&module, &config);
        let mut compiler = Compile::new(module, EvmCompiler::default()).with_opt_level(level);
        verify_module_or_panic(compiler.optimize(), &config);
        let artifacts = compiler.compile().expect("nested indices should compile");
        let runtime = artifacts[0]
            .sections
            .iter()
            .find(|(name, _)| name.0 == "runtime")
            .unwrap();
        let mut harness = EvmHarness::from_runtime(&runtime.1.bytes);
        for input in [0, 1] {
            let result = harness.call(&IrU256::from(input).to_big_endian());
            let ExecutionResult::Success {
                output: Output::Call(actual),
                ..
            } = result
            else {
                panic!("{level:?}, input={input}: {result:?}");
            };
            assert_eq!(actual.len(), size);
            for (bytes, (name, _, expected)) in actual.as_chunks::<32>().0.iter().zip(&cases) {
                assert_eq!(
                    *bytes,
                    IrU256::from(expected[input] as u64).to_big_endian(),
                    "{level:?}, input={input}, {name}"
                );
            }
        }
    }
}

#[test]
fn evm_exp_wraps_to_declared_width() {
    for bits in [1, 8, 16, 32, 64, 128, 256] {
        let operation = if bits == 256 {
            "v5.i256 = evm_exp v0 v1;".to_string()
        } else {
            format!(
                "v2.i{bits} = trunc v0 i{bits};
                 v3.i{bits} = trunc v1 i{bits};
                 v4.i{bits} = evm_exp v2 v3;
                 v5.i256 = zext v4 i256;"
            )
        };
        let source = format!(
            r#"
target = "evm-ethereum-osaka"

func public %entry() {{
    block0:
        v0.i256 = evm_calldata_load 0.i256;
        v1.i256 = evm_calldata_load 32.i256;
        {operation}
        mstore 0.i256 v5 i256;
        evm_return 0.i256 32.i256;
}}

object @Contract {{
    section runtime {{
        entry %entry;
    }}
}}
"#
        );
        let mask = IrU256::MAX >> (256 - bits);
        let cases = [
            (IrU256::zero(), IrU256::zero()),
            (2.into(), bits.into()),
            (3.into(), 5.into()),
            (200.into(), IrU256::one()),
            (mask, mask),
            (mask, mask - IrU256::one()),
            (2.into(), mask),
        ];
        for optimized in [false, true] {
            let mut parsed = parse_sona(&source);
            if optimized {
                Pipeline::speed().run(&mut parsed.module);
            }
            let backend = EvmBackend::new(Evm::new(parsed.module.ctx.triple))
                .with_late_cleanup_profile(if optimized {
                    LateCleanupProfile::Speed
                } else {
                    LateCleanupProfile::Off
                });
            let artifact = compile_object(
                &parsed.module,
                &backend,
                "Contract",
                &CompileOptions::default(),
            )
            .expect("exponentiation should compile");
            let runtime = artifact
                .sections
                .iter()
                .find(|(name, _)| name.0 == "runtime")
                .expect("missing runtime section");
            let mut harness = EvmHarness::from_runtime(&runtime.1.bytes);
            for (base, exponent) in cases {
                let calldata = [base.to_big_endian(), exponent.to_big_endian()].concat();
                let expected = (base & mask).overflowing_pow(exponent & mask).0 & mask;
                let result = harness.call(&calldata);
                let ExecutionResult::Success {
                    output: Output::Call(actual),
                    ..
                } = result
                else {
                    panic!("i{bits}, optimized={optimized}: {result:?}");
                };
                assert_eq!(
                    actual.as_ref(),
                    expected.to_big_endian(),
                    "i{bits}, optimized={optimized}, base={base}, exponent={exponent}"
                );
            }
        }
    }
}

fn run_opt_pipeline(module: &mut Module, opt_pipeline: EvmOptPipeline) {
    match opt_pipeline {
        EvmOptPipeline::O0 => {}
        EvmOptPipeline::O1 => Pipeline::speed().run(module),
        EvmOptPipeline::Os => Pipeline::size().run(module),
        EvmOptPipeline::O2 => Pipeline::speed().run(module),
    }
}

fn prune_unreachable_funcs_for_optimized_evm_snapshots(
    module: &mut Module,
    opt_pipeline: EvmOptPipeline,
) {
    if opt_pipeline != EvmOptPipeline::O0 {
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
    let verifier_cfg = VerifierConfig::for_level(VerificationLevel::Full);
    verify_module_or_panic(&parsed.module, &verifier_cfg);
    let cfg = evm_directives::parse_evm_config(&parsed.debug.module_comments)
        .unwrap_or_else(|e| panic!("{}: {e}", fixture.path()));
    let stackify_reach_depth = cfg.stack_reach.unwrap_or(16);
    let emit_vcode = cfg.vcode.unwrap_or(false);
    let emit_bytecode_hex = cfg.bytecode_hex.unwrap_or(false);
    let emit_stackify_trace = cfg.stackify_trace.unwrap_or(false);
    let emit_evm_trace = cfg.evm_trace.unwrap_or(false);
    let emit_observability = cfg.emit_observability.unwrap_or(false);
    let emit_mem_plan_detail = cfg.mem_plan_detail.unwrap_or(false);
    let opt_pipeline = cfg.opt.unwrap_or(EvmOptPipeline::O0);

    let cases = evm_directives::parse_evm_cases(&parsed.debug.module_comments)
        .unwrap_or_else(|e| panic!("{}: {e}", fixture.path()));

    run_opt_pipeline(&mut parsed.module, opt_pipeline);
    prune_unreachable_funcs_for_optimized_evm_snapshots(&mut parsed.module, opt_pipeline);
    verify_module_or_panic(&parsed.module, &verifier_cfg);
    let opt_ir_snapshot = (opt_pipeline != EvmOptPipeline::O0).then(|| {
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

    let stackify_search_profile = match opt_pipeline {
        EvmOptPipeline::O0 => StackifySearchProfile::Fast,
        EvmOptPipeline::O1 => StackifySearchProfile::GreedyWide,
        EvmOptPipeline::Os | EvmOptPipeline::O2 => StackifySearchProfile::Exact,
    };

    let backend = EvmBackend::new(Evm::new(sonatina_triple::TargetTriple {
        architecture: Architecture::Evm,
        vendor: Vendor::Ethereum,
        operating_system: OperatingSystem::Evm(sonatina_triple::EvmVersion::Osaka),
    }))
    .with_stackify_reach_depth(stackify_reach_depth)
    .with_late_cleanup_profile(match opt_pipeline {
        EvmOptPipeline::O0 => LateCleanupProfile::Off,
        EvmOptPipeline::O1 => LateCleanupProfile::Speed,
        EvmOptPipeline::Os => LateCleanupProfile::Size,
        EvmOptPipeline::O2 => LateCleanupProfile::Speed,
    })
    .with_stackify_search_profile(stackify_search_profile)
    .with_stackify_trace_capture(emit_stackify_trace)
    .with_immediate_materialization_mode(match opt_pipeline {
        EvmOptPipeline::Os => ImmediateMaterializationMode::Size,
        EvmOptPipeline::O2 => ImmediateMaterializationMode::Balanced,
        EvmOptPipeline::O0 | EvmOptPipeline::O1 => ImmediateMaterializationMode::Gas,
    });

    let prepared = backend
        .prepare_section(SectionWorkModule::from_roots(
            &parsed.module,
            func_order[0],
            &func_order[1..],
            &[],
        ))
        .unwrap();

    let mem_plan = if emit_mem_plan_detail {
        backend.snapshot_mem_plan_detail(&prepared)
    } else {
        backend.snapshot_mem_plan(&prepared)
    };
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
                    let stackify = prepared
                        .stackify_trace(*fref)
                        .unwrap_or_else(|| panic!("missing stackify trace for {name}"));
                    write!(&mut stackify_out, "// ").unwrap();
                    FunctionSignature.write(&mut stackify_out, &ctx).unwrap();
                    writeln!(&mut stackify_out).unwrap();
                    write!(&mut stackify_out, "{}", fmt_stackify_trace(stackify)).unwrap();
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
    let opt_pipeline_suffix = if opt_pipeline == EvmOptPipeline::O0 {
        String::new()
    } else {
        format!(" opt={}", opt_pipeline.as_label())
    };
    let mem_plan_detail_suffix = if emit_mem_plan_detail {
        " mem_plan_detail=true"
    } else {
        ""
    };
    writeln!(
        &mut out,
        "evm.config: stack_reach={stackify_reach_depth} vcode={emit_vcode} bytecode_hex={emit_bytecode_hex} stackify_trace={emit_stackify_trace} evm_trace={emit_evm_trace} emit_observability={emit_observability}{opt_pipeline_suffix}{mem_plan_detail_suffix}",
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
    if emit_mem_plan_detail {
        writeln!(&mut out, "\nmem plan detail:").unwrap();
        writeln!(&mut out, "{mem_plan}").unwrap();
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
                    Label::SectionCodeUnit(unit) => {
                        write!(out, " {}", section_code_unit_label_name(unit)).unwrap()
                    }
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
        if rest.starts_with("global_dyn_base=") {
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

#[test]
fn promoted_aggregate_fields_preserve_snapshots_of_larger_objects() {
    let source = r#"
target = "evm-ethereum-osaka"
type @Pair = { i256, [i256; 1] };
type @Large = { [i256; 12], @Pair };
func inline(never) private %snapshot(v0.objref<@Large>, v1.objref<i256>) -> @Pair {
block0:
    v2.objref<@Pair> = obj.proj v0 1.i8;
    v3.@Pair = obj.load v2;
    obj.store v1 22.i256;
    return v3;
}
func public %entry() {
block0:
    v0.i256 = evm_calldata_load 0.i256;
    v1.i256 = evm_calldata_load 32.i256;
    v2.objref<@Large> = obj.alloc @Large;
    v3.objref<i256> = obj.proj v2 1.i8 0.i8;
    v4.objref<[i256; 1]> = obj.proj v2 1.i8 1.i8;
    v5.objref<i256> = obj.index v4 0.i8;
    obj.store v3 v0;
    obj.store v5 v1;
    v6.@Pair = call %snapshot v2 v3;
    v7.i256 = extract_value v6 0.i8;
    v8.[i256; 1] = extract_value v6 1.i8;
    v9.i256 = extract_value v8 0.i8;
    v10.i256 = obj.load v3;
    evm_mstore 0.i256 v7;
    evm_mstore 32.i256 v9;
    evm_mstore 64.i256 v10;
    evm_return 0.i256 96.i256;
}
object @Contract { section runtime { entry %entry; } }
"#;
    let config = VerifierConfig::for_level(VerificationLevel::Full);
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::Os] {
        let module = parse_sona(source).module;
        verify_module_or_panic(&module, &config);
        assert_eq!(ObjectArgPromotion::default().run(&module).promoted_args, 1);
        verify_module_or_panic(&module, &config);
        let mut compiler = Compile::new(module, EvmCompiler::default()).with_opt_level(level);
        verify_module_or_panic(compiler.optimize(), &config);
        let artifacts = compiler.compile().expect("aggregate fields should compile");
        let runtime = artifacts[0]
            .sections
            .iter()
            .find(|(name, _)| name.0 == "runtime")
            .unwrap();
        let mut harness = EvmHarness::from_runtime(&runtime.1.bytes);
        for (lhs, rhs) in [
            (IrU256::zero(), IrU256::one()),
            (IrU256::MAX, IrU256::one()),
            (IrU256::one() << 255, IrU256::MAX),
        ] {
            let result = harness.call(&[lhs.to_big_endian(), rhs.to_big_endian()].concat());
            let ExecutionResult::Success {
                output: Output::Call(output),
                ..
            } = result
            else {
                panic!("{level:?}, lhs={lhs}, rhs={rhs}: {result:?}");
            };
            let expected = [lhs, rhs, IrU256::from(22)]
                .into_iter()
                .flat_map(|word| word.to_big_endian())
                .collect::<Vec<_>>();
            assert_eq!(output.as_ref(), expected, "{level:?}");
        }
    }
}

#[test]
fn entry_backedges_preserve_first_invocation_branch() {
    let source = r#"
target = "evm-ethereum-osaka"
func inline(never) private %allocate(v0.i1) -> i256 {
block0:
    v1.*i8 = evm_malloc 32.i256;
    v2.i256 = ptr_to_int v1 i256;
    br v0 block0 block1;
block1:
    return v2;
}
func public %entry() {
block0:
    evm_mstore 64.i256 0.i256;
    v0.i256 = evm_calldata_load 0.i256;
    v1.i1 = trunc v0 i1;
    v2.i256 = call %allocate v1;
    v3.i1 = lt v2 96.i256;
    v4.i256 = zext v3 i256;
    evm_mstore 0.i256 v4;
    evm_return 0.i256 32.i256;
}
object @Contract { section runtime { entry %entry; } }
"#;
    let config = VerifierConfig::for_level(VerificationLevel::Full);
    for indirect in [false, true] {
        for loop_on_true in [false, true] {
            let latch = if indirect { "block2" } else { "block0" };
            let branch = if loop_on_true {
                format!("br v0 {latch} block1;")
            } else {
                format!("br v0 block1 {latch};")
            };
            let mut source = source.replace("br v0 block0 block1;", &branch);
            if indirect {
                source = source.replace(
                    "    return v2;",
                    "    return v2;\nblock2:\n    jump block0;",
                );
            }
            for (level, initial_free_ptr) in
                [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::Os]
                    .into_iter()
                    .flat_map(|level| [0, 64, 512].map(|initial| (level, initial)))
            {
                let source = source.replace(
                    "evm_mstore 64.i256 0.i256;",
                    &format!("evm_mstore 64.i256 {initial_free_ptr}.i256;"),
                );
                let module = parse_sona(&source).module;
                verify_module_or_panic(&module, &config);
                let mut compiler =
                    Compile::new(module, EvmCompiler::default()).with_opt_level(level);
                verify_module_or_panic(compiler.optimize(), &config);
                let artifacts = compiler.compile().expect("entry loop should compile");
                let runtime = artifacts[0]
                    .sections
                    .iter()
                    .find(|(name, _)| name.0 == "runtime")
                    .unwrap();
                for condition in [false, true] {
                    let harness = EvmHarness::from_runtime(&runtime.1.bytes);
                    let mut env = Env::default();
                    env.tx.clear();
                    env.tx.transact_to = TransactTo::Call(harness.contract);
                    env.tx.gas_limit = 100_000;
                    env.tx.data = IrU256::from(u8::from(condition))
                        .to_big_endian()
                        .to_vec()
                        .into();
                    let (result, _) = EvmHarness::run_tx(harness.db, env);
                    if condition == loop_on_true {
                        assert!(
                            matches!(
                                result,
                                ExecutionResult::Halt {
                                    reason: HaltReason::OutOfGas(_),
                                    ..
                                }
                            ),
                            "{level:?}, indirect={indirect}, loop_on_true={loop_on_true}: {result:?}"
                        );
                    } else {
                        let ExecutionResult::Success {
                            output: Output::Call(output),
                            ..
                        } = result
                        else {
                            panic!(
                                "{level:?}, indirect={indirect}, loop_on_true={loop_on_true}: {result:?}"
                            );
                        };
                        assert_eq!(output.as_ref(), [0; 32]);
                    }
                }
            }
        }
    }
}

#[test]
fn object_argument_promotion_preserves_repeated_loop_reads() {
    let source = r#"
target = "evm-ethereum-osaka"
type @Pair = { i256, i256 };
func inline(never) private %read_loop(v0.objref<@Pair>, v1.objref<i256>, v2.objref<i1>) -> i256 {
block0:
    jump block1;
block1:
    v3.objref<i256> = obj.proj v0 0.i8;
    v4.i256 = obj.load v3;
    v5.i1 = obj.load v2;
    br v5 block3 block2;
block2:
    obj.store v1 22.i256;
    obj.store v2 1.i1;
    jump block1;
block3:
    return v4;
}
func public %entry() {
block0:
    v0.objref<@Pair> = obj.alloc @Pair;
    v1.objref<i256> = obj.proj v0 0.i8;
    v2.objref<i256> = obj.proj v0 1.i8;
    obj.store v1 11.i256;
    obj.store v2 33.i256;
    v4.objref<i1> = obj.alloc i1;
    obj.store v4 0.i1;
    v3.i256 = call %read_loop v0 v1 v4;
    evm_mstore 0.i256 v3;
    evm_return 0.i256 32.i256;
}
object @Contract { section runtime { entry %entry; } }
"#;
    let config = VerifierConfig::for_level(VerificationLevel::Full);
    for aliased in [true, false] {
        let source = if aliased {
            source.to_owned()
        } else {
            source.replace("call %read_loop v0 v1", "call %read_loop v0 v2")
        };
        for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::Os] {
            let module = parse_sona(&source).module;
            verify_module_or_panic(&module, &config);
            ObjectArgPromotion::default().run(&module);
            verify_module_or_panic(&module, &config);
            let mut compiler = Compile::new(module, EvmCompiler::default()).with_opt_level(level);
            verify_module_or_panic(compiler.optimize(), &config);
            let artifacts = compiler.compile().expect("loop reads should compile");
            let runtime = artifacts[0]
                .sections
                .iter()
                .find(|(name, _)| name.0 == "runtime")
                .unwrap();
            let mut harness = EvmHarness::from_runtime(&runtime.1.bytes);
            let result = harness.call(&[]);
            let ExecutionResult::Success {
                output: Output::Call(output),
                ..
            } = result
            else {
                panic!("{level:?}, aliased={aliased}: {result:?}");
            };
            let expected = IrU256::from(if aliased { 22 } else { 11 });
            assert_eq!(
                output.as_ref(),
                expected.to_big_endian(),
                "{level:?}, aliased={aliased}"
            );
        }
    }
}

#[test]
fn promoted_object_arguments_preserve_alias_snapshots_and_reverts() {
    let source = r#"
target = "evm-ethereum-osaka"
type @Pair = { i256, i256 };
func inline(never) private %snapshot(v0.objref<@Pair>, v1.objref<i256>) -> i256 {
block0:
    v2.objref<i256> = obj.proj v0 0.i8;
    v3.i256 = obj.load v2;
    v4.objref<i256> = obj.proj v0 1.i8;
    v5.i256 = obj.load v4;
    v6.i1 = is_zero v5;
    br v6 block1 block2;
block1:
    evm_mstore 0.i256 v3;
    evm_revert 0.i256 32.i256;
block2:
    obj.store v1 22.i256;
    v7.i256 = xor v3 v5;
    evm_sstore 0.i256 v7;
    return v7;
}
func public %entry() {
block0:
    v0.i256 = evm_calldata_load 0.i256;
    v1.i256 = evm_calldata_load 32.i256;
    v2.objref<@Pair> = obj.alloc @Pair;
    v3.objref<i256> = obj.proj v2 0.i8;
    v4.objref<i256> = obj.proj v2 1.i8;
    obj.store v3 v0;
    obj.store v4 v1;
    v5.objref<i256> = obj.alloc i256;
    obj.store v5 33.i256;
    v6.i256 = call %snapshot v2 v3;
    v7.i256 = obj.load v3;
    v8.i256 = evm_sload 0.i256;
    evm_mstore 0.i256 v6;
    evm_mstore 32.i256 v7;
    evm_mstore 64.i256 v8;
    evm_return 0.i256 96.i256;
}
object @Contract { section runtime { entry %entry; } }
"#;
    let pairs = [
        (IrU256::zero(), IrU256::one()),
        (IrU256::MAX, IrU256::one()),
        (IrU256::one() << 255, IrU256::MAX),
        (IrU256::one(), IrU256::zero()),
        (IrU256::MAX, IrU256::zero()),
    ];
    let config = VerifierConfig::for_level(VerificationLevel::Full);
    for aliased in [true, false] {
        let source = if aliased {
            source.to_owned()
        } else {
            source.replace("call %snapshot v2 v3", "call %snapshot v2 v5")
        };
        for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::Os] {
            let module = parse_sona(&source).module;
            verify_module_or_panic(&module, &config);
            assert_eq!(ObjectArgPromotion::default().run(&module).promoted_args, 1);
            verify_module_or_panic(&module, &config);
            let mut compiler = Compile::new(module, EvmCompiler::default()).with_opt_level(level);
            verify_module_or_panic(compiler.optimize(), &config);
            let artifacts = compiler
                .compile()
                .expect("promoted object args should compile");
            let runtime = artifacts[0]
                .sections
                .iter()
                .find(|(name, _)| name.0 == "runtime")
                .unwrap();
            let mut harness = EvmHarness::from_runtime(&runtime.1.bytes);
            for (lhs, rhs) in pairs {
                let result = harness.call(&[lhs.to_big_endian(), rhs.to_big_endian()].concat());
                if rhs.is_zero() {
                    let ExecutionResult::Revert { output, .. } = result else {
                        panic!("{level:?}, aliased={aliased}, lhs={lhs}, rhs={rhs}: {result:?}");
                    };
                    assert_eq!(output.as_ref(), lhs.to_big_endian());
                } else {
                    let ExecutionResult::Success {
                        output: Output::Call(output),
                        ..
                    } = result
                    else {
                        panic!("{level:?}, aliased={aliased}, lhs={lhs}, rhs={rhs}: {result:?}");
                    };
                    let after = if aliased { IrU256::from(22) } else { lhs };
                    let expected = [lhs ^ rhs, after, lhs ^ rhs]
                        .into_iter()
                        .flat_map(|word| word.to_big_endian())
                        .collect::<Vec<_>>();
                    assert_eq!(output.as_ref(), expected, "{level:?}, aliased={aliased}");
                }
            }
        }
    }
}

#[test]
fn promoted_object_arguments_keep_materialized_pointees_alive() {
    let source = r#"
target = "evm-ethereum-osaka"
type @Pair = { i256, i256 };
func inline(never) private %read(v0.objref<@Pair>) -> i256 {
block0:
    v1.objref<i256> = obj.proj v0 0.i8;
    v2.i256 = obj.load v1;
    v3.objref<i256> = obj.proj v0 1.i8;
    v4.i256 = obj.load v3;
    v5.i256 = add v2 32.i256;
    v6.i256 = evm_mload v5;
    v7.i256 = add v6 v4;
    return v7;
}
func public %entry() {
block0:
    v0.i256 = evm_calldata_load 0.i256;
    v1.objref<@Pair> = obj.alloc @Pair;
    v2.objref<i256> = obj.proj v1 0.i8;
    v3.objref<i256> = obj.proj v1 1.i8;
    obj.store v2 0.i256;
    obj.store v3 v0;
    v4.*@Pair = obj.materialize.stack v1;
    v5.i256 = ptr_to_int v4 i256;
    obj.store v2 v5;
    v6.i256 = call %read v1;
    evm_mstore 0.i256 v6;
    evm_return 0.i256 32.i256;
}
object @Contract { section runtime { entry %entry; } }
"#;
    let config = VerifierConfig::for_level(VerificationLevel::Full);
    for promote in [false, true] {
        for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::Os] {
            let module = parse_sona(source).module;
            verify_module_or_panic(&module, &config);
            if promote {
                assert_eq!(ObjectArgPromotion::default().run(&module).promoted_args, 1);
                verify_module_or_panic(&module, &config);
            }
            let mut compiler = Compile::new(module, EvmCompiler::default()).with_opt_level(level);
            verify_module_or_panic(compiler.optimize(), &config);
            let artifacts = compiler
                .compile()
                .expect("materialized object args should compile");
            let runtime = artifacts[0]
                .sections
                .iter()
                .find(|(name, _)| name.0 == "runtime")
                .unwrap();
            let mut harness = EvmHarness::from_runtime(&runtime.1.bytes);
            for input in [IrU256::zero(), IrU256::from(17), IrU256::MAX] {
                let result = harness.call(&input.to_big_endian());
                let ExecutionResult::Success {
                    output: Output::Call(output),
                    ..
                } = result
                else {
                    panic!("{level:?}, promote={promote}, input={input}: {result:?}");
                };
                assert_eq!(
                    output.as_ref(),
                    input.overflowing_mul(IrU256::from(2)).0.to_big_endian(),
                    "{level:?}, promote={promote}, input={input}"
                );
            }
        }
    }
}

#[test]
fn memory_planning_at_all_optimization_levels() {
    for (name, source) in [
        (
            "rematerialization",
            include_str!("../test_files/evm/calldata_rematerialization.sntn"),
        ),
        (
            "branch storage",
            include_str!("../test_files/evm/branch_exclusive_unknown_storage.sntn"),
        ),
        (
            "branch spills",
            include_str!("../test_files/evm/branch_exclusive_final_spills.sntn"),
        ),
        (
            "heap across spill loop",
            include_str!("../test_files/evm/heap_live_across_final_spill_loop.sntn"),
        ),
    ] {
        for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::Os] {
            let parsed = parse_sona(source);
            let cases = evm_directives::parse_evm_cases(&parsed.debug.module_comments).unwrap();
            let compiler =
                Compile::new(parsed.module, EvmCompiler::default()).with_opt_level(level);
            let artifacts = compiler.compile().expect("memory fixture compiles");
            let runtime = artifacts[0]
                .sections
                .iter()
                .find(|(name, _)| name.0 == "runtime")
                .unwrap();
            for case in cases {
                let mut harness = EvmHarness::from_runtime(&runtime.1.bytes);
                let result = harness.call(&case.calldata);
                assert_case(&case, &result, &format!("{name} {level:?}"));
            }
        }
    }
}
