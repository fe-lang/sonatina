use std::fmt::Write;

use revm::primitives::{AccountInfo, Address, Bytes, Env, TransactTo, U256 as EvmU256, keccak256};
use sonatina_codegen::{
    compile::{EvmCompile, OptLevel},
    isa::evm::{
        EvmBackend, ImmediateMaterializationMode, LateCleanupProfile, SwitchLoweringStrategy,
    },
    object::{CompileOptions, compile_all_objects},
    stackalloc::StackifySearchProfile,
};
use sonatina_ir::{U256, isa::evm::Evm};

use super::{
    EvmHarness, ExecutionResult, Output, execution_gas_used, initial_tx_gas_for_call, parse_sona,
};

fn compile_switch(source: &str, strategy: SwitchLoweringStrategy, level: OptLevel) -> Vec<u8> {
    let mut compiler = EvmCompile::new(parse_sona(source).module).with_opt_level(level);
    let module = compiler.optimize();
    // Configure the override using the complete public optimization profile, and
    // cross-check Auto against EvmCompile below so profile drift fails the tests.
    let (profile, search, mode) = match level {
        OptLevel::O0 => (
            LateCleanupProfile::Off,
            StackifySearchProfile::Fast,
            ImmediateMaterializationMode::Gas,
        ),
        OptLevel::O1 => (
            LateCleanupProfile::Speed,
            StackifySearchProfile::GreedyWide,
            ImmediateMaterializationMode::Gas,
        ),
        OptLevel::O2 => (
            LateCleanupProfile::Speed,
            StackifySearchProfile::Exact,
            ImmediateMaterializationMode::Balanced,
        ),
        OptLevel::Os => (
            LateCleanupProfile::Size,
            StackifySearchProfile::Exact,
            ImmediateMaterializationMode::Size,
        ),
    };
    let backend = EvmBackend::new(Evm::new(module.ctx.triple))
        .with_late_cleanup_profile(profile)
        .with_stackify_search_profile(search)
        .with_immediate_materialization_mode(mode)
        .with_switch_lowering_strategy(strategy);
    let artifacts = compile_all_objects(module, &backend, &CompileOptions::default())
        .expect("switch should compile");
    if strategy == SwitchLoweringStrategy::Auto {
        let public = compiler.compile().expect("public compiler should succeed");
        assert_eq!(artifacts.len(), public.len());
        assert_eq!(artifacts[0].sections.len(), public[0].sections.len());
        for ((name, manual), (public_name, public_section)) in
            artifacts[0].sections.iter().zip(&public[0].sections)
        {
            assert_eq!(name, public_name);
            assert_eq!(manual.bytes, public_section.bytes);
        }
    }
    assert_eq!(artifacts.len(), 1);
    let artifact = artifacts.into_iter().next().unwrap();
    artifact
        .sections
        .into_iter()
        .find(|(name, _)| name.0 == "runtime")
        .unwrap()
        .1
        .bytes
}

fn switch_source(keys: &[U256], bits: usize) -> String {
    let mut source = String::from(
        "target = \"evm-ethereum-osaka\"\n\
         func public %entry() {\nblock0:\n\
         v0.i256 = evm_calldata_load 0.i256;\n",
    );
    let scrutinee = if bits == 256 {
        "v0"
    } else {
        writeln!(source, "v1.i{bits} = trunc v0 i{bits};").unwrap();
        "v1"
    };
    write!(source, "br_table {scrutinee} block1").unwrap();
    for (index, key) in keys.iter().enumerate() {
        write!(source, " (0x{key:x}.i{bits} block{})", index + 2).unwrap();
    }
    source.push_str(";\nblock1:\nmstore 0.i256 0.i256 i256;\nevm_return 0.i256 32.i256;\n");
    for (index, _) in keys.iter().enumerate() {
        writeln!(
            source,
            "block{}:\nmstore 0.i256 {}.i256 i256;\nevm_return 0.i256 32.i256;",
            index + 2,
            index + 1
        )
        .unwrap();
    }
    source.push_str("}\nobject @Contract { section runtime { entry %entry; } }\n");
    source
}

fn check_call(harness: &mut EvmHarness, calldata: &[u8], expected: U256) -> u64 {
    let result = harness.call(calldata);
    let ExecutionResult::Success {
        output: Output::Call(actual),
        ..
    } = &result
    else {
        panic!("calldata={calldata:?}: {result:?}");
    };
    assert_eq!(
        actual.as_ref(),
        expected.to_big_endian(),
        "calldata={calldata:?}"
    );
    execution_gas_used(&result) - initial_tx_gas_for_call(calldata)
}

#[test]
fn switch_lowering_scaling() {
    let mut measurements =
        String::from("cases strategy bytes min_gas mean_gas max_gas max_default_gas\n");
    for count in [1, 2, 4, 5, 6, 8, 16, 32, 64, 128] {
        // Spread selectors across both halves of the unsigned 32-bit domain, and
        // deliberately present them out of numeric order.
        let keys: Vec<_> = (0..count)
            .map(|index| {
                U256::from(
                    (index as u32)
                        .wrapping_mul(0x9e3779b9)
                        .wrapping_add(0x10203040),
                )
            })
            .collect();
        let source = switch_source(&keys, 32);
        let mut means = Vec::new();
        for strategy in [SwitchLoweringStrategy::Linear, SwitchLoweringStrategy::Tree] {
            let bytes = compile_switch(&source, strategy, OptLevel::O2);
            let mut harness = EvmHarness::from_runtime(&bytes);
            let gas: Vec<_> = keys
                .iter()
                .enumerate()
                .map(|(index, &key)| {
                    check_call(&mut harness, &key.to_big_endian(), (index + 1).into())
                })
                .collect();
            let unknown: Vec<_> = keys
                .iter()
                .map(|key| key + U256::one())
                .chain([U256::zero(), u32::MAX.into()])
                .collect();
            let default_gas = unknown
                .into_iter()
                .map(|key| check_call(&mut harness, &key.to_big_endian(), U256::zero()))
                .max()
                .unwrap();
            let sum: u64 = gas.iter().sum();
            means.push(sum);
            writeln!(
                measurements,
                "{count:3} {strategy:?} {} {} {:.1} {} {default_gas}",
                bytes.len(),
                gas.iter().min().unwrap(),
                sum as f64 / count as f64,
                gas.iter().max().unwrap()
            )
            .unwrap();
        }
        if count >= 8 {
            assert!(
                means[1] < means[0],
                "tree should reduce average gas for {count} cases"
            );
        }
    }
    println!("{measurements}");
    insta::assert_snapshot!("switch_lowering_scaling", measurements);
}

#[test]
fn switch_lowering_unsigned_words_and_narrow_values() {
    for bits in [8, 16, 32, 64, 128, 256] {
        let max = U256::MAX >> (256 - bits);
        let high = U256::one() << (bits - 1);
        let keys = [
            max,
            7.into(),
            high,
            U256::zero(),
            high - U256::one(),
            2.into(),
            max - U256::one(),
        ];
        let source = switch_source(&keys, bits);
        for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::Os] {
            for strategy in [SwitchLoweringStrategy::Linear, SwitchLoweringStrategy::Tree] {
                let bytes = compile_switch(&source, strategy, level);
                let mut harness = EvmHarness::from_runtime(&bytes);
                let inputs = keys.iter().copied().chain([
                    1.into(),
                    3.into(),
                    6.into(),
                    high + U256::one(),
                    max - U256::from(2),
                ]);
                for input in inputs {
                    let expected = keys
                        .iter()
                        .position(|&key| key == input)
                        .map_or(0, |index| index + 1);
                    check_call(&mut harness, &input.to_big_endian(), expected.into());
                    if bits < 256 {
                        check_call(
                            &mut harness,
                            &(input | (U256::one() << bits)).to_big_endian(),
                            expected.into(),
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn switch_lowering_automatic_profile_selection() {
    let keys: Vec<_> = (0..16).map(|index| U256::from(index * 3)).collect();
    let source = switch_source(&keys, 256);
    for (level, expected) in [
        (OptLevel::O0, SwitchLoweringStrategy::Linear),
        (OptLevel::Os, SwitchLoweringStrategy::Linear),
        (OptLevel::O1, SwitchLoweringStrategy::Tree),
        (OptLevel::O2, SwitchLoweringStrategy::Tree),
    ] {
        assert_eq!(
            compile_switch(&source, SwitchLoweringStrategy::Auto, level),
            compile_switch(&source, expected, level)
        );
    }
}

#[test]
fn switch_lowering_keeps_linear_when_pivot_materialization_is_expensive() {
    let pivot = U256::one() << 200;
    let keys = [
        U256::one(),
        2.into(),
        pivot,
        pivot + U256::one(),
        pivot + U256::from(2),
    ];
    let source = switch_source(&keys, 256);
    let linear = compile_switch(&source, SwitchLoweringStrategy::Linear, OptLevel::O2);
    let tree = compile_switch(&source, SwitchLoweringStrategy::Tree, OptLevel::O2);
    assert_eq!(linear, tree);
    let mut harness = EvmHarness::from_runtime(&tree);
    for (index, key) in keys.into_iter().enumerate() {
        check_call(&mut harness, &key.to_big_endian(), (index + 1).into());
    }
}

#[test]
fn switch_lowering_fe_dispatch_64() {
    let source = include_str!("../fixtures/fe_dispatch_64.sntn");
    let mut measurements = String::from("strategy bytes min_gas mean_gas max_gas unknown_gas\n");
    for strategy in [SwitchLoweringStrategy::Linear, SwitchLoweringStrategy::Tree] {
        let bytes = compile_switch(source, strategy, OptLevel::O2);
        assert_eq!(bytes, compile_switch(source, strategy, OptLevel::O1));
        if strategy == SwitchLoweringStrategy::Tree {
            for level in [OptLevel::O1, OptLevel::O2] {
                assert_eq!(
                    bytes,
                    compile_switch(source, SwitchLoweringStrategy::Auto, level)
                );
            }
        }
        let mut harness = EvmHarness::from_runtime(&bytes);
        let gas: Vec<_> = (0..64)
            .map(|index| {
                let hash = keccak256(format!("f{index:03}()"));
                check_call(&mut harness, &hash[..4], U256::from(index))
            })
            .collect();
        let unknown = [0xde, 0xad, 0xbe, 0xef];
        let result = harness.call(&unknown);
        assert!(matches!(result, ExecutionResult::Revert { .. }));
        let unknown_gas = execution_gas_used(&result) - initial_tx_gas_for_call(&unknown);
        let setter = keccak256("setSink(uint256)");
        for calldata in [&[][..], &[0][..], &[0, 0][..], &[0, 0, 0][..], &setter[..4]] {
            assert!(matches!(
                harness.call(calldata),
                ExecutionResult::Revert { .. }
            ));
        }
        let setter_calldata = [&setter[..4], &U256::from(123).to_big_endian()].concat();
        check_call(&mut harness, &setter_calldata, 123.into());
        check_call(&mut harness, &keccak256("sink()")[..4], 123.into());

        // Enter a valid selector with value to verify that routing still reaches
        // Fe's generated nonpayable wrapper before executing the handler.
        let caller = Address::repeat_byte(0x34);
        harness.db.insert_account_info(
            caller,
            AccountInfo {
                balance: EvmU256::from(100),
                ..AccountInfo::default()
            },
        );
        let mut env = Env::default();
        env.tx.clear();
        env.tx.caller = caller;
        env.tx.transact_to = TransactTo::Call(harness.contract);
        env.tx.data = Bytes::copy_from_slice(&keccak256("f000()")[..4]);
        env.tx.value = EvmU256::from(1);
        let (result, _) = EvmHarness::run_tx(harness.db, env);
        assert!(matches!(result, ExecutionResult::Revert { .. }));
        writeln!(
            measurements,
            "{strategy:?} {} {} {:.1} {} {unknown_gas}",
            bytes.len(),
            gas.iter().min().unwrap(),
            gas.iter().sum::<u64>() as f64 / gas.len() as f64,
            gas.iter().max().unwrap()
        )
        .unwrap();
    }
    println!("{measurements}");
    insta::assert_snapshot!("switch_lowering_fe_dispatch_64", measurements);
}

#[test]
fn switch_lowering_under_stack_pressure() {
    // Each bit selects one of 18 independent calldata words, preserving the
    // distinct per-edge live sets from the cost-model regression reproducers.
    let mixed_keys = (0..7)
        .map(|index| {
            if index < 3 {
                (U256::one() << (120 + index)) - U256::one()
            } else {
                (U256::one() << 140) + U256::from(index)
            }
        })
        .collect::<Vec<_>>();
    let boundary_keys = (0..9)
        .rev()
        .map(|index| {
            if index < 4 {
                U256::from(index + 1)
            } else {
                (U256::one() << 200) - U256::one() + U256::from(index - 4)
            }
        })
        .collect::<Vec<_>>();
    let examples: [(&str, Vec<U256>, &[u32]); 4] = [
        (
            "six",
            (1..=6).map(U256::from).collect(),
            &[0x3b7cf, 0x3b7cf, 0x2f68c, 0x22625, 0x349f2, 0x2b00e],
        ),
        (
            "mixed",
            mixed_keys,
            &[
                0x39e34, 0x244ed, 0x26e29, 0x31317, 0x2a494, 0x2aa31, 0x35a83,
            ],
        ),
        (
            "subtree",
            boundary_keys,
            &[
                0x2b0f1, 0x3f972, 0x3f144, 0x24e52, 0x2c998, 0x3b870, 0x37db1, 0x37d29, 0x35bd3,
            ],
        ),
        (
            "large",
            (1..=32).map(U256::from).collect(),
            &[
                0x2727c, 0x2161c, 0x2c83c, 0x3b2b7, 0x3bc5e, 0x33512, 0x3c5d1, 0x29370, 0x37f38,
                0x2936c, 0x23546, 0x2384a, 0x3eb63, 0x25f81, 0x3249d, 0x3686b, 0x220cd, 0x3d440,
                0x23896, 0x2ec85, 0x2c7bf, 0x3284e, 0x26c62, 0x327aa, 0x35e8f, 0x2f762, 0x28c38,
                0x2f103, 0x32ee5, 0x28d30, 0x331af, 0x22ebb,
            ],
        ),
    ];
    let mut measurements = String::from("example level strategy bytes mean_gas max_gas\n");
    for (name, keys, masks) in examples {
        let mut source = String::from(
            "target = \"evm-ethereum-osaka\"\nfunc public %entry() {\nblock0:\n\
             v0.i256 = evm_calldata_load 0.i256;\n",
        );
        let payload: Vec<_> = (1..=18).map(|index| U256::from(index * 17)).collect();
        for (index, _) in payload.iter().enumerate() {
            writeln!(
                source,
                "v{}.i256 = evm_calldata_load {}.i256;",
                index + 1,
                (index + 1) * 32
            )
            .unwrap();
        }
        source.push_str("br_table v0 block1");
        for (index, key) in keys.iter().enumerate() {
            write!(source, " (0x{key:x}.i256 block{})", index + 2).unwrap();
        }
        source.push_str(";\nblock1:\nevm_revert 0.i256 0.i256;\n");
        let mut next_value = payload.len() + 1;
        for (index, mask) in masks.iter().enumerate() {
            writeln!(source, "block{}:", index + 2).unwrap();
            let mut sum = format!("{}.i256", index + 1);
            for (word, _) in payload.iter().enumerate() {
                if mask & (1 << word) != 0 {
                    writeln!(source, "v{next_value}.i256 = add {sum} v{};", word + 1).unwrap();
                    sum = format!("v{next_value}");
                    next_value += 1;
                }
            }
            writeln!(
                source,
                "mstore 0.i256 {sum} i256;\nevm_return 0.i256 32.i256;"
            )
            .unwrap();
        }
        source.push_str("}\nobject @Contract { section runtime { entry %entry; } }\n");
        for level in [OptLevel::O1, OptLevel::O2] {
            let linear = compile_switch(&source, SwitchLoweringStrategy::Linear, level);
            let auto = compile_switch(&source, SwitchLoweringStrategy::Auto, level);
            if keys.len() <= 8 {
                assert_eq!(auto, linear, "{name} {level:?} should remain linear");
            } else {
                assert_ne!(auto, linear, "{name} {level:?} should still split");
            }
            let mut total_gas = Vec::new();
            for (strategy, bytes) in [("Linear", linear), ("Auto", auto)] {
                let mut harness = EvmHarness::from_runtime(&bytes);
                let gas: Vec<_> = keys
                    .iter()
                    .zip(masks)
                    .enumerate()
                    .map(|(index, (key, mask))| {
                        let calldata: Vec<_> = [*key]
                            .iter()
                            .chain(&payload)
                            .flat_map(|word| word.to_big_endian())
                            .collect();
                        let expected = payload
                            .iter()
                            .enumerate()
                            .filter(|(word, _)| mask & (1 << word) != 0)
                            .fold(U256::from(index + 1), |sum, (_, value)| sum + value);
                        check_call(&mut harness, &calldata, expected)
                    })
                    .collect();
                for unknown in [U256::zero(), U256::MAX] {
                    assert!(matches!(
                        harness.call(&unknown.to_big_endian()),
                        ExecutionResult::Revert { .. }
                    ));
                }
                let sum: u64 = gas.iter().sum();
                total_gas.push(sum);
                writeln!(
                    measurements,
                    "{name} {level:?} {strategy} {} {:.2} {}",
                    bytes.len(),
                    sum as f64 / keys.len() as f64,
                    gas.iter().max().unwrap()
                )
                .unwrap();
            }
            assert!(total_gas[1] <= total_gas[0], "{name} {level:?}");
            if name == "large" {
                assert!(total_gas[1] * 3 < total_gas[0] * 2);
            }
        }
    }
    insta::assert_snapshot!("switch_lowering_under_stack_pressure", measurements);
}

#[test]
fn switch_lowering_preserves_shared_phi_edges_and_loops() {
    let source = r#"
target = "evm-ethereum-osaka"
func public %entry() {
block0:
    v0.i256 = evm_calldata_load 0.i256;
    v1.i1 = eq v0 0.i256;
    br v1 block3 block1;
block1:
    v2.i256 = phi (v0 block0) (v4 block1);
    v3.i256 = phi (7.i256 block0) (v5 block1);
    v4.i256 = sub v2 1.i256;
    v5.i256 = add v3 v2;
br_table v2 block3 (1.i256 block1) (2.i256 block1) (3.i256 block1) (4.i256 block1) (5.i256 block1) (6.i256 block1) (7.i256 block1) (8.i256 block1) (9.i256 block1) (10.i256 block1) (11.i256 block1) (12.i256 block1) (13.i256 block2) (14.i256 block2) (15.i256 block3) (16.i256 block3);
block2:
    v6.i256 = mul v2 100.i256;
    jump block3;
block3:
    v7.i256 = phi (99.i256 block0) (v3 block1) (v6 block2);
    mstore 0.i256 v7 i256;
    evm_return 0.i256 32.i256;
}
object @Contract { section runtime { entry %entry; } }
"#;
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2] {
        for strategy in [SwitchLoweringStrategy::Linear, SwitchLoweringStrategy::Tree] {
            let bytes = compile_switch(source, strategy, level);
            let mut harness = EvmHarness::from_runtime(&bytes);
            for input in 0..20 {
                let expected = match input {
                    0 => 99,
                    1..=12 => 7 + input * (input + 1) / 2,
                    13 | 14 => input * 100,
                    _ => 7,
                };
                check_call(
                    &mut harness,
                    &U256::from(input).to_big_endian(),
                    expected.into(),
                );
            }
        }
    }
}
