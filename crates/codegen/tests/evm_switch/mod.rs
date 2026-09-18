use std::fmt::Write;

use revm::primitives::{AccountInfo, Address, Bytes, Env, TransactTo, U256 as EvmU256, keccak256};
use sonatina_codegen::{
    isa::evm::{EvmBackend, LateCleanupProfile, SwitchLoweringStrategy},
    object::{CompileOptions, compile_all_objects},
    optim::pipeline::Pipeline,
};
use sonatina_ir::{U256, isa::evm::Evm};

use super::{
    EvmHarness, ExecutionResult, Output, execution_gas_used, initial_tx_gas_for_call, parse_sona,
};

fn compile_switch(
    source: &str,
    strategy: SwitchLoweringStrategy,
    profile: LateCleanupProfile,
) -> Vec<u8> {
    let mut parsed = parse_sona(source);
    match profile {
        LateCleanupProfile::Speed => Pipeline::speed().run(&mut parsed.module),
        LateCleanupProfile::Size => Pipeline::size().run(&mut parsed.module),
        LateCleanupProfile::Off => {}
    }
    let backend = EvmBackend::new(Evm::new(parsed.module.ctx.triple))
        .with_late_cleanup_profile(profile)
        .with_switch_lowering_strategy(strategy);
    let artifacts = compile_all_objects(&parsed.module, &backend, &CompileOptions::default())
        .expect("switch should compile");
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
            let bytes = compile_switch(&source, strategy, LateCleanupProfile::Speed);
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
        for profile in [
            LateCleanupProfile::Off,
            LateCleanupProfile::Speed,
            LateCleanupProfile::Size,
        ] {
            for strategy in [SwitchLoweringStrategy::Linear, SwitchLoweringStrategy::Tree] {
                let bytes = compile_switch(&source, strategy, profile);
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
    for (profile, expected) in [
        (LateCleanupProfile::Off, SwitchLoweringStrategy::Linear),
        (LateCleanupProfile::Size, SwitchLoweringStrategy::Linear),
        (LateCleanupProfile::Speed, SwitchLoweringStrategy::Tree),
    ] {
        assert_eq!(
            compile_switch(&source, SwitchLoweringStrategy::Auto, profile),
            compile_switch(&source, expected, profile)
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
    let linear = compile_switch(
        &source,
        SwitchLoweringStrategy::Linear,
        LateCleanupProfile::Speed,
    );
    let tree = compile_switch(
        &source,
        SwitchLoweringStrategy::Tree,
        LateCleanupProfile::Speed,
    );
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
        let bytes = compile_switch(source, strategy, LateCleanupProfile::Speed);
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
    for profile in [LateCleanupProfile::Off, LateCleanupProfile::Speed] {
        for strategy in [SwitchLoweringStrategy::Linear, SwitchLoweringStrategy::Tree] {
            let bytes = compile_switch(source, strategy, profile);
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
