use sonatina_codegen::compile::OptLevel;
use sonatina_sp1_integration::link;
use sp1_sdk::{
    ProvingKey,
    blocking::{ProveRequest, Prover, ProverClient, SP1Stdin},
};

const IO: &str = include_str!("../fixtures/io.sntn");

fn input(value: u32, wide: u64) -> SP1Stdin {
    let mut stdin = SP1Stdin::new();
    stdin.write_slice(&value.to_le_bytes());
    stdin.write_slice(&wide.to_le_bytes());
    stdin
}

#[test]
fn input_checked_arithmetic_and_public_values() {
    let client = ProverClient::builder().cpu().build();
    for level in [OptLevel::O0, OptLevel::O2] {
        let elf = link(IO, level);
        for value in [0, 41, i32::MAX as u32, u32::MAX - 1] {
            for wide in [0, i64::MAX as u64, u64::MAX] {
                let (values, report) = client
                    .execute(elf.clone(), input(value, wide))
                    .run()
                    .unwrap();
                assert_eq!(report.exit_code, 0);
                let expected = [(value + 1).to_le_bytes().as_slice(), &wide.to_le_bytes()].concat();
                assert_eq!(values.as_slice(), expected, "{level:?}: {value}, {wide}");
            }
        }
        // First establish that this exact ELF runs successfully above, then
        // require overflow to fail. Portable SP1 6.8.0 reports taken EBREAK as
        // a worker panic rather than a typed trap; its message is not an API.
        assert!(client.execute(elf, input(u32::MAX, 0)).run().is_err());
    }
}

#[test]
fn missing_and_malformed_inputs_fail() {
    let client = ProverClient::builder().cpu().build();
    let elf = link(IO, OptLevel::O2);
    let (values, report) = client.execute(elf.clone(), SP1Stdin::new()).run().unwrap();
    assert_eq!(report.exit_code, 1);
    assert!(values.as_slice().is_empty());
    for length in [0, 3, 5, 8] {
        let mut stdin = SP1Stdin::new();
        stdin.write_slice(&vec![0; length]);
        stdin.write_slice(&0u64.to_le_bytes());
        let (values, report) = client.execute(elf.clone(), stdin).run().unwrap();
        assert_eq!(report.exit_code, 1);
        assert!(values.as_slice().is_empty());
    }
}

#[test]
#[ignore = "CPU core proof; run explicitly in the SP1 proof job"]
fn proves_and_verifies_checked_input_program() {
    let client = ProverClient::builder().cpu().build();
    let pk = client.setup(link(IO, OptLevel::O2)).unwrap();
    let proof = client.prove(&pk, input(41, u64::MAX)).core().run().unwrap();
    let expected = [42u32.to_le_bytes().as_slice(), &u64::MAX.to_le_bytes()].concat();
    assert_eq!(proof.public_values.as_slice(), expected);
    client.verify(&proof, pk.verifying_key(), None).unwrap();

    assert!(client.prove(&pk, input(u32::MAX, 0)).core().run().is_err());
    // Guest panic may be reported as a failed-status proof, not a host error.
    // In either case it must never verify against the default success status.
    if let Ok(proof) = client.prove(&pk, SP1Stdin::new()).core().run() {
        assert!(client.verify(&proof, pk.verifying_key(), None).is_err());
    }
}
