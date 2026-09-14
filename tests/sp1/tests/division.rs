use sonatina_codegen::compile::OptLevel;
use sonatina_ir::{I256, Immediate, Type};
use sonatina_sp1_integration::link;
use sp1_sdk::blocking::{Prover, ProverClient, SP1Stdin};

#[test]
fn wide_division_and_remainder_compose_with_phi_loops() {
    let client = ProverClient::builder().cpu().build();
    for (width, ty) in [(128, Type::I128), (256, Type::I256)] {
        for (div, rem) in [("udiv", "umod"), ("sdiv", "smod")] {
            let (inputs, lhs, rhs, output, result) = if width == 256 {
                (String::new(), "v0", "v1", String::new(), "v7")
            } else {
                (
                    "v3.i128 = trunc v0 i128;\n    v4.i128 = trunc v1 i128;".to_string(),
                    "v3",
                    "v4",
                    "v11.i256 = zext v7 i256;".to_string(),
                    "v11",
                )
            };
            let source = format!(
                r#"
declare external %sys_sp1_read_u32() -> i32;
{}
func public %main() -> i32 {{
block0:
    v0.i256 = call %read_wide;
    v1.i256 = call %read_wide;
    v2.i32 = call %sys_sp1_read_u32;
    {inputs}
    jump block1;
block1:
    v5.i{width} = phi ({lhs} block0) (v7 block1);
    v6.i32 = phi (0.i32 block0) (v10 block1);
    v8.i{width} = {div} v5 {rhs};
    v9.i{width} = {rem} v5 {rhs};
    v7.i{width} = add v8 v9;
    v10.i32 = add v6 1.i32;
    v12.i1 = lt v10 v2;
    br v12 block1 block2;
block2:
    {output}
    call %commit_wide {result} 0.i1;
    return 0.i32;
}}
"#,
                include_str!("../fixtures/words.sntn")
            );
            for level in [OptLevel::O0, OptLevel::O2] {
                let elf = link(&source, level);
                for lhs in [
                    Immediate::signed_min(ty),
                    Immediate::all_one(ty),
                    Immediate::signed_max(ty),
                ] {
                    for rhs in [3, -7, -1].map(|n| Immediate::from_i256(I256::from(n), ty)) {
                        for count in [1u32, 2, 5] {
                            let mut stdin = SP1Stdin::new();
                            for value in [lhs, rhs] {
                                for word in value
                                    .zext(Type::I256)
                                    .as_i256()
                                    .to_u256()
                                    .to_little_endian()
                                    .as_chunks::<8>()
                                    .0
                                {
                                    stdin.write_slice(word);
                                }
                            }
                            stdin.write_slice(&count.to_le_bytes());
                            let mut expected = lhs;
                            for _ in 0..count {
                                expected = if div == "sdiv" {
                                    expected.sdiv(rhs) + expected.srem(rhs)
                                } else {
                                    expected.udiv(rhs) + expected.urem(rhs)
                                };
                            }
                            let mut bytes = expected
                                .zext(Type::I256)
                                .as_i256()
                                .to_u256()
                                .to_little_endian()
                                .to_vec();
                            bytes.extend_from_slice(&0u32.to_le_bytes());
                            let (values, report) =
                                client.execute(elf.clone(), stdin).run().unwrap();
                            assert_eq!(report.exit_code, 0);
                            assert_eq!(
                                values.as_slice(),
                                bytes,
                                "i{width} {div} {level:?}: {lhs:?}, {rhs:?}, {count}"
                            );
                        }
                    }
                }
            }
        }
    }
}
