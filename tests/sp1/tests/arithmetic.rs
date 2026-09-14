use std::fmt::Write;

use sonatina_codegen::compile::OptLevel;
use sonatina_ir::{I256, Immediate, Type};
use sonatina_sp1_integration::link;
use sp1_sdk::blocking::{Prover, ProverClient, SP1Stdin};

const TYPES: [Type; 7] = [
    Type::I1,
    Type::I8,
    Type::I16,
    Type::I32,
    Type::I64,
    Type::I128,
    Type::I256,
];
const OPS: [&str; 6] = ["uaddo", "saddo", "usubo", "ssubo", "umulo", "smulo"];

#[test]
fn checked_arithmetic_matches_ir_at_every_width() {
    let mut source = include_str!("../fixtures/words.sntn").to_string();
    let mut main = String::from(
        "func public %main() -> i32 {\nblock0:\n    v0.i256 = call %read_wide;\n    v1.i256 = call %read_wide;\n",
    );
    for ty in TYPES {
        let ty_name = format!("{ty:?}").to_lowercase();
        for op in OPS {
            let (inputs, lhs, rhs, output, result) = if ty == Type::I256 {
                (String::new(), "v0", "v1", String::new(), "v4")
            } else {
                (
                    format!(
                        "v2.{ty_name} = trunc v0 {ty_name};\n    v3.{ty_name} = trunc v1 {ty_name};"
                    ),
                    "v2",
                    "v3",
                    "v6.i256 = zext v4 i256;".to_string(),
                    "v6",
                )
            };
            writeln!(
                source,
                r#"
func inline(never) private %apply_{op}_{ty_name}(v0.i256, v1.i256) {{
block0:
    {inputs}
    (v4.{ty_name}, v5.i1) = {op} {lhs} {rhs};
    {output}
    call %commit_wide {result} v5;
    return;
}}
"#
            )
            .unwrap();
            writeln!(main, "    call %apply_{op}_{ty_name} v0 v1;").unwrap();
        }
    }
    source.push_str(&main);
    source.push_str("    return 0.i32;\n}\n");
    let client = ProverClient::builder().cpu().build();
    let mut cases = vec![I256::zero(), I256::one(), I256::from(-1)];
    for ty in TYPES {
        cases.push(Immediate::signed_min(ty).zext(Type::I256).as_i256());
        cases.push(Immediate::signed_max(ty).zext(Type::I256).as_i256());
    }
    for level in [OptLevel::O0, OptLevel::O2] {
        let elf = link(&source, level);
        for &lhs in &cases {
            for &rhs in &[I256::zero(), I256::one(), I256::from(-1), I256::from(7)] {
                let mut stdin = SP1Stdin::new();
                for value in [lhs, rhs] {
                    for word in value.to_u256().to_little_endian().as_chunks::<8>().0 {
                        stdin.write_slice(word);
                    }
                }
                let (values, report) = client.execute(elf.clone(), stdin).run().unwrap();
                assert_eq!(report.exit_code, 0);
                let mut expected = Vec::new();
                for ty in TYPES {
                    let lhs = Immediate::from_i256(lhs, ty);
                    let rhs = Immediate::from_i256(rhs, ty);
                    for (result, overflow) in [
                        lhs.overflowing_uadd(rhs),
                        lhs.overflowing_sadd(rhs),
                        lhs.overflowing_usub(rhs),
                        lhs.overflowing_ssub(rhs),
                        lhs.overflowing_umul(rhs),
                        lhs.overflowing_smul(rhs),
                    ] {
                        expected.extend_from_slice(
                            &result
                                .zext(Type::I256)
                                .as_i256()
                                .to_u256()
                                .to_little_endian(),
                        );
                        expected.extend_from_slice(&u32::from(overflow).to_le_bytes());
                    }
                }
                assert_eq!(values.as_slice(), expected, "{level:?}: {lhs:?}, {rhs:?}");
            }
        }
    }
}
