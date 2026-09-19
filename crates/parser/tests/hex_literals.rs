use ir::{Immediate, U256, global_variable::GvInitializer};
use sonatina_parser::{Error, parse_module};

#[test]
fn hexadecimal_immediates_accept_odd_and_even_digit_counts() {
    for bits in [8, 16, 32, 64, 128, 256] {
        let mask = U256::MAX >> (256 - bits);
        let values = [
            U256::zero(),
            7.into(),
            15.into(),
            16.into(),
            127.into(),
            U256::one() << (bits - 1),
            mask >> 4,
            mask,
        ];
        for expected in values {
            for digits in [format!("{expected:x}"), format!("{expected:X}")] {
                let source = format!(
                    "target = \"evm-ethereum-osaka\"\n\
                     func public %f() -> i{bits} {{\n\
                     block0:\nreturn 0x{digits}.i{bits};\n}}"
                );
                let parsed = parse_module(&source).expect("valid hexadecimal immediate");
                parsed
                    .module
                    .func_store
                    .view(parsed.module.funcs()[0], |func| {
                        let block = func.layout.entry_block().unwrap();
                        let term = func.layout.last_inst_of(block).unwrap();
                        let value = func.dfg.inst(term).collect_values()[0];
                        let actual = func.dfg.value_imm(value).unwrap().as_i256().to_u256() & mask;
                        assert_eq!(actual, expected, "i{bits}: 0x{digits}");
                    });
            }
        }
    }
}

#[test]
fn hexadecimal_global_initializers_accept_odd_digits_and_leading_zeroes() {
    for (literal, expected) in [("0x0", 0), ("0x7", 7), ("0x00F", 15), ("0xAbC", 2748)] {
        let source = format!(
            "target = \"evm-ethereum-osaka\"\n\
             global private const i256 $VALUE = {literal};"
        );
        let parsed = parse_module(&source).expect("valid hexadecimal initializer");
        parsed.module.ctx.with_gv_store(|store| {
            let gv = store.lookup_gv("VALUE").unwrap();
            assert_eq!(
                store.init_data(gv),
                Some(&GvInitializer::Immediate(Immediate::I256(expected.into())))
            );
        });
    }
}

#[test]
fn oversized_hexadecimal_literals_report_errors() {
    for bits in [8, 16, 32, 64, 128, 256] {
        for prefix in ["1", "10"] {
            let digits = format!("{prefix}{}", "0".repeat(bits / 4));
            let source = format!(
                "target = \"evm-ethereum-osaka\"\n\
                 func public %f() -> i{bits} {{\n\
                 block0:\nreturn 0x{digits}.i{bits};\n}}"
            );
            let errors = parse_module(&source)
                .err()
                .expect("oversized immediate must be rejected");
            assert!(
                matches!(errors.as_slice(), [Error::NumberOutOfBounds(_)]),
                "{errors:?}"
            );
            if bits == 256 {
                let source = format!(
                    "target = \"evm-ethereum-osaka\"\n\
                     global private const i256 $VALUE = 0x{digits};"
                );
                let errors = parse_module(&source)
                    .err()
                    .expect("oversized initializer must be rejected");
                assert!(
                    matches!(errors.as_slice(), [Error::NumberOutOfBounds(_)]),
                    "{errors:?}"
                );
            }
        }
    }
}
