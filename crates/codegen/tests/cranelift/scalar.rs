use sonatina_codegen::{Compile, compile::OptLevel, isa::cranelift::CraneliftJitBackend};
use sonatina_ir::{I256, Immediate, Type, U256, isa::Isa, module::ModuleCtx};

use super::native_isa;

fn check_scalar_cases(op: &str, ty: Type, cases: &[(Immediate, Immediate, Immediate, bool)]) {
    let ty_name = format!("{ty:?}").to_lowercase();
    let expression = match op {
        "snego" => format!("(v5.{ty_name}, v6.i1) = snego v3;"),
        "smulo" | "umulo" => format!("(v5.{ty_name}, v6.i1) = {op} v3 v4;"),
        "not" => format!("v5.{ty_name} = not v3;"),
        "shl" | "shr" | "sar" => format!("v5.{ty_name} = {op} v4 v3;"),
        _ => format!("v5.{ty_name} = {op} v3 v4;"),
    };
    let status = if matches!(op, "snego" | "smulo" | "umulo") {
        "v7.i8 = zext v6 i8;\n    return v7;"
    } else {
        "return 0.i8;"
    };
    let triple = native_isa().triple();
    let source = format!(
        r#"target = "{triple}"
func public %apply(v0.*{ty_name}, v1.*{ty_name}, v2.*{ty_name}) -> i8 {{
block0:
    v3.{ty_name} = mload v0 {ty_name};
    v4.{ty_name} = mload v1 {ty_name};
    {expression}
    mstore v2 v5 {ty_name};
    {status}
}}
"#
    );
    for level in [OptLevel::O0, OptLevel::O2] {
        let module = sonatina_parser::parse_module(&source)
            .expect("scalar IR should parse")
            .module;
        let artifact = Compile::new(module, CraneliftJitBackend::new())
            .with_opt_level(level)
            .compile()
            .unwrap_or_else(|errors| panic!("{op} {ty_name} {level:?}: {errors:?}"));
        let apply: unsafe extern "C" fn(*const u8, *const u8, *mut u8) -> u8 =
            unsafe { std::mem::transmute(artifact.function_address("apply").unwrap()) };
        let size = native_isa()
            .type_layout()
            .size_of(ty, &ModuleCtx::new(&native_isa()))
            .unwrap();
        for &(lhs, rhs, expected, overflow) in cases {
            let lhs_bytes = lhs.zext(Type::I256).as_i256().to_u256().to_little_endian();
            let rhs_bytes = rhs.zext(Type::I256).as_i256().to_u256().to_little_endian();
            let expected_bytes = expected
                .zext(Type::I256)
                .as_i256()
                .to_u256()
                .to_little_endian();
            let mut result = [0xa5u8; 32];
            let status =
                unsafe { apply(lhs_bytes.as_ptr(), rhs_bytes.as_ptr(), result.as_mut_ptr()) };
            assert_eq!(
                &result[..size],
                &expected_bytes[..size],
                "{op} {lhs:?} {rhs:?} {level:?}"
            );
            assert_eq!(status, u8::from(overflow), "{op} {lhs:?} {rhs:?} {level:?}");
        }
    }
}

#[test]
fn boolean_not_preserves_one_bit() {
    check_scalar_cases(
        "not",
        Type::I1,
        &[
            (false.into(), false.into(), true.into(), false),
            (true.into(), false.into(), false.into(), false),
        ],
    );
}

#[test]
fn scalar_shifts_preserve_overshift_semantics() {
    for (ty, width) in [
        (Type::I1, 1),
        (Type::I8, 8),
        (Type::I16, 16),
        (Type::I32, 32),
        (Type::I64, 64),
        (Type::I128, 128),
    ] {
        for op in ["shl", "shr", "sar"] {
            let mut cases = Vec::new();
            let counts = if ty == Type::I1 {
                vec![U256::zero(), U256::one()]
            } else {
                vec![
                    U256::zero(),
                    U256::from(width - 1),
                    U256::from(width),
                    U256::from(width + 1),
                    U256::from(255u16),
                ]
            };
            for lhs in [
                Immediate::zero(ty),
                Immediate::one(ty),
                Immediate::signed_min(ty),
                Immediate::all_one(ty),
            ] {
                for &count in &counts {
                    let rhs = Immediate::from_i256(I256::from(count), ty);
                    let expected = match op {
                        "shl" if count >= U256::from(width) => Immediate::zero(ty),
                        "shl" => lhs << rhs,
                        "shr" => lhs.lshr(rhs),
                        "sar" => lhs.ashr(rhs),
                        _ => unreachable!(),
                    };
                    cases.push((lhs, rhs, expected, false));
                }
                if ty == Type::I128 {
                    let rhs = Immediate::I128(1 << 64);
                    let expected = if op == "sar" {
                        lhs.ashr(rhs)
                    } else {
                        Immediate::zero(ty)
                    };
                    cases.push((lhs, rhs, expected, false));
                }
            }
            check_scalar_cases(op, ty, &cases);
        }
    }
}

#[test]
fn scalar_signed_division_wraps_overflow() {
    for ty in [Type::I8, Type::I16, Type::I32, Type::I64, Type::I128] {
        let min = Immediate::signed_min(ty);
        let minus_one = Immediate::all_one(ty);
        let cases = [
            (min, minus_one),
            (min, Immediate::one(ty)),
            (minus_one, minus_one),
            (
                Immediate::from_i256(I256::from(-17), ty),
                Immediate::from_i256(I256::from(3), ty),
            ),
        ]
        .map(|(lhs, rhs)| (lhs, rhs, lhs.sdiv(rhs), false));
        check_scalar_cases("sdiv", ty, &cases);
    }
}

#[test]
fn signed_i128_edge_operations_compile_and_execute() {
    let values = [
        i128::MIN,
        i128::MIN + 1,
        -(1 << 96),
        -(1 << 64),
        -3,
        -1,
        0,
        1,
        3,
        1 << 63,
        1 << 64,
        (1 << 96) + 1,
        i128::MAX - 1,
        i128::MAX,
    ];
    for op in [
        "snego", "saddsat", "ssubsat", "smulsat", "smulo", "umulo", "umulsat", "sdiv",
    ] {
        let mut cases = Vec::new();
        for lhs in values {
            for rhs in values {
                let (expected, overflow) = match op {
                    "snego" => lhs.overflowing_neg(),
                    "saddsat" => (lhs.saturating_add(rhs), false),
                    "ssubsat" => (lhs.saturating_sub(rhs), false),
                    "smulsat" => (lhs.saturating_mul(rhs), false),
                    "smulo" => lhs.overflowing_mul(rhs),
                    "umulo" => {
                        let (value, overflow) = (lhs as u128).overflowing_mul(rhs as u128);
                        (value as i128, overflow)
                    }
                    "umulsat" => ((lhs as u128).saturating_mul(rhs as u128) as i128, false),
                    "sdiv" if rhs == 0 => continue,
                    "sdiv" => (lhs.wrapping_div(rhs), false),
                    _ => unreachable!(),
                };
                cases.push((lhs.into(), rhs.into(), expected.into(), overflow));
            }
        }
        check_scalar_cases(op, Type::I128, &cases);
    }
}
