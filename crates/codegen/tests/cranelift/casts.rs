use sonatina_codegen::{Compile, compile::OptLevel, isa::cranelift::CraneliftJitBackend};
use sonatina_ir::{I256, Immediate, Type, U256};

use super::parse_native_module;

fn check_cast(op: &str, from: Type, to: Type, inputs: &[Immediate]) {
    let from_name = format!("{from:?}").to_lowercase();
    let to_name = format!("{to:?}").to_lowercase();
    let source = format!(
        r#"
func public %cast(v0.*{from_name}, v1.*{to_name}) {{
block0:
    v2.{from_name} = mload v0 {from_name};
    v3.{to_name} = {op} v2 {to_name};
    mstore v1 v3 {to_name};
    return;
}}
"#
    );
    for level in [OptLevel::O0, OptLevel::O2] {
        let module = parse_native_module(&source);
        let size = module.ctx.size_of(to).unwrap();
        let artifact = Compile::new(module, CraneliftJitBackend::new())
            .with_opt_level(level)
            .compile()
            .unwrap_or_else(|errors| panic!("{op} {from:?} -> {to:?} {level:?}: {errors:?}"));
        let cast: unsafe extern "C" fn(*const u8, *mut u8) =
            unsafe { std::mem::transmute(artifact.function_address("cast").unwrap()) };
        for &input in inputs {
            let expected = match op {
                "sext" => input.sext(to),
                "zext" => input.zext(to),
                "trunc" => input.trunc(to),
                _ => unreachable!(),
            }
            .zext(Type::I256)
            .as_i256()
            .to_u256()
            .to_little_endian();
            let bytes = input
                .zext(Type::I256)
                .as_i256()
                .to_u256()
                .to_little_endian();
            let mut result = [0xa5; 32];
            unsafe { cast(bytes.as_ptr(), result.as_mut_ptr()) };
            assert_eq!(
                &result[..size],
                &expected[..size],
                "{op} {input:?} -> {to:?} {level:?}"
            );
            assert!(result[size..].iter().all(|&byte| byte == 0xa5));
        }
    }
}

#[test]
fn i128_extensions_preserve_both_words() {
    let inputs = [
        i128::MIN,
        i128::MIN + 1,
        -(1 << 96) + 17,
        -1,
        0,
        1,
        (1 << 63) + 1,
        1 << 64,
        (1 << 96) + 17,
        i128::MAX,
    ]
    .map(Immediate::I128);
    for op in ["zext", "sext"] {
        check_cast(op, Type::I128, Type::I256, &inputs);
    }
}

#[test]
fn narrow_extensions_to_wide_integers_match_ir_semantics() {
    for from in [Type::I8, Type::I16, Type::I32, Type::I64] {
        let inputs = [
            Immediate::zero(from),
            Immediate::one(from),
            Immediate::signed_min(from),
            Immediate::signed_max(from),
            Immediate::all_one(from),
        ];
        for to in [Type::I128, Type::I256] {
            for op in ["zext", "sext"] {
                check_cast(op, from, to, &inputs);
            }
        }
    }
}

#[test]
fn boolean_extensions_match_ir_semantics() {
    for to in [
        Type::I8,
        Type::I16,
        Type::I32,
        Type::I64,
        Type::I128,
        Type::I256,
    ] {
        for op in ["zext", "sext"] {
            check_cast(op, Type::I1, to, &[false.into(), true.into()]);
        }
    }
}

#[test]
fn integer_truncations_keep_exactly_the_destination_bits() {
    let bits = [
        U256::zero(),
        U256::one(),
        U256::from(2u8),
        U256::from(255u16),
        U256::one() << 64,
        (U256::one() << 96) + U256::from(2u8),
        U256::one() << 128,
        (U256::one() << 192) + U256::one(),
        U256::MAX,
    ];
    for from in [
        Type::I8,
        Type::I16,
        Type::I32,
        Type::I64,
        Type::I128,
        Type::I256,
    ] {
        let inputs = bits.map(|bits| Immediate::from_i256(I256::from(bits), from));
        for to in [
            Type::I1,
            Type::I8,
            Type::I16,
            Type::I32,
            Type::I64,
            Type::I128,
        ] {
            if to < from {
                check_cast("trunc", from, to, &inputs);
            }
        }
    }
}

#[test]
fn i128_pointer_casts_preserve_the_native_address_width() {
    let source = r#"
func public %widen(v0.*i8, v1.*i128) {
block0:
    v2.i128 = ptr_to_int v0 i128;
    mstore v1 v2 i128;
    return;
}
func public %narrow(v0.*i128) -> *i8 {
block0:
    v1.i128 = mload v0 i128;
    v2.*i8 = int_to_ptr v1 *i8;
    return v2;
}
"#;
    for level in [OptLevel::O0, OptLevel::O2] {
        let artifact = Compile::new(parse_native_module(source), CraneliftJitBackend::new())
            .with_opt_level(level)
            .compile()
            .expect("i128 pointer casts should compile");
        let widen: unsafe extern "C" fn(*const u8, *mut u8) =
            unsafe { std::mem::transmute(artifact.function_address("widen").unwrap()) };
        let narrow: unsafe extern "C" fn(*const u8) -> *const u8 =
            unsafe { std::mem::transmute(artifact.function_address("narrow").unwrap()) };
        let value = 42u8;
        let pointer = &value as *const u8;
        let mut result = [0xa5; 16];
        unsafe { widen(pointer, result.as_mut_ptr()) };
        assert_eq!(u128::from_le_bytes(result), pointer as usize as u128);
        for high in [0, 1, u64::MAX] {
            let bits = (pointer as usize as u128) | (u128::from(high) << 64);
            assert_eq!(unsafe { narrow(bits.to_le_bytes().as_ptr()) }, pointer);
        }
    }
}
