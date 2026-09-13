use sonatina_codegen::{Compile, compile::OptLevel, isa::cranelift::CraneliftJitBackend};
use sonatina_ir::{I256, Immediate, Type, U256};

use super::{parse_native_module, parse_verified_native_module};

#[test]
fn bitcasts_preserve_contents_across_native_representations() {
    for (from, to, size) in [
        ("i1", "[i8; 1]", 1),
        ("i8", "[i8; 1]", 1),
        ("i16", "[i8; 2]", 2),
        ("i32", "[i8; 4]", 4),
        ("i64", "[i64; 1]", 8),
        ("i128", "[i8; 16]", 16),
        ("i256", "[i8; 32]", 32),
        ("i64", "@Word", 8),
        ("i128", "@Pair", 16),
        ("*i8", "@Word", 8),
        ("*i8", "i64", 8),
        ("*i8", "*i64", 8),
        ("[i8; 16]", "[i128; 1]", 16),
        ("[i8; 32]", "@Padded", 32),
        ("[i8; 48]", "[@Pair; 3]", 48),
        ("[i8; 0]", "[i128; 0]", 0),
    ] {
        for (from, to) in [(from, to), (to, from)] {
            let source = format!(
                r#"
type @Word = {{i64}};
type @Pair = {{i64, i64}};
type @Padded = {{i8, i128}};
func private %cast(v0.{from}) -> {to} {{
block0:
    v1.{to} = bitcast v0 {to};
    return v1;
}}
func public %apply(v0.*{from}, v1.*{to}) {{
block0:
    v2.{from} = mload v0 {from};
    v3.{to} = call %cast v2;
    mstore v1 v3 {to};
    return;
}}
"#
            );
            for level in [OptLevel::O0, OptLevel::O2] {
                let artifact = Compile::new(
                    parse_verified_native_module(&source),
                    CraneliftJitBackend::new(),
                )
                .with_opt_level(level)
                .compile()
                .unwrap_or_else(|errors| panic!("{from} -> {to} {level:?}: {errors:?}"));
                let apply: unsafe extern "C" fn(*const u8, *mut u8) =
                    unsafe { std::mem::transmute(artifact.function_address("apply").unwrap()) };
                for seed in [0u8, 1, 2, 3, 127, 255] {
                    let input: [u8; 64] =
                        std::array::from_fn(|index| seed.wrapping_add(index as u8));
                    let mut expected = input;
                    if from == "i1" || to == "i1" {
                        expected[0] &= 1;
                    }
                    let mut output = [0xa5; 64];
                    unsafe { apply(input.as_ptr(), output.as_mut_ptr()) };
                    assert_eq!(
                        &output[..size],
                        &expected[..size],
                        "{from} -> {to} {level:?} {seed}"
                    );
                    assert!(output[size..].iter().all(|&byte| byte == 0xa5));
                }
            }
        }
    }
}

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
        let module = parse_verified_native_module(&source);
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
                "bitcast" => input.bitcast(to),
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
fn boolean_bitcasts_keep_only_the_low_bit() {
    let bytes: Vec<_> = (i8::MIN..=i8::MAX).map(Immediate::I8).collect();
    check_cast("bitcast", Type::I8, Type::I1, &bytes);
    check_cast("bitcast", Type::I1, Type::I8, &[false.into(), true.into()]);
}

#[test]
fn pointer_to_boolean_keeps_only_the_low_bit() {
    let source = r#"
func public %low_bit(v0.*i8) -> i8 {
block0:
    v1.i1 = ptr_to_int v0 i1;
    v2.i8 = zext v1 i8;
    return v2;
}
"#;
    for level in [OptLevel::O0, OptLevel::O2] {
        let artifact = Compile::new(
            parse_verified_native_module(source),
            CraneliftJitBackend::new(),
        )
        .with_opt_level(level)
        .compile()
        .unwrap();
        let low_bit: unsafe extern "C" fn(*const u8) -> u8 =
            unsafe { std::mem::transmute(artifact.function_address("low_bit").unwrap()) };
        for address in [0usize, 1, 2, 3, 255, 256, 257, 258, usize::MAX] {
            assert_eq!(
                unsafe { low_bit(address as *const u8) },
                (address & 1) as u8,
                "{address:#x} {level:?}"
            );
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
