use sonatina_codegen::{Compile, compile::OptLevel, isa::cranelift::CraneliftJitBackend};

use super::parse_verified_native_module;

#[test]
fn mutable_globals_are_shared_between_functions_and_calls() {
    let source = r#"
global public i64 $counter = 41;
global private i64 $zero;
func public %bump(v0.i64) -> i64 {
block0:
    v1.i64 = mload $counter i64;
    v2.i64 = add v1 v0;
    mstore $counter v2 i64;
    return v2;
}
func public %read(v0.i8) -> i64 {
block0:
    v1.i1 = is_zero v0;
    br v1 block1 block2;
block1:
    jump block3;
block2:
    jump block3;
block3:
    v2.*i64 = phi ($counter block1) ($zero block2);
    v3.i64 = mload v2 i64;
    return v3;
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
        let bump: unsafe extern "C" fn(i64) -> i64 =
            unsafe { std::mem::transmute(artifact.function_address("bump").unwrap()) };
        let read: unsafe extern "C" fn(u8) -> i64 =
            unsafe { std::mem::transmute(artifact.function_address("read").unwrap()) };
        assert_eq!(unsafe { read(0) }, 41);
        assert_eq!(unsafe { read(1) }, 0);
        assert_eq!(unsafe { bump(1) }, 42);
        assert_eq!(unsafe { bump(2) }, 44);
        assert_eq!(unsafe { read(0) }, 44);
    }
}

#[test]
fn static_initializers_preserve_native_contents_padding_and_alignment() {
    let mut record = vec![0u8; 80];
    record[0] = 7;
    record[16..32].copy_from_slice(&i128::MIN.to_le_bytes());
    record[32..38].copy_from_slice(&[1, 0, 255, 255, 3, 0]);
    record[48..80].fill(255);
    for (ty, initializer, expected, alignment) in [
        ("i1", "1".to_string(), vec![1], 1),
        ("i8", "-2".to_string(), vec![254], 1),
        ("i16", "-3".to_string(), (-3i16).to_le_bytes().to_vec(), 2),
        ("i32", "-4".to_string(), (-4i32).to_le_bytes().to_vec(), 4),
        ("i64", "-5".to_string(), (-5i64).to_le_bytes().to_vec(), 8),
        (
            "i128",
            i128::MIN.to_string(),
            i128::MIN.to_le_bytes().to_vec(),
            16,
        ),
        ("i256", "-1".to_string(), vec![255; 32], 16),
        ("*i8", "258".to_string(), 258u64.to_le_bytes().to_vec(), 8),
        (
            "@Record",
            format!("{{7, {}, [1, -1, 3], -1}}", i128::MIN),
            record,
            16,
        ),
        ("[i128; 0]", "[]".to_string(), vec![], 16),
    ] {
        let const_reader = if ty == "*i8" {
            String::new()
        } else {
            let load = if ty.starts_with('i') {
                format!("v2.{ty} = const.load v1;\n    mstore v0 v2 {ty};")
            } else {
                format!(
                    "v2.objref<{ty}> = obj.alloc {ty};\n    obj.init.const v2 v1;\n    v3.{ty} = obj.load v2;\n    mstore v0 v3 {ty};"
                )
            };
            format!(
                r#"
func public %via_const(v0.*{ty}) {{
block0:
    v1.constref<{ty}> = const.ref $data;
    {load}
    return;
}}
"#
            )
        };
        let source = format!(
            r#"
type @Record = {{i8, i128, [i16; 3], i256}};
global public const {ty} $data = {initializer};
func public %via_address(v0.*{ty}) {{
block0:
    v1.{ty} = mload $data {ty};
    mstore v0 v1 {ty};
    return;
}}
{const_reader}
func public %address() -> *i8 {{
block0:
    v0.*i8 = bitcast $data *i8;
    return v0;
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
            .unwrap();
            let address: unsafe extern "C" fn() -> *const u8 =
                unsafe { std::mem::transmute(artifact.function_address("address").unwrap()) };
            assert_eq!(
                unsafe { address() } as usize % alignment,
                0,
                "{ty} {level:?}"
            );
            assert_eq!(unsafe { address() }, unsafe { address() });
            for name in ["via_address", "via_const"] {
                if name == "via_const" && const_reader.is_empty() {
                    continue;
                }
                let read: unsafe extern "C" fn(*mut u8) =
                    unsafe { std::mem::transmute(artifact.function_address(name).unwrap()) };
                let mut output = [0xa5; 96];
                unsafe { read(output.as_mut_ptr()) };
                assert_eq!(
                    &output[..expected.len()],
                    &expected,
                    "{name} {ty} {level:?}"
                );
                assert!(output[expected.len()..].iter().all(|&byte| byte == 0xa5));
            }
        }
    }
}

#[test]
fn undef_materializes_zero_for_scalar_pointer_and_aggregate_values() {
    for (ty, size) in [
        ("i1", 1),
        ("i8", 1),
        ("i16", 2),
        ("i32", 4),
        ("i64", 8),
        ("i128", 16),
        ("i256", 32),
        ("*i8", 8),
        ("[i8; 15]", 15),
        ("[i128; 0]", 0),
        ("@Padded", 32),
    ] {
        let source = format!(
            r#"
type @Padded = {{i8, i128}};
func private %make() -> {ty} {{
block0:
    return undef.{ty};
}}
func public %write(v0.*{ty}) {{
block0:
    v1.{ty} = call %make;
    mstore v0 v1 {ty};
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
            .unwrap();
            let write: unsafe extern "C" fn(*mut u8) =
                unsafe { std::mem::transmute(artifact.function_address("write").unwrap()) };
            let mut output = [0xa5; 48];
            unsafe { write(output.as_mut_ptr()) };
            assert!(
                output[..size].iter().all(|&byte| byte == 0),
                "{ty} {level:?}"
            );
            assert!(output[size..].iter().all(|&byte| byte == 0xa5));
        }
    }
}

#[test]
fn partial_aggregate_insert_keeps_undef_fields_and_padding_zero() {
    let source = r#"
type @Padded = {i8, i128};
func public %write(v0.*@Padded) {
block0:
    v1.@Padded = insert_value undef.@Padded 0.i64 7.i8;
    mstore v0 v1 @Padded;
    return;
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
        let write: unsafe extern "C" fn(*mut u8) =
            unsafe { std::mem::transmute(artifact.function_address("write").unwrap()) };
        let mut output = [0xa5; 32];
        unsafe { write(output.as_mut_ptr()) };
        assert_eq!(output[0], 7);
        assert!(output[1..].iter().all(|&byte| byte == 0), "{level:?}");
    }
}
