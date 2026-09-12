use sonatina_codegen::{Compile, compile::OptLevel, isa::cranelift::CraneliftJitBackend};

use super::parse_native_module;

#[test]
fn object_and_constant_indices_zero_extend_narrow_integers() {
    let values = (0..256)
        .map(|i| (1000 + i).to_string())
        .collect::<Vec<_>>()
        .join(", ");
    let source = format!(
        r#"
global private const [i64; 256] $values = [{values}];
func public %read_const(v0.i8) -> i64 {{
block0:
    v1.constref<[i64; 256]> = const.ref $values;
    v2.constref<i64> = const.index v1 v0;
    v3.i64 = const.load v2;
    return v3;
}}
func public %read_object(v0.i8) -> i64 {{
block0:
    v1.objref<[i64; 256]> = obj.alloc [i64; 256];
    v2.objref<i64> = obj.index v1 128.i64;
    obj.store v2 1128.i64;
    v3.objref<i64> = obj.index v1 255.i64;
    obj.store v3 1255.i64;
    v4.objref<i64> = obj.index v1 v0;
    v5.i64 = obj.load v4;
    return v5;
}}
"#
    );
    for level in [OptLevel::O0, OptLevel::O2] {
        let artifact = Compile::new(parse_native_module(&source), CraneliftJitBackend::new())
            .with_opt_level(level)
            .compile()
            .expect("unsigned index functions should compile");
        for name in ["read_const", "read_object"] {
            let read: unsafe extern "C" fn(u8) -> i64 =
                unsafe { std::mem::transmute(artifact.function_address(name).unwrap()) };
            for index in [128, 255] {
                assert_eq!(
                    unsafe { read(index) },
                    1000 + i64::from(index),
                    "{name} {level:?}"
                );
            }
        }
    }
}

#[test]
fn gep_indices_still_sign_extend_narrow_integers() {
    let source = r#"
func public %read(v0.*i64, v1.i8) -> i64 {
block0:
    v2.*i64 = gep v0 v1;
    v3.i64 = mload v2 i64;
    return v3;
}
"#;
    for level in [OptLevel::O0, OptLevel::O2] {
        let artifact = Compile::new(parse_native_module(source), CraneliftJitBackend::new())
            .with_opt_level(level)
            .compile()
            .expect("signed GEP should compile");
        let read: unsafe extern "C" fn(*const i64, i8) -> i64 =
            unsafe { std::mem::transmute(artifact.function_address("read").unwrap()) };
        let values = [11i64, 22, 33];
        assert_eq!(unsafe { read(values.as_ptr().add(1), -1) }, 11);
        assert_eq!(unsafe { read(values.as_ptr().add(1), 1) }, 33);
    }
}
