use sonatina_codegen::{Compile, compile::OptLevel, isa::cranelift::CraneliftJitBackend};

use super::parse_verified_native_module;

#[test]
fn selecting_between_borrowed_arguments_preserves_mutation_aliases() {
    let source = r#"
func private %choose(v0.i1, v1.objref<i64>, v2.objref<i64>) -> objref<i64> {
block0:
    br v0 block1 block2;
block1:
    jump block3;
block2:
    jump block3;
block3:
    v3.objref<i64> = phi (v1 block1) (v2 block2);
    return v3;
}
func public %exercise(v0.i8) -> i64 {
block0:
    v1.objref<i64> = obj.alloc i64;
    v2.objref<i64> = obj.alloc i64;
    obj.store v1 11.i64;
    obj.store v2 22.i64;
    v3.i1 = trunc v0 i1;
    v4.objref<i64> = call %choose v3 v1 v2;
    obj.store v4 99.i64;
    v5.i64 = obj.load v1;
    v6.i64 = obj.load v2;
    v7.i64 = mul v5 100.i64;
    v8.i64 = add v7 v6;
    return v8;
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
        let exercise: unsafe extern "C" fn(u8) -> i64 =
            unsafe { std::mem::transmute(artifact.function_address("exercise").unwrap()) };
        assert_eq!(unsafe { exercise(0) }, 1199, "{level:?}");
        assert_eq!(unsafe { exercise(1) }, 9922, "{level:?}");
    }
}

#[test]
fn mixed_returns_preserve_fresh_lifetimes_and_borrowed_projection_aliases() {
    for separate_returns in [true, false] {
        let choose = if separate_returns {
            r#"block0:
    br v0 block1 block2;
block1:
    v3.objref<i64> = obj.alloc i64;
    obj.store v3 v2;
    return v3;
block2:
    v4.objref<i64> = obj.index v1 1.i64;
    return v4;"#
        } else {
            r#"block0:
    br v0 block1 block2;
block1:
    v3.objref<i64> = obj.alloc i64;
    obj.store v3 v2;
    jump block3;
block2:
    v4.objref<i64> = obj.index v1 1.i64;
    jump block3;
block3:
    v5.objref<i64> = phi (v3 block1) (v4 block2);
    return v5;"#
        };
        let source = format!(
            r#"
func private %choose(v0.i1, v1.objref<[i64; 2]>, v2.i64) -> objref<i64> {{
{choose}
}}
func private %forward(v0.i1, v1.objref<[i64; 2]>, v2.i64) -> objref<i64> {{
block0:
    v3.objref<i64> = call %choose v0 v1 v2;
    return v3;
}}
func public %exercise(v0.i8, v1.i8) -> i64 {{
block0:
    v2.objref<[i64; 2]> = obj.alloc [i64; 2];
    v3.objref<i64> = obj.index v2 1.i64;
    obj.store v3 42.i64;
    v4.i1 = trunc v0 i1;
    v5.i1 = trunc v1 i1;
    v6.objref<i64> = call %forward v4 v2 111.i64;
    v7.objref<i64> = call %forward v5 v2 222.i64;
    v8.i64 = obj.load v6;
    v9.i64 = obj.load v7;
    v10.i64 = add v8 v9;
    obj.store v6 10.i64;
    v11.i64 = obj.load v7;
    v12.i64 = obj.load v3;
    v13.i64 = mul v10 10000.i64;
    v14.i64 = mul v11 100.i64;
    v15.i64 = add v13 v14;
    v16.i64 = add v15 v12;
    return v16;
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
            let exercise: unsafe extern "C" fn(u8, u8) -> i64 =
                unsafe { std::mem::transmute(artifact.function_address("exercise").unwrap()) };
            for first in [0, 1] {
                for second in [0, 1] {
                    let lhs = if first == 1 { 111 } else { 42 };
                    let rhs = if second == 1 { 222 } else { 42 };
                    let borrowed = if first == 1 { 42 } else { 10 };
                    let second_after = if second == 1 { 222 } else { borrowed };
                    let expected = (lhs + rhs) * 10000 + second_after * 100 + borrowed;
                    assert_eq!(
                        unsafe { exercise(first, second) },
                        expected,
                        "{first} {second} {level:?}"
                    );
                }
            }
        }
    }
}
