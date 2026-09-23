use sonatina_codegen::{
    Compile, compile::OptLevel, isa::cranelift::CraneliftJitBackend,
    transform::aggregate::ObjectAggregateAbi,
};
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

use super::parse_verified_native_module;

#[test]
fn synthetic_output_survives_mutating_byvalue_call_at_all_optimization_levels() {
    let source = r#"
func inline(never) private %mutate(v0.[i64; 8]) -> i64 {
block0:
    v1.objref<[i64; 8]> = obj.alloc [i64; 8];
    obj.store v1 v0;
    v2.objref<i64> = obj.index v1 0.i8;
    obj.store v2 99.i64;
    v3.i64 = obj.load v2;
    return v3;
}
func inline(never) private %make() -> objref<[i64; 8]> {
block0:
    v0.objref<[i64; 8]> = obj.alloc [i64; 8];
    v1.[i64; 8] = insert_value undef.[i64; 8] 0.i8 7.i64;
    obj.store v0 v1;
    v2.[i64; 8] = obj.load v0;
    v3.i64 = call %mutate v2;
    return v0;
}
func public %entry() -> i64 {
block0:
    v0.objref<[i64; 8]> = call %make;
    v1.objref<i64> = obj.index v0 0.i8;
    v2.i64 = obj.load v1;
    return v2;
}
"#;
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2] {
        let module = parse_verified_native_module(source);
        ObjectAggregateAbi::default().run(&module);
        let report = verify_module(&module, &VerifierConfig::for_level(VerificationLevel::Full));
        assert!(report.is_ok(), "{level:?}: {report}");
        let mut compiler = Compile::new(module, CraneliftJitBackend::new()).with_opt_level(level);
        let report = verify_module(
            compiler.optimize(),
            &VerifierConfig::for_level(VerificationLevel::Full),
        );
        assert!(report.is_ok(), "{level:?}: {report}");
        let artifact = compiler
            .compile()
            .expect("lowered output ABI should compile");
        let entry: unsafe extern "C" fn() -> i64 =
            unsafe { std::mem::transmute(artifact.function_address("entry").unwrap()) };
        assert_eq!(
            unsafe { entry() },
            7,
            "{level:?}: result buffer was mutated"
        );
    }
}
