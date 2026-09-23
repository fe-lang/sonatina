use sonatina_codegen::{
    Compile, compile::OptLevel, isa::cranelift::CraneliftJitBackend,
    transform::aggregate::ObjectAggregateAbi,
};
use sonatina_ir::ir_writer::ModuleWriter;
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

use super::{alias_execution, parse_verified_native_module};

#[test]
fn captured_alias_retains_native_stack_lifetime_rejection() {
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2] {
        let mut compiler = Compile::new(
            parse_verified_native_module(alias_execution::CAPTURE_SOURCE),
            CraneliftJitBackend::new(),
        )
        .with_opt_level(level);
        let report = verify_module(
            compiler.optimize(),
            &VerifierConfig::for_level(VerificationLevel::Full),
        );
        assert!(report.is_ok(), "{level:?}: {report}");
        let errors = match compiler.compile() {
            Ok(_) => panic!("native captured stack reference unexpectedly accepted"),
            Err(errors) => errors,
        };
        assert!(
            errors.iter().any(|error| error.to_string().contains(
                "native reference lifetime in captured_alias: unproven escape of local object"
            )),
            "{level:?}: {errors:?}"
        );
    }
}

#[test]
fn object_alias_execution_matrix_at_all_optimization_levels() {
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2] {
        let mut compiler = Compile::new(
            parse_verified_native_module(alias_execution::SOURCE),
            CraneliftJitBackend::new(),
        )
        .with_opt_level(level);
        let module = compiler.optimize();
        let report = verify_module(module, &VerifierConfig::for_level(VerificationLevel::Full));
        assert!(report.is_ok(), "{level:?}: {report}");
        let text = ModuleWriter::new(module).dump_string();
        assert_eq!(text.matches("call %read_after_write").count(), 3, "{text}");
        let artifact = compiler.compile().expect("alias matrix should compile");
        for &(name, expected) in alias_execution::CASES {
            let entry: unsafe extern "C" fn() -> i64 =
                unsafe { std::mem::transmute(artifact.function_address(name).unwrap()) };
            assert_eq!(unsafe { entry() }, expected, "{level:?}: {name}");
        }
    }
}

// T01/T02: the same generic no-inline callee is used by both callers.
const MIXED_CALLERS: &str = r#"
func inline(never) private %read_after_write(v0.objref<i64>, v1.objref<i64>) -> i64 {
block0:
    obj.store v1 22.i64;
    v2.i64 = obj.load v0;
    return v2;
}
func public %aliased() -> i64 {
block0:
    v0.objref<i64> = obj.alloc i64;
    obj.store v0 11.i64;
    v1.i64 = call %read_after_write v0 v0;
    return v1;
}
func public %distinct() -> i64 {
block0:
    v0.objref<i64> = obj.alloc i64;
    v1.objref<i64> = obj.alloc i64;
    obj.store v0 11.i64;
    obj.store v1 33.i64;
    v2.i64 = call %read_after_write v0 v1;
    return v2;
}
"#;

#[test]
fn incoming_aliases_execute_correctly_at_all_optimization_levels() {
    let mut results = Vec::new();
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2] {
        let mut compiler = Compile::new(
            parse_verified_native_module(MIXED_CALLERS),
            CraneliftJitBackend::new(),
        )
        .with_opt_level(level);
        let module = compiler.optimize();
        let report = verify_module(module, &VerifierConfig::for_level(VerificationLevel::Full));
        assert!(report.is_ok(), "{level:?}: {report}");
        let text = ModuleWriter::new(module).dump_string();
        assert_eq!(text.matches("call %read_after_write").count(), 2, "{text}");
        let artifact = compiler
            .compile()
            .expect("mixed alias callers should compile");
        for (name, expected) in [("aliased", 22), ("distinct", 11)] {
            let entry: unsafe extern "C" fn() -> i64 =
                unsafe { std::mem::transmute(artifact.function_address(name).unwrap()) };
            results.push((level, name, unsafe { entry() }, expected));
        }
    }
    assert!(
        results
            .iter()
            .all(|(_, _, actual, expected)| actual == expected),
        "T01/T02: {results:?}"
    );
}

#[test]
fn closed_disjoint_callers_promote_without_inlining_at_optimized_levels() {
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2] {
        let mut compiler = Compile::new(
            parse_verified_native_module(alias_execution::DISJOINT_SOURCE),
            CraneliftJitBackend::new(),
        )
        .with_opt_level(level);
        let module = compiler.optimize();
        let report = verify_module(module, &VerifierConfig::for_level(VerificationLevel::Full));
        assert!(report.is_ok(), "{report}");
        let text = ModuleWriter::new(module).dump_string();
        assert_eq!(text.matches("call %read_after_write").count(), 1, "{text}");
        if level != OptLevel::O0 {
            let read = text.find("obj.load").unwrap();
            let write = text.find("obj.store").unwrap();
            assert!(read < write, "{level:?}: {text}");
        }
        let artifact = compiler.compile().unwrap();
        let entry: unsafe extern "C" fn() -> i64 =
            unsafe { std::mem::transmute(artifact.function_address("disjoint_only").unwrap()) };
        assert_eq!(unsafe { entry() }, 11, "{level:?}");
    }
}

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
