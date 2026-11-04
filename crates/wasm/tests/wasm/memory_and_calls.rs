//! Calls, imports, exports and scalar access to linear memory.

use sonatina_codegen::{Backend, BackendOptions};
use sonatina_wasm::WasmBackend;
use wasmparser::{Parser, Payload, TypeRef};
use wasmtime::Val;

use crate::harness::{Machine, compile_valid, i32s, parse};

fn machine(source: &str) -> Machine {
    Machine::new(&compile_valid(&parse(source)))
}

#[test]
fn direct_calls_resolve_in_any_definition_order() {
    // `main` precedes its callees, and `fact` calls itself.
    let source = "func public %main(v0.i64) -> i64 {
    block0:
        v1.i64 = call %fact v0;
        v2.i64 = call %twice v1;
        return v2;
}
func private %twice(v0.i64) -> i64 {
    block0:
        v1.i64 = add v0 v0;
        return v1;
}
func private %fact(v0.i64) -> i64 {
    block0:
        v1.i1 = is_zero v0;
        br v1 block1 block2;
    block1:
        return 1.i64;
    block2:
        v2.i64 = sub v0 1.i64;
        v3.i64 = call %fact v2;
        v4.i64 = mul v0 v3;
        return v4;
}
";
    let mut machine = machine(source);
    let main = machine.func("main");
    for (n, want) in [(0i64, 2i64), (1, 2), (5, 240), (10, 7_257_600)] {
        assert_eq!(machine.call(&main, &[Val::I64(n)])[0].unwrap_i64(), want);
    }
}

#[test]
fn multiple_results_keep_their_order_and_types() {
    let source = "func private %split(v0.i64) -> (i32, i64, i1, i8) {
    block0:
        v1.i32 = trunc v0 i32;
        v2.i64 = shr 32.i64 v0;
        v3.i1 = trunc v0 i1;
        v4.i8 = trunc v0 i8;
        return (v1, v2, v3, v4);
}
func public %forward(v0.i64) -> (i8, i1, i64, i32) {
    block0:
        (v1.i32, v2.i64, v3.i1, v4.i8) = call %split v0;
        return (v4, v3, v2, v1);
}
func public %unit_call(v0.i32) -> i32 {
    block0:
        call %nothing v0;
        return v0;
}
func private %nothing(v0.i32) {
    block0:
        return;
}
";
    let mut machine = machine(source);
    let forward = machine.func("forward");
    let results = machine.call(&forward, &[Val::I64(0x0000_0102_0304_0507)]);
    assert_eq!(results[0].unwrap_i32(), 0x07);
    assert_eq!(results[1].unwrap_i32(), 1);
    assert_eq!(results[2].unwrap_i64(), 0x0102);
    assert_eq!(results[3].unwrap_i32(), 0x0304_0507);
    let unit_call = machine.func("unit_call");
    assert_eq!(i32s(&machine.call(&unit_call, &[Val::I32(9)])), [9]);
}

#[test]
fn only_public_functions_and_the_memory_are_exported() {
    let source = "func private %hidden() -> i32 {
    block0:
        return 1.i32;
}
func public %shown() -> i32 {
    block0:
        v0.i32 = call %hidden;
        return v0;
}
";
    let module = parse(source);
    let artifact = WasmBackend::new()
        .compile_module(&module, &BackendOptions::default())
        .unwrap();
    assert_eq!(artifact.exported_functions(), ["shown"]);
    let mut machine = Machine::new(artifact.as_bytes());
    assert!(machine.has_export("shown"));
    assert!(machine.has_export("memory"));
    assert!(!machine.has_export("hidden"));
}

fn imports(bytes: &[u8]) -> Vec<(String, String)> {
    let mut found = Vec::new();
    for payload in Parser::new(0).parse_all(bytes) {
        if let Payload::ImportSection(section) = payload.unwrap() {
            for import in section.into_imports() {
                let import = import.unwrap();
                assert!(
                    matches!(import.ty, TypeRef::Func(_)),
                    "only functions are imported"
                );
                found.push((import.module.to_string(), import.name.to_string()));
            }
        }
    }
    found
}

const IMPORTS: &str = "func external %host_add(v0.i32, v1.i32) -> i32 {
}
func external %host_byte() -> i8 {
}
func external %host_pair(v0.i64) -> (i64, i1) {
}
func external %host_log(v0.i32) {
}
func public %run(v0.i32, v1.i32) -> i32 {
    block0:
        v2.i32 = call %host_add v0 v1;
        call %host_log v2;
        v3.i8 = call %host_byte;
        v4.i32 = zext v3 i32;
        v5.i32 = add v2 v4;
        return v5;
}
func public %pair(v0.i64) -> (i64, i1) {
    block0:
        (v1.i64, v2.i1) = call %host_pair v0;
        return (v1, v2);
}
";

#[test]
fn extern_functions_are_scalar_imports() {
    let module = parse(IMPORTS);
    let bytes = compile_valid(&module);
    let found = imports(&bytes);
    assert_eq!(
        found,
        ["host_add", "host_byte", "host_pair", "host_log"]
            .map(|name| ("env".to_string(), name.to_string())),
    );

    let log = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
    let recorded = log.clone();
    let mut machine = Machine::with_imports(&bytes, |linker| {
        linker
            .func_wrap("env", "host_add", |a: i32, b: i32| a.wrapping_add(b))
            .unwrap();
        // The host returns bits above the width of an i8 result.
        linker.func_wrap("env", "host_byte", || 0x1ffi32).unwrap();
        linker
            .func_wrap("env", "host_pair", |x: i64| (x + 1, 1i32))
            .unwrap();
        linker
            .func_wrap("env", "host_log", move |x: i32| {
                recorded.lock().unwrap().push(x)
            })
            .unwrap();
    });
    let run = machine.func("run");
    // 3 + 4, plus the canonical byte 0xff.
    assert_eq!(
        i32s(&machine.call(&run, &[Val::I32(3), Val::I32(4)])),
        [7 + 0xff]
    );
    assert_eq!(*log.lock().unwrap(), [7]);
    let pair = machine.func("pair");
    let results = machine.call(&pair, &[Val::I64(41)]);
    assert_eq!((results[0].unwrap_i64(), results[1].unwrap_i32()), (42, 1));
}

#[test]
fn the_import_module_can_be_chosen() {
    let module = parse(IMPORTS);
    let artifact = WasmBackend::new()
        .with_import_module("fe")
        .compile_module(&module, &BackendOptions::default())
        .unwrap();
    assert!(
        imports(artifact.as_bytes())
            .iter()
            .all(|(module, _)| module == "fe")
    );
}

fn typed_memory_module() -> String {
    let mut source = String::new();
    for ty in ["i8", "i16", "i32", "i64"] {
        source += &format!(
            "func public %store_{ty}(v0.i32, v1.{ty}) {{
    block0:
        mstore v0 v1 {ty};
        return;
}}
func public %load_{ty}(v0.i32) -> {ty} {{
    block0:
        v1.{ty} = mload v0 {ty};
        return v1;
}}
"
        );
    }
    source += "func public %load_i1(v0.i32) -> i1 {
    block0:
        v1.i1 = mload v0 i1;
        return v1;
}
func public %store_i1(v0.i32, v1.i1) {
    block0:
        mstore v0 v1 i1;
        return;
}
func public %through_pointer(v0.i32, v1.i64) -> i64 {
    block0:
        v2.*i64 = int_to_ptr v0 *i64;
        mstore v2 v1 i64;
        v3.i32 = ptr_to_int v2 i32;
        v4.i64 = mload v2 i64;
        v5.i1 = eq v3 v0;
        v6.i64 = zext v5 i64;
        v7.i64 = add v4 v6;
        return v7;
}
";
    source
}

#[test]
fn scalar_loads_and_stores_use_little_endian_linear_memory() {
    let mut machine = machine(&typed_memory_module());
    let (store_i64, load_i64) = (machine.func("store_i64"), machine.func("load_i64"));
    machine.call(&store_i64, &[Val::I32(64), Val::I64(0x0102_0304_0506_0708)]);
    assert_eq!(machine.read(64, 8), [8, 7, 6, 5, 4, 3, 2, 1]);
    assert_eq!(
        machine.call(&load_i64, &[Val::I32(64)])[0].unwrap_i64(),
        0x0102_0304_0506_0708
    );

    // Narrow loads read exactly their width and zero-extend; an unaligned
    // address is valid.
    let (load_i8, load_i16, load_i32) = (
        machine.func("load_i8"),
        machine.func("load_i16"),
        machine.func("load_i32"),
    );
    assert_eq!(i32s(&machine.call(&load_i8, &[Val::I32(64)])), [8]);
    assert_eq!(i32s(&machine.call(&load_i16, &[Val::I32(65)])), [0x0607]);
    assert_eq!(
        i32s(&machine.call(&load_i32, &[Val::I32(66)])),
        [0x0304_0506]
    );

    // Narrow stores write exactly their width.
    machine.write(128, &[0xee; 8]);
    let (store_i8, store_i16) = (machine.func("store_i8"), machine.func("store_i16"));
    machine.call(&store_i8, &[Val::I32(128), Val::I32(0x1ab)]);
    machine.call(&store_i16, &[Val::I32(130), Val::I32(0x1_2345)]);
    assert_eq!(machine.read(128, 6), [0xab, 0xee, 0x45, 0x23, 0xee, 0xee]);

    // An i1 load keeps the low bit of the byte.
    let (load_i1, store_i1) = (machine.func("load_i1"), machine.func("store_i1"));
    machine.write(200, &[0, 1, 2, 3, 0xff]);
    for (offset, want) in [(0, 0), (1, 1), (2, 0), (3, 1), (4, 1)] {
        assert_eq!(
            i32s(&machine.call(&load_i1, &[Val::I32(200 + offset)])),
            [want]
        );
    }
    machine.call(&store_i1, &[Val::I32(210), Val::I32(1)]);
    assert_eq!(machine.read(210, 1), [1]);
}

#[test]
fn pointers_are_32_bit_offsets() {
    let mut machine = machine(&typed_memory_module());
    let through_pointer = machine.func("through_pointer");
    let result = machine.call(&through_pointer, &[Val::I32(300), Val::I64(1000)]);
    assert_eq!(result[0].unwrap_i64(), 1001);
    assert_eq!(machine.read(300, 8), 1000i64.to_le_bytes());
}

#[test]
fn accesses_outside_the_memory_trap() {
    let mut machine = machine(&typed_memory_module());
    let load_i32 = machine.func("load_i32");
    // One page is 65536 bytes.
    assert!(machine.try_call(&load_i32, &[Val::I32(65532)]).is_ok());
    assert!(machine.try_call(&load_i32, &[Val::I32(65533)]).is_err());
    assert!(machine.try_call(&load_i32, &[Val::I32(-1)]).is_err());
}
