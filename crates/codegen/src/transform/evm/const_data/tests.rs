use super::ConstDataLower;
use crate::{
    isa::evm::EvmBackend,
    object::{CompileOptions, SymbolId, compile_all_objects},
};
use sonatina_ir::{
    global_variable::GvInitializer,
    ir_writer::{FuncWriter, ModuleWriter},
    isa::evm::Evm,
    module::FuncRef,
};
use sonatina_parser::parse_module;
use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

fn parse(src: &str) -> sonatina_parser::ParsedModule {
    parse_module(src).unwrap_or_else(|errs| panic!("parse failed: {errs:?}"))
}

fn find_func_ref(parsed: &sonatina_parser::ParsedModule, name: &str) -> FuncRef {
    parsed
        .module
        .funcs()
        .into_iter()
        .find(|&func_ref| {
            parsed
                .module
                .ctx
                .func_sig(func_ref, |sig| sig.name() == name)
        })
        .unwrap_or_else(|| panic!("function `{name}` should exist"))
}

fn test_backend() -> EvmBackend {
    let triple = TargetTriple::new(
        Architecture::Evm,
        Vendor::Ethereum,
        OperatingSystem::Evm(EvmVersion::Osaka),
    );
    EvmBackend::new(Evm::new(triple))
}

fn global_symbols_with_prefix(parsed: &sonatina_parser::ParsedModule, prefix: &str) -> Vec<String> {
    let mut symbols = parsed.module.ctx.with_gv_store(|store| {
        store
            .all_gv_data()
            .map(|data| data.symbol.clone())
            .filter(|symbol| symbol.starts_with(prefix))
            .collect::<Vec<_>>()
    });
    symbols.sort();
    symbols
}

fn lowered_blob_bytes(parsed: &sonatina_parser::ParsedModule, source_symbol: &str) -> Vec<u8> {
    let blob = parsed.module.ctx.with_gv_store(|store| {
        let source = store
            .lookup_gv(source_symbol)
            .unwrap_or_else(|| panic!("{source_symbol} global should exist"));
        let symbol = format!(
            "{}{source_symbol}_{}",
            super::CONST_WORD_POOL_PREFIX,
            source.as_u32()
        );
        store
            .lookup_gv(&symbol)
            .expect("synthesized blob should exist")
    });
    parsed.module.ctx.with_gv_store(|store| {
        let init = store
            .gv_data(blob)
            .initializer
            .clone()
            .expect("blob should have initializer");
        let GvInitializer::Array(bytes) = init else {
            panic!("blob initializer should be a byte array");
        };
        bytes
            .into_iter()
            .map(|byte| {
                let GvInitializer::Immediate(imm) = byte else {
                    panic!("blob bytes must be immediates");
                };
                imm.as_i256().to_u256().low_u32() as u8
            })
            .collect()
    })
}

#[test]
fn const_load_static_index_folds_to_immediate() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

global private const [i256; 4] $arr = [1, 2, 3, 4];

func private %entry() -> i256 {
    block0:
        v0.constref<[i256; 4]> = const.ref $arr;
        v1.constref<i256> = const.index v0 2.i8;
        v2.i256 = const.load v1;
        return v2;
}
"#,
    );

    ConstDataLower::default().run(&parsed.module);

    let entry = find_func_ref(&parsed, "entry");
    let dumped = parsed
        .module
        .func_store
        .view(entry, |func| FuncWriter::new(entry, func).dump_string());
    assert!(dumped.contains("return 3.i256;"));
    assert!(!dumped.contains("const."));
}

#[test]
fn const_load_dynamic_index_lowers_to_codecopy() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

global private const [i256; 5] $arr = [1, 3, 7, 15, 31];

func private %entry(v0.i256) -> i256 {
    block0:
        v1.constref<[i256; 5]> = const.ref $arr;
        v2.constref<i256> = const.index v1 v0;
        v3.i256 = const.load v2;
        return v3;
}
"#,
    );

    ConstDataLower::default().run(&parsed.module);

    let mut writer = ModuleWriter::with_debug_provider(&parsed.module, &parsed.debug);
    let dumped = writer.dump_string();
    assert!(dumped.contains("sym_addr $__sonatina_const_words_arr_"));
    assert!(!dumped.contains("sym_addr $arr"));
    assert!(dumped.contains("evm_code_copy"));
    assert!(dumped.contains("mload"));
    assert!(!dumped.contains("const."));
}

#[test]
fn const_load_huge_immediate_index_lowers_to_codecopy() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

global private const [i256; 4] $arr = [1, 2, 3, 4];

func private %entry() -> i256 {
    block0:
        v0.constref<[i256; 4]> = const.ref $arr;
        v1.constref<i256> = const.index v0 1606938044258990275541962092341162602522202993782792835301376.i256;
        v2.i256 = const.load v1;
        return v2;
}
"#,
    );

    ConstDataLower::default().run(&parsed.module);

    let mut writer = ModuleWriter::with_debug_provider(&parsed.module, &parsed.debug);
    let dumped = writer.dump_string();
    assert!(dumped.contains("evm_code_copy"));
    assert!(dumped.contains("mload"));
    assert!(!dumped.contains("return 1.i256;"));
    assert!(!dumped.contains("return 2.i256;"));
    assert!(!dumped.contains("return 3.i256;"));
    assert!(!dumped.contains("return 4.i256;"));
    assert!(!dumped.contains("const."));
}

#[test]
fn const_load_phi_same_path_folds_to_immediate_despite_layout_order() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

global private const [i256; 4] $arr = [1, 2, 3, 4];

func private %entry() -> i256 {
    block0:
        br 1.i1 block1 block2;

    block3:
        v4.constref<i256> = phi (v1 block1) (v3 block2);
        v5.i256 = const.load v4;
        return v5;

    block1:
        v0.constref<[i256; 4]> = const.ref $arr;
        v1.constref<i256> = const.index v0 2.i8;
        jump block3;

    block2:
        v2.constref<[i256; 4]> = const.ref $arr;
        v3.constref<i256> = const.index v2 2.i8;
        jump block3;
}
"#,
    );

    ConstDataLower::default().run(&parsed.module);

    let entry = find_func_ref(&parsed, "entry");
    let dumped = parsed
        .module
        .func_store
        .view(entry, |func| FuncWriter::new(entry, func).dump_string());
    assert!(dumped.contains("return 3.i256;"));
    assert!(!dumped.contains("const."));
}

#[test]
fn dynamic_const_load_collision_uses_fresh_blob_symbol() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

global private const [i64; 5] $arr = [1, 3, 7, 15, 31];
global private const [i8; 1] $__sonatina_const_words_arr_0 = [99];

func private %entry(v0.i256) -> i64 {
    block0:
        v1.constref<[i64; 5]> = const.ref $arr;
        v2.constref<i64> = const.index v1 v0;
        v3.i64 = const.load v2;
        return v3;
}
"#,
    );

    ConstDataLower::default().run(&parsed.module);

    let base_symbol = parsed.module.ctx.with_gv_store(|store| {
        let source = store.lookup_gv("arr").expect("arr global should exist");
        format!("__sonatina_const_words_arr_{}", source.as_u32())
    });
    assert_eq!(
        global_symbols_with_prefix(&parsed, &base_symbol),
        vec![base_symbol.clone(), format!("{base_symbol}_1")]
    );

    let mut writer = ModuleWriter::with_debug_provider(&parsed.module, &parsed.debug);
    let dumped = writer.dump_string();
    assert!(dumped.contains("evm_code_copy"));
    assert!(dumped.contains("mload"));
    assert!(!dumped.contains("const."));
}

#[test]
fn adjacent_dynamic_const_loads_share_row_codecopy() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

global private const [i256; 6] $arr = [11, 42, 7, 99, 5, 31];

func private %entry(v0.i256) -> i256 {
    block0:
        v1.constref<[i256; 6]> = const.ref $arr;
        v2.constref<i256> = const.index v1 v0;
        v3.i256 = const.load v2;
        v4.i256 = add v0 1.i256;
        v5.constref<i256> = const.index v1 v4;
        v6.i256 = const.load v5;
        v7.i256 = add v0 2.i256;
        v8.constref<i256> = const.index v1 v7;
        v9.i256 = const.load v8;
        v10.i256 = add v3 v6;
        v11.i256 = add v10 v9;
        return v11;
}
"#,
    );

    ConstDataLower::default().run(&parsed.module);

    let entry = find_func_ref(&parsed, "entry");
    let dumped = parsed
        .module
        .func_store
        .view(entry, |func| FuncWriter::new(entry, func).dump_string());
    assert_eq!(dumped.matches("evm_code_copy").count(), 1, "{dumped}");
    assert_eq!(dumped.matches("mload").count(), 3, "{dumped}");
    assert!(dumped.contains("alloca [i256; 3]"), "{dumped}");
    assert!(!dumped.contains("const."));
}

#[test]
fn adjacent_dynamic_const_loads_share_row_codecopy_with_nested_offset() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

global private const [i256; 9] $arr = [11, 42, 7, 99, 5, 31, 17, 23, 13];

func private %entry(v0.i256) -> i256 {
    block0:
        v1.constref<[i256; 9]> = const.ref $arr;
        v2.i256 = add 3.i256 v0;
        v3.constref<i256> = const.index v1 v2;
        v4.i256 = const.load v3;
        v5.i256 = add v2 1.i256;
        v6.constref<i256> = const.index v1 v5;
        v7.i256 = const.load v6;
        v8.i256 = add v2 2.i256;
        v9.constref<i256> = const.index v1 v8;
        v10.i256 = const.load v9;
        v11.i256 = add v4 v7;
        v12.i256 = add v11 v10;
        return v12;
}
"#,
    );

    ConstDataLower::default().run(&parsed.module);

    let entry = find_func_ref(&parsed, "entry");
    let dumped = parsed
        .module
        .func_store
        .view(entry, |func| FuncWriter::new(entry, func).dump_string());
    assert_eq!(dumped.matches("evm_code_copy").count(), 1, "{dumped}");
    assert_eq!(dumped.matches("mload").count(), 3, "{dumped}");
    assert!(dumped.contains("alloca [i256; 3]"), "{dumped}");
    assert!(!dumped.contains("const."));
}

#[test]
fn adjacent_dynamic_const_load_row_stops_at_memory_write() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

global private const [i256; 6] $arr = [11, 42, 7, 99, 5, 31];

func private %entry(v0.i256) -> i256 {
    block0:
        v1.constref<[i256; 6]> = const.ref $arr;
        v2.constref<i256> = const.index v1 v0;
        v3.i256 = const.load v2;
        v4.*i256 = alloca i256;
        mstore v4 v3 i256;
        v5.i256 = add v0 1.i256;
        v6.constref<i256> = const.index v1 v5;
        v7.i256 = const.load v6;
        v8.i256 = add v0 2.i256;
        v9.constref<i256> = const.index v1 v8;
        v10.i256 = const.load v9;
        v11.i256 = add v7 v10;
        return v11;
}
"#,
    );

    ConstDataLower::default().run(&parsed.module);

    let entry = find_func_ref(&parsed, "entry");
    let dumped = parsed
        .module
        .func_store
        .view(entry, |func| FuncWriter::new(entry, func).dump_string());
    assert_eq!(dumped.matches("evm_code_copy").count(), 3, "{dumped}");
    assert!(!dumped.contains("alloca [i256; 3]"), "{dumped}");
    assert!(!dumped.contains("const."));
}

#[test]
fn dynamic_const_load_affine_i256_lowers_to_expression() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

global private const [i256; 4] $arr = [10, 12, 14, 16];

func private %entry(v0.i256) -> i256 {
    block0:
        v1.constref<[i256; 4]> = const.ref $arr;
        v2.constref<i256> = const.index v1 v0;
        v3.i256 = const.load v2;
        return v3;
}
"#,
    );

    ConstDataLower::default().run(&parsed.module);

    let entry = find_func_ref(&parsed, "entry");
    let dumped = parsed
        .module
        .func_store
        .view(entry, |func| FuncWriter::new(entry, func).dump_string());
    assert!(dumped.contains("mul"));
    assert!(dumped.contains("add"));
    assert!(!dumped.contains("evm_code_copy"));
    assert!(!dumped.contains("__sonatina_const_words"));
    assert!(!dumped.contains("const."));
}

#[test]
fn dynamic_const_load_power_of_two_i256_lowers_to_shift() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

global private const [i256; 4] $arr = [1, 2, 4, 8];

func private %entry(v0.i256) -> i256 {
    block0:
        v1.constref<[i256; 4]> = const.ref $arr;
        v2.constref<i256> = const.index v1 v0;
        v3.i256 = const.load v2;
        return v3;
}
"#,
    );

    ConstDataLower::default().run(&parsed.module);

    let entry = find_func_ref(&parsed, "entry");
    let dumped = parsed
        .module
        .func_store
        .view(entry, |func| FuncWriter::new(entry, func).dump_string());
    assert!(dumped.contains("shl"));
    assert!(!dumped.contains("evm_code_copy"));
    assert!(!dumped.contains("__sonatina_const_words"));
    assert!(!dumped.contains("const."));
}

#[test]
fn dynamic_const_load_periodic_i256_lowers_to_mod_expression() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

global private const [i256; 6] $arr = [5, 13, 9, 5, 13, 9];

func private %entry(v0.i256) -> i256 {
    block0:
        v1.constref<[i256; 6]> = const.ref $arr;
        v2.constref<i256> = const.index v1 v0;
        v3.i256 = const.load v2;
        return v3;
}
"#,
    );

    ConstDataLower::default().run(&parsed.module);

    let entry = find_func_ref(&parsed, "entry");
    let dumped = parsed
        .module
        .func_store
        .view(entry, |func| FuncWriter::new(entry, func).dump_string());
    assert!(dumped.contains("evm_umod"));
    assert!(dumped.contains("eq"));
    assert!(!dumped.contains("evm_code_copy"));
    assert!(!dumped.contains("__sonatina_const_words"));
    assert!(!dumped.contains("const."));
}

#[test]
fn dynamic_const_load_small_i8_lowers_to_packed_byte() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

global private const [i8; 4] $arr = [10, 20, 30, 40];

func private %entry(v0.i256) -> i8 {
    block0:
        v1.constref<[i8; 4]> = const.ref $arr;
        v2.constref<i8> = const.index v1 v0;
        v3.i8 = const.load v2;
        return v3;
}
"#,
    );

    ConstDataLower::default().run(&parsed.module);

    let entry = find_func_ref(&parsed, "entry");
    let dumped = parsed
        .module
        .func_store
        .view(entry, |func| FuncWriter::new(entry, func).dump_string());
    assert!(dumped.contains("evm_byte"));
    assert!(!dumped.contains("evm_code_copy"));
    assert!(!dumped.contains("__sonatina_const_words"));
    assert!(!dumped.contains("const."));
}

#[test]
fn dynamic_const_load_small_i16_lowers_to_packed_subword() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

global private const [i16; 4] $arr = [100, 200, 400, 800];

func private %entry(v0.i256) -> i16 {
    block0:
        v1.constref<[i16; 4]> = const.ref $arr;
        v2.constref<i16> = const.index v1 v0;
        v3.i16 = const.load v2;
        return v3;
}
"#,
    );

    ConstDataLower::default().run(&parsed.module);

    let entry = find_func_ref(&parsed, "entry");
    let dumped = parsed
        .module
        .func_store
        .view(entry, |func| FuncWriter::new(entry, func).dump_string());
    assert!(dumped.contains("shr"));
    assert!(dumped.contains("trunc"));
    assert!(!dumped.contains("evm_code_copy"));
    assert!(!dumped.contains("__sonatina_const_words"));
    assert!(!dumped.contains("const."));
}

#[test]
fn dynamic_const_load_small_i64_lowers_to_packed_subword() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

global private const [i64; 4] $arr = [11, 99, 42, 77];

func private %entry(v0.i256) -> i64 {
    block0:
        v1.constref<[i64; 4]> = const.ref $arr;
        v2.constref<i64> = const.index v1 v0;
        v3.i64 = const.load v2;
        return v3;
}
"#,
    );

    ConstDataLower::default().run(&parsed.module);

    let entry = find_func_ref(&parsed, "entry");
    let dumped = parsed
        .module
        .func_store
        .view(entry, |func| FuncWriter::new(entry, func).dump_string());
    assert!(dumped.contains("shr"));
    assert!(dumped.contains("trunc"));
    assert!(!dumped.contains("evm_code_copy"));
    assert!(!dumped.contains("__sonatina_const_words"));
    assert!(!dumped.contains("const."));
}

#[test]
fn dynamic_const_load_small_i1_lowers_to_bitset() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

global private const [i1; 4] $arr = [0, 1, 0, 1];

func private %entry(v0.i256) -> i1 {
    block0:
        v1.constref<[i1; 4]> = const.ref $arr;
        v2.constref<i1> = const.index v1 v0;
        v3.i1 = const.load v2;
        return v3;
}
"#,
    );

    ConstDataLower::default().run(&parsed.module);

    let entry = find_func_ref(&parsed, "entry");
    let dumped = parsed
        .module
        .func_store
        .view(entry, |func| FuncWriter::new(entry, func).dump_string());
    assert!(dumped.contains("shr"));
    assert!(dumped.contains("and"));
    assert!(!dumped.contains("evm_code_copy"));
    assert!(!dumped.contains("__sonatina_const_words"));
    assert!(!dumped.contains("const."));
}

#[test]
fn dynamic_const_load_small_i256_lowers_to_inline_selectors() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

global private const [i256; 3] $arr = [5, 13, 9];

func private %entry(v0.i256) -> i256 {
    block0:
        v1.constref<[i256; 3]> = const.ref $arr;
        v2.constref<i256> = const.index v1 v0;
        v3.i256 = const.load v2;
        return v3;
}
"#,
    );

    ConstDataLower::default().run(&parsed.module);

    let entry = find_func_ref(&parsed, "entry");
    let dumped = parsed
        .module
        .func_store
        .view(entry, |func| FuncWriter::new(entry, func).dump_string());
    assert!(dumped.contains("eq"));
    assert!(dumped.contains("mul"));
    assert!(!dumped.contains("evm_umod"));
    assert!(!dumped.contains("evm_code_copy"));
    assert!(!dumped.contains("__sonatina_const_words"));
    assert!(!dumped.contains("const."));
}

#[test]
fn dynamic_const_load_single_sparse_exception_lowers_to_expression() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

global private const [i256; 4] $arr = [0, 0, 99, 0];

func private %entry(v0.i256) -> i256 {
    block0:
        v1.constref<[i256; 4]> = const.ref $arr;
        v2.constref<i256> = const.index v1 v0;
        v3.i256 = const.load v2;
        return v3;
}
"#,
    );

    ConstDataLower::default().run(&parsed.module);

    let entry = find_func_ref(&parsed, "entry");
    let dumped = parsed
        .module
        .func_store
        .view(entry, |func| FuncWriter::new(entry, func).dump_string());
    assert!(dumped.contains("eq"));
    assert!(dumped.contains("mul"));
    assert!(!dumped.contains("evm_code_copy"));
    assert!(!dumped.contains("__sonatina_const_words"));
    assert!(!dumped.contains("const."));
}

#[test]
fn dynamic_const_load_exact_synthesized_word_blobs_are_deduped() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

global private const [i64; 5] $a = [1, 3, 7, 15, 31];
global private const [i64; 5] $b = [1, 3, 7, 15, 31];

func private %entry(v0.i256) -> i64 {
    block0:
        v1.constref<[i64; 5]> = const.ref $a;
        v2.constref<i64> = const.index v1 v0;
        v3.i64 = const.load v2;
        v4.constref<[i64; 5]> = const.ref $b;
        v5.constref<i64> = const.index v4 v0;
        v6.i64 = const.load v5;
        v7.i64 = add v3 v6;
        return v7;
}
"#,
    );

    ConstDataLower::default().run(&parsed.module);

    let symbols = global_symbols_with_prefix(&parsed, "__sonatina_const_words_");
    assert_eq!(symbols.len(), 1, "{symbols:?}");
}

#[test]
fn dynamic_const_load_dedups_same_layout_internal_word_blobs() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

type @five = { i256, i256, i256, i256, i256 };

global private const [i256; 5] $arr = [1, 3, 7, 15, 31];
global private const @five $row = {1, 3, 7, 15, 31};

func private %addr_row() -> constref<@five> {
    block0:
        v0.constref<@five> = const.ref $row;
        return v0;
}

func private %entry(v0.i256) -> i256 {
    block0:
        v1.constref<[i256; 5]> = const.ref $arr;
        v2.constref<i256> = const.index v1 v0;
        v3.i256 = const.load v2;
        v4.constref<@five> = call %addr_row;
        v5.constref<i256> = const.proj v4 0.i8;
        v6.i256 = const.load v5;
        v7.i256 = add v3 v6;
        return v7;
}
"#,
    );

    ConstDataLower::default().run(&parsed.module);

    let symbols = global_symbols_with_prefix(&parsed, "__sonatina_const_words_");
    assert_eq!(symbols.len(), 1, "{symbols:?}");
}

#[test]
fn obj_init_const_small_aggregate_lowers_to_stores() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

global private const [i256; 2] $arr = [11, 22];

func private %entry() -> i256 {
    block0:
        v0.objref<[i256; 2]> = obj.alloc [i256; 2];
        v1.constref<[i256; 2]> = const.ref $arr;
        obj.init.const v0 v1;
        v2.objref<i256> = obj.index v0 1.i8;
        v3.i256 = obj.load v2;
        return v3;
}
"#,
    );

    ConstDataLower::default().run(&parsed.module);

    let entry = find_func_ref(&parsed, "entry");
    let dumped = parsed
        .module
        .func_store
        .view(entry, |func| FuncWriter::new(entry, func).dump_string());
    assert!(!dumped.contains("obj.init.const"));
    assert!(dumped.contains("obj.store"));
    assert!(!dumped.contains("obj.materialize.stack"));
    assert!(!dumped.contains("evm_code_copy"));
    assert!(!dumped.contains("__sonatina_const_words"));
    assert!(!dumped.contains("const."));
}

#[test]
fn obj_init_const_small_narrow_aggregate_lowers_to_store() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

global private const [i8; 1] $arr = [-1];

func private %entry() -> i256 {
    block0:
        v0.objref<[i8; 1]> = obj.alloc [i8; 1];
        v1.constref<[i8; 1]> = const.ref $arr;
        obj.init.const v0 v1;
        return 0.i256;
}
"#,
    );

    ConstDataLower::default().run(&parsed.module);

    let entry = find_func_ref(&parsed, "entry");
    let dumped = parsed
        .module
        .func_store
        .view(entry, |func| FuncWriter::new(entry, func).dump_string());
    assert!(dumped.contains("obj.store"));
    assert!(!dumped.contains("evm_code_copy"));
    assert!(!dumped.contains("__sonatina_const_words"));
    assert!(!dumped.contains("const."));
}

#[test]
fn obj_init_const_bulk_codecopy_zero_extends_nested_narrow_words() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

type @inner = { i1, [i16; 2] };
type @outer = { @inner, [i1; 2] };

global private const @outer $value = {{1, [-2, 3]}, [0, 1]};

func private %entry() -> i256 {
    block0:
        v0.objref<@outer> = obj.alloc @outer;
        v1.constref<@outer> = const.ref $value;
        obj.init.const v0 v1;
        return 0.i256;
}
"#,
    );

    ConstDataLower::default().run(&parsed.module);

    let entry = find_func_ref(&parsed, "entry");
    let dumped = parsed
        .module
        .func_store
        .view(entry, |func| FuncWriter::new(entry, func).dump_string());
    assert!(dumped.contains("evm_code_copy"));
    assert!(!dumped.contains("obj.store"));

    let blob_bytes = lowered_blob_bytes(&parsed, "value");
    assert_eq!(blob_bytes.len(), 32 * 5);

    let words: Vec<_> = blob_bytes.chunks_exact(32).collect();
    assert!(words[0][..31].iter().all(|&byte| byte == 0));
    assert_eq!(words[0][31], 1);

    assert!(words[1][..30].iter().all(|&byte| byte == 0));
    assert_eq!(&words[1][30..], &[0xff, 0xfe]);

    assert!(words[2][..30].iter().all(|&byte| byte == 0));
    assert_eq!(&words[2][30..], &[0x00, 0x03]);

    assert!(words[3][..31].iter().all(|&byte| byte == 0));
    assert_eq!(words[3][31], 0);

    assert!(words[4][..31].iter().all(|&byte| byte == 0));
    assert_eq!(words[4][31], 1);
}

#[test]
fn obj_init_const_zero_aggregate_lowers_to_zero_fill_without_blob() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

global private const [i256; 5] $value = [0, 0, 0, 0, 0];

func private %entry() -> i256 {
    block0:
        v0.objref<[i256; 5]> = obj.alloc [i256; 5];
        v1.constref<[i256; 5]> = const.ref $value;
        obj.init.const v0 v1;
        return 0.i256;
}
"#,
    );

    ConstDataLower::default().run(&parsed.module);

    let entry = find_func_ref(&parsed, "entry");
    let dumped = parsed
        .module
        .func_store
        .view(entry, |func| FuncWriter::new(entry, func).dump_string());
    assert!(dumped.contains("evm_code_size"));
    assert!(dumped.contains("evm_code_copy"));
    assert!(!dumped.contains("obj.store"));
    assert!(!dumped.contains("__sonatina_const_words"));
    assert_eq!(
        global_symbols_with_prefix(&parsed, "__sonatina_const_words_").len(),
        0
    );
}

#[test]
fn obj_init_const_splat_aggregate_lowers_to_mcopy_fill_without_blob() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

global private const [i256; 5] $value = [7, 7, 7, 7, 7];

func private %entry() -> i256 {
    block0:
        v0.objref<[i256; 5]> = obj.alloc [i256; 5];
        v1.constref<[i256; 5]> = const.ref $value;
        obj.init.const v0 v1;
        return 0.i256;
}
"#,
    );

    ConstDataLower::default().run(&parsed.module);

    let entry = find_func_ref(&parsed, "entry");
    let dumped = parsed
        .module
        .func_store
        .view(entry, |func| FuncWriter::new(entry, func).dump_string());
    assert!(dumped.contains("mstore"));
    assert!(dumped.contains("evm_mcopy"));
    assert!(!dumped.contains("evm_code_copy"));
    assert!(!dumped.contains("obj.store"));
    assert!(!dumped.contains("__sonatina_const_words"));
    assert_eq!(
        global_symbols_with_prefix(&parsed, "__sonatina_const_words_").len(),
        0
    );
}

#[test]
fn obj_init_const_mixed_aggregate_lowers_to_split_strategies() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

type @mixed = { i256, [i256; 5], [i256; 5] };

global private const @mixed $value = {1, [0, 0, 0, 0, 0], [10, 20, 30, 40, 50]};

func private %entry() -> i256 {
    block0:
        v0.objref<@mixed> = obj.alloc @mixed;
        v1.constref<@mixed> = const.ref $value;
        obj.init.const v0 v1;
        return 0.i256;
}
"#,
    );

    ConstDataLower::default().run(&parsed.module);

    let entry = find_func_ref(&parsed, "entry");
    let dumped = parsed
        .module
        .func_store
        .view(entry, |func| FuncWriter::new(entry, func).dump_string());
    assert!(dumped.contains("obj.store"));
    assert!(dumped.contains("evm_code_size"));
    assert_eq!(dumped.matches("evm_code_copy").count(), 2);
    assert_eq!(
        global_symbols_with_prefix(&parsed, "__sonatina_const_words_").len(),
        1
    );
    assert!(!dumped.contains("obj.init.const"));
}

#[test]
fn obj_init_const_scalar_phi_same_path_uses_immediate_store_despite_layout_order() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

global private const i256 $value = 11;

func private %entry() -> i256 {
    block0:
        br 1.i1 block1 block2;

    block3:
        v2.objref<i256> = obj.alloc i256;
        v3.constref<i256> = phi (v0 block1) (v1 block2);
        obj.init.const v2 v3;
        v4.i256 = obj.load v2;
        return v4;

    block1:
        v0.constref<i256> = const.ref $value;
        jump block3;

    block2:
        v1.constref<i256> = const.ref $value;
        jump block3;
}
"#,
    );

    ConstDataLower::default().run(&parsed.module);

    let entry = find_func_ref(&parsed, "entry");
    let dumped = parsed
        .module
        .func_store
        .view(entry, |func| FuncWriter::new(entry, func).dump_string());
    assert!(!dumped.contains("obj.init.const"));
    assert!(dumped.contains("obj.store"));
    assert!(!dumped.contains("obj.materialize.stack"));
    assert!(!dumped.contains("evm_code_copy"));
    assert!(!dumped.contains("mload"));
    assert!(!dumped.contains("const."));
}

#[test]
fn obj_init_const_scalar_lowers_to_obj_store() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

global private const i256 $value = 11;

func private %entry() -> i256 {
    block0:
        v0.objref<i256> = obj.alloc i256;
        v1.constref<i256> = const.ref $value;
        obj.init.const v0 v1;
        v2.i256 = obj.load v0;
        return v2;
}
"#,
    );

    ConstDataLower::default().run(&parsed.module);

    let entry = find_func_ref(&parsed, "entry");
    let dumped = parsed
        .module
        .func_store
        .view(entry, |func| FuncWriter::new(entry, func).dump_string());
    assert!(!dumped.contains("obj.init.const"));
    assert!(dumped.contains("obj.store"));
    assert!(!dumped.contains("obj.materialize.stack"));
    assert!(!dumped.contains("evm_code_copy"));
    assert!(!dumped.contains("const."));
}

#[test]
fn dynamic_const_load_object_compile_keeps_synthesized_blob_data_reachable() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

global private const [i64; 5] $arr = [1, 3, 7, 15, 31];

func private %entry(v0.i256) -> i64 {
    block0:
        v1.constref<[i64; 5]> = const.ref $arr;
        v2.constref<i64> = const.index v1 v0;
        v3.i64 = const.load v2;
        return v3;
}

object @Contract {
  section runtime { entry %entry; data $arr; }
}
"#,
    );

    let opts = CompileOptions::default();
    compile_all_objects(&parsed.module, &test_backend(), &opts)
        .expect("object compilation should include backend-synthesized const blobs");
}

#[test]
fn object_compile_drops_unreferenced_private_const_data() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

global private const [i256; 2] $dead = [1, 2];

func private %entry() {
    block0:
        evm_stop;
}

object @Contract {
  section runtime { entry %entry; data $dead; }
}
"#,
    );

    let dead = parsed
        .module
        .ctx
        .with_gv_store(|store| store.lookup_gv("dead").expect("dead global should exist"));
    let opts = CompileOptions {
        emit_symtab: true,
        ..Default::default()
    };
    let artifacts = compile_all_objects(&parsed.module, &test_backend(), &opts)
        .expect("object compilation should drop dead private const data");
    let runtime = artifacts[0]
        .sections
        .values()
        .next()
        .expect("runtime section should exist");

    assert!(!runtime.symtab.contains_key(&SymbolId::Global(dead)));
    assert!(
        runtime.bytes.len() < 64,
        "dead data should not be appended: {} bytes",
        runtime.bytes.len()
    );
}

#[test]
fn object_compile_keeps_private_const_data_when_section_size_is_observed() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

global private const [i256; 2] $data = [1, 2];

func private %entry() {
    block0:
        v0.i256 = sym_size .;
        mstore 0.i256 v0 i256;
        evm_return 0.i256 32.i256;
}

object @Contract {
  section runtime { entry %entry; data $data; }
}
"#,
    );

    let data = parsed
        .module
        .ctx
        .with_gv_store(|store| store.lookup_gv("data").expect("data global should exist"));
    let opts = CompileOptions {
        emit_symtab: true,
        ..Default::default()
    };
    let artifacts = compile_all_objects(&parsed.module, &test_backend(), &opts)
        .expect("object compilation should preserve section-size-observed data");
    let runtime = artifacts[0]
        .sections
        .values()
        .next()
        .expect("runtime section should exist");
    let data_def = runtime
        .symtab
        .get(&SymbolId::Global(data))
        .expect("section-size-observed data should be present");

    assert_eq!(data_def.size, 64);
    assert!(runtime.bytes.len() >= 64);
}

#[test]
fn object_compile_keeps_private_const_data_when_code_size_is_observed() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

global private const [i256; 2] $data = [1, 2];

func private %entry() {
    block0:
        v0.i256 = evm_code_size;
        mstore 0.i256 v0 i256;
        evm_return 0.i256 32.i256;
}

object @Contract {
  section runtime { entry %entry; data $data; }
}
"#,
    );

    let data = parsed
        .module
        .ctx
        .with_gv_store(|store| store.lookup_gv("data").expect("data global should exist"));
    let opts = CompileOptions {
        emit_symtab: true,
        ..Default::default()
    };
    let artifacts = compile_all_objects(&parsed.module, &test_backend(), &opts)
        .expect("object compilation should preserve code-size-observed data");
    let runtime = artifacts[0]
        .sections
        .values()
        .next()
        .expect("runtime section should exist");
    let data_def = runtime
        .symtab
        .get(&SymbolId::Global(data))
        .expect("code-size-observed data should be present");

    assert_eq!(data_def.size, 64);
    assert!(runtime.bytes.len() >= 64);
}

#[test]
fn word_compatible_dynamic_const_load_reuses_explicit_data_symbol() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

global private const [i256; 5] $arr = [1, 3, 7, 15, 31];

func private %entry(v0.i256) -> i256 {
    block0:
        v1.constref<[i256; 5]> = const.ref $arr;
        v2.constref<i256> = const.index v1 v0;
        v3.i256 = const.load v2;
        return v3;
}

object @Contract {
  section runtime { entry %entry; data $arr; }
}
"#,
    );

    let arr = parsed
        .module
        .ctx
        .with_gv_store(|store| store.lookup_gv("arr").expect("arr global should exist"));
    let opts = CompileOptions {
        emit_symtab: true,
        ..Default::default()
    };
    let artifacts = compile_all_objects(&parsed.module, &test_backend(), &opts)
        .expect("object compilation should reuse compatible explicit data");
    let runtime = artifacts[0]
        .sections
        .values()
        .next()
        .expect("runtime section should exist");
    let arr_def = runtime
        .symtab
        .get(&SymbolId::Global(arr))
        .expect("arr symbol should be present");
    assert_eq!(arr_def.size, 160);
    assert_eq!(runtime.bytes.len(), 176);
}

#[test]
fn dynamic_const_load_object_compile_succeeds_with_colliding_blob_symbol() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

global private const [i64; 5] $arr = [1, 3, 7, 15, 31];
global private const [i8; 1] $__sonatina_const_words_arr_0 = [99];

func private %entry(v0.i256) -> i64 {
    block0:
        v1.constref<[i64; 5]> = const.ref $arr;
        v2.constref<i64> = const.index v1 v0;
        v3.i64 = const.load v2;
        return v3;
}

object @Contract {
  section runtime {
    entry %entry;
    data $arr;
    data $__sonatina_const_words_arr_0;
  }
}
"#,
    );

    let opts = CompileOptions::default();
    compile_all_objects(&parsed.module, &test_backend(), &opts)
        .expect("object compilation should succeed with colliding synthesized blob symbols");
}

#[test]
fn constref_helper_calls_lower_before_object_compile() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

global private const [i256; 5] $arr = [10, 20, 30, 40, 50];

func private %get(v0.constref<[i256; 5]>, v1.i256) -> i256 {
    block0:
        v2.constref<i256> = const.index v0 v1;
        v3.i256 = const.load v2;
        return v3;
}

func private %entry() {
    block0:
        v0.constref<[i256; 5]> = const.ref $arr;
        jump block1;

    block1:
        v1.i256 = phi (0.i256 block0) (v6 block3);
        v2.i256 = phi (0.i256 block0) (v7 block3);
        v3.i1 = lt v2 5.i256;
        br v3 block2 block4;

    block2:
        v5.i256 = call %get v0 v2;
        v6.i256 = add v1 v5;
        jump block3;

    block3:
        v7.i256 = add v2 1.i256;
        jump block1;

    block4:
        v8.i1 = eq v1 150.i256;
        br v8 block5 block6;

    block5:
        evm_stop;

    block6:
        evm_revert 0.i256 0.i256;
}

object @Contract {
  section runtime { entry %entry; data $arr; }
}
"#,
    );

    let opts = CompileOptions::default();
    compile_all_objects(&parsed.module, &test_backend(), &opts)
        .expect("constref helper calls should lower before object compile");
}

#[test]
fn looped_dynamic_const_load_lowers_before_object_compile() {
    let parsed = parse(
        r#"
target = "evm-ethereum-osaka"

global private const [i256; 5] $arr = [10, 20, 30, 40, 50];

func private %entry() {
    block0:
        v0.constref<[i256; 5]> = const.ref $arr;
        jump block3;

    block3:
        v3.i256 = phi (0.i256 block0) (v12 block5);
        v5.i256 = phi (0.i256 block0) (v15 block5);
        v7.i1 = lt v5 5.i256;
        br v7 block4 block6;

    block4:
        v10.constref<i256> = const.index v0 v5;
        v11.i256 = const.load v10;
        (v12.i256, v13.i1) = uaddo v3 v11;
        br v13 block7 block5;

    block5:
        v15.i256 = add v5 1.i256;
        jump block3;

    block6:
        v9.i1 = eq v3 150.i256;
        br v9 block8 block10;

    block10:
        evm_revert 0.i256 0.i256;

    block8:
        evm_stop;

    block7:
        evm_revert 0.i256 0.i256;
}

object @Contract {
  section runtime { entry %entry; data $arr; }
}
"#,
    );

    let opts = CompileOptions::default();
    compile_all_objects(&parsed.module, &test_backend(), &opts)
        .expect("looped dynamic const loads should lower before object compile");
}
