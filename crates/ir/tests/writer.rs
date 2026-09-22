use sonatina_ir::{
    Function, Module, ValueId,
    ir_writer::{DebugProvider, ModuleWriter},
    module::FuncRef,
};
use sonatina_parser::parse_module;

struct Names([Option<&'static str>; 6]);

impl DebugProvider for Names {
    fn value_name(&self, _: &Function, _: FuncRef, value: ValueId) -> Option<&str> {
        self.0.get(value.as_u32() as usize).copied().flatten()
    }
}

const SOURCE: &str = r#"
target = "evm-ethereum-osaka"

func public %first(v0.i256, v1.i256) -> i256 {
    block0:
        (v2.i256, v3.i1) = uaddo v0 v1;
        br v3 block1 block2;
    block1:
        jump block3;
    block2:
        v4.i256 = sub v2 1.i256;
        jump block3;
    block3:
        v5.i256 = phi (v2 block1) (v4 block2);
        return v5;
}
"#;

fn assert_roundtrip(module: &Module, debug: &dyn DebugProvider) -> String {
    let text = ModuleWriter::with_debug_provider(module, debug).dump_string();
    assert_eq!(
        ModuleWriter::with_debug_provider(module, debug).dump_string(),
        text,
        "writing must be deterministic"
    );
    let reparsed = parse_module(&text)
        .unwrap_or_else(|errors| panic!("writer output should parse: {errors:?}\n{text}"));
    assert_eq!(
        ModuleWriter::new(&reparsed.module).dump_string(),
        ModuleWriter::new(module).dump_string(),
        "renaming must preserve every definition and use"
    );
    assert_eq!(
        ModuleWriter::with_debug_provider(&reparsed.module, &reparsed.debug).dump_string(),
        text
    );
    text
}

#[test]
fn generated_names_do_not_collide_with_preserved_names() {
    let parsed = parse_module(SOURCE).unwrap();
    // The sum's default v2 collides with an argument. v7 and v8 also
    // reserve the first fresh numbers beyond the function's value slots.
    let names = Names([Some("v2"), Some("v8"), None, None, Some("v7"), None]);
    let text = assert_roundtrip(&parsed.module, &names);
    assert!(text.contains("%first(v2.i256, v8.i256)"));
    assert!(text.contains("v7.i256 = sub"));
    assert!(text.contains("v3.i1) = uaddo"));
}

#[test]
fn duplicate_debug_names_are_disambiguated_per_function() {
    let second = SOURCE.split_once("func public").unwrap().1;
    let source = format!(
        "{SOURCE}\nfunc public{}",
        second.replace("%first", "%second")
    );
    let parsed = parse_module(&source).unwrap();
    let names = Names([Some("v2"); 6]);
    let text = assert_roundtrip(&parsed.module, &names);
    assert!(text.contains("%first(v2.i256, v1.i256)"));
    assert!(text.contains("%second(v2.i256, v1.i256)"));
}

#[test]
fn noncolliding_names_and_numeric_defaults_are_preserved() {
    let parsed = parse_module(SOURCE).unwrap();
    let text = assert_roundtrip(&parsed.module, &parsed.debug);
    assert_eq!(text, ModuleWriter::new(&parsed.module).dump_string());
    assert_eq!(text, assert_roundtrip(&parsed.module, &Names([None; 6])));
}
