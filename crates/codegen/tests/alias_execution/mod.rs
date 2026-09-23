// Shared defined-value oracles, independent of optimization level.
pub const SOURCE: &str = include_str!("../fixtures/object_alias_execution.sntn");
pub const CASES: &[(&str, i64)] = &[
    ("aliased", 22),
    ("distinct", 11),
    ("forwarded", 22),
    ("observed", 44),
    ("reread", 11),
    ("diamond_false", 11),
    ("diamond_true", 22),
    ("backedge", 33),
    ("conditional_false", 11),
    ("conditional_true", 22),
    ("nested_alias", 22),
    ("siblings", 11),
    ("enum_alias", 1),
];

pub const DISJOINT_SOURCE: &str = r#"
func inline(never) private %read_after_write(v0.objref<i64>, v1.objref<i64>) -> i64 {
block0:
    obj.store v1 22.i64;
    v2.i64 = obj.load v0;
    return v2;
}
func inline(never) public %disjoint_only() -> i64 {
block0:
    v0.objref<i64> = obj.alloc i64;
    v1.objref<i64> = obj.alloc i64;
    obj.store v0 11.i64;
    obj.store v1 33.i64;
    v2.i64 = call %read_after_write v0 v1;
    return v2;
}
"#;

pub const CAPTURE_SOURCE: &str = include_str!("../fixtures/object_alias_capture.sntn");
