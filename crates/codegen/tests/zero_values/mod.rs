// Shared by the EVM, interpreter and native execution tests.
/// `zero.T` in input IR, of each type class: each case returns an `i64`.
pub const ZERO_SOURCE: &str = include_str!("../fixtures/zero_values.sntn");
pub const ZERO_CASES: &[(&str, i64)] = &[
    ("int", 7),
    ("bool", 2),
    ("null", 3),
    ("unit_field", 4),
    ("unit_operand", 5),
    ("enum_variant", 1),
    ("enum_tag", 1),
    ("struct_store", 0),
    ("zero_field_store", 6),
    ("array_store", 8),
    ("nested_store", 10),
    ("insert_into_zero", 11),
    ("phi_zero", 3),
    ("large_array", 14),
];
