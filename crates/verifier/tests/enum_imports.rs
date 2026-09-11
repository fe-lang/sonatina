//! Importing a reference does not publish previously private objects.
#[path = "support/enum_contract.rs"]
mod contract;

use contract::execute;

#[test]
fn unused_raw_loads_do_not_publish_private_objects() {
    for (ty, value) in [
        ("objref<@E>", "v10"),
        ("@Holder", "v12"),
        ("[objref<@E>; 1]", "v13"),
        ("@Carrier", "v14"),
    ] {
        for effect in ["mstore v100 0.i256 i256;", "call %noise;"] {
            let source = format!(
                r#"
target = "evm-ethereum-osaka"
type @E = enum {{ #None, #Some(i256) }};
type @Holder = {{ objref<@E> }};
type @Carrier = enum {{ #Wrap(objref<@E>) }};
func private %noise() {{
block0:
 return;
}}
func private %entry(v100.*i256) -> i256 {{
block0:
 v10.objref<@E> = obj.alloc @E;
 enum.write_variant v10 #Some (31.i256);
 v12.@Holder = insert_value undef.@Holder 0.i8 v10;
 v13.[objref<@E>; 1] = insert_value undef.[objref<@E>; 1] 0.i8 v10;
 v14.@Carrier = enum.make @Carrier #Wrap (v10);
 v11.*{ty} = alloca {ty};
 mstore v11 {value} {ty};
 v0.objref<@E> = obj.alloc @E;
 enum.write_variant v0 #Some (17.i256);
 v1.objref<i256> = enum.proj v0 #Some 0.i8;
 v2.{ty} = mload v11 {ty};
 {effect}
 v3.i256 = obj.load v1;
 return v3;
}}
"#
            );
            let run = execute(&source, 128);
            assert_eq!(run.invalid_reads(), 0);
            assert_eq!(run.exhausted, 0);
            assert!(run.returned > 0);
        }
    }
}

#[test]
fn raw_loads_recover_published_payload_guards() {
    for retag in [false, true] {
        let mutation = if retag { "enum.set_tag v0 #None;" } else { "" };
        let source = format!(
            r#"
target = "evm-ethereum-osaka"
type @E = enum {{ #None, #Some(i256) }};
func private %entry() -> i256 {{
block0:
 v0.objref<@E> = obj.alloc @E;
 enum.write_variant v0 #Some (17.i256);
 v1.objref<i256> = enum.proj v0 #Some 0.i8;
 v2.*objref<i256> = alloca objref<i256>;
 mstore v2 v1 objref<i256>;
 v3.objref<i256> = mload v2 objref<i256>;
 {mutation}
 v4.i256 = obj.load v3;
 return v4;
}}
"#
        );
        let run = execute(&source, 128);
        assert_eq!(run.invalid_reads(), usize::from(retag));
        assert_eq!(run.exhausted, 0);
        assert_eq!(run.returned, 1);
    }
}

#[test]
fn raw_imported_holders_publish_references_stored_later() {
    for stored in [false, true] {
        let store = if stored { "obj.store v3 v0;" } else { "" };
        let source = format!(
            r#"
target = "evm-ethereum-osaka"
type @E = enum {{ #None, #Some(i256) }};
type @Holder = {{ objref<@E> }};
func private %entry(v100.*i256) -> i256 {{
block0:
 v10.objref<@Holder> = obj.alloc @Holder;
 v11.*objref<@Holder> = alloca objref<@Holder>;
 mstore v11 v10 objref<@Holder>;
 v0.objref<@E> = obj.alloc @E;
 v2.objref<@Holder> = mload v11 objref<@Holder>;
 v3.objref<objref<@E>> = obj.proj v2 0.i8;
 {store}
 enum.write_variant v0 #Some (17.i256);
 v1.objref<i256> = enum.proj v0 #Some 0.i8;
 mstore v100 0.i256 i256;
 v4.i256 = obj.load v1;
 return v4;
}}
"#
        );
        let run = execute(&source, 128);
        assert_eq!(run.invalid_reads(), usize::from(stored));
        assert_eq!(run.exhausted, 0);
        assert!(run.returned > 0);
    }
}

#[test]
fn raw_havoc_cannot_add_private_objects_to_exposed_reference_cells() {
    let source = r#"
target = "evm-ethereum-osaka"
type @E = enum { #None, #Some(i256) };
type @Holder = { objref<@E> };
func private %entry(v100.*i256) -> i256 {
block0:
 v10.objref<@E> = obj.alloc @E;
 enum.write_variant v10 #Some (31.i256);
 v11.objref<@Holder> = obj.alloc @Holder;
 v12.objref<objref<@E>> = obj.proj v11 0.i8;
 obj.store v12 v10;
 v13.*@Holder = obj.materialize.stack v11;
 v0.objref<@E> = obj.alloc @E;
 enum.write_variant v0 #Some (17.i256);
 v1.objref<i256> = enum.proj v0 #Some 0.i8;
 v2.objref<@Holder> = obj.alloc @Holder;
 v3.objref<objref<@E>> = obj.proj v2 0.i8;
 mstore v100 0.i256 i256;
 obj.store v3 v0;
 mstore v100 0.i256 i256;
 v4.i256 = obj.load v1;
 return v4;
}

"#;
    let run = execute(source, 128);
    assert_eq!(run.invalid_reads(), 0);
    assert_eq!(run.exhausted, 0);
    assert!(run.returned > 0);
}

#[test]
fn raw_recovery_without_a_local_projection_still_checks_payload_reads() {
    for retag in [false, true] {
        let mutation = if retag {
            "enum.set_tag v100 #None;"
        } else {
            ""
        };
        let source = format!(
            r#"
target = "evm-ethereum-osaka"
type @E = enum {{ #None, #Some(i256) }};
func private %read(v100.objref<@E>, v101.*objref<i256>) -> i256 {{
block0:
 enum.write_variant v100 #Some (17.i256);
 {mutation}
 v0.objref<i256> = mload v101 objref<i256>;
 v1.i256 = obj.load v0;
 return v1;
}}
func private %entry() -> i256 {{
block0:
 v0.objref<@E> = obj.alloc @E;
 enum.write_variant v0 #Some (17.i256);
 v1.objref<i256> = enum.proj v0 #Some 0.i8;
 v2.*objref<i256> = alloca objref<i256>;
 mstore v2 v1 objref<i256>;
 v3.i256 = call %read v0 v2;
 return v3;
}}
"#
        );
        let run = execute(&source, 128);
        assert_eq!(run.invalid_reads(), usize::from(retag));
        assert_eq!(run.exhausted, 0);
        assert_eq!(run.returned, 1);
    }
}
