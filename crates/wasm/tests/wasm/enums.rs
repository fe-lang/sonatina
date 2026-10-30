//! Enums in the layout of the target, and objects viewing memory in place.

use sonatina_codegen::OptLevel;
use wasmtime::Val;

use super::{aggregates::build_at, harness::Machine};

const LEVELS: [OptLevel; 3] = [OptLevel::O0, OptLevel::O2, OptLevel::Os];

/// A 16-byte-aligned buffer for the host, in a page the module does not use.
fn host_buffer(machine: &mut Machine) -> usize {
    let address = machine.memory_size();
    machine.grow_memory(1);
    address
}

#[test]
fn enum_variants_share_payload_storage() {
    // An i8 tag, then every variant's payload from offset 16, the i256's
    // alignment: `Pair`'s fields lie inside `Some`'s.
    let source = r#"
type @Choice = enum { #None, #Some(i256), #Pair(i8, i64) };
func public %write_pair(v10.*i8, v1.i64) {
block0:
    v0.*@Choice = bitcast v10 *@Choice;
    v2.objref<@Choice> = obj.alloc @Choice;
    enum.write_variant v2 #Pair (3.i8, v1);
    v3.@Choice = obj.load v2;
    mstore v0 v3 @Choice;
    return;
}
func public %write_some(v10.*i8, v1.i64) {
block0:
    v0.*@Choice = bitcast v10 *@Choice;
    v2.objref<@Choice> = obj.alloc @Choice;
    enum.set_tag v2 #Some;
    v3.objref<i256> = enum.proj v2 #Some 0.i8;
    v4.i256 = zext v1 i256;
    obj.store v3 v4;
    v5.@Choice = obj.load v2;
    mstore v0 v5 @Choice;
    return;
}
func public %read(v10.*i8) -> i64 {
block0:
    v0.*@Choice = bitcast v10 *@Choice;
    v1.@Choice = mload v0 @Choice;
    v2.i1 = enum.is_variant v1 #Pair;
    br v2 block1 block2;
block1:
    enum.assert_variant v1 #Pair;
    v3.i64 = enum.extract v1 #Pair 1.i8;
    return v3;
block2:
    v4.i1 = enum.is_variant v1 #Some;
    br v4 block3 block4;
block3:
    enum.assert_variant v1 #Some;
    v5.i256 = enum.extract v1 #Some 0.i8;
    v6.i64 = trunc v5 i64;
    return v6;
block4:
    return -1.i64;
}
func public %object_tag(v10.*i8) -> i64 {
block0:
    v0.*@Choice = bitcast v10 *@Choice;
    v1.@Choice = mload v0 @Choice;
    v2.objref<@Choice> = obj.alloc @Choice;
    obj.store v2 v1;
    v3.enumtag(@Choice) = enum.get_tag v2;
    br_table v3 block4 (0.enumtag(@Choice) block1) (1.enumtag(@Choice) block2) (2.enumtag(@Choice) block3);
block1:
    return 10.i64;
block2:
    return 11.i64;
block3:
    return 12.i64;
block4:
    return -1.i64;
}
func public %value_tag(v10.*i8) -> i64 {
block0:
    v0.*@Choice = bitcast v10 *@Choice;
    v1.@Choice = mload v0 @Choice;
    v2.enumtag(@Choice) = enum.tag v1;
    br_table v2 block4 (0.enumtag(@Choice) block1) (1.enumtag(@Choice) block2) (2.enumtag(@Choice) block3);
block1:
    return 20.i64;
block2:
    return 21.i64;
block3:
    return 22.i64;
block4:
    return -1.i64;
}
"#;
    for level in LEVELS {
        let mut machine = Machine::new(&build_at(source, level));
        let choice = host_buffer(&mut machine);
        let [write_pair, write_some, read, object_tag, value_tag] = [
            "write_pair",
            "write_some",
            "read",
            "object_tag",
            "value_tag",
        ]
        .map(|name| machine.func(name));
        let address = Val::I32(choice as i32);
        let i64_result =
            |machine: &mut Machine, func| machine.call(func, &[address])[0].unwrap_i64();

        machine.write(choice, &[0xaa; 48]);
        machine.call(&write_pair, &[address, Val::I64(0x1122_3344_5566_7788)]);
        let bytes = machine.read(choice, 48);
        assert_eq!(bytes[0], 2, "{level:?}");
        assert_eq!(bytes[16], 3, "{level:?}");
        assert_eq!(
            bytes[24..32],
            0x1122_3344_5566_7788i64.to_le_bytes(),
            "{level:?}"
        );
        assert_eq!(
            i64_result(&mut machine, &read),
            0x1122_3344_5566_7788,
            "{level:?}"
        );
        assert_eq!(i64_result(&mut machine, &object_tag), 12, "{level:?}");
        assert_eq!(i64_result(&mut machine, &value_tag), 22, "{level:?}");

        machine.call(&write_some, &[address, Val::I64(99)]);
        let bytes = machine.read(choice, 48);
        assert_eq!(bytes[0], 1, "{level:?}");
        let mut some = [0; 32];
        some[0] = 99;
        assert_eq!(bytes[16..48], some, "{level:?}");
        assert_eq!(i64_result(&mut machine, &read), 99, "{level:?}");
        assert_eq!(i64_result(&mut machine, &object_tag), 11, "{level:?}");
        assert_eq!(i64_result(&mut machine, &value_tag), 21, "{level:?}");
    }
}

#[test]
fn enum_values_zero_bytes_outside_their_variant() {
    // `dirty` and `clean` place their frames at the same address, so unless
    // they are inlined, `clean`'s slots still hold `dirty`'s values.
    let source = r#"
type @Choice = enum { #None, #Some(i256), #Pair(i8, i64) };
func private %dirty(v10.*i8, v11.*i8) {
block0:
    v0.*@Choice = bitcast v10 *@Choice;
    v1.@Choice = enum.make @Choice #Some (-1.i256);
    mstore v0 v1 @Choice;
    v2.*@Choice = bitcast v11 *@Choice;
    v3.@Choice = enum.make @Choice #Some (-2.i256);
    mstore v2 v3 @Choice;
    return;
}
func private %clean(v10.*i8, v11.*i8, v1.i64) {
block0:
    v0.*@Choice = bitcast v10 *@Choice;
    v2.@Choice = enum.make @Choice #None;
    mstore v0 v2 @Choice;
    v3.*@Choice = bitcast v11 *@Choice;
    v4.@Choice = enum.make @Choice #Pair (3.i8, v1);
    mstore v3 v4 @Choice;
    return;
}
func public %make(v10.*i8, v11.*i8, v1.i64) {
block0:
    call %dirty v10 v11;
    call %clean v10 v11 v1;
    return;
}
"#;
    for level in LEVELS {
        let mut machine = Machine::new(&build_at(source, level));
        let buffer = host_buffer(&mut machine);
        let make = machine.func("make");
        let (none, pair) = (buffer, buffer + 48);
        machine.write(none, &[0xaa; 96]);
        machine.call(
            &make,
            &[
                Val::I32(none as i32),
                Val::I32(pair as i32),
                Val::I64(0x1122_3344_5566_7788),
            ],
        );
        assert_eq!(machine.read(none, 48), [0; 48], "{level:?}");
        let mut expected = [0; 48];
        expected[0] = 2;
        expected[16] = 3;
        expected[24..32].copy_from_slice(&0x1122_3344_5566_7788i64.to_le_bytes());
        assert_eq!(machine.read(pair, 48), expected, "{level:?}");
    }
}

#[test]
fn enums_pass_through_calls_and_loop_phis() {
    // `step` takes an enum and returns one through the caller's buffer; the
    // loop carries the enum in a phi and switches variants as it goes.
    let source = r#"
type @Opt = enum { #None, #Some(i64) };
func private %step(v0.@Opt, v1.i64) -> @Opt {
block0:
    v2.i1 = enum.is_variant v0 #Some;
    br v2 block1 block2;
block1:
    v3.i64 = enum.extract v0 #Some 0.i8;
    v4.i64 = add v3 v1;
    v5.i1 = gt v4 100.i64;
    br v5 block3 block4;
block2:
    v6.@Opt = enum.make @Opt #Some (v1);
    return v6;
block3:
    v7.@Opt = enum.make @Opt #None;
    return v7;
block4:
    v8.@Opt = enum.make @Opt #Some (v4);
    return v8;
}
func public %run(v0.i64) -> i64 {
block0:
    v1.@Opt = enum.make @Opt #None;
    jump block1;
block1:
    v2.i64 = phi (0.i64 block0) (v5 block1);
    v3.@Opt = phi (v1 block0) (v4 block1);
    v4.@Opt = call %step v3 v0;
    v5.i64 = add v2 1.i64;
    v6.i1 = lt v5 10.i64;
    br v6 block1 block2;
block2:
    v7.i1 = enum.is_variant v4 #Some;
    br v7 block3 block4;
block3:
    v8.i64 = enum.extract v4 #Some 0.i8;
    return v8;
block4:
    return -1.i64;
}
"#;
    // Ten steps from None with increment n: the running sum restarts after it
    // passes 100.
    let model = |n: i64| {
        let mut state: Option<i64> = None;
        for _ in 0..10 {
            state = match state {
                None => Some(n),
                Some(value) if value + n > 100 => None,
                Some(value) => Some(value + n),
            };
        }
        state.unwrap_or(-1)
    };
    for level in LEVELS {
        let mut machine = Machine::new(&build_at(source, level));
        let run = machine.func("run");
        for n in [1, 7, 30, 51, 120] {
            let got = machine.call(&run, &[Val::I64(n)])[0].unwrap_i64();
            assert_eq!(got, model(n), "{level:?} n={n}");
        }
    }
}

#[test]
fn views_of_host_memory_are_objects_in_place() {
    // One `%bump` serves a local object and a view of host memory; a raw load
    // after a store through a view reads the stored value.
    let source = r#"
type @Rec = { i8, i64, i256 };
func private %bump(v0.objref<@Rec>, v1.i64) {
block0:
    v2.objref<i64> = obj.proj v0 1.i8;
    v3.i64 = obj.load v2;
    v4.i64 = add v3 v1;
    obj.store v2 v4;
    v5.objref<i256> = obj.proj v0 2.i8;
    v6.i256 = zext v4 i256;
    obj.store v5 v6;
    return;
}
func public %bump_host(v10.*i8, v1.i64) {
block0:
    v0.*@Rec = bitcast v10 *@Rec;
    v2.objref<@Rec> = obj.from_ptr v0;
    call %bump v2 v1;
    return;
}
func public %bump_local(v1.i64) -> i64 {
block0:
    v0.objref<@Rec> = obj.alloc @Rec;
    v2.@Rec = insert_value undef.@Rec 0.i8 0.i8;
    v3.@Rec = insert_value v2 1.i8 0.i64;
    v4.@Rec = insert_value v3 2.i8 0.i256;
    obj.store v0 v4;
    call %bump v0 v1;
    v5.objref<i64> = obj.proj v0 1.i8;
    v6.i64 = obj.load v5;
    return v6;
}
func public %store_through_view(v10.*i8) -> i64 {
block0:
    v0.*@Rec = bitcast v10 *@Rec;
    v1.*i64 = gep v0 0.i32 1.i32;
    mstore v1 1.i64 i64;
    v2.objref<@Rec> = obj.from_ptr v0;
    v3.objref<i64> = obj.proj v2 1.i8;
    obj.store v3 5.i64;
    v4.i64 = mload v1 i64;
    return v4;
}
"#;
    for level in LEVELS {
        let mut machine = Machine::new(&build_at(source, level));
        let rec = host_buffer(&mut machine);
        let address = Val::I32(rec as i32);
        let [bump_host, bump_local, store_through_view] =
            ["bump_host", "bump_local", "store_through_view"].map(|name| machine.func(name));
        machine.call(&bump_host, &[address, Val::I64(7)]);
        machine.call(&bump_host, &[address, Val::I64(7)]);
        let bytes = machine.read(rec, 48);
        assert_eq!(bytes[8..16], 14i64.to_le_bytes(), "{level:?}");
        let mut wide = [0; 32];
        wide[0] = 14;
        assert_eq!(bytes[16..48], wide, "{level:?}");
        assert_eq!(
            machine.call(&bump_local, &[Val::I64(3)])[0].unwrap_i64(),
            3,
            "{level:?}"
        );
        assert_eq!(
            machine.call(&store_through_view, &[address])[0].unwrap_i64(),
            5,
            "{level:?}"
        );
    }
}
