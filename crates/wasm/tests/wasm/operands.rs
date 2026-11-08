//! Operand forms the verifier accepts: constant and wide indices, integer
//! addresses, pointer tests, switches on 256-bit integers and boolean
//! bitcasts. A constant operand behaves as the same value computed at run
//! time, so an optimization that folds it changes nothing.

use sonatina_codegen::OptLevel;
use wasmtime::Val;

use super::{aggregates::build_at, harness::Machine};

const LEVELS: [OptLevel; 2] = [OptLevel::O0, OptLevel::O2];

#[test]
fn black_box_returns_its_operand() {
    let source = "func public %narrow(v0.i32) -> i32 {
    block0:
        v1.i32 = black_box v0;
        return v1;
}
func public %wide(v0.i64) -> i64 {
    block0:
        v1.i256 = zext v0 i256;
        v2.i256 = black_box v1;
        v3.i64 = trunc v2 i64;
        return v3;
}";
    for level in LEVELS {
        let bytes = build_at(source, level);
        let mut machine = Machine::new(&bytes);
        let narrow = machine.func("narrow");
        assert_eq!(machine.call(&narrow, &[Val::I32(7)])[0].unwrap_i32(), 7);
        let wide = machine.func("wide");
        assert_eq!(machine.call(&wide, &[Val::I64(-2)])[0].unwrap_i64(), -2);
    }
}

#[test]
fn a_constant_gep_index_steps_as_the_same_index_at_run_time() {
    // `true` of type `i1` is -1, as a constant and at run time.
    let source = "func public %constant(v0.*i32) -> i32 {
    block0:
        v1.*i32 = gep v0 1.i1;
        v2.i32 = ptr_to_int v1 i32;
        return v2;
}
func public %dynamic(v0.*i32, v1.i1) -> i32 {
    block0:
        v2.*i32 = gep v0 v1;
        v3.i32 = ptr_to_int v2 i32;
        return v3;
}
func public %folded(v0.*i32) -> i32 {
    block0:
        v1.i32 = ptr_to_int v0 i32;
        v2.i1 = eq v1 v1;
        v3.*i32 = gep v0 v2;
        v4.i32 = ptr_to_int v3 i32;
        return v4;
}";
    for level in LEVELS {
        let mut machine = Machine::new(&build_at(source, level));
        let [constant, dynamic, folded] =
            ["constant", "dynamic", "folded"].map(|name| machine.func(name));
        let base = Val::I32(100);
        assert_eq!(
            machine.call(&constant, &[base])[0].unwrap_i32(),
            96,
            "{level:?}"
        );
        assert_eq!(
            machine.call(&dynamic, &[base, Val::I32(1)])[0].unwrap_i32(),
            96,
            "{level:?}"
        );
        assert_eq!(
            machine.call(&folded, &[base])[0].unwrap_i32(),
            96,
            "{level:?}"
        );
    }
}

#[test]
fn a_constant_index_outside_32_bits_traps_when_executed() {
    // The index traps as it does at run time, and a function that never
    // executes it compiles.
    let source = "func public %constant(v0.i32) -> i32 {
    block0:
        v1.*i32 = int_to_ptr v0 *i32;
        v2.*i32 = gep v1 4294967296.i64;
        v3.i32 = ptr_to_int v2 i32;
        return v3;
}
func public %dynamic(v0.i32, v1.i64) -> i32 {
    block0:
        v2.*i32 = int_to_ptr v0 *i32;
        v3.*i32 = gep v2 v1;
        v4.i32 = ptr_to_int v3 i32;
        return v4;
}
func public %guarded(v0.i32, v1.i1) -> i32 {
    block0:
        br v1 block1 block2;
    block1:
        v2.*i32 = int_to_ptr v0 *i32;
        v3.*i32 = gep v2 4611686018427387904.i64;
        v4.i32 = ptr_to_int v3 i32;
        return v4;
    block2:
        return 0.i32;
}
func public %negative(v0.i32) -> i32 {
    block0:
        v1.*i32 = int_to_ptr v0 *i32;
        v2.*i32 = gep v1 -2.i64;
        v3.i32 = ptr_to_int v2 i32;
        return v3;
}";
    for level in LEVELS {
        let mut machine = Machine::new(&build_at(source, level));
        let [constant, dynamic, guarded, negative] =
            ["constant", "dynamic", "guarded", "negative"].map(|name| machine.func(name));
        let base = Val::I32(1000);
        assert!(machine.try_call(&constant, &[base]).is_err(), "{level:?}");
        assert!(
            machine
                .try_call(&dynamic, &[base, Val::I64(1 << 32)])
                .is_err(),
            "{level:?}"
        );
        assert_eq!(
            machine.call(&guarded, &[base, Val::I32(0)])[0].unwrap_i32(),
            0
        );
        assert!(machine.try_call(&guarded, &[base, Val::I32(1)]).is_err());
        assert_eq!(machine.call(&negative, &[base])[0].unwrap_i32(), 992);
    }
}

#[test]
fn integer_addresses_of_any_width_trap_when_they_do_not_fit() {
    // An address of 64 bits, like one of 256, traps when it does not fit in 32
    // bits; a narrow one is its value.
    let source = "func public %load(v0.i64) -> i32 {
    block0:
        v1.i32 = mload v0 i32;
        return v1;
}
func public %load16(v0.i16) -> i32 {
    block0:
        v1.i32 = mload v0 i32;
        return v1;
}
func public %via_pointer(v0.i64) -> i32 {
    block0:
        v1.*i32 = int_to_ptr v0 *i32;
        v2.i32 = mload v1 i32;
        return v2;
}
func public %via_wide_pointer(v0.i64) -> i32 {
    block0:
        v1.i256 = zext v0 i256;
        v2.*i32 = int_to_ptr v1 *i32;
        v3.i32 = mload v2 i32;
        return v3;
}";
    for level in LEVELS {
        let mut machine = Machine::new(&build_at(source, level));
        let address = machine.memory_size() - 4;
        machine.write(address, &7i32.to_le_bytes());
        machine.write(16, &5i32.to_le_bytes());
        for name in ["load", "via_pointer", "via_wide_pointer"] {
            let func = machine.func(name);
            assert_eq!(
                machine.call(&func, &[Val::I64(address as i64)])[0].unwrap_i32(),
                7,
                "{name} {level:?}"
            );
            assert!(
                machine
                    .try_call(&func, &[Val::I64(0x1_0000_0000 + 16)])
                    .is_err(),
                "{name} {level:?}"
            );
        }
        let load16 = machine.func("load16");
        assert_eq!(machine.call(&load16, &[Val::I32(16)])[0].unwrap_i32(), 5);
    }
}

#[test]
fn is_zero_tests_a_pointer_for_null() {
    let source = "func public %null(v0.*i8) -> i1 {
    block0:
        v1.i1 = is_zero v0;
        return v1;
}";
    for level in LEVELS {
        let mut machine = Machine::new(&build_at(source, level));
        let null = machine.func("null");
        assert_eq!(machine.call(&null, &[Val::I32(0)])[0].unwrap_i32(), 1);
        assert_eq!(machine.call(&null, &[Val::I32(64)])[0].unwrap_i32(), 0);
    }
}

#[test]
fn br_table_switches_on_a_256_bit_integer() {
    // The cases differ only above the low limb, so every limb is compared.
    let source = "func public %pick(v0.i64, v1.i64) -> i32 {
    block0:
        v2.i256 = zext v0 i256;
        v3.i256 = zext v1 i256;
        v4.i256 = shl 192.i256 v3;
        v5.i256 = or v2 v4;
        br_table v5 block4 (1.i256 block1) (2.i256 block2) (6277101735386680763835789423207666416102355444464034512897.i256 block3);
    block1:
        return 10.i32;
    block2:
        return 20.i32;
    block3:
        return 30.i32;
    block4:
        return 40.i32;
}";
    for level in LEVELS {
        let mut machine = Machine::new(&build_at(source, level));
        let pick = machine.func("pick");
        for (low, high, want) in [(1, 0, 10), (2, 0, 20), (1, 1, 30), (2, 1, 40), (3, 0, 40)] {
            assert_eq!(
                machine.call(&pick, &[Val::I64(low), Val::I64(high)])[0].unwrap_i32(),
                want,
                "{low} {high} {level:?}"
            );
        }
    }
}

#[test]
fn a_bitcast_of_a_256_bit_integer_to_itself_needs_no_frame() {
    let source = "func public %f(v0.i64) -> i64 {
    block0:
        v1.i256 = zext v0 i256;
        v2.i256 = bitcast v1 i256;
        v3.i64 = trunc v2 i64;
        return v3;
}";
    let mut machine = Machine::new(&super::harness::compile_valid(&super::harness::parse(
        source,
    )));
    let f = machine.func("f");
    assert_eq!(machine.call(&f, &[Val::I64(-3)])[0].unwrap_i64(), -3);
}

#[test]
fn boolean_bitcasts_keep_only_the_low_bit() {
    let source = "func public %to_bool(v0.i8) -> i1 {
    block0:
        v1.i1 = bitcast v0 i1;
        return v1;
}
func public %from_bool(v0.i1) -> i8 {
    block0:
        v1.i8 = bitcast v0 i8;
        return v1;
}";
    for level in LEVELS {
        let mut machine = Machine::new(&build_at(source, level));
        let [to_bool, from_bool] = ["to_bool", "from_bool"].map(|name| machine.func(name));
        for byte in 0..=255 {
            assert_eq!(
                machine.call(&to_bool, &[Val::I32(byte)])[0].unwrap_i32(),
                byte & 1,
                "{byte} {level:?}"
            );
        }
        for bit in [0, 1] {
            assert_eq!(
                machine.call(&from_bool, &[Val::I32(bit)])[0].unwrap_i32(),
                bit,
                "{bit} {level:?}"
            );
        }
    }
}

#[test]
fn modular_arithmetic_of_narrow_integers_is_exact() {
    // As on the native target, the operands are zero-extended, so the sum and
    // product do not wrap at the operands' width.
    let source = "func public %add8(v0.i8, v1.i8, v2.i8) -> i8 {
    block0:
        v3.i8 = evm_add_mod v0 v1 v2;
        return v3;
}
func public %mul64(v0.i64, v1.i64, v2.i64) -> i64 {
    block0:
        v3.i64 = evm_mul_mod v0 v1 v2;
        return v3;
}";
    for level in LEVELS {
        let mut machine = Machine::new(&build_at(source, level));
        let [add8, mul64] = ["add8", "mul64"].map(|name| machine.func(name));
        for (a, b, m) in [
            (200u8, 100u8, 7u8),
            (255, 255, 254),
            (3, 4, 0),
            (250, 9, 255),
        ] {
            let want = if m == 0 {
                0
            } else {
                ((u32::from(a) + u32::from(b)) % u32::from(m)) as u8
            };
            let args = [a, b, m].map(|value| Val::I32(i32::from(value)));
            assert_eq!(
                machine.call(&add8, &args)[0].unwrap_i32(),
                i32::from(want),
                "{a} + {b} mod {m} {level:?}"
            );
        }
        for (a, b, m) in [
            (u64::MAX, u64::MAX, u64::MAX - 1),
            (1 << 63, 4, 1_000_000_007),
            (5, 6, 0),
        ] {
            let want = if m == 0 {
                0
            } else {
                ((u128::from(a) * u128::from(b)) % u128::from(m)) as u64
            };
            let args = [a, b, m].map(|value| Val::I64(value as i64));
            assert_eq!(
                machine.call(&mul64, &args)[0].unwrap_i64() as u64,
                want,
                "{a} * {b} mod {m} {level:?}"
            );
        }
    }
}

#[test]
fn selects_choose_narrow_and_wide_values() {
    let source = "func public %narrow(v0.i32, v1.i32, v2.i32) -> i32 {
    block0:
        v3.i1 = ne v0 0.i32;
        v4.i32 = select v3 v1 v2;
        return v4;
}
func public %wide(v0.i32, v1.i64, v2.i64) -> i64 {
    block0:
        v3.i1 = ne v0 0.i32;
        v4.i256 = sext v1 i256;
        v5.i256 = zext v2 i256;
        v6.i256 = select v3 v4 v5;
        v7.i256 = shr 192.i256 v6;
        v8.i64 = trunc v7 i64;
        return v8;
}";
    for level in LEVELS {
        let bytes = build_at(source, level);
        let mut machine = Machine::new(&bytes);
        let narrow = machine.func("narrow");
        let wide = machine.func("wide");
        for cond in [0, 1, -1] {
            let chosen = machine.call(&narrow, &[Val::I32(cond), Val::I32(7), Val::I32(-9)]);
            assert_eq!(chosen[0].unwrap_i32(), if cond != 0 { 7 } else { -9 });
            // The top limb: all ones from the sign-extended -5, zero from 5.
            let top = machine.call(&wide, &[Val::I32(cond), Val::I64(-5), Val::I64(5)]);
            assert_eq!(top[0].unwrap_i64(), if cond != 0 { -1 } else { 0 });
        }
    }
}
