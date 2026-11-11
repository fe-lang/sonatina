//! `sha256_compress`, against the padded message "abc" and a reference
//! compression.

use sonatina_codegen::OptLevel;
use wasmtime::Val;

use super::{aggregates::build_at, harness::Machine};

const IV: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

/// The state after the 64 rounds of `block`, as FIPS 180-4 defines it.
fn reference(state: [u32; 8], block: [u32; 16]) -> [u32; 8] {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];
    let mut w = [0u32; 64];
    w[..16].copy_from_slice(&block);
    for t in 16..64 {
        let s0 = w[t - 15].rotate_right(7) ^ w[t - 15].rotate_right(18) ^ (w[t - 15] >> 3);
        let s1 = w[t - 2].rotate_right(17) ^ w[t - 2].rotate_right(19) ^ (w[t - 2] >> 10);
        w[t] = s1
            .wrapping_add(w[t - 7])
            .wrapping_add(s0)
            .wrapping_add(w[t - 16]);
    }
    let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = state;
    for t in 0..64 {
        let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
        let ch = (e & f) ^ (!e & g);
        let t1 = h
            .wrapping_add(s1)
            .wrapping_add(ch)
            .wrapping_add(K[t])
            .wrapping_add(w[t]);
        let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
        let maj = (a & b) ^ (a & c) ^ (b & c);
        let t2 = s0.wrapping_add(maj);
        (h, g, f, e, d, c, b, a) = (g, f, e, d.wrapping_add(t1), c, b, a, t1.wrapping_add(t2));
    }
    let words = [a, b, c, d, e, f, g, h];
    std::array::from_fn(|i| state[i].wrapping_add(words[i]))
}

/// `%compress(state, block, dst)` loads both operands, compresses and stores
/// the result; `%undefs(dst)` compresses `undef` operands.
const SOURCE: &str = "func public %compress(v0.*i8, v1.*i8, v2.*i8) {
    block0:
        v3.*[i32; 8] = bitcast v0 *[i32; 8];
        v4.*[i32; 16] = bitcast v1 *[i32; 16];
        v5.*[i32; 8] = bitcast v2 *[i32; 8];
        v6.[i32; 8] = mload v3 [i32; 8];
        v7.[i32; 16] = mload v4 [i32; 16];
        v8.[i32; 8] = sha256_compress v6 v7;
        mstore v5 v8 [i32; 8];
        return;
}
func public %undefs(v0.*i8) {
    block0:
        v1.*[i32; 8] = bitcast v0 *[i32; 8];
        v2.[i32; 8] = sha256_compress undef.[i32; 8] undef.[i32; 16];
        mstore v1 v2 [i32; 8];
        return;
}";

fn words(bytes: &[u8]) -> Vec<u32> {
    bytes
        .chunks(4)
        .map(|chunk| u32::from_le_bytes(chunk.try_into().unwrap()))
        .collect()
}

fn bytes(words: &[u32]) -> Vec<u8> {
    words.iter().flat_map(|word| word.to_le_bytes()).collect()
}

#[test]
fn sha256_compress_matches_the_reference() {
    // "abc", padded, is one block, and its digest is the state after it.
    let mut abc = [0u32; 16];
    abc[0] = 0x6162_6380;
    abc[15] = 24;
    let digest = [
        0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223, 0xb00361a3, 0x96177a9c, 0xb410ff61,
        0xf20015ad,
    ];
    assert_eq!(reference(IV, abc), digest);
    let mut seed = 0x9e37_79b9_u32;
    let mut next = || {
        seed ^= seed << 13;
        seed ^= seed >> 17;
        seed ^= seed << 5;
        seed
    };
    let mut cases = vec![(IV, abc)];
    cases.extend((0..16).map(|_| {
        (
            std::array::from_fn(|_| next()),
            std::array::from_fn(|_| next()),
        )
    }));
    for level in [OptLevel::O0, OptLevel::O2, OptLevel::Os] {
        let mut machine = Machine::new(&build_at(SOURCE, level));
        let base = machine.memory_size();
        machine.grow_memory(1);
        let (state, block, dst) = (base, base + 32, base + 96);
        let compress = machine.func("compress");
        for &(input, message) in &cases {
            machine.write(state, &bytes(&input));
            machine.write(block, &bytes(&message));
            let args = [state, block, dst].map(|address| Val::I32(address as i32));
            machine.call(&compress, &args);
            assert_eq!(
                words(&machine.read(dst, 32)),
                reference(input, message),
                "{level:?}"
            );
        }
        // An undefined operand is zero.
        let undefs = machine.func("undefs");
        machine.call(&undefs, &[Val::I32(dst as i32)]);
        assert_eq!(
            words(&machine.read(dst, 32)),
            reference([0; 8], [0; 16]),
            "{level:?}"
        );
    }
}
