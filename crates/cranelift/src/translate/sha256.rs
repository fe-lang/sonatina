//! `sha256_compress`: one SHA-256 compression of eight state words by sixteen
//! message words, each operand and the result in memory. With the x64 SHA
//! extensions it is sixteen groups of four rounds, each two `sha256rnds2`,
//! with the message schedule from `sha256msg1` and `sha256msg2`; elsewhere
//! the 64 rounds are scalar code.

use cranelift_codegen::ir::{
    self as clif, ConstantData, InstBuilder, MemFlagsData,
    types::{I8X16, I32, I32X4},
};
use cranelift_frontend::FunctionBuilder;

use super::LOAD_FLAGS;

const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

/// Writes to `dst` the compression of the state words at `state` by the
/// message words at `block`. `hardware` selects the x64 SHA extensions.
pub(super) fn compress(
    state: clif::Value,
    block: clif::Value,
    dst: clif::Value,
    hardware: bool,
    builder: &mut FunctionBuilder,
) {
    if hardware {
        compress_sha_ni(state, block, dst, builder)
    } else {
        compress_scalar(state, block, dst, builder)
    }
}

/// The SHA extensions keep the working variables as A, B, E, F and C, D,
/// G, H, each from lane 3 down, and take the message four words at a time.
fn compress_sha_ni(
    state: clif::Value,
    block: clif::Value,
    dst: clif::Value,
    builder: &mut FunctionBuilder,
) {
    let low = builder.ins().load(I32X4, LOAD_FLAGS, state, 0);
    let high = builder.ins().load(I32X4, LOAD_FLAGS, state, 16);
    // `low` is a, b, c, d and `high` e, f, g, h, from lane 0.
    let abef0 = shuffle32(builder, high, low, [1, 0, 5, 4]);
    let cdgh0 = shuffle32(builder, high, low, [3, 2, 7, 6]);
    let (mut abef, mut cdgh) = (abef0, cdgh0);
    let mut w = [abef0; 16];
    for group in 0..16 {
        w[group] = if group < 4 {
            // Word by word: the block is often just written a word at a
            // time, and a wider load could not take its data from the stores.
            let offset = 16 * group as i32;
            let first = builder.ins().load(I32, LOAD_FLAGS, block, offset);
            let mut words = builder.ins().scalar_to_vector(I32X4, first);
            for lane in 1..4 {
                let word = builder
                    .ins()
                    .load(I32, LOAD_FLAGS, block, offset + 4 * i32::from(lane));
                words = builder.ins().insertlane(words, word, lane);
            }
            words
        } else {
            // Words 4g..4g+3: w[t-16] + sigma0(w[t-15]) from `sha256msg1`,
            // plus w[t-7], then sigma1(w[t-2]) from `sha256msg2`.
            let first = builder.ins().x86_sha256msg1(w[group - 4], w[group - 3]);
            let seventh = shuffle32(builder, w[group - 2], w[group - 1], [1, 2, 3, 4]);
            let sum = builder.ins().iadd(first, seventh);
            builder.ins().x86_sha256msg2(sum, w[group - 1])
        };
        let k = vector(builder, &K[4 * group..4 * group + 4]);
        let wk = builder.ins().iadd(w[group], k);
        let next = builder.ins().x86_sha256rnds2(cdgh, abef, wk);
        let wk_high = shuffle32(builder, wk, wk, [2, 3, 2, 3]);
        cdgh = next;
        abef = builder.ins().x86_sha256rnds2(abef, next, wk_high);
    }
    let abef = builder.ins().iadd(abef, abef0);
    let cdgh = builder.ins().iadd(cdgh, cdgh0);
    let low = shuffle32(builder, abef, cdgh, [3, 2, 7, 6]);
    let high = shuffle32(builder, abef, cdgh, [1, 0, 5, 4]);
    builder.ins().store(MemFlagsData::new(), low, dst, 0);
    builder.ins().store(MemFlagsData::new(), high, dst, 16);
}

/// The 32-bit lanes `lanes` of `a` then `b`, numbered 0 to 7.
fn shuffle32(
    builder: &mut FunctionBuilder,
    a: clif::Value,
    b: clif::Value,
    lanes: [u8; 4],
) -> clif::Value {
    let mut bytes = |value| {
        builder.ins().bitcast(
            I8X16,
            MemFlagsData::new().with_endianness(clif::Endianness::Little),
            value,
        )
    };
    let (a, b) = (bytes(a), bytes(b));
    let mask: Vec<u8> = lanes
        .iter()
        .flat_map(|&lane| (0..4).map(move |byte| lane * 4 + byte))
        .collect();
    let mask = builder.func.dfg.immediates.push(ConstantData::from(mask));
    let shuffled = builder.ins().shuffle(a, b, mask);
    builder.ins().bitcast(
        I32X4,
        MemFlagsData::new().with_endianness(clif::Endianness::Little),
        shuffled,
    )
}

fn vector(builder: &mut FunctionBuilder, words: &[u32]) -> clif::Value {
    let bytes: Vec<u8> = words.iter().flat_map(|word| word.to_le_bytes()).collect();
    let constant = builder.func.dfg.constants.insert(ConstantData::from(bytes));
    builder.ins().vconst(I32X4, constant)
}

fn compress_scalar(
    state: clif::Value,
    block: clif::Value,
    dst: clif::Value,
    builder: &mut FunctionBuilder,
) {
    let initial: Vec<_> = (0..8)
        .map(|i| builder.ins().load(I32, LOAD_FLAGS, state, 4 * i))
        .collect();
    let mut w: Vec<_> = (0..16)
        .map(|i| builder.ins().load(I32, LOAD_FLAGS, block, 4 * i))
        .collect();
    let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = initial[..] else {
        unreachable!()
    };
    let sigma = |builder: &mut FunctionBuilder, x, rotations: [i64; 2], shift: i64| {
        let first = builder.ins().rotr_imm_u(x, rotations[0]);
        let second = builder.ins().rotr_imm_u(x, rotations[1]);
        let third = builder.ins().ushr_imm_u(x, shift);
        let mixed = builder.ins().bxor(first, second);
        builder.ins().bxor(mixed, third)
    };
    let big_sigma = |builder: &mut FunctionBuilder, x, rotations: [i64; 3]| {
        let first = builder.ins().rotr_imm_u(x, rotations[0]);
        let second = builder.ins().rotr_imm_u(x, rotations[1]);
        let third = builder.ins().rotr_imm_u(x, rotations[2]);
        let mixed = builder.ins().bxor(first, second);
        builder.ins().bxor(mixed, third)
    };
    for (t, &k) in K.iter().enumerate() {
        if t >= 16 {
            let s0 = sigma(builder, w[(t + 1) % 16], [7, 18], 3);
            let s1 = sigma(builder, w[(t + 14) % 16], [17, 19], 10);
            let sum = builder.ins().iadd(w[t % 16], s0);
            let sum = builder.ins().iadd(sum, w[(t + 9) % 16]);
            w[t % 16] = builder.ins().iadd(sum, s1);
        }
        let s1 = big_sigma(builder, e, [6, 11, 25]);
        let picked = builder.ins().band(e, f);
        let other = builder.ins().band_not(g, e);
        let choice = builder.ins().bxor(picked, other);
        let t1 = builder.ins().iadd(h, s1);
        let t1 = builder.ins().iadd(t1, choice);
        let t1 = builder.ins().iadd_imm_u(t1, i64::from(k));
        let t1 = builder.ins().iadd(t1, w[t % 16]);
        let s0 = big_sigma(builder, a, [2, 13, 22]);
        let ab = builder.ins().band(a, b);
        let either = builder.ins().bor(a, b);
        let c_either = builder.ins().band(c, either);
        let majority = builder.ins().bor(ab, c_either);
        let t2 = builder.ins().iadd(s0, majority);
        (h, g, f) = (g, f, e);
        e = builder.ins().iadd(d, t1);
        (d, c, b) = (c, b, a);
        a = builder.ins().iadd(t1, t2);
    }
    for (i, (word, start)) in [a, b, c, d, e, f, g, h]
        .into_iter()
        .zip(initial)
        .enumerate()
    {
        let sum = builder.ins().iadd(word, start);
        builder
            .ins()
            .store(MemFlagsData::new(), sum, dst, 4 * i as i32);
    }
}

#[cfg(all(test, feature = "jit"))]
mod tests {
    use cranelift_codegen::{
        ir::{AbiParam, UserFuncName, types::I64},
        settings::{self, Configurable},
    };
    use cranelift_frontend::FunctionBuilderContext;
    use cranelift_jit::{JITBuilder, JITModule};
    use cranelift_module::{Linkage, Module};

    use super::*;

    fn reference(state: [u32; 8], w: [u32; 16]) -> [u32; 8] {
        let mut w: Vec<u32> = w.to_vec();
        for t in 16..64 {
            let s0 = w[t - 15].rotate_right(7) ^ w[t - 15].rotate_right(18) ^ (w[t - 15] >> 3);
            let s1 = w[t - 2].rotate_right(17) ^ w[t - 2].rotate_right(19) ^ (w[t - 2] >> 10);
            w.push(
                w[t - 16]
                    .wrapping_add(s0)
                    .wrapping_add(w[t - 7])
                    .wrapping_add(s1),
            );
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = state;
        for t in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let choice = (e & f) ^ (!e & g);
            let t1 = h
                .wrapping_add(s1)
                .wrapping_add(choice)
                .wrapping_add(K[t])
                .wrapping_add(w[t]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let t2 = s0.wrapping_add((a & b) ^ (a & c) ^ (b & c));
            (h, g, f, e, d, c, b, a) = (g, f, e, d.wrapping_add(t1), c, b, a, t1.wrapping_add(t2));
        }
        let words = [a, b, c, d, e, f, g, h];
        std::array::from_fn(|i| state[i].wrapping_add(words[i]))
    }

    /// Compiles `compress` into a function of three pointers and runs it.
    fn compile(hardware: bool) -> impl Fn([u32; 8], [u32; 16]) -> [u32; 8] {
        let isa = cranelift_native::builder()
            .unwrap()
            .finish(settings::Flags::new({
                let mut flags = settings::builder();
                flags.set("opt_level", "speed").unwrap();
                flags
            }))
            .unwrap();
        let mut module = JITModule::new(JITBuilder::with_isa(
            isa,
            cranelift_module::default_libcall_names(),
        ));
        let mut signature = module.make_signature();
        signature.params.extend([AbiParam::new(I64); 3]);
        let id = module
            .declare_function("compress", Linkage::Local, &signature)
            .unwrap();
        let mut context = module.make_context();
        context.func.signature = signature;
        context.func.name = UserFuncName::user(0, id.as_u32());
        let mut builder_context = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut context.func, &mut builder_context);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        builder.seal_block(entry);
        let [state, block, dst] = builder.block_params(entry)[..] else {
            unreachable!()
        };
        compress(state, block, dst, hardware, &mut builder);
        builder.ins().return_(&[]);
        builder.finalize(module.isa().frontend_config());
        module.define_function(id, &mut context).unwrap();
        module.finalize_definitions().unwrap();
        let code = module.get_finalized_function(id);
        let function: unsafe extern "C" fn(*const u32, *const u32, *mut u32) =
            unsafe { std::mem::transmute(code) };
        // The module owns the code, so it lives as long as the closure.
        move |state: [u32; 8], block: [u32; 16]| {
            let _module = &module;
            let mut out = [0u32; 8];
            unsafe { function(state.as_ptr(), block.as_ptr(), out.as_mut_ptr()) };
            out
        }
    }

    #[test]
    fn compress_matches_the_reference() {
        const IV: [u32; 8] = [
            0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
            0x5be0cd19,
        ];
        // "abc", padded: its digest is the state after one block.
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
        let inputs: Vec<([u32; 8], [u32; 16])> = (0..32)
            .map(|_| {
                (
                    std::array::from_fn(|_| next()),
                    std::array::from_fn(|_| next()),
                )
            })
            .collect();
        #[cfg(target_arch = "x86_64")]
        let has_sha = std::is_x86_feature_detected!("sha");
        #[cfg(not(target_arch = "x86_64"))]
        let has_sha = false;
        for hardware in std::iter::once(false).chain(has_sha.then_some(true)) {
            let compress = compile(hardware);
            assert_eq!(compress(IV, abc), digest, "hardware {hardware}");
            for &(state, block) in &inputs {
                assert_eq!(
                    compress(state, block),
                    reference(state, block),
                    "hardware {hardware}"
                );
            }
        }
    }
}
