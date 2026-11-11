//! `sha256_compress(state, block, dst)`: one SHA-256 compression, a function of
//! the module that every `sha256_compress` instruction calls with the addresses
//! of its eight state words, its sixteen message words and its result.
//!
//! WebAssembly has no SHA instructions, so the function runs the 64 rounds in a
//! loop. The round constants are a table in global data, followed by the 64
//! words of the message schedule, which the function writes before the rounds.
//! It is a leaf function: it calls nothing, so nothing else runs while the
//! schedule is in use. It reads the state and the block before it writes `dst`,
//! which may be either of them.

use waffle::{
    BlockTarget, FunctionBody, Memory, MemoryArg, Module as WModule, Operator, Signature,
    SignatureData, Terminator, Type as WType,
};

use super::{arith::Emit, memory::signature as module_signature};

/// The round constants: the first 32 bits of the fractional parts of the cube
/// roots of the first 64 primes.
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

/// The name of the function in the module's name section.
pub(super) const NAME: &str = "sha256_compress";

/// The bytes of the table of round constants.
const TABLE_BYTES: u32 = 64 * 4;

/// The bytes of global data the function uses: the table, then the schedule.
pub(super) const AREA_BYTES: u32 = 2 * TABLE_BYTES;

/// The initial contents of the area: the table, little-endian. The schedule
/// after it needs no initial contents.
pub(super) fn table() -> Vec<u8> {
    K.iter().flat_map(|k| k.to_le_bytes()).collect()
}

type V = waffle::Value;

/// The signature `(i32, i32, i32) -> ()` of the function.
pub(super) fn signature(wmod: &mut WModule<'static>) -> Signature {
    module_signature(
        wmod,
        SignatureData {
            params: vec![WType::I32; 3],
            returns: vec![],
        },
    )
}

fn word(memory: Memory, offset: u32) -> MemoryArg {
    MemoryArg {
        align: 2,
        offset,
        memory,
    }
}

fn target(block: waffle::Block, args: Vec<V>) -> BlockTarget {
    BlockTarget { block, args }
}

impl Emit<'_> {
    fn load(&mut self, memory: Memory, address: V, offset: u32) -> V {
        self.op(
            Operator::I32Load {
                memory: word(memory, offset),
            },
            &[address],
            WType::I32,
        )
    }

    fn store(&mut self, memory: Memory, address: V, offset: u32, value: V) {
        self.body.add_op(
            self.block,
            Operator::I32Store {
                memory: word(memory, offset),
            },
            &[address, value],
            &[],
        );
    }

    fn i32(&mut self, op: Operator, a: V, b: V) -> V {
        self.op(op, &[a, b], WType::I32)
    }

    fn add(&mut self, values: &[V]) -> V {
        values
            .iter()
            .copied()
            .reduce(|sum, value| self.i32(Operator::I32Add, sum, value))
            .expect("a sum of at least one value")
    }

    fn xor3(&mut self, a: V, b: V, c: V) -> V {
        let ab = self.i32(Operator::I32Xor, a, b);
        self.i32(Operator::I32Xor, ab, c)
    }

    /// The offset after `at` in a loop over the 64 words, and whether the loop
    /// goes on.
    fn step(&mut self, at: V) -> (V, V) {
        let four = self.c32(4);
        let next = self.i32(Operator::I32Add, at, four);
        let end = self.c32(TABLE_BYTES);
        (next, self.i32(Operator::I32Ne, next, end))
    }

    /// `x` rotated right by each of `amounts`, combined with `xor`.
    fn rotations(&mut self, x: V, amounts: [u32; 3]) -> V {
        let [a, b, c] = amounts.map(|amount| {
            let amount = self.c32(amount);
            self.i32(Operator::I32Rotr, x, amount)
        });
        self.xor3(a, b, c)
    }

    /// `x` rotated right by `r1` and `r2`, and shifted right by `s`, combined
    /// with `xor`: the small sigmas of the message schedule.
    fn sigma(&mut self, x: V, r1: u32, r2: u32, s: u32) -> V {
        let [a, b] = [r1, r2].map(|amount| {
            let amount = self.c32(amount);
            self.i32(Operator::I32Rotr, x, amount)
        });
        let s = self.c32(s);
        let shifted = self.i32(Operator::I32ShrU, x, s);
        self.xor3(a, b, shifted)
    }
}

/// The function `sha256_compress(state, block, dst)`, whose table of round
/// constants is at `area` and whose schedule follows it.
pub(super) fn build_compress(
    wmod: &WModule<'static>,
    sig: Signature,
    memory: Memory,
    area: u32,
) -> FunctionBody {
    let schedule = area + TABLE_BYTES;
    let mut body = FunctionBody::new(wmod, sig);
    let entry = body.entry;
    let [state, block, dst] = [0, 1, 2].map(|index| body.blocks[entry].params[index].1);
    let expand = body.add_block();
    let rounds = body.add_block();
    let round = body.add_block();
    let finish = body.add_block();

    // Words 0 to 15 of the schedule are the message.
    let mut em = Emit {
        body: &mut body,
        block: entry,
    };
    let base = em.c32(schedule);
    for index in 0..16 {
        let word = em.load(memory, block, 4 * index);
        em.store(memory, base, 4 * index, word);
    }
    let first = em.c32(64);
    body.set_terminator(
        entry,
        Terminator::Br {
            target: target(expand, vec![first]),
        },
    );

    // Word `t` from 16 to 63, at offset `at = 4t` of the schedule, is
    // `sigma1(w[t-2]) + w[t-7] + sigma0(w[t-15]) + w[t-16]`.
    let at = body.add_blockparam(expand, WType::I32);
    let mut em = Emit {
        body: &mut body,
        block: expand,
    };
    let w16 = em.load(memory, at, schedule - 64);
    let w15 = em.load(memory, at, schedule - 60);
    let w7 = em.load(memory, at, schedule - 28);
    let w2 = em.load(memory, at, schedule - 8);
    let s0 = em.sigma(w15, 7, 18, 3);
    let s1 = em.sigma(w2, 17, 19, 10);
    let word = em.add(&[s1, w7, s0, w16]);
    em.store(memory, at, schedule, word);
    let (next, more) = em.step(at);
    body.set_terminator(
        expand,
        Terminator::CondBr {
            cond: more,
            if_true: target(expand, vec![next]),
            if_false: target(rounds, vec![]),
        },
    );

    // The rounds, with the working variables `a` to `h` as parameters of
    // `round` after the offset `at = 4t` of round `t` in the table and the
    // schedule.
    let mut em = Emit {
        body: &mut body,
        block: rounds,
    };
    let mut initial = vec![em.c32(0)];
    initial.extend((0..8).map(|index| em.load(memory, state, 4 * index)));
    body.set_terminator(
        rounds,
        Terminator::Br {
            target: target(round, initial),
        },
    );

    let at = body.add_blockparam(round, WType::I32);
    let [a, b, c, d, e, f, g, h] = [(); 8].map(|()| body.add_blockparam(round, WType::I32));
    let mut em = Emit {
        body: &mut body,
        block: round,
    };
    let k = em.load(memory, at, area);
    let w = em.load(memory, at, schedule);
    let big_s1 = em.rotations(e, [6, 11, 25]);
    // ch(e, f, g) = g ^ (e & (f ^ g))
    let fg = em.i32(Operator::I32Xor, f, g);
    let efg = em.i32(Operator::I32And, e, fg);
    let ch = em.i32(Operator::I32Xor, g, efg);
    let t1 = em.add(&[h, big_s1, ch, k, w]);
    let big_s0 = em.rotations(a, [2, 13, 22]);
    // maj(a, b, c) = (a & b) | (c & (a | b))
    let ab = em.i32(Operator::I32And, a, b);
    let a_or_b = em.i32(Operator::I32Or, a, b);
    let c_ab = em.i32(Operator::I32And, c, a_or_b);
    let maj = em.i32(Operator::I32Or, ab, c_ab);
    let t2 = em.i32(Operator::I32Add, big_s0, maj);
    let new_a = em.i32(Operator::I32Add, t1, t2);
    let new_e = em.i32(Operator::I32Add, d, t1);
    let (next, more) = em.step(at);
    let after = vec![new_a, a, b, c, new_e, e, f, g];
    let mut again = vec![next];
    again.extend(&after);
    body.set_terminator(
        round,
        Terminator::CondBr {
            cond: more,
            if_true: target(round, again),
            if_false: target(finish, after),
        },
    );

    // The result is the state plus the working variables, word by word.
    let vars = [(); 8].map(|()| body.add_blockparam(finish, WType::I32));
    let mut em = Emit {
        body: &mut body,
        block: finish,
    };
    let sums: Vec<V> = vars
        .into_iter()
        .zip(0..)
        .map(|(var, index)| {
            let word = em.load(memory, state, 4 * index);
            em.i32(Operator::I32Add, word, var)
        })
        .collect();
    for (sum, index) in sums.into_iter().zip(0..) {
        em.store(memory, dst, 4 * index, sum);
    }
    body.set_terminator(finish, Terminator::Return { values: vec![] });
    body
}
