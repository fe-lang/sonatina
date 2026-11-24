//! `sha256_compress`: one SHA-256 compression of eight state words by sixteen
//! message words. With the x64 SHA extensions it is sixteen groups of four
//! rounds, each two `sha256rnds2`, with the message schedule from
//! `sha256msg1` and `sha256msg2`; elsewhere the 64 rounds are scalar code.
//!
//! A state or block that only passes between compressions, extracts,
//! inserts, `agg.make`s and constants is held as its words, in registers
//! (`Sha256Words`); any other is in memory, like other aggregates. The
//! schedule of a block of constant words is computed here.

use cranelift_codegen::ir::{
    self as clif, ConstantData, InstBuilder, MemFlagsData,
    types::{I8X16, I32, I32X4},
};
use cranelift_frontend::FunctionBuilder;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use sonatina_ir::{
    Function, Immediate, Type, Value, ValueId,
    global_variable::GvInitializer,
    inst::{
        InstId,
        data::{ConstLoad, ConstRef, ExtractValue, InsertValue, Sha256Compress},
        inst_set::InstSetExt,
        native::inst_set::NativeInstKind,
    },
    isa::native::inst_set as native_inst_set,
    types::CompoundType,
};

use super::{
    LOAD_FLAGS, ValueMap, constant_value_index, frame::FrameSlots, is_zero_literal, resolve_value,
};

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

/// A word of an `[i32; N]` held in registers: a constant, an i32 value, or
/// a lane of an i32x4 value.
#[derive(Clone, Copy, Debug)]
pub(super) enum Word {
    Const(u32),
    Value(clif::Value),
    Lane(clif::Value, u8),
}

impl Word {
    fn constant(self) -> Option<u32> {
        match self {
            Self::Const(constant) => Some(constant),
            Self::Value(_) | Self::Lane(..) => None,
        }
    }
}

pub(super) type Words = SmallVec<[Word; 16]>;

/// The `[i32; N]` values of a function held as words rather than in memory.
/// They are reached from the operands and results of compressions through
/// inserts; each is the result of a compression, an insert, an `agg.make`
/// or a load of a constant, and only compressions, extracts and inserts
/// take it. The source of an insert held is held or `zero`, and an insert
/// into a value held is held, so each is built and read word by word.
pub(super) struct Sha256Words {
    /// Whether compressions use the x64 SHA extensions.
    hardware: bool,
    held: FxHashSet<ValueId>,
    /// The words of the values held, as they are translated; a constant's
    /// from the start.
    words: FxHashMap<ValueId, Words>,
}

impl Sha256Words {
    pub fn new(function: &Function, hardware: bool) -> Self {
        let dfg = &function.dfg;
        // Whether `value` can be held, with its words if it is a constant:
        // only the constants reached from compressions are decoded.
        let takes_words = |value: ValueId| -> Option<Option<Words>> {
            let inst = dfg.value_inst(value)?;
            if word_count(function, value).is_none()
                || !dfg.users(value).all(|&user| {
                    match native_inst_set().resolve_inst(dfg.inst(user)) {
                        NativeInstKind::Sha256Compress(_) | NativeInstKind::ExtractValue(_) => true,
                        NativeInstKind::InsertValue(insert) => *insert.dest() == value,
                        _ => false,
                    }
                })
            {
                return None;
            }
            match native_inst_set().resolve_inst(dfg.inst(inst)) {
                NativeInstKind::Sha256Compress(_)
                | NativeInstKind::InsertValue(_)
                | NativeInstKind::AggMake(_) => Some(None),
                NativeInstKind::ConstLoad(_) => constant_words(function, inst).map(Some),
                _ => None,
            }
        };
        // The source of `value` if it is an insert, unless `zero`, and the
        // inserts into it.
        let neighbours = |value: ValueId| -> SmallVec<[ValueId; 2]> {
            let source = dfg
                .value_inst(value)
                .and_then(|inst| dfg.downcast::<&InsertValue>(inst))
                .map(|insert| *insert.dest())
                .filter(|&source| !is_zero_literal(function, source));
            let inserts = dfg.users(value).filter_map(|&user| {
                dfg.downcast::<&InsertValue>(user)
                    .filter(|insert| *insert.dest() == value)
                    .and_then(|_| dfg.inst_result(user))
            });
            source.into_iter().chain(inserts).collect()
        };
        let mut held = FxHashSet::default();
        let mut words = FxHashMap::default();
        let mut pending: Vec<_> = function
            .layout
            .iter_block()
            .flat_map(|block| function.layout.iter_inst(block))
            .filter_map(|inst| {
                let compress = dfg.downcast::<&Sha256Compress>(inst)?;
                Some(
                    [*compress.state(), *compress.block()]
                        .into_iter()
                        .chain(dfg.inst_result(inst)),
                )
            })
            .flatten()
            .collect();
        while let Some(value) = pending.pop() {
            if !held.contains(&value)
                && let Some(constant) = takes_words(value)
            {
                held.insert(value);
                words.extend(constant.map(|constant| (value, constant)));
                pending.extend(neighbours(value));
            }
        }
        // Drop each value next to one not held, until none is.
        while let Some(value) = held
            .iter()
            .copied()
            .find(|&value| neighbours(value).iter().any(|next| !held.contains(next)))
        {
            held.remove(&value);
        }
        words.retain(|value, _| held.contains(value));
        Self {
            hardware,
            held,
            words,
        }
    }

    pub fn holds(&self, value: ValueId) -> bool {
        self.held.contains(&value)
    }

    /// Translates `inst`, an `insert_value`, `agg.make` or `const.load`
    /// whose result is held.
    pub fn build(
        &mut self,
        function: &Function,
        inst: InstId,
        value_map: &ValueMap,
        builder: &mut FunctionBuilder,
    ) -> Result<(), String> {
        let result = function.dfg.inst_result(inst).ok_or("no result to hold")?;
        let words = match native_inst_set().resolve_inst(function.dfg.inst(inst)) {
            NativeInstKind::InsertValue(insert) => {
                let mut words =
                    self.operand(function, *insert.dest(), false, value_map, builder)?;
                let index = constant_value_index(function, *insert.idx(), "insert_value")?;
                *words
                    .get_mut(index)
                    .ok_or("insert_value index out of range")? =
                    word(function, *insert.value(), value_map, builder)?;
                words
            }
            NativeInstKind::AggMake(make) => make
                .values()
                .iter()
                .map(|&field| word(function, field, value_map, builder))
                .collect::<Result<_, _>>()?,
            // A constant's words are known from the start.
            _ => return Ok(()),
        };
        self.words.insert(result, words);
        Ok(())
    }

    /// The word `extract` takes of a value held.
    pub fn extract(
        &self,
        function: &Function,
        extract: &ExtractValue,
        builder: &mut FunctionBuilder,
    ) -> Result<clif::Value, String> {
        let index = constant_value_index(function, *extract.idx(), "extract_value")?;
        let word = self
            .words
            .get(extract.dest())
            .and_then(|words| words.get(index))
            .ok_or_else(|| format!("v{} has no word {index}", extract.dest().0))?;
        Ok(scalar(builder, *word))
    }

    /// Translates the compression `inst`, whose result is held or written
    /// to its storage.
    pub fn compress(
        &mut self,
        function: &Function,
        inst: InstId,
        op: &Sha256Compress,
        value_map: &mut ValueMap,
        frame: &FrameSlots,
        builder: &mut FunctionBuilder,
    ) -> Result<(), String> {
        let result = function
            .dfg
            .inst_result(inst)
            .ok_or("sha256_compress has no result")?;
        let state = self.operand(function, *op.state(), self.hardware, value_map, builder)?;
        let block = self.operand(function, *op.block(), false, value_map, builder)?;
        let words = compress(&state, &block, self.hardware, builder);
        if self.holds(result) {
            self.words.insert(result, words);
        } else {
            let dst = frame.address(result, builder)?;
            store_words(&words, dst, self.hardware, builder);
            value_map.insert(result, dst);
        }
        Ok(())
    }

    /// The words of `value`: its own if held, zeros for `zero`, and
    /// otherwise those in its storage, loaded four at a time if `wide`.
    fn operand(
        &self,
        function: &Function,
        value: ValueId,
        wide: bool,
        value_map: &ValueMap,
        builder: &mut FunctionBuilder,
    ) -> Result<Words, String> {
        if let Some(words) = self.words.get(&value) {
            return Ok(words.clone());
        }
        let count = word_count(function, value)
            .ok_or_else(|| format!("v{} is not an array of i32 words", value.0))?;
        if is_zero_literal(function, value) {
            return Ok(Words::from_elem(Word::Const(0), count));
        }
        let address = resolve_value(function, value, value_map, builder)?;
        Ok(load_words(address, count, wide, builder))
    }
}

/// The length of the type of `value` if it is an array of i32 words.
fn word_count(function: &Function, value: ValueId) -> Option<usize> {
    match function
        .dfg
        .value_ty(value)
        .resolve_compound(function.ctx())?
    {
        CompoundType::Array {
            elem: Type::I32,
            len,
        } => Some(len),
        _ => None,
    }
}

/// The words `inst` loads if it is a `const.load` of a whole constant array
/// of i32 words.
fn constant_words(function: &Function, inst: InstId) -> Option<Words> {
    let dfg = &function.dfg;
    let load = dfg.downcast::<&ConstLoad>(inst)?;
    let global = dfg
        .downcast::<&ConstRef>(dfg.value_inst(*load.object())?)?
        .global()
        .gv();
    function.ctx().with_gv_store(|globals| {
        let data = globals.gv_data(global);
        match &data.initializer {
            Some(GvInitializer::Array(elements)) if data.is_const => elements
                .iter()
                .map(|element| match element {
                    GvInitializer::Immediate(Immediate::I32(word)) => {
                        Some(Word::Const(*word as u32))
                    }
                    _ => None,
                })
                .collect(),
            _ => None,
        }
    })
}

/// The word an i32 `value` is.
fn word(
    function: &Function,
    value: ValueId,
    value_map: &ValueMap,
    builder: &mut FunctionBuilder,
) -> Result<Word, String> {
    Ok(match function.dfg.value(value) {
        Value::Immediate {
            imm: Immediate::I32(word),
            ..
        } => Word::Const(*word as u32),
        Value::Zero { .. } => Word::Const(0),
        _ => Word::Value(resolve_value(function, value, value_map, builder)?),
    })
}

/// The compression of the state words `state` by the message words
/// `block`. `hardware` selects the x64 SHA extensions, which leave the
/// result in lanes of two vectors.
fn compress(
    state: &[Word],
    block: &[Word],
    hardware: bool,
    builder: &mut FunctionBuilder,
) -> Words {
    if hardware {
        compress_sha_ni(state, block, builder)
    } else {
        compress_scalar(state, block, builder)
    }
}

/// The `count` words at `address`, loaded as i32x4 vectors if `wide`. A
/// block is often just written a word at a time, and a wider load could
/// not take its data from the stores.
fn load_words(
    address: clif::Value,
    count: usize,
    wide: bool,
    builder: &mut FunctionBuilder,
) -> Words {
    if wide {
        (0..count / 4)
            .flat_map(|group| {
                let offset = 16 * group as i32;
                let vector = builder.ins().load(I32X4, LOAD_FLAGS, address, offset);
                (0..4u8).map(move |lane| Word::Lane(vector, lane))
            })
            .collect()
    } else {
        (0..count)
            .map(|index| {
                let offset = 4 * index as i32;
                Word::Value(builder.ins().load(I32, LOAD_FLAGS, address, offset))
            })
            .collect()
    }
}

/// Stores `words` at `dst`, as i32x4 vectors if `wide`.
fn store_words(words: &[Word], dst: clif::Value, wide: bool, builder: &mut FunctionBuilder) {
    if wide {
        for (offset, group) in (0..).step_by(16).zip(words.chunks(4)) {
            let vector = vector(builder, group);
            builder
                .ins()
                .store(MemFlagsData::new(), vector, dst, offset);
        }
    } else {
        for (offset, &word) in (0..).step_by(4).zip(words) {
            let value = scalar(builder, word);
            builder.ins().store(MemFlagsData::new(), value, dst, offset);
        }
    }
}

/// The message schedule of a block of constant words.
fn constant_schedule(block: &[Word]) -> Option<[u32; 64]> {
    let mut w = [0; 64];
    for (slot, word) in w.iter_mut().zip(block) {
        *slot = word.constant()?;
    }
    for t in 16..64 {
        let s0 = w[t - 15].rotate_right(7) ^ w[t - 15].rotate_right(18) ^ (w[t - 15] >> 3);
        let s1 = w[t - 2].rotate_right(17) ^ w[t - 2].rotate_right(19) ^ (w[t - 2] >> 10);
        w[t] = w[t - 16]
            .wrapping_add(s0)
            .wrapping_add(w[t - 7])
            .wrapping_add(s1);
    }
    Some(w)
}

/// The SHA extensions keep the working variables as A, B, E, F and C, D,
/// G, H, each from lane 3 down, and take the message four words at a time.
/// The result's words are lanes of the two, so a next compression takes
/// them as they are.
fn compress_sha_ni(state: &[Word], block: &[Word], builder: &mut FunctionBuilder) -> Words {
    let abef0 = vector(builder, &[state[5], state[4], state[1], state[0]]);
    let cdgh0 = vector(builder, &[state[7], state[6], state[3], state[2]]);
    let (mut abef, mut cdgh) = (abef0, cdgh0);
    let schedule = constant_schedule(block);
    let mut w = [abef0; 16];
    for group in 0..16 {
        let lanes = 4 * group..4 * group + 4;
        let (wk, wk_high) = if let Some(schedule) = schedule {
            let wk: Vec<u32> = schedule[lanes.clone()]
                .iter()
                .zip(&K[lanes])
                .map(|(word, k)| word.wrapping_add(*k))
                .collect();
            (
                constant_vector(builder, &wk),
                constant_vector(builder, &[wk[2], wk[3], wk[2], wk[3]]),
            )
        } else {
            w[group] = if group < 4 {
                vector(builder, &block[lanes.clone()])
            } else {
                // Words 4g..4g+3: w[t-16] + sigma0(w[t-15]) from `sha256msg1`,
                // plus w[t-7], then sigma1(w[t-2]) from `sha256msg2`.
                let first = builder.ins().x86_sha256msg1(w[group - 4], w[group - 3]);
                let seventh = shuffle32(builder, w[group - 2], w[group - 1], [1, 2, 3, 4]);
                let sum = builder.ins().iadd(first, seventh);
                builder.ins().x86_sha256msg2(sum, w[group - 1])
            };
            let k = constant_vector(builder, &K[lanes]);
            let wk = builder.ins().iadd(w[group], k);
            (wk, shuffle32(builder, wk, wk, [2, 3, 2, 3]))
        };
        let next = builder.ins().x86_sha256rnds2(cdgh, abef, wk);
        cdgh = next;
        abef = builder.ins().x86_sha256rnds2(abef, next, wk_high);
    }
    let abef = builder.ins().iadd(abef, abef0);
    let cdgh = builder.ins().iadd(cdgh, cdgh0);
    [
        (abef, 3),
        (abef, 2),
        (cdgh, 3),
        (cdgh, 2),
        (abef, 1),
        (abef, 0),
        (cdgh, 1),
        (cdgh, 0),
    ]
    .into_iter()
    .map(|(vector, lane)| Word::Lane(vector, lane))
    .collect()
}

/// An i32x4 of four words: a shuffle of the vectors they are lanes of, if
/// at most two, and otherwise their constants with the other words
/// inserted.
fn vector(builder: &mut FunctionBuilder, words: &[Word]) -> clif::Value {
    let mut sources = SmallVec::<[clif::Value; 2]>::new();
    let mut lanes = [0; 4];
    let shuffled = words.iter().zip(&mut lanes).all(|(&word, slot)| {
        let Word::Lane(vector, lane) = word else {
            return false;
        };
        let source = sources
            .iter()
            .position(|&known| known == vector)
            .unwrap_or_else(|| {
                sources.push(vector);
                sources.len() - 1
            });
        *slot = 4 * source as u8 + lane;
        source < 2
    });
    if shuffled {
        let (first, last) = (sources[0], sources[sources.len() - 1]);
        return if first == last && lanes == [0, 1, 2, 3] {
            first
        } else {
            shuffle32(builder, first, last, lanes)
        };
    }
    let constants: Vec<u32> = words
        .iter()
        .map(|word| word.constant().unwrap_or(0))
        .collect();
    let mut vector = None;
    for (lane, &word) in (0u8..).zip(words) {
        if word.constant().is_some() {
            continue;
        }
        let value = scalar(builder, word);
        vector = Some(match vector {
            Some(vector) => builder.ins().insertlane(vector, value, lane),
            None if lane == 0 && constants.iter().all(|&constant| constant == 0) => {
                builder.ins().scalar_to_vector(I32X4, value)
            }
            None => {
                let base = constant_vector(builder, &constants);
                builder.ins().insertlane(base, value, lane)
            }
        });
    }
    vector.unwrap_or_else(|| constant_vector(builder, &constants))
}

/// The i32 value of `word`.
fn scalar(builder: &mut FunctionBuilder, word: Word) -> clif::Value {
    match word {
        Word::Const(constant) => builder.ins().iconst(I32, i64::from(constant)),
        Word::Value(value) => value,
        Word::Lane(vector, lane) => builder.ins().extractlane(vector, lane),
    }
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

fn constant_vector(builder: &mut FunctionBuilder, words: &[u32]) -> clif::Value {
    let bytes: Vec<u8> = words.iter().flat_map(|word| word.to_le_bytes()).collect();
    let constant = builder.func.dfg.constants.insert(ConstantData::from(bytes));
    builder.ins().vconst(I32X4, constant)
}

fn compress_scalar(state: &[Word], block: &[Word], builder: &mut FunctionBuilder) -> Words {
    let initial: Vec<_> = state.iter().map(|&word| scalar(builder, word)).collect();
    let schedule = constant_schedule(block);
    let mut w: Vec<_> = if schedule.is_some() {
        Vec::new()
    } else {
        block.iter().map(|&word| scalar(builder, word)).collect()
    };
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
        let s1 = big_sigma(builder, e, [6, 11, 25]);
        let picked = builder.ins().band(e, f);
        let other = builder.ins().band_not(g, e);
        let choice = builder.ins().bxor(picked, other);
        let t1 = builder.ins().iadd(h, s1);
        let t1 = builder.ins().iadd(t1, choice);
        let t1 = match schedule {
            // The word and the round constant add as one constant.
            Some(schedule) => builder
                .ins()
                .iadd_imm_u(t1, i64::from(k.wrapping_add(schedule[t]))),
            None => {
                if t >= 16 {
                    let s0 = sigma(builder, w[(t + 1) % 16], [7, 18], 3);
                    let s1 = sigma(builder, w[(t + 14) % 16], [17, 19], 10);
                    let sum = builder.ins().iadd(w[t % 16], s0);
                    let sum = builder.ins().iadd(sum, w[(t + 9) % 16]);
                    w[t % 16] = builder.ins().iadd(sum, s1);
                }
                let t1 = builder.ins().iadd_imm_u(t1, i64::from(k));
                builder.ins().iadd(t1, w[t % 16])
            }
        };
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
    [a, b, c, d, e, f, g, h]
        .into_iter()
        .zip(initial)
        .map(|(word, start)| Word::Value(builder.ins().iadd(word, start)))
        .collect()
}

#[cfg(all(test, feature = "jit"))]
mod tests {
    use cranelift_codegen::{
        ir::{AbiParam, Opcode, UserFuncName, types::I64},
        settings::{self, Configurable},
    };
    use cranelift_frontend::FunctionBuilderContext;
    use cranelift_jit::{JITBuilder, JITModule};
    use cranelift_module::{Linkage, Module};

    use super::*;

    const IV: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];

    /// The padding block of a 64-byte message.
    const PADDING: [u32; 16] = [0x8000_0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 512];

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

    /// The scalar code, and the SHA extensions if the host has them.
    fn modes() -> impl Iterator<Item = bool> {
        #[cfg(target_arch = "x86_64")]
        let has_sha = std::is_x86_feature_detected!("sha");
        #[cfg(not(target_arch = "x86_64"))]
        let has_sha = false;
        std::iter::once(false).chain(has_sha.then_some(true))
    }

    /// `words` as constant words.
    fn constants(words: &[u32]) -> Words {
        words.iter().copied().map(Word::Const).collect()
    }

    /// Compiles a function of a state, a block and a result pointer, whose
    /// body `body` builds from their addresses, and runs it.
    fn compile(
        body: impl FnOnce(clif::Value, clif::Value, clif::Value, &mut FunctionBuilder),
    ) -> impl Fn([u32; 8], [u32; 16]) -> [u32; 8] {
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
        body(state, block, dst, &mut builder);
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

    /// Thirty-two random states and blocks.
    fn inputs() -> Vec<([u32; 8], [u32; 16])> {
        let mut seed = 0x9e37_79b9_u32;
        let mut next = || {
            seed ^= seed << 13;
            seed ^= seed >> 17;
            seed ^= seed << 5;
            seed
        };
        (0..32)
            .map(|_| {
                (
                    std::array::from_fn(|_| next()),
                    std::array::from_fn(|_| next()),
                )
            })
            .collect()
    }

    #[test]
    fn compress_matches_the_reference() {
        // "abc", padded: its digest is the state after one block.
        let mut abc = [0u32; 16];
        abc[0] = 0x6162_6380;
        abc[15] = 24;
        let digest = [
            0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223, 0xb00361a3, 0x96177a9c, 0xb410ff61,
            0xf20015ad,
        ];
        assert_eq!(reference(IV, abc), digest);
        for hardware in modes() {
            let compress = compile(|state, block, dst, builder| {
                let state = load_words(state, 8, hardware, builder);
                let block = load_words(block, 16, false, builder);
                let words = super::compress(&state, &block, hardware, builder);
                store_words(&words, dst, hardware, builder);
            });
            assert_eq!(compress(IV, abc), digest, "hardware {hardware}");
            for (state, block) in inputs() {
                assert_eq!(
                    compress(state, block),
                    reference(state, block),
                    "hardware {hardware}"
                );
            }
        }
    }

    #[test]
    fn chained_compressions_hash_two_blocks() {
        // Each message's second block is its padding, a constant: 64 zero
        // bytes, and the 448-bit message of FIPS 180-4.
        let mut fips = [0u32; 16];
        fips[15] = 448;
        let mut message = [0u32; 16];
        for (word, bytes) in message.iter_mut().zip(
            b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq\x80\0\0\0\0\0\0\0".chunks(4),
        ) {
            *word = u32::from_be_bytes(bytes.try_into().unwrap());
        }
        let cases = [
            (
                PADDING,
                [0; 16],
                [
                    0xf5a5fd42, 0xd16a2030, 0x2798ef6e, 0xd309979b, 0x43003d23, 0x20d9f0e8,
                    0xea9831a9, 0x2759fb4b,
                ],
            ),
            (
                fips,
                message,
                [
                    0x248d6a61, 0xd20638b8, 0xe5c02693, 0x0c3e6039, 0xa33ce459, 0x64ff2167,
                    0xf6ecedd4, 0x19db06c1,
                ],
            ),
        ];
        for hardware in modes() {
            for (padding, first, digest) in cases {
                let hash = compile(|state, block, dst, builder| {
                    let state = load_words(state, 8, hardware, builder);
                    let block = load_words(block, 16, false, builder);
                    let middle = super::compress(&state, &block, hardware, builder);
                    let words = super::compress(&middle, &constants(&padding), hardware, builder);
                    store_words(&words, dst, hardware, builder);
                });
                assert_eq!(hash(IV, first), digest, "hardware {hardware}");
                for (state, block) in inputs() {
                    assert_eq!(
                        hash(state, block),
                        reference(reference(state, block), padding),
                        "hardware {hardware}"
                    );
                }
            }
        }
    }

    #[test]
    fn constant_blocks_have_their_schedule_computed() {
        // Only the schedule shifts the words, and only the schedule takes
        // `sha256msg1` and `sha256msg2`.
        for hardware in modes() {
            let compress = compile(|state, _, dst, builder| {
                let state = load_words(state, 8, hardware, builder);
                let words = super::compress(&state, &constants(&PADDING), hardware, builder);
                store_words(&words, dst, hardware, builder);
                let func = &builder.func;
                let opcodes: Vec<_> = func
                    .layout
                    .blocks()
                    .flat_map(|block| func.layout.block_insts(block))
                    .map(|inst| func.dfg.insts[inst].opcode())
                    .collect();
                assert!(
                    !opcodes.iter().any(|opcode| matches!(
                        opcode,
                        Opcode::Ushr | Opcode::X86Sha256msg1 | Opcode::X86Sha256msg2
                    )),
                    "hardware {hardware}: {opcodes:?}"
                );
            });
            for (state, _) in inputs() {
                assert_eq!(
                    compress(state, [0; 16]),
                    reference(state, PADDING),
                    "hardware {hardware}"
                );
            }
        }
    }

    #[test]
    fn partly_constant_blocks_match_the_reference() {
        // Groups of four words mixing constants, some with the high bit set,
        // and words loaded at run time: a constant before a loaded word, a
        // loaded word before nonzero constants, a loaded word before zeros,
        // and constants only.
        let pattern = [
            Some(0x8000_0001),
            None,
            Some(0),
            None,
            None,
            Some(0xdead_beef),
            None,
            Some(7),
            None,
            Some(0),
            Some(0),
            None,
            Some(0xffff_ffff),
            Some(0x0123_4567),
            Some(0x8000_0000),
            Some(1),
        ];
        for hardware in modes() {
            let compress = compile(|state, block, dst, builder| {
                let state = load_words(state, 8, hardware, builder);
                let loaded = load_words(block, 16, false, builder);
                let block: Words = pattern
                    .iter()
                    .zip(loaded)
                    .map(|(constant, word)| constant.map_or(word, Word::Const))
                    .collect();
                let words = super::compress(&state, &block, hardware, builder);
                store_words(&words, dst, hardware, builder);
            });
            for (state, block) in inputs() {
                let block = std::array::from_fn(|index| pattern[index].unwrap_or(block[index]));
                assert_eq!(
                    compress(state, block),
                    reference(state, block),
                    "hardware {hardware}"
                );
            }
        }
    }

    #[test]
    fn constant_states_match_the_reference() {
        // The initial state, and a state of words with the high bit set.
        let states = [
            IV,
            [
                0x8000_0000,
                0xffff_ffff,
                0x9e37_79b9,
                0x8000_0001,
                0xc0de_d00d,
                0xffff_fffe,
                0x8765_4321,
                0xa5a5_a5a5,
            ],
        ];
        for hardware in modes() {
            for constant in states {
                let compress = compile(|_, block, dst, builder| {
                    let block = load_words(block, 16, false, builder);
                    let words = super::compress(&constants(&constant), &block, hardware, builder);
                    store_words(&words, dst, hardware, builder);
                });
                for (_, block) in inputs() {
                    assert_eq!(
                        compress([0; 8], block),
                        reference(constant, block),
                        "hardware {hardware}"
                    );
                }
            }
        }
    }

    #[test]
    fn states_of_several_results_match_the_reference() {
        // A state of words of three compressions, a loaded word and a
        // constant: on the SHA extensions, ABEF takes lanes of three vectors,
        // more than a shuffle does, and CDGH mixes lanes with other words.
        for hardware in modes() {
            let compress = compile(|state, block, dst, builder| {
                let state = load_words(state, 8, hardware, builder);
                let block = load_words(block, 16, false, builder);
                let first = super::compress(&state, &block, hardware, builder);
                let second = super::compress(&constants(&IV), &block, hardware, builder);
                let third = super::compress(&first, &constants(&PADDING), hardware, builder);
                let mixed = [
                    first[0],
                    third[1],
                    block[3],
                    Word::Const(0x8000_0000),
                    second[4],
                    first[5],
                    third[6],
                    second[7],
                ];
                let words = super::compress(&mixed, &block, hardware, builder);
                store_words(&words, dst, hardware, builder);
            });
            for (state, block) in inputs() {
                let first = reference(state, block);
                let second = reference(IV, block);
                let third = reference(first, PADDING);
                let mixed = [
                    first[0],
                    third[1],
                    block[3],
                    0x8000_0000,
                    second[4],
                    first[5],
                    third[6],
                    second[7],
                ];
                assert_eq!(
                    compress(state, block),
                    reference(mixed, block),
                    "hardware {hardware}"
                );
            }
        }
    }
}
