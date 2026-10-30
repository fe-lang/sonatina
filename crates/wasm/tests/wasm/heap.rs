//! The heap: size classes, reuse of freed blocks, the external `malloc` and
//! `free`, failure, `arena_mark` and `arena_release` together with free lists,
//! and a model that checks random sequences of all of them.

use std::collections::BTreeMap;

use sonatina_codegen::{Compile, OptLevel};
use sonatina_wasm::WasmBackend;
use wasmtime::Val;

use super::{
    harness::parse,
    memory_runtime::{DATA_BASE, Limited, PAGE, build_with, call_i32, with_host_allocator},
};
use crate::Lcg;

/// A module with the allocator of the module (`mem.alloc_dynamic` as `d`, the
/// external `malloc` as `m` and `free` as `f`) and a loop that allocates, writes
/// and frees.
const HEAP: &str = "declare external %malloc(i32) -> *i8;
declare external %free(*i8);
func public %m(v0.i32) -> i32 {
    block0:
        v1.*i8 = call %malloc v0;
        v2.i32 = ptr_to_int v1 i32;
        return v2;
}
func public %f(v0.i32) {
    block0:
        v1.*i8 = int_to_ptr v0 *i8;
        call %free v1;
        return;
}
func public %d(v0.i32) -> i32 {
    block0:
        v1.*i8 = mem.alloc_dynamic v0;
        v2.i32 = ptr_to_int v1 i32;
        return v2;
}
func public %churn(v0.i32, v1.i32) -> i32 {
    block0:
        jump block1;
    block1:
        v2.i32 = phi (0.i32 block0) (v8 block2);
        v3.i1 = lt v2 v0;
        br v3 block2 block3;
    block2:
        v4.*i8 = call %malloc v1;
        v5.*i32 = bitcast v4 *i32;
        mstore v5 v2 i32;
        call %free v4;
        v8.i32 = add v2 1.i32;
        jump block1;
    block3:
        return v2;
}
";

const STACK: usize = 1 << 16;
/// The heap starts on the page after the stack.
fn heap_start() -> u32 {
    (DATA_BASE + 128 + STACK).next_multiple_of(PAGE) as u32
}

fn machine(level: OptLevel, limit: usize) -> Limited {
    Limited::new(&with_host_allocator(HEAP, level), limit)
}

fn m(machine: &mut Limited, size: u32) -> u32 {
    call_i32(machine, "m", &[Val::I32(size as i32)]).unwrap()
}

fn d(machine: &mut Limited, size: u32) -> Result<u32, wasmtime::Error> {
    call_i32(machine, "d", &[Val::I32(size as i32)])
}

fn free(machine: &mut Limited, address: u32) -> Result<(), wasmtime::Error> {
    machine.call("f", &[Val::I32(address as i32)]).map(|_| ())
}

fn mark(machine: &mut Limited) -> u32 {
    call_i32(machine, "arena_mark", &[]).unwrap()
}

fn release(machine: &mut Limited, mark: u32) -> Result<(), wasmtime::Error> {
    machine
        .call("arena_release", &[Val::I32(mark as i32)])
        .map(|_| ())
}

const LEVELS: [OptLevel; 2] = [OptLevel::O0, OptLevel::O2];

#[test]
fn external_malloc_and_free_are_module_functions_and_not_imports() {
    for level in LEVELS {
        // The module instantiates with an empty linker, so it imports nothing.
        let mut machine = machine(level, usize::MAX);
        let start = heap_start();
        let a = m(&mut machine, 100);
        // The payload follows a 16-byte header; a 100-byte request takes 128
        // payload bytes.
        assert_eq!(a, start + 16, "{level:?}");
        assert_eq!(machine.read(a - 16, 4), 7u32.to_le_bytes(), "the class");
        assert_eq!(machine.read(a - 12, 4), 1u32.to_le_bytes(), "the state");
        let b = m(&mut machine, 100);
        assert_eq!(b, a + 128 + 16, "{level:?}");
    }
}

#[test]
fn a_freed_block_is_reused_before_the_heap_grows() {
    for level in LEVELS {
        let mut machine = machine(level, usize::MAX);
        let a = m(&mut machine, 100);
        let b = m(&mut machine, 100);
        let top = mark(&mut machine);
        free(&mut machine, a).unwrap();
        free(&mut machine, b).unwrap();
        // The last block freed is the first reused.
        assert_eq!(m(&mut machine, 128), b, "{level:?}");
        assert_eq!(m(&mut machine, 1), a + 128 + 16 + 128 + 16, "another class");
        assert_eq!(m(&mut machine, 65), a, "{level:?}");
        assert_eq!(
            mark(&mut machine),
            top + 32,
            "only the new class grew the heap"
        );
    }
}

#[test]
fn requests_round_up_to_a_power_of_two_class_of_at_least_16_bytes() {
    let mut machine = machine(OptLevel::O2, usize::MAX);
    let mut expected = heap_start();
    for (size, payload) in [
        (0u32, 16u32),
        (1, 16),
        (16, 16),
        (17, 32),
        (32, 32),
        (33, 64),
        (1000, 1024),
        (1024, 1024),
        (1025, 2048),
    ] {
        let address = m(&mut machine, size);
        assert_eq!(address, expected + 16, "size {size}");
        expected += 16 + payload;
        assert_eq!(mark(&mut machine), expected, "size {size}");
    }
}

#[test]
fn blocks_of_different_classes_use_different_lists() {
    let mut machine = machine(OptLevel::O2, usize::MAX);
    let small = m(&mut machine, 20);
    free(&mut machine, small).unwrap();
    let big = m(&mut machine, 100);
    assert_ne!(
        big, small,
        "a 128-byte request does not take a 32-byte block"
    );
    assert_eq!(
        m(&mut machine, 30),
        small,
        "a request of the same class does"
    );
}

#[test]
fn free_of_null_does_nothing() {
    let mut machine = machine(OptLevel::O2, usize::MAX);
    let before = mark(&mut machine);
    free(&mut machine, 0).unwrap();
    assert_eq!(mark(&mut machine), before);
    assert_eq!(m(&mut machine, 16), heap_start() + 16);
}

#[test]
fn double_free_and_free_of_a_non_block_trap_and_change_nothing() {
    for level in LEVELS {
        let mut machine = machine(level, usize::MAX);
        let a = m(&mut machine, 32);
        let b = m(&mut machine, 32);
        free(&mut machine, a).unwrap();
        // A second free of the same block, an address inside it, an address
        // below the heap, and one above the top all trap.
        assert!(free(&mut machine, a).is_err(), "double free");
        assert!(free(&mut machine, b + 1).is_err(), "misaligned");
        assert!(free(&mut machine, b + 16).is_err(), "inside a payload");
        assert!(free(&mut machine, 64).is_err(), "below the heap");
        let top = mark(&mut machine);
        assert!(free(&mut machine, top + 32).is_err(), "above the top");
        // The traps changed nothing: the freed block is still the first reused,
        // and the other block is still in use.
        assert_eq!(m(&mut machine, 32), a, "{level:?}");
        assert!(free(&mut machine, b).is_ok());
        assert_eq!(m(&mut machine, 32), b, "{level:?}");
    }
}

#[test]
fn malloc_returns_null_when_it_cannot_meet_a_request_and_dynamic_allocation_traps() {
    for level in LEVELS {
        // The host lets the memory grow to 8 MiB.
        let limit = 8 << 20;
        let mut machine = machine(level, limit);
        let before = machine.memory_bytes();
        // A request above 2 GiB fails at once, without growing the memory.
        assert_eq!(m(&mut machine, 0x8000_0001), 0);
        assert_eq!(m(&mut machine, u32::MAX), 0);
        assert!(d(&mut machine, 0x8000_0001).is_err());
        assert_eq!(machine.memory_bytes(), before);
        // A request the engine refuses to grow for returns null, and the heap
        // stays usable.
        let kept = m(&mut machine, 1000);
        machine.write(kept, &[0xab; 1000]);
        let top = mark(&mut machine);
        assert_eq!(m(&mut machine, 1 << 30), 0);
        assert!(d(&mut machine, 1 << 30).is_err());
        assert_eq!(mark(&mut machine), top, "a failure moves nothing");
        assert_eq!(machine.read(kept, 1000), vec![0xab; 1000]);
        assert_ne!(m(&mut machine, 64), 0);
    }
}

#[test]
fn a_module_that_only_frees_has_a_heap() {
    let source = "declare external %free(*i8);
func public %f(v0.i32) {
    block0:
        v1.*i8 = int_to_ptr v0 *i8;
        call %free v1;
        return;
}";
    let bytes = build_with(source, OptLevel::O2, WasmBackend::new());
    let mut machine = Limited::new(&bytes, usize::MAX);
    machine.call("f", &[Val::I32(0)]).unwrap();
    // A non-null address is not a block in a heap that has none.
    assert!(machine.call("f", &[Val::I32(1 << 20)]).is_err());
}

#[test]
fn a_mismatched_external_free_or_malloc_is_an_error() {
    for source in [
        "declare external %free(i64);
func public %f(v0.i64) {
    block0:
        call %free v0;
        return;
}",
        "declare external %malloc(i64) -> *i8;
func public %f(v0.i64) -> i32 {
    block0:
        v1.*i8 = call %malloc v0;
        v2.i32 = ptr_to_int v1 i32;
        return v2;
}",
        "declare external %malloc(i32) -> i32;
func public %f(v0.i32) -> i32 {
    block0:
        v1.i32 = call %malloc v0;
        return v1;
}",
    ] {
        let errors = Compile::new(parse(source), WasmBackend::new())
            .with_opt_level(OptLevel::O0)
            .compile()
            .err()
            .unwrap_or_else(|| panic!("the module should be rejected:\n{source}"));
        let text = format!("{errors:?}");
        assert!(
            text.contains("is the allocator of the WebAssembly module"),
            "{text}"
        );
    }
}

#[test]
fn blocks_freed_above_the_mark_are_forgotten_by_release() {
    for level in LEVELS {
        let mut machine = machine(level, usize::MAX);
        let mark_value = mark(&mut machine);
        // A block cut above the mark and freed sits on a list. Release forgets
        // it: after the release a smaller block takes its address, and a request
        // of the freed class must not hand out the stale entry.
        let stale = m(&mut machine, 100);
        assert_eq!(stale, mark_value + 16);
        free(&mut machine, stale).unwrap();
        release(&mut machine, mark_value).unwrap();
        assert_eq!(mark(&mut machine), mark_value);
        let small = m(&mut machine, 10);
        assert_eq!(small, mark_value + 16, "{level:?}");
        let big = m(&mut machine, 100);
        assert_eq!(big, mark_value + 32 + 16, "no overlap with the small block");
    }
}

#[test]
fn blocks_allocated_before_the_mark_and_freed_after_it_are_reused_after_release() {
    for level in LEVELS {
        let mut machine = machine(level, usize::MAX);
        let below = m(&mut machine, 100);
        let mark_value = mark(&mut machine);
        let above = m(&mut machine, 100);
        free(&mut machine, below).unwrap();
        free(&mut machine, above).unwrap();
        release(&mut machine, mark_value).unwrap();
        // The block below the mark stays on its list; the one above is gone.
        assert_eq!(m(&mut machine, 100), below, "{level:?}");
        assert_eq!(m(&mut machine, 100), mark_value + 16, "{level:?}");
    }
}

#[test]
fn a_free_list_chain_crossing_the_mark_keeps_its_low_part() {
    // Blocks of one class on both sides of the mark, freed in each order, so the
    // chain alternates between them.
    for order in [[0usize, 1, 2, 3], [3, 2, 1, 0], [1, 3, 0, 2], [2, 0, 3, 1]] {
        let mut machine = machine(OptLevel::O2, usize::MAX);
        let low = [m(&mut machine, 100), m(&mut machine, 100)];
        let mark_value = mark(&mut machine);
        let high = [m(&mut machine, 100), m(&mut machine, 100)];
        let all = [low[0], low[1], high[0], high[1]];
        for &index in &order {
            free(&mut machine, all[index]).unwrap();
        }
        release(&mut machine, mark_value).unwrap();
        // Both low blocks are still free, in the order they were freed last
        // first; both high ones are gone.
        let expected: Vec<u32> = order
            .iter()
            .rev()
            .map(|&index| all[index])
            .filter(|address| *address < mark_value)
            .collect();
        let got = [m(&mut machine, 100), m(&mut machine, 100)];
        assert_eq!(got.to_vec(), expected, "order {order:?}");
        assert_eq!(m(&mut machine, 100), mark_value + 16, "order {order:?}");
    }
}

#[test]
fn marks_nest() {
    let mut machine = machine(OptLevel::O2, usize::MAX);
    let outer = mark(&mut machine);
    let a = m(&mut machine, 50);
    let inner = mark(&mut machine);
    let b = m(&mut machine, 50);
    free(&mut machine, b).unwrap();
    release(&mut machine, inner).unwrap();
    assert_eq!(mark(&mut machine), inner);
    // The inner block is gone; the outer one is still in use and can be freed.
    free(&mut machine, a).unwrap();
    release(&mut machine, outer).unwrap();
    assert_eq!(mark(&mut machine), outer);
    // A mark above the top is refused.
    assert!(release(&mut machine, inner).is_err());
    assert_eq!(m(&mut machine, 50), outer + 16);
}

#[test]
fn a_mark_inside_a_block_does_not_corrupt_the_free_lists() {
    let mut machine = machine(OptLevel::O2, usize::MAX);
    let start = heap_start();
    let block = m(&mut machine, 100);
    free(&mut machine, block).unwrap();
    // A 16-byte-aligned address that `arena_mark` never returned.
    release(&mut machine, start + 32).unwrap();
    assert_eq!(mark(&mut machine), start + 32);
    // The block that crossed the mark is not handed out again.
    assert_eq!(m(&mut machine, 100), start + 32 + 16);
}

#[test]
fn a_bad_mark_traps_and_changes_nothing() {
    let mut machine = machine(OptLevel::O2, usize::MAX);
    let start = heap_start();
    let a = m(&mut machine, 100);
    free(&mut machine, a).unwrap();
    let top = mark(&mut machine);
    assert!(release(&mut machine, start - 16).is_err(), "below the heap");
    assert!(release(&mut machine, start + 8).is_err(), "misaligned");
    assert!(release(&mut machine, top + 16).is_err(), "above the top");
    assert_eq!(mark(&mut machine), top);
    assert_eq!(m(&mut machine, 100), a, "the list is unchanged");
}

#[test]
fn the_host_allocator_never_reuses_a_listed_block_and_returns_zeroes() {
    for level in LEVELS {
        let mut machine = machine(level, usize::MAX);
        let a = m(&mut machine, 16);
        machine.write(a, &[0xee; 16]);
        free(&mut machine, a).unwrap();
        let host = machine.alloc(16).unwrap();
        assert_ne!(host, a, "{level:?}");
        assert_eq!(machine.read(host, 16), vec![0; 16], "{level:?}");
        // The module allocator still has the freed block.
        assert_eq!(m(&mut machine, 16), a);
    }
}

#[test]
fn a_block_taken_from_a_list_may_hold_old_contents_and_a_fresh_block_is_zero() {
    let mut machine = machine(OptLevel::O2, usize::MAX);
    let a = m(&mut machine, 32);
    assert_eq!(machine.read(a, 32), vec![0; 32], "a fresh block is zero");
    machine.write(a, &[0x5a; 32]);
    free(&mut machine, a).unwrap();
    let again = m(&mut machine, 32);
    assert_eq!(again, a);
    // Only the link word is overwritten by the free; the rest is as it was left.
    assert_eq!(machine.read(a + 4, 28), vec![0x5a; 28]);
}

#[test]
fn a_churn_loop_stays_bounded() {
    for level in LEVELS {
        for (size, other) in [(100u32, 100u32), (4000, 4000), (24, 3000)] {
            let mut machine = machine(level, usize::MAX);
            let run = |machine: &mut Limited, rounds: i32, size: u32| {
                machine
                    .call("churn", &[Val::I32(rounds), Val::I32(size as i32)])
                    .unwrap()[0]
                    .unwrap_i32()
            };
            assert_eq!(run(&mut machine, 1, size), 1);
            let after_one = (machine.memory_bytes(), mark(&mut machine));
            assert_eq!(run(&mut machine, 100_000, size), 100_000);
            assert_eq!(run(&mut machine, 100_000, other), 100_000);
            let after_many = machine.memory_bytes();
            // One more class may add one block; nothing grows with the rounds.
            assert!(
                after_many <= after_one.0 + PAGE * 2,
                "{level:?} {size}/{other}: {} bytes after one round, {after_many} after many",
                after_one.0
            );
            assert!(
                (mark(&mut machine) - after_one.1) as usize <= 16 + 4096 + 16 + 4096,
                "{level:?} {size}/{other}: the top moved by more than the blocks of two classes"
            );
        }
    }
}

#[test]
fn churn_between_text_calls_stays_bounded() {
    let mut machine = machine(OptLevel::O2, usize::MAX);
    let mut tops = Vec::new();
    for round in 0..50 {
        // A call that frees what it allocates, outside any mark.
        machine
            .call("churn", &[Val::I32(1000), Val::I32(500)])
            .unwrap();
        // A call that follows the host protocol: mark, allocate, release.
        let mark_value = mark(&mut machine);
        let text = machine.alloc(300).unwrap();
        machine.write(text, &[round as u8; 300]);
        release(&mut machine, mark_value).unwrap();
        tops.push(mark(&mut machine));
    }
    assert!(
        tops.windows(2).skip(1).all(|pair| pair[0] == pair[1]),
        "the top changed between cycles: {tops:?}"
    );
}

/// A model of the heap: the same classes, last-in-first-out lists, and release
/// rule, over addresses only.
struct Model {
    top: u32,
    lists: Vec<Vec<u32>>,
    /// Payload address to class, for the blocks in use.
    live: BTreeMap<u32, u32>,
}

impl Model {
    fn new(start: u32) -> Self {
        Self {
            top: start,
            lists: vec![Vec::new(); 32],
            live: BTreeMap::new(),
        }
    }

    fn class(size: u32) -> u32 {
        32 - (size.max(16) - 1).leading_zeros()
    }

    /// Whether a request is served from a fresh cut, and where.
    fn malloc(&mut self, size: u32, from_list: bool) -> Option<(u32, bool)> {
        if size > 0x8000_0000 {
            return None;
        }
        let class = Self::class(size);
        if from_list && let Some(address) = self.lists[class as usize].pop() {
            self.live.insert(address, class);
            return Some((address, false));
        }
        let end = u64::from(self.top) + 16 + (1u64 << class);
        if end >> 32 != 0 {
            return None;
        }
        let address = self.top + 16;
        self.top = end as u32;
        self.live.insert(address, class);
        Some((address, true))
    }

    fn free(&mut self, address: u32) {
        let class = self.live.remove(&address).expect("a block in use");
        self.lists[class as usize].push(address);
    }

    fn release(&mut self, mark: u32) {
        for (class, list) in self.lists.iter_mut().enumerate() {
            list.retain(|&address| u64::from(address) + (1u64 << class) <= u64::from(mark));
        }
        self.live.retain(|&address, _| address - 16 < mark);
        self.top = mark;
    }
}

#[test]
fn random_alloc_free_mark_release_sequences_match_a_reference_heap() {
    let sizes = [
        0u32, 1, 15, 16, 17, 31, 32, 33, 63, 64, 65, 100, 255, 256, 257, 1000, 1023, 1024, 1025,
        4096, 5000, 65_535, 65_536, 65_537,
    ];
    for level in LEVELS {
        for seed in 1..=4u64 {
            let mut machine = machine(level, usize::MAX);
            let mut model = Model::new(heap_start());
            let mut rng = Lcg(0x5eed + seed);
            let mut marks: Vec<u32> = vec![model.top];
            // The pattern written into each block in use.
            let mut patterns: BTreeMap<u32, (usize, u8)> = BTreeMap::new();
            for step in 0..500 {
                let size = if rng.next().is_multiple_of(4) {
                    (rng.next() % 3000) as u32
                } else {
                    sizes[(rng.next() % sizes.len() as u64) as usize]
                };
                match rng.next() % 10 {
                    // Allocate with the allocator of the module (null on failure).
                    0..=2 => {
                        let want = model.malloc(size, true);
                        let got = m(&mut machine, size);
                        let (address, fresh) = want.expect("these requests fit");
                        assert_eq!(got, address, "step {step} seed {seed} {level:?}: m({size})");
                        check_new_block(&mut machine, got, size, fresh, &mut patterns, step);
                    }
                    // Allocate with `mem.alloc_dynamic`.
                    3 => {
                        let want = model.malloc(size, true);
                        let got = d(&mut machine, size).unwrap();
                        let (address, fresh) = want.expect("these requests fit");
                        assert_eq!(got, address, "step {step} seed {seed} {level:?}: d({size})");
                        check_new_block(&mut machine, got, size, fresh, &mut patterns, step);
                    }
                    // Allocate with the host allocator: always a fresh, zeroed block.
                    4 => {
                        let want = model.malloc(size, false);
                        let got = machine.alloc(size).unwrap();
                        let (address, fresh) = want.expect("these requests fit");
                        assert!(fresh);
                        assert_eq!(
                            got, address,
                            "step {step} seed {seed} {level:?}: alloc({size})"
                        );
                        check_new_block(&mut machine, got, size, true, &mut patterns, step);
                    }
                    // Free a random block in use.
                    5..=7 => {
                        if model.live.is_empty() {
                            continue;
                        }
                        let index = (rng.next() % model.live.len() as u64) as usize;
                        let address = *model.live.keys().nth(index).unwrap();
                        free(&mut machine, address).unwrap();
                        model.free(address);
                        patterns.remove(&address);
                    }
                    // Take a mark.
                    8 => {
                        let got = mark(&mut machine);
                        assert_eq!(got, model.top, "step {step} seed {seed} {level:?}: mark");
                        marks.push(got);
                    }
                    // Release to an earlier mark, or be refused for one above the top.
                    _ => {
                        let target = marks[(rng.next() % marks.len() as u64) as usize];
                        let result = release(&mut machine, target);
                        if target > model.top {
                            assert!(result.is_err(), "a mark above the top is refused");
                        } else {
                            result.unwrap();
                            model.release(target);
                            patterns.retain(|&address, _| model.live.contains_key(&address));
                            marks.retain(|&mark| mark <= model.top);
                        }
                    }
                }
                if step % 50 == 49 {
                    verify(&mut machine, &model, &patterns, seed, level);
                }
            }
            verify(&mut machine, &model, &patterns, seed, level);
            assert_eq!(mark(&mut machine), model.top);
        }
    }
}

/// A fresh block reads as zero; fill the block with a pattern of its own.
fn check_new_block(
    machine: &mut Limited,
    address: u32,
    size: u32,
    fresh: bool,
    patterns: &mut BTreeMap<u32, (usize, u8)>,
    step: usize,
) {
    assert_eq!(address % 16, 0, "alignment");
    let length = size.max(1) as usize;
    if fresh {
        assert!(
            machine.read(address, length).iter().all(|&byte| byte == 0),
            "step {step}: a fresh block is not zero"
        );
    }
    let fill = (step % 250) as u8 + 1;
    machine.write(address, &vec![fill; length]);
    patterns.insert(address, (length, fill));
}

/// Every block in use holds its own pattern, and blocks in use do not overlap.
fn verify(
    machine: &mut Limited,
    model: &Model,
    patterns: &BTreeMap<u32, (usize, u8)>,
    seed: u64,
    level: OptLevel,
) {
    let mut previous_end = 0u64;
    for (&address, &(length, fill)) in patterns {
        assert!(
            u64::from(address) >= previous_end,
            "seed {seed} {level:?}: blocks overlap at {address}"
        );
        let class = model.live[&address];
        previous_end = u64::from(address) + (1u64 << class);
        assert!(
            machine
                .read(address, length)
                .iter()
                .all(|&byte| byte == fill),
            "seed {seed} {level:?}: the block at {address} was overwritten"
        );
    }
}

#[test]
fn a_heap_with_a_small_memory_limit_fails_cleanly_in_the_middle_of_a_sequence() {
    for level in LEVELS {
        // 4 MiB: the stack page and a few pages of heap.
        let mut machine = machine(level, 4 << 20);
        let mut kept: Vec<(u32, u8)> = Vec::new();
        let mut failures = 0;
        for i in 0..200u32 {
            let size = 40_000 + (i % 7) * 1000;
            let before = mark(&mut machine);
            let address = m(&mut machine, size);
            if address == 0 {
                failures += 1;
                assert_eq!(mark(&mut machine), before, "a failure moves nothing");
                // Free something so that later requests can succeed again.
                if let Some((victim, _)) = kept.pop() {
                    free(&mut machine, victim).unwrap();
                }
            } else {
                let fill = (i % 250) as u8 + 1;
                machine.write(address, &vec![fill; size as usize]);
                kept.push((address, fill));
            }
            if i % 5 == 4 {
                // Everything still held is intact.
                for &(address, fill) in &kept {
                    assert_eq!(machine.read(address, 16), vec![fill; 16]);
                }
            }
        }
        assert!(failures > 0, "the limit was never reached ({level:?})");
        assert!(!kept.is_empty());
    }
}

#[test]
fn heap_poison_fills_a_freed_block_except_its_link() {
    for level in LEVELS {
        let bytes = build_with(
            HEAP,
            level,
            WasmBackend::new()
                .with_stack_size(STACK as u32)
                .with_host_allocator()
                .with_heap_poison(),
        );
        let mut machine = Limited::new(&bytes, usize::MAX);
        let a = m(&mut machine, 32);
        machine.write(a, &[0x11; 32]);
        free(&mut machine, a).unwrap();
        // A program that reads the block after freeing it sees the pattern.
        assert_eq!(machine.read(a + 4, 28), vec![0xA5; 28], "{level:?}");
        // The link in the first word is intact: the block is still reused.
        assert_eq!(m(&mut machine, 32), a, "{level:?}");
        assert_eq!(machine.read(a + 4, 28), vec![0xA5; 28], "{level:?}");
    }
}
