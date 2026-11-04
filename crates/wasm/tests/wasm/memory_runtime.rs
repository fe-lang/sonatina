//! The stack, the arena, global data and their limits.

use sonatina_codegen::{Backend, BackendOptions, Compile, OptLevel};
use sonatina_wasm::WasmBackend;
use wasmtime::{
    Caller, Engine, Instance, Linker, Module, Store, StoreLimits, StoreLimitsBuilder, Val,
};

use super::{
    aggregates::build_at,
    harness::{Machine, parse},
};
use crate::Lcg;

pub(crate) const PAGE: usize = 65536;
/// The lowest address the backend uses.
pub(crate) const DATA_BASE: usize = 16;

pub(crate) fn build_with(source: &str, level: OptLevel, backend: WasmBackend) -> Vec<u8> {
    let bytes = Compile::new(parse(source), backend)
        .with_opt_level(level)
        .compile()
        .unwrap_or_else(|errors| panic!("wasm compilation failed: {errors:?}\n{source}"))
        .into_bytes();
    wasmparser::Validator::new()
        .validate_all(&bytes)
        .unwrap_or_else(|error| panic!("emitted module is invalid: {error}"));
    bytes
}

/// A running module whose memory the host can limit.
pub(crate) struct Limited {
    store: Store<StoreLimits>,
    instance: Instance,
}

impl Limited {
    pub(crate) fn new(bytes: &[u8], memory_limit: usize) -> Self {
        Self::with_imports(bytes, memory_limit, |_| {})
    }

    fn with_imports(
        bytes: &[u8],
        memory_limit: usize,
        define: impl FnOnce(&mut Linker<StoreLimits>),
    ) -> Self {
        let engine = Engine::default();
        let module = Module::new(&engine, bytes).expect("wasmtime accepts the module");
        let mut linker = Linker::new(&engine);
        define(&mut linker);
        let limits = StoreLimitsBuilder::new().memory_size(memory_limit).build();
        let mut store = Store::new(&engine, limits);
        store.limiter(|limits| limits);
        let instance = linker
            .instantiate(&mut store, &module)
            .expect("instantiates");
        Self { store, instance }
    }

    pub(crate) fn call(&mut self, name: &str, args: &[Val]) -> Result<Vec<Val>, wasmtime::Error> {
        let func = self
            .instance
            .get_func(&mut self.store, name)
            .expect("export");
        let mut results = vec![Val::I32(0); func.ty(&self.store).results().len()];
        func.call(&mut self.store, args, &mut results)?;
        Ok(results)
    }

    pub(crate) fn alloc(&mut self, size: u32) -> Result<u32, wasmtime::Error> {
        Ok(self.call("alloc", &[Val::I32(size as i32)])?[0].unwrap_i32() as u32)
    }

    pub(crate) fn memory_bytes(&mut self) -> usize {
        let memory = self.instance.get_memory(&mut self.store, "memory").unwrap();
        memory.data_size(&self.store)
    }

    pub(crate) fn read(&mut self, address: u32, len: usize) -> Vec<u8> {
        let memory = self.instance.get_memory(&mut self.store, "memory").unwrap();
        memory.data(&self.store)[address as usize..address as usize + len].to_vec()
    }

    pub(crate) fn write(&mut self, address: u32, bytes: &[u8]) {
        let memory = self.instance.get_memory(&mut self.store, "memory").unwrap();
        memory.data_mut(&mut self.store)[address as usize..address as usize + bytes.len()]
            .copy_from_slice(bytes);
    }
}

const ALLOC: &str = "func public %alloc(v0.i32) -> *i8 {
    block0:
        v1.*i8 = mem.alloc_dynamic v0;
        return v1;
}
func public %alloc64(v0.i64) -> *i8 {
    block0:
        v1.*i8 = mem.alloc_dynamic v0;
        return v1;
}
func public %alloc_wide(v0.i64, v1.i64) -> *i8 {
    block0:
        v2.i256 = zext v0 i256;
        v3.i256 = zext v1 i256;
        v4.i256 = shl 64.i256 v3;
        v5.i256 = or v2 v4;
        v6.*i8 = mem.alloc_dynamic v5;
        return v6;
}
";

#[test]
fn arena_blocks_are_aligned_zeroed_and_never_overlap() {
    let stack = 1 << 16;
    for level in [OptLevel::O0, OptLevel::O2] {
        let bytes = build_with(ALLOC, level, WasmBackend::new().with_stack_size(stack));
        let mut machine = Limited::new(&bytes, usize::MAX);
        // The arena starts on the page after the stack.
        let arena = (DATA_BASE + stack as usize).next_multiple_of(PAGE);
        let mut rng = Lcg(0xa73a);
        let mut blocks: Vec<(u32, usize)> = Vec::new();
        let sizes = [
            0u32, 1, 15, 16, 17, 31, 100, 4096, 65535, 65536, 65537, 200_000, 1,
        ];
        for round in 0..400 {
            let size = if round < sizes.len() {
                sizes[round]
            } else {
                (rng.next() % 3000) as u32
            };
            let address = machine.alloc(size).unwrap();
            assert_eq!(address % 16, 0, "block {round} is not 16-byte aligned");
            assert!(
                address as usize >= arena,
                "block {round} lies below the arena"
            );
            if round == 0 {
                // The first block starts the heap, and its payload follows its
                // 16-byte header.
                assert_eq!(
                    address as usize,
                    arena + 16,
                    "the heap starts after the stack"
                );
            }
            let length = size.max(1) as usize;
            // A block cut from the top of the heap reads as zero (nothing has
            // been freed here, so every block is cut from the top).
            let content = machine.read(address, length);
            assert!(
                content.iter().all(|&b| b == 0),
                "block {round} is not zeroed"
            );
            // Fill the block with a pattern of its own.
            machine.write(address, &vec![(round % 251) as u8 + 1; length]);
            blocks.push((address, length));
        }
        // Blocks are disjoint, in increasing order, and each still holds its
        // own pattern after all the others were written.
        for pair in blocks.windows(2) {
            assert!(
                pair[0].0 as usize + pair[0].1 <= pair[1].0 as usize,
                "{pair:?} overlap"
            );
        }
        for (round, &(address, length)) in blocks.iter().enumerate() {
            let content = machine.read(address, length);
            assert!(
                content.iter().all(|&b| b == (round % 251) as u8 + 1),
                "block {round} was overwritten"
            );
        }
        // The memory grew to hold the last block.
        let (last, length) = *blocks.last().unwrap();
        assert!(machine.memory_bytes() >= last as usize + length);
    }
}

#[test]
fn sizes_of_other_widths_are_checked() {
    let bytes = build_with(ALLOC, OptLevel::O2, WasmBackend::new());
    let mut machine = Limited::new(&bytes, usize::MAX);
    // A 64-bit size in range is fine; one beyond 32 bits traps.
    let ok = machine.call("alloc64", &[Val::I64(100)]).unwrap();
    assert!(ok[0].unwrap_i32() != 0);
    assert!(machine.call("alloc64", &[Val::I64(1 << 32)]).is_err());
    assert!(machine.call("alloc64", &[Val::I64(-1)]).is_err());
    // A 256-bit size too: high limbs set, or low limb above 32 bits.
    assert!(
        machine
            .call("alloc_wide", &[Val::I64(8), Val::I64(0)])
            .is_ok()
    );
    assert!(
        machine
            .call("alloc_wide", &[Val::I64(1 << 32), Val::I64(0)])
            .is_err()
    );
    assert!(
        machine
            .call("alloc_wide", &[Val::I64(8), Val::I64(1)])
            .is_err()
    );
    // After the traps, small allocations still work.
    assert!(machine.alloc(16).is_ok());
}

#[test]
fn exhaustion_traps_and_corrupts_nothing() {
    let bytes = build_with(
        ALLOC,
        OptLevel::O2,
        WasmBackend::new().with_stack_size(1 << 16),
    );
    // The host lets the memory grow to 8 MiB and no further.
    let limit = 8 << 20;
    let mut machine = Limited::new(&bytes, limit);
    let first = machine.alloc(1000).unwrap();
    machine.write(first, &[0xab; 1000]);
    let mut kept = vec![(first, 1000usize, 0xabu8)];
    let mut allocated = 0usize;
    let mut failed = false;
    for i in 0.. {
        match machine.alloc(1 << 20) {
            Ok(address) => {
                let fill = (i + 1) as u8;
                machine.write(address, &vec![fill; 1 << 20]);
                kept.push((address, 1 << 20, fill));
                allocated += 1 << 20;
            }
            Err(_) => {
                failed = true;
                break;
            }
        }
        assert!(i < 16, "the 8 MiB limit was never reached");
    }
    assert!(failed);
    assert!(
        allocated < limit,
        "{allocated} bytes fit in a limit of {limit}"
    );
    // The failed requests wrote nothing: every block that was handed out still
    // holds its own fill.
    for &(address, length, fill) in &kept {
        assert!(machine.read(address, length).iter().all(|&b| b == fill));
    }
    // A request that cannot be met fails again, and a large one fails at
    // once, without moving the arena...
    assert!(machine.alloc(1 << 20).is_err());
    assert!(machine.alloc(0xffff_fff0).is_err());
    assert!(machine.alloc(u32::MAX).is_err());
    // ...so a small block that fits in the memory that exists still succeeds,
    // right after the last good block: its header follows the 1 MiB payload.
    let small = machine.alloc(64).unwrap();
    let (last, length, _) = *kept.last().unwrap();
    assert_eq!(small as usize, last as usize + length + 16);
    machine.write(small, &[7; 64]);
    assert!(machine.read(small, 64).iter().all(|&b| b == 7));
    for &(address, length, fill) in &kept {
        assert!(machine.read(address, length).iter().all(|&b| b == fill));
    }
}

#[test]
fn memory_grows_without_a_ceiling_of_the_backend() {
    // The module declares no maximum: the arena grows as far as the host lets
    // the memory grow. Here the host allows 256 MiB.
    let bytes = build_with(
        ALLOC,
        OptLevel::O2,
        WasmBackend::new().with_stack_size(1 << 16),
    );
    let mut machine = Limited::new(&bytes, 256 << 20);
    for _ in 0..200 {
        machine.alloc(1 << 20).unwrap();
    }
    assert!(machine.memory_bytes() >= 200 << 20);
    let module = wasmparser::Parser::new(0).parse_all(&bytes);
    for payload in module {
        if let wasmparser::Payload::MemorySection(section) = payload.unwrap() {
            for memory in section {
                assert_eq!(memory.unwrap().maximum, None);
            }
        }
    }
}

const RECURSION: &str = "func private %deep(v0.i32) -> i32 {
    block0:
        v1.*[i32; 64] = alloca [i32; 64];
        v2.*i32 = gep v1 0.i32 63.i32;
        mstore v2 v0 i32;
        v3.i1 = is_zero v0;
        br v3 block1 block2;
    block1:
        return 0.i32;
    block2:
        v4.i32 = sub v0 1.i32;
        v5.i32 = call %deep v4;
        v6.i32 = mload v2 i32;
        v7.i32 = sub v6 v0;
        v8.i32 = add v5 1.i32;
        v9.i32 = add v8 v7;
        return v9;
}
func public %run(v0.i32) -> i32 {
    block0:
        v1.i32 = call %deep v0;
        return v1;
}
";

#[test]
fn the_stack_has_a_size_and_overflowing_it_traps() {
    // Each frame is 256 bytes. The stack is 64 KiB rounded up to a page
    // boundary after the reserved block, 128 KiB less 16 bytes, so it holds
    // about 500 levels.
    for level in [OptLevel::O0, OptLevel::O2] {
        let bytes = build_with(
            RECURSION,
            level,
            WasmBackend::new().with_stack_size(1 << 16),
        );
        let mut machine = Machine::new(&bytes);
        // Memory beyond the stack exists, so only the stack's own limit stops
        // a deep call.
        machine.grow_memory(64);
        let run = machine.func("run");
        for depth in [0, 1, 50, 200] {
            let got = machine.call(&run, &[Val::I32(depth)])[0].unwrap_i32();
            assert_eq!(got, depth, "{level:?}");
        }
        assert!(
            machine.try_call(&run, &[Val::I32(1000)]).is_err(),
            "{level:?}"
        );
        assert!(
            machine.try_call(&run, &[Val::I32(100_000)]).is_err(),
            "{level:?}"
        );
        // The trap left nothing behind: the same depth works again.
        let got = machine.call(&run, &[Val::I32(200)])[0].unwrap_i32();
        assert_eq!(got, 200, "{level:?}");
    }
    // A larger stack holds the deeper call.
    let bytes = build_with(
        RECURSION,
        OptLevel::O0,
        WasmBackend::new().with_stack_size(1 << 20),
    );
    let mut machine = Machine::new(&bytes);
    let run = machine.func("run");
    assert_eq!(machine.call(&run, &[Val::I32(300)])[0].unwrap_i32(), 300);
}

#[test]
fn a_frame_larger_than_the_stack_traps_at_once() {
    let source = "func public %f(v0.i32) -> i32 {
    block0:
        v1.*[i8; 200000] = alloca [i8; 200000];
        v2.*i8 = gep v1 0.i32 v0;
        mstore v2 7.i8 i8;
        v3.i8 = mload v2 i8;
        v4.i32 = zext v3 i32;
        return v4;
}";
    let mut machine = Machine::new(&build_with(
        source,
        OptLevel::O0,
        WasmBackend::new().with_stack_size(1 << 16),
    ));
    let f = machine.func("f");
    assert!(machine.try_call(&f, &[Val::I32(5)]).is_err());
    let mut machine = Machine::new(&build_with(
        source,
        OptLevel::O0,
        WasmBackend::new().with_stack_size(1 << 18),
    ));
    let f = machine.func("f");
    assert_eq!(machine.call(&f, &[Val::I32(199_999)])[0].unwrap_i32(), 7);
}

#[test]
fn a_host_call_back_into_an_export_does_not_overwrite_the_caller_frame() {
    let source = "declare external %host(i32) -> i32;
func public %scribble(v0.i32) -> i32 {
    block0:
        v1.*[i32; 8] = alloca [i32; 8];
        v2.*i32 = gep v1 0.i32 0.i32;
        mstore v2 v0 i32;
        v3.*i32 = gep v1 0.i32 7.i32;
        mstore v3 v0 i32;
        v4.i32 = mload v2 i32;
        v5.i32 = mload v3 i32;
        v6.i32 = add v4 v5;
        return v6;
}
func public %outer(v0.i32) -> i32 {
    block0:
        v1.*[i32; 8] = alloca [i32; 8];
        v2.*i32 = gep v1 0.i32 0.i32;
        mstore v2 v0 i32;
        v3.*i32 = gep v1 0.i32 7.i32;
        mstore v3 100.i32 i32;
        v4.i32 = call %host v0;
        v5.i32 = mload v2 i32;
        v6.i32 = mload v3 i32;
        v7.i32 = add v5 v6;
        v8.i32 = add v7 v4;
        return v8;
}";
    for level in [OptLevel::O0, OptLevel::O2] {
        let bytes = build_with(source, level, WasmBackend::new());
        let mut machine = Limited::with_imports(&bytes, usize::MAX, |linker| {
            linker
                .func_wrap(
                    "env",
                    "host",
                    |mut caller: Caller<'_, StoreLimits>, x: i32| -> i32 {
                        let scribble = caller.get_export("scribble").unwrap().into_func().unwrap();
                        let mut out = [Val::I32(0)];
                        scribble
                            .call(&mut caller, &[Val::I32(x + 1000)], &mut out)
                            .unwrap();
                        out[0].unwrap_i32()
                    },
                )
                .unwrap();
        });
        // outer keeps its own cells (x and 100); the callee wrote 2 * (x + 1000)
        // to a frame that must lie above them.
        let got = machine.call("outer", &[Val::I32(5)]).unwrap()[0].unwrap_i32();
        assert_eq!(got, 5 + 100 + 2 * 1005, "{level:?}");
        // After the call the next top-level call starts from the bottom again.
        let got = machine.call("outer", &[Val::I32(6)]).unwrap()[0].unwrap_i32();
        assert_eq!(got, 6 + 100 + 2 * 1006, "{level:?}");
    }
}

#[test]
fn a_trap_after_a_host_call_leaves_the_stack_as_it_was() {
    // Each call to `run` has a 1 KiB frame and calls the host, which makes the
    // module note where the caller's stack ends. The division after it traps
    // when the argument is zero. The stack is 128 KiB less 16 bytes (64 KiB
    // rounded up to a page boundary after the reserved block), so if every
    // trap left the note behind, 128 traps would use it up.
    let source = "declare external %host(i32) -> i32;
func public %run(v0.i32) -> i32 {
    block0:
        v1.*[i8; 1024] = alloca [i8; 1024];
        v2.*i8 = gep v1 0.i32 0.i32;
        mstore v2 1.i8 i8;
        v3.i32 = call %host v0;
        v4.i32 = udiv 100.i32 v0;
        v5.i8 = mload v2 i8;
        v6.i32 = zext v5 i32;
        v7.i32 = add v4 v6;
        v8.i32 = add v7 v3;
        return v8;
}";
    for level in [OptLevel::O0, OptLevel::O2] {
        let bytes = build_with(source, level, WasmBackend::new().with_stack_size(1 << 16));
        let mut machine = Limited::with_imports(&bytes, usize::MAX, |linker| {
            linker.func_wrap("env", "host", |x: i32| x + 1000).unwrap();
        });
        for round in 0..200 {
            assert!(
                machine.call("run", &[Val::I32(0)]).is_err(),
                "{level:?}: round {round} should trap"
            );
        }
        let got = machine.call("run", &[Val::I32(5)]).unwrap()[0].unwrap_i32();
        assert_eq!(got, 20 + 1 + 1005, "{level:?}");
    }
}

#[test]
fn global_data_has_its_alignment_contents_and_is_writable() {
    let source = "type @Record = { i8, i64, i16 };
global private i8 $first = 5;
global private i64 $wide = 0x1122334455667788;
global private [i16; 3] $shorts = [1, -2, 3];
global private @Record $record = {7, -9, 258};
global private i32 $counter = 41;
global private const i32 $zero_const = 0;
func public %bump(v0.i32) -> i32 {
    block0:
        v1.i32 = mload $counter i32;
        v2.i32 = add v1 v0;
        mstore $counter v2 i32;
        return v2;
}
func public %read_wide() -> i64 {
    block0:
        v0.i64 = mload $wide i64;
        return v0;
}
func public %where(v0.i32) -> i32 {
    block0:
        v1.i32 = ptr_to_int $first i32;
        v2.i32 = ptr_to_int $wide i32;
        v3.i32 = ptr_to_int $shorts i32;
        v4.i32 = ptr_to_int $record i32;
        br v0 block1 block2;
    block1:
        return v2;
    block2:
        v5.i32 = add v1 v3;
        v6.i32 = add v5 v4;
        return v6;
}
func public %record_field(v0.i32) -> i64 {
    block0:
        v1.*i64 = gep $record 0.i32 1.i32;
        v2.i64 = mload v1 i64;
        v3.*i16 = gep $record 0.i32 2.i32;
        v4.i16 = mload v3 i16;
        v5.i64 = zext v4 i64;
        v6.i64 = add v2 v5;
        return v6;
}
func public %short(v0.i32) -> i16 {
    block0:
        v1.*i16 = gep $shorts 0.i32 v0;
        v2.i16 = mload v1 i16;
        return v2;
}";
    for level in [OptLevel::O0, OptLevel::O2] {
        let mut machine = Machine::new(&build_with(source, level, WasmBackend::new()));
        let bump = machine.func("bump");
        assert_eq!(machine.call(&bump, &[Val::I32(1)])[0].unwrap_i32(), 42);
        assert_eq!(machine.call(&bump, &[Val::I32(2)])[0].unwrap_i32(), 44);
        let wide = machine.func("read_wide");
        assert_eq!(machine.call(&wide, &[])[0].unwrap_i64(), 0x1122334455667788);
        let record = machine.func("record_field");
        assert_eq!(
            machine.call(&record, &[Val::I32(0)])[0].unwrap_i64(),
            -9 + 258
        );
        let short = machine.func("short");
        for (i, want) in [1i32, -2, 3].into_iter().enumerate() {
            let got = machine.call(&short, &[Val::I32(i as i32)])[0].unwrap_i32();
            assert_eq!(got & 0xffff, want & 0xffff, "short {i}");
        }
        // Addresses: each global at its natural alignment, after the reserved
        // block, in declaration order.
        let place = machine.func("where");
        let wide_at = machine.call(&place, &[Val::I32(1)])[0].unwrap_i32();
        assert_eq!(wide_at, 24, "i8 at 16, then i64 at 24");
        let all = machine.call(&place, &[Val::I32(0)])[0].unwrap_i32();
        // first = 16, shorts = 32, record = 40 (aligned to 8 after 32 + 6)
        assert_eq!(all, 16 + 32 + 40);
        // The data is where the layout says it is.
        assert_eq!(machine.read(16, 1), [5]);
        assert_eq!(machine.read(24, 8), 0x1122334455667788u64.to_le_bytes());
        assert_eq!(machine.read(32, 6), [1, 0, 0xfe, 0xff, 3, 0]);
    }
}

#[test]
fn gep_follows_the_native_rules_for_indices() {
    let source = "func public %narrow(v0.*i64, v1.i8) -> i64 {
    block0:
        v2.*i64 = gep v0 v1;
        v3.i64 = mload v2 i64;
        return v3;
}
func public %truth(v0.*i64, v1.i32) -> i64 {
    block0:
        v2.i1 = trunc v1 i1;
        v3.*i64 = gep v0 v2;
        v4.i64 = mload v3 i64;
        return v4;
}
func public %wide_index(v0.*i64, v1.i64) -> i64 {
    block0:
        v2.*i64 = gep v0 v1;
        v3.i64 = mload v2 i64;
        return v3;
}
func public %nested(v0.*[[i16; 3]; 2], v1.i32, v2.i32) -> i16 {
    block0:
        v3.*i16 = gep v0 0.i32 v1 v2;
        v4.i16 = mload v3 i16;
        return v4;
}";
    for level in [OptLevel::O0, OptLevel::O2] {
        let mut machine = Machine::new(&build_with(source, level, WasmBackend::new()));
        // Use the start of the memory (below the module's own region is not
        // used here: this module has no frames, data or arena).
        let values: Vec<u8> = [11i64, 22, 33]
            .iter()
            .flat_map(|v| v.to_le_bytes())
            .collect();
        machine.write(64, &values);
        let narrow = machine.func("narrow");
        // A narrow index is sign-extended: -1 steps back one element.
        assert_eq!(
            machine.call(&narrow, &[Val::I32(72), Val::I32(0xff)])[0].unwrap_i64(),
            11
        );
        assert_eq!(
            machine.call(&narrow, &[Val::I32(72), Val::I32(1)])[0].unwrap_i64(),
            33
        );
        // `true` is -1 in an index, as on the native target.
        let truth = machine.func("truth");
        assert_eq!(
            machine.call(&truth, &[Val::I32(72), Val::I32(1)])[0].unwrap_i64(),
            11
        );
        assert_eq!(
            machine.call(&truth, &[Val::I32(72), Val::I32(0)])[0].unwrap_i64(),
            22
        );
        // A 64-bit index that does not fit in 32 bits traps, however it wraps.
        let wide = machine.func("wide_index");
        assert_eq!(
            machine.call(&wide, &[Val::I32(72), Val::I64(1)])[0].unwrap_i64(),
            33
        );
        assert_eq!(
            machine.call(&wide, &[Val::I32(72), Val::I64(-1)])[0].unwrap_i64(),
            11
        );
        assert!(
            machine
                .try_call(&wide, &[Val::I32(72), Val::I64(1 << 32)])
                .is_err()
        );
        assert!(
            machine
                .try_call(&wide, &[Val::I32(72), Val::I64(i64::MIN)])
                .is_err()
        );
        // Field and element offsets add up through nested arrays.
        let shorts: Vec<u8> = (0..6i16).flat_map(|v| (v * 10 + 1).to_le_bytes()).collect();
        machine.write(256, &shorts);
        let nested = machine.func("nested");
        for (row, col) in [(0, 0), (0, 2), (1, 0), (1, 2)] {
            let got = machine.call(&nested, &[Val::I32(256), Val::I32(row), Val::I32(col)])[0]
                .unwrap_i32() as i16;
            assert_eq!(got, ((row * 3 + col) * 10 + 1) as i16);
        }
    }
}

#[test]
fn memzero_clears_a_range_and_checks_the_memory() {
    let source = "func public %clear(v0.i32, v1.i32) {
    block0:
        v2.*i8 = int_to_ptr v0 *i8;
        memzero v2 v1;
        return;
}";
    let mut machine = Machine::new(&build_with(source, OptLevel::O0, WasmBackend::new()));
    machine.write(100, &[0xff; 32]);
    let clear = machine.func("clear");
    machine.call(&clear, &[Val::I32(104), Val::I32(8)]);
    let bytes = machine.read(100, 32);
    assert_eq!(&bytes[..4], &[0xff; 4]);
    assert_eq!(&bytes[4..12], &[0; 8]);
    assert_eq!(&bytes[12..], &[0xff; 20]);
    machine.call(&clear, &[Val::I32(104), Val::I32(0)]);
    // A range that leaves the memory traps.
    assert!(
        machine
            .try_call(&clear, &[Val::I32(65_000), Val::I32(2000)])
            .is_err()
    );
}

#[test]
fn memcopy_moves_overlapping_ranges_and_checks_the_memory() {
    let source = "func public %copy(v0.i32, v1.i32, v2.i32) {
    block0:
        v3.*i8 = int_to_ptr v0 *i8;
        v4.*i8 = int_to_ptr v1 *i8;
        memcopy v3 v4 v2;
        return;
}";
    let mut machine = Machine::new(&build_with(source, OptLevel::O0, WasmBackend::new()));
    let start: Vec<u8> = (0..16).collect();
    machine.write(100, &start);
    let copy = machine.func("copy");
    // Destination after source, overlapping: the source is read before it is overwritten.
    machine.call(&copy, &[Val::I32(104), Val::I32(100), Val::I32(8)]);
    assert_eq!(
        machine.read(100, 16),
        [0, 1, 2, 3, 0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15]
    );
    // Destination before source, overlapping.
    machine.call(&copy, &[Val::I32(100), Val::I32(102), Val::I32(8)]);
    assert_eq!(
        machine.read(100, 16),
        [2, 3, 0, 1, 2, 3, 4, 5, 4, 5, 6, 7, 12, 13, 14, 15]
    );
    machine.call(&copy, &[Val::I32(100), Val::I32(108), Val::I32(0)]);
    // A range that leaves the memory traps.
    assert!(
        machine
            .try_call(&copy, &[Val::I32(100), Val::I32(65_000), Val::I32(2000)])
            .is_err()
    );
}

#[test]
fn aggregate_phis_are_parallel_copies() {
    // Two struct phis that swap on every pass, and an array phi that rotates.
    let source = "type @P = { i32, i32 };
func public %swap(v0.i32, v1.i32, v2.i32) -> i32 {
    block0:
        v3.@P = insert_value undef.@P 0.i32 v0;
        v4.@P = insert_value v3 1.i32 100.i32;
        v5.@P = insert_value undef.@P 0.i32 v1;
        v6.@P = insert_value v5 1.i32 200.i32;
        jump block1;
    block1:
        v7.@P = phi (v4 block0) (v8 block2);
        v8.@P = phi (v6 block0) (v7 block2);
        v9.i32 = phi (0.i32 block0) (v13 block2);
        v10.i1 = lt v9 v2;
        br v10 block2 block3;
    block2:
        v13.i32 = add v9 1.i32;
        jump block1;
    block3:
        v11.i32 = extract_value v7 0.i32;
        v12.i32 = extract_value v8 0.i32;
        v14.i32 = mul v11 1000.i32;
        v15.i32 = add v14 v12;
        return v15;
}";
    for level in LEVELS_ALL {
        let mut machine = Machine::new(&build_at(source, level));
        let swap = machine.func("swap");
        for n in 0..5 {
            let (a, b) = if n % 2 == 0 { (3, 4) } else { (4, 3) };
            let got = machine.call(&swap, &[Val::I32(3), Val::I32(4), Val::I32(n)])[0].unwrap_i32();
            assert_eq!(got, a * 1000 + b, "{level:?} after {n} swaps");
        }
    }
}

const LEVELS_ALL: [OptLevel; 3] = [OptLevel::O0, OptLevel::O2, OptLevel::Os];

#[test]
fn aggregates_cannot_cross_the_module_boundary() {
    let compile_error = |source: &str| -> String {
        let module = parse(source);
        let errors = WasmBackend::new()
            .compile_module(&module, &BackendOptions::default())
            .expect_err("rejected");
        errors[0].to_string()
    };
    let by_value = compile_error(
        "type @P = { i32, i32 };
func public %f(v0.@P) -> i32 {
    block0:
        v1.i32 = extract_value v0 0.i32;
        return v1;
}",
    );
    assert!(
        by_value.contains("function `f`") && by_value.contains("parameter 0"),
        "{by_value}"
    );
    assert!(by_value.contains("a struct"), "{by_value}");
    let result = compile_error(
        "type @P = { i32, i32 };
func public %g(v0.i32) -> @P {
    block0:
        v1.@P = insert_value undef.@P 0.i32 v0;
        return v1;
}",
    );
    assert!(
        result.contains("function `g`") && result.contains("result 0"),
        "{result}"
    );
    // The verifier of signatures, which the native backend shares, refuses
    // references in a public signature.
    let reference = {
        let module = parse(
            "func public %h(v0.objref<i32>) -> i32 {
    block0:
        v1.i32 = obj.load v0;
        return v1;
}",
        );
        let errors = WasmBackend::new()
            .compile_module(&module, &BackendOptions::default())
            .expect_err("rejected");
        errors[0].to_string()
    };
    assert!(
        reference.contains("must not expose object references"),
        "{reference}"
    );
    let mixed = compile_error(
        "type @P = { i32, i32 };
func private %m(v0.i32) -> (i32, @P) {
    block0:
        v1.@P = insert_value undef.@P 0.i32 v0;
        return (v0, v1);
}
func public %k(v0.i32) -> i32 {
    block0:
        (v1.i32, v2.@P) = call %m v0;
        return v1;
}",
    );
    assert!(mixed.contains("function `m`"), "{mixed}");
}

#[test]
fn memmove_and_memcpy_are_memory_copy_and_not_imports() {
    let source = "declare external %memmove(*i8, *i8, i64) -> *i8;
declare external %memcpy(*i8, *i8, i32) -> *i8;
func public %move(v0.i32, v1.i32, v2.i64) -> i32 {
    block0:
        v3.*i8 = int_to_ptr v0 *i8;
        v4.*i8 = int_to_ptr v1 *i8;
        v5.*i8 = call %memmove v3 v4 v2;
        v6.i32 = ptr_to_int v5 i32;
        return v6;
}
func public %copy(v0.i32, v1.i32, v2.i32) {
    block0:
        v3.*i8 = int_to_ptr v0 *i8;
        v4.*i8 = int_to_ptr v1 *i8;
        v5.*i8 = call %memcpy v3 v4 v2;
        return;
}";
    for level in [OptLevel::O0, OptLevel::O2] {
        let bytes = build_with(source, level, WasmBackend::new());
        // No import: the module runs with an empty linker.
        let mut machine = Machine::new(&bytes);
        let bytes_in = |from: u8| (from..from + 16).collect::<Vec<u8>>();
        machine.write(100, &bytes_in(1));
        let mv = machine.func("move");
        // Overlapping ranges behave as `memmove`, and the call returns the
        // destination.
        let got = machine.call(&mv, &[Val::I32(104), Val::I32(100), Val::I64(8)]);
        assert_eq!(got[0].unwrap_i32(), 104);
        assert_eq!(
            machine.read(100, 16),
            [1, 2, 3, 4, 1, 2, 3, 4, 5, 6, 7, 8, 13, 14, 15, 16]
        );
        machine.write(200, &bytes_in(50));
        let copy = machine.func("copy");
        machine.call(&copy, &[Val::I32(300), Val::I32(200), Val::I32(5)]);
        assert_eq!(machine.read(300, 6), [50, 51, 52, 53, 54, 0]);
        // A length of zero copies nothing. As in `memory.copy`, an address
        // beyond the memory traps even then, and so does a length that does not
        // fit in the memory or in 32 bits.
        machine.call(&copy, &[Val::I32(300), Val::I32(200), Val::I32(0)]);
        assert!(
            machine
                .try_call(&copy, &[Val::I32(-1), Val::I32(0), Val::I32(0)])
                .is_err()
        );
        assert!(
            machine
                .try_call(&mv, &[Val::I32(0), Val::I32(0), Val::I64(1 << 32)])
                .is_err()
        );
        assert!(
            machine
                .try_call(&mv, &[Val::I32(0), Val::I32(64), Val::I64(100_000)])
                .is_err()
        );
    }
}

#[test]
fn a_load_is_not_moved_past_a_later_store() {
    // `v1` is read before the store and used after it, through a chain of
    // pure operations.
    let source = "func public %f(v0.i32, v1.i32) -> i32 {
    block0:
        v2.*i32 = int_to_ptr v0 *i32;
        v3.i32 = mload v2 i32;
        v4.i32 = add v3 1.i32;
        mstore v2 v1 i32;
        v5.i32 = add v4 100.i32;
        v6.i32 = mul v5 3.i32;
        return v6;
}";
    for level in [OptLevel::O0, OptLevel::O2] {
        let mut machine = Machine::new(&build_with(source, level, WasmBackend::new()));
        machine.write(64, &7i32.to_le_bytes());
        let f = machine.func("f");
        let got = machine.call(&f, &[Val::I32(64), Val::I32(500)])[0].unwrap_i32();
        assert_eq!(got, (7 + 1 + 100) * 3, "{level:?}");
    }
}

/// A module whose code never allocates: it sums `len` bytes at an address that
/// the host chose, and allocates one block when asked.
const HOST_TEXT: &str = "func public %sum(v0.*i8, v1.i32) -> i32 {
    block0:
        jump block1;
    block1:
        v2.i32 = phi (0.i32 block0) (v7 block2);
        v3.i32 = phi (0.i32 block0) (v8 block2);
        v4.i1 = lt v3 v1;
        br v4 block2 block3;
    block2:
        v5.*i8 = gep v0 v3;
        v6.i8 = mload v5 i8;
        v9.i32 = zext v6 i32;
        v7.i32 = add v2 v9;
        v8.i32 = add v3 1.i32;
        jump block1;
    block3:
        return v2;
}
func public %grab(v0.i32) -> *i8 {
    block0:
        v1.*i8 = mem.alloc_dynamic v0;
        return v1;
}
";

pub(crate) fn with_host_allocator(source: &str, level: OptLevel) -> Vec<u8> {
    build_with(
        source,
        level,
        WasmBackend::new()
            .with_stack_size(1 << 16)
            .with_host_allocator(),
    )
}

pub(crate) fn call_i32(
    machine: &mut Limited,
    name: &str,
    args: &[Val],
) -> Result<u32, wasmtime::Error> {
    Ok(machine.call(name, args)?[0].unwrap_i32() as u32)
}

#[test]
fn the_host_allocator_places_data_that_the_module_reads() {
    for level in [OptLevel::O0, OptLevel::O2] {
        let bytes = with_host_allocator(HOST_TEXT, level);
        let mut machine = Limited::new(&bytes, usize::MAX);
        // The exports exist, and the arena starts after the stack.
        let arena = (DATA_BASE + (1 << 16)).next_multiple_of(PAGE) as u32;
        assert_eq!(call_i32(&mut machine, "arena_mark", &[]).unwrap(), arena);
        let text = b"hello, host";
        let address = machine.alloc(text.len() as u32).unwrap();
        // The first block's payload follows its 16-byte header.
        assert_eq!(address, arena + 16, "{level:?}");
        machine.write(address, text);
        let want: u32 = text.iter().map(|&b| u32::from(b)).sum();
        let got = call_i32(
            &mut machine,
            "sum",
            &[Val::I32(address as i32), Val::I32(text.len() as i32)],
        );
        assert_eq!(got.unwrap(), want, "{level:?}");
        // A module allocation and a host allocation share the arena and do not
        // overlap.
        // The 11-byte text took a block of 16 payload bytes and a header; the
        // 40-byte request takes 64 payload bytes and a header, and the next block
        // follows it.
        let own = call_i32(&mut machine, "grab", &[Val::I32(40)]).unwrap();
        assert_eq!(own, address + 16 + 16, "{level:?}");
        let next = machine.alloc(1).unwrap();
        assert_eq!(next, own + 64 + 16, "{level:?}");
        // The text is intact.
        assert_eq!(machine.read(address, text.len()), text);
        // A length of zero is a valid text and still has an address of its own.
        let empty = machine.alloc(0).unwrap();
        assert_ne!(empty, next);
        let got = call_i32(&mut machine, "sum", &[Val::I32(empty as i32), Val::I32(0)]);
        assert_eq!(got.unwrap(), 0);
    }
}

#[test]
fn releasing_to_a_mark_frees_the_blocks_after_it_and_clears_them() {
    for level in [OptLevel::O0, OptLevel::O2] {
        let bytes = with_host_allocator(HOST_TEXT, level);
        let mut machine = Limited::new(&bytes, usize::MAX);
        let kept = machine.alloc(100).unwrap();
        machine.write(kept, &[7; 100]);
        let mark = call_i32(&mut machine, "arena_mark", &[]).unwrap();
        // The 100-byte request took a block of 128 payload bytes.
        assert_eq!(mark, kept + 128);
        // Allocate across a page boundary so that the memory grows.
        let first = machine.alloc(70_000).unwrap();
        let second = call_i32(&mut machine, "grab", &[Val::I32(10)]).unwrap();
        machine.write(first, &vec![0xAB; 70_000]);
        machine.write(second, &[0xCD; 10]);
        let grown = machine.memory_bytes();
        machine
            .call("arena_release", &[Val::I32(mark as i32)])
            .unwrap();
        // The top is back at the mark and the released bytes read as zero.
        assert_eq!(call_i32(&mut machine, "arena_mark", &[]).unwrap(), mark);
        assert!(machine.read(first, 70_000).iter().all(|&b| b == 0));
        assert!(machine.read(second, 10).iter().all(|&b| b == 0));
        // The next allocation reuses the address and is zero, as a new one is.
        let again = machine.alloc(70_000).unwrap();
        assert_eq!(again, first, "{level:?}");
        assert!(machine.read(again, 70_000).iter().all(|&b| b == 0));
        // The block before the mark is unchanged, and the memory stays grown.
        assert_eq!(machine.read(kept, 100), vec![7; 100]);
        assert_eq!(machine.memory_bytes(), grown);
        // Releasing to the current top changes nothing.
        let top = call_i32(&mut machine, "arena_mark", &[]).unwrap();
        machine
            .call("arena_release", &[Val::I32(top as i32)])
            .unwrap();
        assert_eq!(call_i32(&mut machine, "arena_mark", &[]).unwrap(), top);
    }
}

#[test]
fn a_bad_mark_traps_and_changes_nothing() {
    let bytes = with_host_allocator(HOST_TEXT, OptLevel::O2);
    let mut machine = Limited::new(&bytes, usize::MAX);
    let arena = call_i32(&mut machine, "arena_mark", &[]).unwrap();
    let block = machine.alloc(64).unwrap();
    machine.write(block, &[9; 64]);
    let top = call_i32(&mut machine, "arena_mark", &[]).unwrap();
    for bad in [
        0,
        arena - 16,
        arena - 1,
        // Not 16-byte aligned.
        arena + 8,
        // Above the top.
        top + 16,
        u32::MAX,
    ] {
        let result = machine.call("arena_release", &[Val::I32(bad as i32)]);
        assert!(result.is_err(), "mark {bad} was accepted");
        assert_eq!(call_i32(&mut machine, "arena_mark", &[]).unwrap(), top);
        assert_eq!(machine.read(block, 64), vec![9; 64]);
    }
    // The first mark of the arena is valid, and a mark released twice is not
    // valid once the top has moved below it.
    machine
        .call("arena_release", &[Val::I32(arena as i32)])
        .unwrap();
    assert!(
        machine
            .call("arena_release", &[Val::I32(top as i32)])
            .is_err()
    );
}

#[test]
fn the_host_allocator_traps_like_the_arena_when_memory_is_refused() {
    let bytes = with_host_allocator(HOST_TEXT, OptLevel::O2);
    let mut machine = Limited::new(&bytes, 4 << 20);
    let mark = call_i32(&mut machine, "arena_mark", &[]).unwrap();
    assert!(machine.alloc(8 << 20).is_err());
    assert_eq!(call_i32(&mut machine, "arena_mark", &[]).unwrap(), mark);
    assert!(machine.alloc(1000).is_ok());
}

#[test]
fn the_host_allocator_is_not_exported_unless_asked_for() {
    let bytes = build_with(HOST_TEXT, OptLevel::O2, WasmBackend::new());
    let mut machine = Machine::new(&bytes);
    for name in ["alloc", "arena_mark", "arena_release"] {
        assert!(!machine.has_export(name), "{name}");
    }
    // A module that uses neither frames nor an arena is unchanged by default,
    // and gains a stack and an arena with the option.
    let plain = "func public %f(v0.i32) -> i32 {
    block0:
        v1.i32 = add v0 1.i32;
        return v1;
}";
    let default = build_with(plain, OptLevel::O2, WasmBackend::new());
    let with = build_with(
        plain,
        OptLevel::O2,
        WasmBackend::new().with_host_allocator(),
    );
    assert_ne!(default, with);
    let mut machine = Machine::new(&with);
    for name in ["alloc", "arena_mark", "arena_release", "f"] {
        assert!(machine.has_export(name), "{name}");
    }
    let f = machine.func("f");
    assert_eq!(machine.call(&f, &[Val::I32(41)])[0].unwrap_i32(), 42);
    // The same module and options give the same bytes.
    assert_eq!(
        with,
        build_with(
            plain,
            OptLevel::O2,
            WasmBackend::new().with_host_allocator()
        )
    );
}

#[test]
fn the_names_of_the_host_allocator_are_reserved() {
    for name in ["alloc", "arena_mark", "arena_release"] {
        let source = format!(
            "func public %{name}(v0.i32) -> i32 {{
    block0:
        return v0;
}}"
        );
        // Without the option the name is an ordinary export.
        build_with(&source, OptLevel::O0, WasmBackend::new());
        let errors = Compile::new(parse(&source), WasmBackend::new().with_host_allocator())
            .compile()
            .expect_err("the name is reserved");
        let message = format!("{errors:?}");
        assert!(
            message.contains(&format!("`{name}` is reserved for the host allocator")),
            "{message}"
        );
    }
}
