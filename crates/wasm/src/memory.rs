//! The linear-memory layout and the runtime helpers of a module.
//!
//! A module that does not use frames, global data or the arena keeps the
//! layout of the integer slice: one exported page that the backend does not
//! touch. Any other module gets this layout, from the lowest address:
//!
//! 1. A reserved block of [`DATA_BASE`] bytes. No object lives there, so a null
//!    pointer is never the address of one.
//! 2. The global variables, each at its natural alignment, filled from the
//!    module's initializers.
//! 3. The stack, at least [`WasmBackend::with_stack_size`](super::WasmBackend)
//!    bytes (1 MiB by default), up to the next page boundary. It holds the
//!    frames of `alloca`, `obj.alloc` and aggregate temporaries.
//! 4. The arena, from that page boundary to the end of the memory. It holds
//!    `mem.alloc_dynamic` blocks and objects that outlive their frame, and it
//!    grows by `memory.grow` as needed.
//!
//! The initial memory covers regions 1 to 3, and one page of the arena if the
//! module uses it. The host does not place anything in regions 3 and 4.

use waffle::{
    BlockTarget, FunctionBody, Global, GlobalData, Memory, MemorySegment, Module as WModule,
    Operator, Signature, SignatureData, Terminator, Type as WType,
};

use rustc_hash::FxHashMap;
use sonatina_ir::{
    GlobalVariableRef, Immediate, Linkage, Module, Type, global_variable::GvInitializer,
    module::ModuleCtx, types::CompoundType,
};

use super::{WasmError, arith::Emit};

/// The size of a WebAssembly page.
pub(super) const PAGE: u64 = 65536;

/// The lowest address that the backend uses.
pub(super) const DATA_BASE: u32 = 16;

/// The alignment of every frame, stack slot base and arena block.
pub(super) const ALIGN: u32 = 16;

pub(super) const DEFAULT_STACK_BYTES: u32 = 1 << 20;

/// Where the pieces of a module live in linear memory, and which runtime pieces
/// the module needs.
pub(super) struct MemoryPlan {
    /// Functions take a hidden stack-top parameter, exports are wrapped, and
    /// the stack and global data exist.
    pub(super) runtime: bool,
    /// The module allocates from the arena.
    pub(super) arena: bool,
    pub(super) globals: FxHashMap<GlobalVariableRef, u32>,
    pub(super) segments: Vec<MemorySegment>,
    pub(super) stack_base: u32,
    pub(super) stack_limit: u32,
    pub(super) initial_pages: usize,
}

impl MemoryPlan {
    /// The layout of a module that has no runtime: one page, nothing placed.
    pub(super) fn bare() -> Self {
        Self {
            runtime: false,
            arena: false,
            globals: FxHashMap::default(),
            segments: Vec::new(),
            stack_base: 0,
            stack_limit: 0,
            initial_pages: 1,
        }
    }
}

pub(super) fn align_up(value: u32, align: u32) -> Option<u32> {
    let mask = align.checked_sub(1)?;
    value.checked_add(mask).map(|v| v & !mask)
}

/// Place the global variables and size the initial memory.
pub(super) fn plan_memory(
    module: &Module,
    needs_runtime: bool,
    needs_arena: bool,
    stack_bytes: u32,
) -> Result<MemoryPlan, WasmError> {
    let has_globals = module.ctx.with_gv_store(|store| !store.is_empty());
    if !needs_runtime && !has_globals {
        debug_assert!(!needs_arena);
        return Ok(MemoryPlan::bare());
    }

    let too_large = || {
        WasmError::Unsupported(
            "the global data and the stack do not fit in a 32-bit address space".to_string(),
        )
    };
    let mut globals = FxHashMap::default();
    let mut segments = Vec::new();
    let mut cursor = DATA_BASE;
    module.ctx.with_gv_store(|store| {
        for gv in store.all_gv_refs() {
            let data = store.gv_data(gv);
            let symbol = &data.symbol;
            if data.linkage != Linkage::Private {
                return Err(WasmError::Unsupported(format!(
                    "global variable `{symbol}` has {} linkage; only private global variables \
                     are placed in linear memory",
                    if data.linkage == Linkage::Public {
                        "public"
                    } else {
                        "external"
                    }
                )));
            }
            let size = module.ctx.size_of(data.ty).map_err(|error| {
                WasmError::Unsupported(format!(
                    "global variable `{symbol}`: cannot lay out its type: {error:?}"
                ))
            })?;
            let align = module.ctx.align_of(data.ty).map_err(|error| {
                WasmError::Unsupported(format!(
                    "global variable `{symbol}`: cannot lay out its type: {error:?}"
                ))
            })?;
            let align = u32::try_from(align.max(1)).map_err(|_| too_large())?;
            let size = u32::try_from(size).map_err(|_| too_large())?;
            let address = align_up(cursor, align).ok_or_else(too_large)?;
            let mut bytes = vec![0u8; size as usize];
            if let Some(init) = &data.initializer {
                serialize_initializer(init, data.ty, &mut bytes, &module.ctx).map_err(
                    |message| {
                        WasmError::Unsupported(format!("global variable `{symbol}`: {message}"))
                    },
                )?;
            }
            globals.insert(gv, address);
            // Memory starts zeroed, so only non-zero data needs a segment.
            if bytes.iter().any(|&byte| byte != 0) {
                segments.push(MemorySegment {
                    offset: address as usize,
                    data: bytes,
                });
            }
            cursor = address.checked_add(size.max(1)).ok_or_else(too_large)?;
        }
        Ok::<(), WasmError>(())
    })?;

    let stack_base = align_up(cursor, ALIGN).ok_or_else(too_large)?;
    // The stack ends on a page boundary, so the slack of the last page belongs
    // to the stack and the arena starts on a fresh page.
    let stack_limit = stack_base
        .checked_add(align_up(stack_bytes, ALIGN).ok_or_else(too_large)?)
        .and_then(|end| align_up(end, PAGE as u32))
        .ok_or_else(too_large)?;
    let initial_pages = (stack_limit as u64 / PAGE) as usize + usize::from(needs_arena);
    Ok(MemoryPlan {
        runtime: needs_runtime || has_globals,
        arena: needs_arena,
        globals,
        segments,
        stack_base,
        stack_limit,
        initial_pages,
    })
}

/// The bytes of an initializer laid out as the type is in memory.
fn serialize_initializer(
    init: &GvInitializer,
    ty: Type,
    bytes: &mut [u8],
    ctx: &ModuleCtx,
) -> Result<(), String> {
    match init {
        GvInitializer::Immediate(imm) => {
            if matches!(imm, Immediate::EnumTag { .. }) {
                return Err("an enum tag initializer survived legalization".into());
            }
            if imm.ty() != ty && !(ty.is_pointer(ctx) && imm.ty() == ctx.type_layout.pointer_repl())
            {
                return Err(format!(
                    "initializer type mismatch: expected {ty:?}, found {:?}",
                    imm.ty()
                ));
            }
            let words = imm.zext(Type::I256).as_i256().to_u256().to_little_endian();
            bytes.copy_from_slice(&words[..bytes.len()]);
        }
        GvInitializer::Array(elements) => {
            let Some(CompoundType::Array { elem, len }) = ty.resolve_compound(ctx) else {
                return Err(format!("array initializer used for {ty:?}"));
            };
            if elements.len() != len {
                return Err(format!(
                    "array initializer length mismatch: expected {len}, found {}",
                    elements.len()
                ));
            }
            let size = ctx
                .size_of(elem)
                .map_err(|error| format!("cannot lay out {elem:?}: {error:?}"))?;
            for (index, init) in elements.iter().enumerate() {
                let start = index * size;
                serialize_initializer(init, elem, &mut bytes[start..start + size], ctx)?;
            }
        }
        GvInitializer::Struct(fields) => {
            let Some(CompoundType::Struct(data)) = ty.resolve_compound(ctx) else {
                return Err(format!("struct initializer used for {ty:?}"));
            };
            if fields.len() != data.fields.len() {
                return Err(format!(
                    "struct initializer field count mismatch: expected {}, found {}",
                    data.fields.len(),
                    fields.len()
                ));
            }
            for (index, (init, field)) in fields.iter().zip(data.fields).enumerate() {
                let (offset, _) = ctx
                    .aggregate_elem_offset(ty, index)
                    .ok_or_else(|| format!("cannot lay out field {index} of {ty:?}"))?;
                let size = ctx
                    .size_of(field)
                    .map_err(|error| format!("cannot lay out {field:?}: {error:?}"))?;
                serialize_initializer(init, field, &mut bytes[offset..offset + size], ctx)?;
            }
        }
    }
    Ok(())
}

/// The two mutable globals of the runtime.
#[derive(Clone, Copy)]
pub(super) struct RuntimeGlobals {
    /// The address at which the next exported call places its first frame.
    pub(super) stack_top: Global,
    /// The address of the next free byte of the arena.
    pub(super) arena_top: Option<Global>,
}

pub(super) fn declare_runtime_globals(
    wmod: &mut WModule<'static>,
    plan: &MemoryPlan,
) -> RuntimeGlobals {
    let stack_top = wmod.globals.push(GlobalData {
        ty: WType::I32,
        value: Some(u64::from(plan.stack_base)),
        mutable: true,
    });
    let arena_top = plan.arena.then(|| {
        wmod.globals.push(GlobalData {
            ty: WType::I32,
            value: Some(u64::from(plan.stack_limit)),
            mutable: true,
        })
    });
    RuntimeGlobals {
        stack_top,
        arena_top,
    }
}

/// The signature of the arena allocator: size in bytes, address out.
pub(super) fn arena_signature(wmod: &mut WModule<'static>) -> Signature {
    wmod.signatures.push(SignatureData {
        params: vec![WType::I32],
        returns: vec![WType::I32],
    })
}

/// The body of the arena allocator.
///
/// `alloc(size)` rounds `size` up to 16 bytes (a request for zero bytes gets
/// 16 so that it still has a distinct address), moves the arena top and returns
/// the old top. If the new top is above the memory, the memory grows by the
/// missing pages. The call traps if the new top does not fit in 32 bits or if
/// the engine refuses to grow the memory, and then leaves the arena unchanged.
/// Memory that has never been used reads as zero, and the arena never reuses a
/// block, so every allocation starts zeroed.
pub(super) fn build_arena_allocator(
    wmod: &WModule<'static>,
    sig: Signature,
    memory: Memory,
    arena_top: Global,
) -> FunctionBody {
    let mut body = FunctionBody::new(wmod, sig);
    let entry = body.entry;
    let size = body.blocks[entry].params[0].1;

    let trap = body.add_block();
    body.set_terminator(trap, Terminator::Unreachable);
    let grow = body.add_block();
    let done = body.add_block();

    let mut e = Emit {
        body: &mut body,
        block: entry,
    };
    let top = e.op(
        Operator::GlobalGet {
            global_index: arena_top,
        },
        &[],
        WType::I32,
    );
    // The block size, at least one unit of the alignment.
    let one = e.c32(1);
    let zero = e.c32(0);
    let is_empty = e.op(Operator::I32Eq, &[size, zero], WType::I32);
    let size = e.op(Operator::Select, &[one, size, is_empty], WType::I32);
    let size64 = e.op(Operator::I64ExtendI32U, &[size], WType::I64);
    let round = e.c64(u64::from(ALIGN - 1));
    let padded = e.op(Operator::I64Add, &[size64, round], WType::I64);
    let mask = e.c64(!u64::from(ALIGN - 1));
    let block_size = e.op(Operator::I64And, &[padded, mask], WType::I64);
    let top64 = e.op(Operator::I64ExtendI32U, &[top], WType::I64);
    let new_top = e.op(Operator::I64Add, &[top64, block_size], WType::I64);
    let shift32 = e.c64(32);
    let high = e.op(Operator::I64ShrU, &[new_top, shift32], WType::I64);
    let zero64 = e.c64(0);
    let overflow = e.op(Operator::I64Ne, &[high, zero64], WType::I32);
    let pages = e.op(Operator::MemorySize { mem: memory }, &[], WType::I32);
    let pages64 = e.op(Operator::I64ExtendI32U, &[pages], WType::I64);
    let shift16 = e.c64(16);
    let have = e.op(Operator::I64Shl, &[pages64, shift16], WType::I64);
    let short = e.op(Operator::I64GtU, &[new_top, have], WType::I32);
    let check = body.add_block();
    body.set_terminator(
        entry,
        Terminator::CondBr {
            cond: overflow,
            if_true: BlockTarget {
                block: trap,
                args: vec![],
            },
            if_false: BlockTarget {
                block: check,
                args: vec![],
            },
        },
    );
    body.set_terminator(
        check,
        Terminator::CondBr {
            cond: short,
            if_true: BlockTarget {
                block: grow,
                args: vec![],
            },
            if_false: BlockTarget {
                block: done,
                args: vec![],
            },
        },
    );

    // Grow by the missing pages.
    let mut g = Emit {
        body: &mut body,
        block: grow,
    };
    let page_mask = g.c64(PAGE - 1);
    let rounded = g.op(Operator::I64Add, &[new_top, page_mask], WType::I64);
    let sixteen = g.c64(16);
    let need_pages = g.op(Operator::I64ShrU, &[rounded, sixteen], WType::I64);
    let missing = g.op(Operator::I64Sub, &[need_pages, pages64], WType::I64);
    let missing32 = g.op(Operator::I32WrapI64, &[missing], WType::I32);
    let grown = g.op(
        Operator::MemoryGrow { mem: memory },
        &[missing32],
        WType::I32,
    );
    let minus_one = g.c32(u32::MAX);
    let refused = g.op(Operator::I32Eq, &[grown, minus_one], WType::I32);
    body.set_terminator(
        grow,
        Terminator::CondBr {
            cond: refused,
            if_true: BlockTarget {
                block: trap,
                args: vec![],
            },
            if_false: BlockTarget {
                block: done,
                args: vec![],
            },
        },
    );

    let mut d = Emit {
        body: &mut body,
        block: done,
    };
    let new_top32 = d.op(Operator::I32WrapI64, &[new_top], WType::I32);
    d.body.add_op(
        done,
        Operator::GlobalSet {
            global_index: arena_top,
        },
        &[new_top32],
        &[],
    );
    body.set_terminator(done, Terminator::Return { values: vec![top] });
    body.convert_to_max_ssa(None);
    body
}

/// The body of `arena_mark`: the arena top, which is the address the next
/// allocation gets.
pub(super) fn build_arena_mark(
    wmod: &WModule<'static>,
    sig: Signature,
    arena_top: Global,
) -> FunctionBody {
    let mut body = FunctionBody::new(wmod, sig);
    let entry = body.entry;
    let top = body.add_op(
        entry,
        Operator::GlobalGet {
            global_index: arena_top,
        },
        &[],
        &[WType::I32],
    );
    body.set_terminator(entry, Terminator::Return { values: vec![top] });
    body
}

/// The body of `arena_release(mark)`: frees every block allocated since `mark`
/// was read from `arena_mark`.
///
/// The bytes from `mark` to the arena top are cleared, so the blocks that the
/// arena hands out next are zero again, and the top moves back to `mark`. The
/// call traps, and changes nothing, unless `mark` is 16-byte aligned, not below
/// the start of the arena (`arena_start`) and not above the top. A mark that
/// was valid once can be above the top later (after a release to a lower mark);
/// it is refused as well.
pub(super) fn build_arena_release(
    wmod: &WModule<'static>,
    sig: Signature,
    memory: Memory,
    arena_top: Global,
    arena_start: u32,
) -> FunctionBody {
    let mut body = FunctionBody::new(wmod, sig);
    let entry = body.entry;
    let mark = body.blocks[entry].params[0].1;

    let trap = body.add_block();
    body.set_terminator(trap, Terminator::Unreachable);
    let clear = body.add_block();

    let mut e = Emit {
        body: &mut body,
        block: entry,
    };
    let top = e.op(
        Operator::GlobalGet {
            global_index: arena_top,
        },
        &[],
        WType::I32,
    );
    let start = e.c32(arena_start);
    let below = e.op(Operator::I32LtU, &[mark, start], WType::I32);
    let above = e.op(Operator::I32GtU, &[mark, top], WType::I32);
    let align_mask = e.c32(ALIGN - 1);
    let low_bits = e.op(Operator::I32And, &[mark, align_mask], WType::I32);
    let no_bits = e.c32(0);
    let bad_low = e.op(Operator::I32Ne, &[low_bits, no_bits], WType::I32);
    let bad = e.op(Operator::I32Or, &[below, above], WType::I32);
    let bad = e.op(Operator::I32Or, &[bad, bad_low], WType::I32);
    body.set_terminator(
        entry,
        Terminator::CondBr {
            cond: bad,
            if_true: BlockTarget {
                block: trap,
                args: vec![],
            },
            if_false: BlockTarget {
                block: clear,
                args: vec![],
            },
        },
    );

    let mut c = Emit {
        body: &mut body,
        block: clear,
    };
    let len = c.op(Operator::I32Sub, &[top, mark], WType::I32);
    let zero = c.c32(0);
    body.add_op(
        clear,
        Operator::MemoryFill { mem: memory },
        &[mark, zero, len],
        &[],
    );
    body.add_op(
        clear,
        Operator::GlobalSet {
            global_index: arena_top,
        },
        &[mark],
        &[],
    );
    body.set_terminator(clear, Terminator::Return { values: vec![] });
    body.convert_to_max_ssa(None);
    body
}
