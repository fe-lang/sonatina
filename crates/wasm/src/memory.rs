//! The linear-memory layout and the runtime helpers of a module.
//!
//! A module that does not use frames, global data or the heap keeps the
//! layout of the integer slice: one exported page that the backend does not
//! touch. Any other module gets this layout, from the lowest address:
//!
//! 1. A reserved block of [`DATA_BASE`] bytes. No object lives there, so a null
//!    pointer is never the address of one.
//! 2. The global variables, each at its natural alignment, filled from the
//!    module's initializers.
//! 3. When the module has a heap, the table of free-list heads
//!    ([`heap::TABLE_BYTES`] bytes, one word for each size class).
//! 4. The stack, at least [`WasmBackend::with_stack_size`](super::WasmBackend)
//!    bytes (1 MiB by default), up to the next page boundary. It holds the
//!    frames of `alloca`, `obj.alloc` and aggregate temporaries.
//! 5. The heap, from that page boundary to the end of the memory. It holds the
//!    blocks of `mem.alloc_dynamic` and of the external `malloc`, and it grows
//!    by `memory.grow` as needed. See the [`heap`] module.
//!
//! The initial memory covers regions 1 to 4, and one page of the heap if the
//! module uses it. The host does not place anything in regions 3 to 5.

use waffle::{
    FunctionBody, Global, GlobalData, MemorySegment, Module as WModule, Operator, Signature,
    Terminator, Type as WType,
};

use rustc_hash::FxHashMap;
use sonatina_ir::{
    GlobalVariableRef, Immediate, Linkage, Module, Type, global_variable::GvInitializer,
    module::ModuleCtx, types::CompoundType,
};

use super::{WasmError, heap};

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
    /// The module allocates from the heap.
    pub(super) arena: bool,
    /// The address of the table of free-list heads, one word per size class,
    /// when the module has a heap.
    pub(super) lists: u32,
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
            lists: 0,
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

    // The table of free-list heads follows the globals.
    let lists = if needs_arena {
        let at = align_up(cursor, ALIGN).ok_or_else(too_large)?;
        cursor = at.checked_add(heap::TABLE_BYTES).ok_or_else(too_large)?;
        at
    } else {
        0
    };
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
        lists,
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

/// The body of `arena_mark`: the top of the heap. The next block cut from the
/// top has its header here, and its payload 16 bytes later.
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
