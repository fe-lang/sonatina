//! The heap: a size-class allocator with free lists.
//!
//! Every block starts with a 16-byte header, so payloads stay 16-byte aligned:
//! the class at offset 0 and the state at offset 4. A block of class `k` has a
//! payload of `2**k` bytes, for `k` from 4 to 31. A freed block goes on the list
//! of its class and is the first one reused. The first word of a free payload is
//! the link to the next free block of the class. Blocks are only cut from the top
//! of the heap and are never split or merged, so every block lies wholly below or
//! wholly above any past value of the top. That is what makes
//! `arena_release` safe (see [`build_release`]).
//!
//! The functions here are leaf functions of the module. They take no stack
//! argument, do not touch `stack_top` and call no imports, so a host callback
//! cannot interrupt them. Each checks everything before it writes anything, so a
//! trap or a null result changes nothing.

use waffle::{
    BlockTarget, FunctionBody, Global, Memory, MemoryArg, Module as WModule, Operator, Signature,
    SignatureData, Terminator, Type as WType,
};

use super::{
    arith::Emit,
    memory::{ALIGN, PAGE},
};

/// The size of a block header.
pub(super) const HEADER: u32 = 16;
/// The smallest class: a payload of 16 bytes.
pub(super) const MIN_CLASS: u32 = 4;
/// The number of entries in the table of list heads, indexed by class.
pub(super) const CLASSES: u32 = 32;
/// The bytes of the table of list heads.
pub(super) const TABLE_BYTES: u32 = CLASSES * 4;
/// The largest request: `2**31` bytes.
const MAX_REQUEST: u32 = 1 << 31;
/// The state of a block that is in use.
pub(super) const LIVE: u32 = 1;
/// The state of a block on a free list.
pub(super) const FREE: u32 = 2;

type V = waffle::Value;

fn word(memory: Memory) -> MemoryArg {
    MemoryArg {
        align: 2,
        offset: 0,
        memory,
    }
}

fn word_at(memory: Memory, offset: u32) -> MemoryArg {
    MemoryArg {
        align: 2,
        offset,
        memory,
    }
}

fn target(block: waffle::Block, args: Vec<V>) -> BlockTarget {
    BlockTarget { block, args }
}

/// The signature `(i32) -> i32` of the allocators.
pub(super) fn alloc_signature(wmod: &mut WModule<'static>) -> Signature {
    wmod.signatures.push(SignatureData {
        params: vec![WType::I32],
        returns: vec![WType::I32],
    })
}

/// The signature `(i32) -> ()` of `free` and `arena_release`.
pub(super) fn consume_signature(wmod: &mut WModule<'static>) -> Signature {
    wmod.signatures.push(SignatureData {
        params: vec![WType::I32],
        returns: vec![],
    })
}

/// The address of the list head of `class`, a value of type `i32`.
fn list_head(e: &mut Emit<'_>, lists: u32, class: V) -> V {
    let two = e.c32(2);
    let offset = e.op(Operator::I32Shl, &[class, two], WType::I32);
    let base = e.c32(lists);
    e.op(Operator::I32Add, &[base, offset], WType::I32)
}

/// The two ways of failing and the one way of reusing a block.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Mode {
    /// `mem.alloc_dynamic` and the external `malloc`: reuse a freed block when
    /// there is one, and return null when the request cannot be met.
    Module,
    /// The `alloc` export of the host allocator: cut a fresh block from the top,
    /// which is zeroed, and trap when the request cannot be met.
    Host,
}

/// The allocator `malloc(size) -> address`.
///
/// A request of at most 16 bytes takes class 4; otherwise the class is the bit
/// length of `size - 1`. A request above `2**31` bytes fails. In [`Mode::Module`]
/// the first block on the class's list is taken when there is one. Otherwise a
/// block is cut from the top of the heap: the memory grows by the missing pages,
/// and the request fails if the end would not fit in 32 bits or the engine
/// refuses to grow. A failure returns 0 in [`Mode::Module`] and traps in
/// [`Mode::Host`]; either way nothing has changed.
///
/// A block taken from a list keeps whatever its last user left in it. A block cut
/// from the top is zero, because memory above the top is always zero.
pub(super) fn build_malloc(
    wmod: &WModule<'static>,
    sig: Signature,
    memory: Memory,
    top: Global,
    lists: u32,
    mode: Mode,
) -> FunctionBody {
    let mut body = FunctionBody::new(wmod, sig);
    let entry = body.entry;
    let size = body.blocks[entry].params[0].1;

    let fail = body.add_block();
    match mode {
        Mode::Module => {
            let null = Emit {
                body: &mut body,
                block: fail,
            }
            .c32(0);
            body.set_terminator(fail, Terminator::Return { values: vec![null] });
        }
        Mode::Host => body.set_terminator(fail, Terminator::Unreachable),
    }
    let sized = body.add_block();
    let fresh = body.add_block();
    let check = body.add_block();
    let grow = body.add_block();
    let ready = body.add_block();

    let max = Emit {
        body: &mut body,
        block: entry,
    }
    .c32(MAX_REQUEST);
    let too_big = Emit {
        body: &mut body,
        block: entry,
    }
    .op(Operator::I32GtU, &[size, max], WType::I32);
    body.set_terminator(
        entry,
        Terminator::CondBr {
            cond: too_big,
            if_true: target(fail, vec![]),
            if_false: target(sized, vec![]),
        },
    );

    // The class of the request.
    let mut e = Emit {
        body: &mut body,
        block: sized,
    };
    let min = e.c32(1 << MIN_CLASS);
    let small = e.op(Operator::I32LtU, &[size, min], WType::I32);
    let size = e.op(Operator::Select, &[min, size, small], WType::I32);
    let one = e.c32(1);
    let below = e.op(Operator::I32Sub, &[size, one], WType::I32);
    let leading = e.op(Operator::I32Clz, &[below], WType::I32);
    let thirty_two = e.c32(32);
    let class = e.op(Operator::I32Sub, &[thirty_two, leading], WType::I32);
    let head = list_head(&mut e, lists, class);
    match mode {
        Mode::Module => {
            let first = e.op(
                Operator::I32Load {
                    memory: word(memory),
                },
                &[head],
                WType::I32,
            );
            let reuse = body.add_block();
            body.set_terminator(
                sized,
                Terminator::CondBr {
                    cond: first,
                    if_true: target(reuse, vec![]),
                    if_false: target(fresh, vec![]),
                },
            );
            // Take the first block of the list.
            let mut r = Emit {
                body: &mut body,
                block: reuse,
            };
            let next = r.op(
                Operator::I32Load {
                    memory: word(memory),
                },
                &[first],
                WType::I32,
            );
            r.body.add_op(
                reuse,
                Operator::I32Store {
                    memory: word(memory),
                },
                &[head, next],
                &[],
            );
            let mut r = Emit {
                body: &mut body,
                block: reuse,
            };
            let state_offset = r.c32(HEADER - 4);
            let state_address = r.op(Operator::I32Sub, &[first, state_offset], WType::I32);
            let live = r.c32(LIVE);
            body.add_op(
                reuse,
                Operator::I32Store {
                    memory: word(memory),
                },
                &[state_address, live],
                &[],
            );
            body.set_terminator(
                reuse,
                Terminator::Return {
                    values: vec![first],
                },
            );
        }
        Mode::Host => {
            body.set_terminator(
                sized,
                Terminator::Br {
                    target: target(fresh, vec![]),
                },
            );
        }
    }

    // Cut a fresh block from the top.
    let mut f = Emit {
        body: &mut body,
        block: fresh,
    };
    let block = f.op(Operator::GlobalGet { global_index: top }, &[], WType::I32);
    let one64 = f.c64(1);
    let class64 = f.op(Operator::I64ExtendI32U, &[class], WType::I64);
    let payload = f.op(Operator::I64Shl, &[one64, class64], WType::I64);
    let block64 = f.op(Operator::I64ExtendI32U, &[block], WType::I64);
    let header = f.c64(u64::from(HEADER));
    let with_header = f.op(Operator::I64Add, &[block64, header], WType::I64);
    let end = f.op(Operator::I64Add, &[with_header, payload], WType::I64);
    let shift32 = f.c64(32);
    let high = f.op(Operator::I64ShrU, &[end, shift32], WType::I64);
    let zero64 = f.c64(0);
    let overflow = f.op(Operator::I64Ne, &[high, zero64], WType::I32);
    let pages = f.op(Operator::MemorySize { mem: memory }, &[], WType::I32);
    let pages64 = f.op(Operator::I64ExtendI32U, &[pages], WType::I64);
    let shift16 = f.c64(16);
    let have = f.op(Operator::I64Shl, &[pages64, shift16], WType::I64);
    let short = f.op(Operator::I64GtU, &[end, have], WType::I32);
    body.set_terminator(
        fresh,
        Terminator::CondBr {
            cond: overflow,
            if_true: target(fail, vec![]),
            if_false: target(check, vec![]),
        },
    );
    body.set_terminator(
        check,
        Terminator::CondBr {
            cond: short,
            if_true: target(grow, vec![]),
            if_false: target(ready, vec![]),
        },
    );

    // Grow by the missing pages.
    let mut g = Emit {
        body: &mut body,
        block: grow,
    };
    let page_mask = g.c64(PAGE - 1);
    let rounded = g.op(Operator::I64Add, &[end, page_mask], WType::I64);
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
            if_true: target(fail, vec![]),
            if_false: target(ready, vec![]),
        },
    );

    // Everything is checked: record the block and move the top.
    let mut d = Emit {
        body: &mut body,
        block: ready,
    };
    let end32 = d.op(Operator::I32WrapI64, &[end], WType::I32);
    let live = d.c32(LIVE);
    d.body.add_op(
        ready,
        Operator::GlobalSet { global_index: top },
        &[end32],
        &[],
    );
    body.add_op(
        ready,
        Operator::I32Store {
            memory: word(memory),
        },
        &[block, class],
        &[],
    );
    body.add_op(
        ready,
        Operator::I32Store {
            memory: word_at(memory, 4),
        },
        &[block, live],
        &[],
    );
    let header32 = Emit {
        body: &mut body,
        block: ready,
    }
    .c32(HEADER);
    let payload_address = Emit {
        body: &mut body,
        block: ready,
    }
    .op(Operator::I32Add, &[block, header32], WType::I32);
    body.set_terminator(
        ready,
        Terminator::Return {
            values: vec![payload_address],
        },
    );
    body.convert_to_max_ssa(None);
    body
}

/// `free(address)`.
///
/// A null address does nothing. Any other address must be the payload of a block
/// in use: 16-byte aligned, inside the heap, with the state `LIVE`, a class from
/// 4 to 31, and a block that ends at or below the top. Anything else traps and
/// changes nothing, which catches a double free and a free of a non-block.
pub(super) fn build_free(
    wmod: &WModule<'static>,
    sig: Signature,
    memory: Memory,
    top: Global,
    lists: u32,
    heap_start: u32,
) -> FunctionBody {
    let mut body = FunctionBody::new(wmod, sig);
    let entry = body.entry;
    let address = body.blocks[entry].params[0].1;

    let trap = body.add_block();
    body.set_terminator(trap, Terminator::Unreachable);
    let done = body.add_block();
    body.set_terminator(done, Terminator::Return { values: vec![] });
    let range = body.add_block();
    let load = body.add_block();
    let release = body.add_block();

    body.set_terminator(
        entry,
        Terminator::CondBr {
            cond: address,
            if_true: target(range, vec![]),
            if_false: target(done, vec![]),
        },
    );

    // The payload must be aligned and inside the heap.
    let mut r = Emit {
        body: &mut body,
        block: range,
    };
    let top_value = r.op(Operator::GlobalGet { global_index: top }, &[], WType::I32);
    let align_mask = r.c32(ALIGN - 1);
    let low_bits = r.op(Operator::I32And, &[address, align_mask], WType::I32);
    let no_bits = r.c32(0);
    let misaligned = r.op(Operator::I32Ne, &[low_bits, no_bits], WType::I32);
    let first_payload = r.c32(heap_start + HEADER);
    let before = r.op(Operator::I32LtU, &[address, first_payload], WType::I32);
    let beyond = r.op(Operator::I32GeU, &[address, top_value], WType::I32);
    let bad = r.op(Operator::I32Or, &[misaligned, before], WType::I32);
    let bad = r.op(Operator::I32Or, &[bad, beyond], WType::I32);
    body.set_terminator(
        range,
        Terminator::CondBr {
            cond: bad,
            if_true: target(trap, vec![]),
            if_false: target(load, vec![]),
        },
    );

    // The header must say a block in use whose end is at or below the top.
    let mut l = Emit {
        body: &mut body,
        block: load,
    };
    let header = l.c32(HEADER);
    let block = l.op(Operator::I32Sub, &[address, header], WType::I32);
    let class = l.op(
        Operator::I32Load {
            memory: word(memory),
        },
        &[block],
        WType::I32,
    );
    let state = l.op(
        Operator::I32Load {
            memory: word_at(memory, 4),
        },
        &[block],
        WType::I32,
    );
    let live = l.c32(LIVE);
    let not_live = l.op(Operator::I32Ne, &[state, live], WType::I32);
    let min_class = l.c32(MIN_CLASS);
    let too_small = l.op(Operator::I32LtU, &[class, min_class], WType::I32);
    let max_class = l.c32(CLASSES - 1);
    let too_large = l.op(Operator::I32GtU, &[class, max_class], WType::I32);
    let bad = l.op(Operator::I32Or, &[not_live, too_small], WType::I32);
    let bad = l.op(Operator::I32Or, &[bad, too_large], WType::I32);
    // The class is only meaningful when the checks above hold, so a bad class
    // makes the shift below irrelevant: the branch is taken first.
    let one64 = l.c64(1);
    let class64 = l.op(Operator::I64ExtendI32U, &[class], WType::I64);
    let payload = l.op(Operator::I64Shl, &[one64, class64], WType::I64);
    let address64 = l.op(Operator::I64ExtendI32U, &[address], WType::I64);
    let end = l.op(Operator::I64Add, &[address64, payload], WType::I64);
    let top64 = l.op(Operator::I64ExtendI32U, &[top_value], WType::I64);
    let past = l.op(Operator::I64GtU, &[end, top64], WType::I32);
    let bad = l.op(Operator::I32Or, &[bad, past], WType::I32);
    body.set_terminator(
        load,
        Terminator::CondBr {
            cond: bad,
            if_true: target(trap, vec![]),
            if_false: target(release, vec![]),
        },
    );

    // Put the block on the front of its class's list.
    let mut p = Emit {
        body: &mut body,
        block: release,
    };
    let head = list_head(&mut p, lists, class);
    let first = p.op(
        Operator::I32Load {
            memory: word(memory),
        },
        &[head],
        WType::I32,
    );
    let freed = p.c32(FREE);
    p.body.add_op(
        release,
        Operator::I32Store {
            memory: word_at(memory, 4),
        },
        &[block, freed],
        &[],
    );
    body.add_op(
        release,
        Operator::I32Store {
            memory: word(memory),
        },
        &[address, first],
        &[],
    );
    body.add_op(
        release,
        Operator::I32Store {
            memory: word(memory),
        },
        &[head, address],
        &[],
    );
    body.set_terminator(release, Terminator::Return { values: vec![] });
    body.convert_to_max_ssa(None);
    body
}

/// `arena_release(mark)`: frees every block at or above `mark`.
///
/// `mark` must be 16-byte aligned, not below the start of the heap and not above
/// the top; otherwise the call traps and changes nothing. Then every free list is
/// walked once, and each free block that does not end at or below `mark` is
/// unlinked, keeping the order of the others. The walk checks every node it
/// visits (aligned, inside the heap, state `FREE`) and allows at most as many
/// nodes as the heap can hold, and traps otherwise, which stops a loop made by
/// damage to a freed block. Only then are the bytes from `mark` to the top
/// cleared and the top moved back to `mark`, so the blocks the host allocator
/// hands out next are zero again.
///
/// Blocks in use that were cut above the mark are forgotten with the rest of the
/// region. Blocks that were taken from a list below the mark stay as they are.
pub(super) fn build_release(
    wmod: &WModule<'static>,
    sig: Signature,
    memory: Memory,
    top: Global,
    lists: u32,
    heap_start: u32,
) -> FunctionBody {
    let mut body = FunctionBody::new(wmod, sig);
    let entry = body.entry;
    let mark = body.blocks[entry].params[0].1;

    let trap = body.add_block();
    body.set_terminator(trap, Terminator::Unreachable);
    let walk = body.add_block();
    let header = body.add_block();
    let next_class = body.add_block();
    let load_head = body.add_block();
    let visit = body.add_block();
    let check_state = body.add_block();
    let test_end = body.add_block();
    let unlink = body.add_block();
    let keep = body.add_block();
    let clear = body.add_block();

    // The mark must be a valid one.
    let mut e = Emit {
        body: &mut body,
        block: entry,
    };
    let top_value = e.op(Operator::GlobalGet { global_index: top }, &[], WType::I32);
    let start = e.c32(heap_start);
    let below = e.op(Operator::I32LtU, &[mark, start], WType::I32);
    let above = e.op(Operator::I32GtU, &[mark, top_value], WType::I32);
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
            if_true: target(trap, vec![]),
            if_false: target(walk, vec![]),
        },
    );

    // The first list and the most nodes the heap can hold (each block takes at
    // least 32 bytes).
    let mut w = Emit {
        body: &mut body,
        block: walk,
    };
    let first_class = w.c32(MIN_CLASS);
    let first_head = list_head(&mut w, lists, first_class);
    let first_node = w.op(
        Operator::I32Load {
            memory: word(memory),
        },
        &[first_head],
        WType::I32,
    );
    let span = w.op(Operator::I32Sub, &[top_value, start], WType::I32);
    let five = w.c32(5);
    let nodes = w.op(Operator::I32ShrU, &[span, five], WType::I32);
    let one = w.c32(1);
    let budget = w.op(Operator::I32Add, &[nodes, one], WType::I32);
    body.set_terminator(
        walk,
        Terminator::Br {
            target: target(header, vec![first_class, first_head, first_node, budget]),
        },
    );

    // The loop over the nodes of all lists.
    let class = body.add_blockparam(header, WType::I32);
    let link = body.add_blockparam(header, WType::I32);
    let node = body.add_blockparam(header, WType::I32);
    let left = body.add_blockparam(header, WType::I32);
    let end_of_list = Emit {
        body: &mut body,
        block: header,
    }
    .op(Operator::I32Eqz, &[node], WType::I32);
    body.set_terminator(
        header,
        Terminator::CondBr {
            cond: end_of_list,
            if_true: target(next_class, vec![]),
            if_false: target(visit, vec![]),
        },
    );

    // The next list, or the end of the walk.
    let mut n = Emit {
        body: &mut body,
        block: next_class,
    };
    let one = n.c32(1);
    let next = n.op(Operator::I32Add, &[class, one], WType::I32);
    let last = n.c32(CLASSES);
    let done = n.op(Operator::I32Eq, &[next, last], WType::I32);
    body.set_terminator(
        next_class,
        Terminator::CondBr {
            cond: done,
            if_true: target(clear, vec![]),
            if_false: target(load_head, vec![]),
        },
    );
    let mut h = Emit {
        body: &mut body,
        block: load_head,
    };
    let next_head = list_head(&mut h, lists, next);
    let next_node = h.op(
        Operator::I32Load {
            memory: word(memory),
        },
        &[next_head],
        WType::I32,
    );
    body.set_terminator(
        load_head,
        Terminator::Br {
            target: target(header, vec![next, next_head, next_node, left]),
        },
    );

    // A node must be aligned, inside the heap, and the walk must not have run
    // out of budget.
    let mut v = Emit {
        body: &mut body,
        block: visit,
    };
    let align_mask = v.c32(ALIGN - 1);
    let low_bits = v.op(Operator::I32And, &[node, align_mask], WType::I32);
    let no_bits = v.c32(0);
    let misaligned = v.op(Operator::I32Ne, &[low_bits, no_bits], WType::I32);
    let first_payload = v.c32(heap_start + HEADER);
    let before = v.op(Operator::I32LtU, &[node, first_payload], WType::I32);
    let beyond = v.op(Operator::I32GeU, &[node, top_value], WType::I32);
    let exhausted = v.op(Operator::I32Eqz, &[left], WType::I32);
    let bad = v.op(Operator::I32Or, &[misaligned, before], WType::I32);
    let bad = v.op(Operator::I32Or, &[bad, beyond], WType::I32);
    let bad = v.op(Operator::I32Or, &[bad, exhausted], WType::I32);
    body.set_terminator(
        visit,
        Terminator::CondBr {
            cond: bad,
            if_true: target(trap, vec![]),
            if_false: target(check_state, vec![]),
        },
    );

    // The node must be a free block.
    let mut s = Emit {
        body: &mut body,
        block: check_state,
    };
    let twelve = s.c32(HEADER - 4);
    let state_address = s.op(Operator::I32Sub, &[node, twelve], WType::I32);
    let state = s.op(
        Operator::I32Load {
            memory: word(memory),
        },
        &[state_address],
        WType::I32,
    );
    let free = s.c32(FREE);
    let not_free = s.op(Operator::I32Ne, &[state, free], WType::I32);
    body.set_terminator(
        check_state,
        Terminator::CondBr {
            cond: not_free,
            if_true: target(trap, vec![]),
            if_false: target(test_end, vec![]),
        },
    );

    // Does the block end above the mark?
    let mut t = Emit {
        body: &mut body,
        block: test_end,
    };
    let after = t.op(
        Operator::I32Load {
            memory: word(memory),
        },
        &[node],
        WType::I32,
    );
    let one64 = t.c64(1);
    let class64 = t.op(Operator::I64ExtendI32U, &[class], WType::I64);
    let payload = t.op(Operator::I64Shl, &[one64, class64], WType::I64);
    let node64 = t.op(Operator::I64ExtendI32U, &[node], WType::I64);
    let block_end = t.op(Operator::I64Add, &[node64, payload], WType::I64);
    let mark64 = t.op(Operator::I64ExtendI32U, &[mark], WType::I64);
    let above_mark = t.op(Operator::I64GtU, &[block_end, mark64], WType::I32);
    let one = t.c32(1);
    let left_after = t.op(Operator::I32Sub, &[left, one], WType::I32);
    body.set_terminator(
        test_end,
        Terminator::CondBr {
            cond: above_mark,
            if_true: target(unlink, vec![]),
            if_false: target(keep, vec![]),
        },
    );
    // Unlink the node: the link before it now names the node after it.
    body.add_op(
        unlink,
        Operator::I32Store {
            memory: word(memory),
        },
        &[link, after],
        &[],
    );
    body.set_terminator(
        unlink,
        Terminator::Br {
            target: target(header, vec![class, link, after, left_after]),
        },
    );
    // Keep the node: it holds the link to the node after it.
    body.set_terminator(
        keep,
        Terminator::Br {
            target: target(header, vec![class, node, after, left_after]),
        },
    );

    // Clear the region above the mark and move the top back.
    let mut c = Emit {
        body: &mut body,
        block: clear,
    };
    let len = c.op(Operator::I32Sub, &[top_value, mark], WType::I32);
    let zero = c.c32(0);
    body.add_op(
        clear,
        Operator::MemoryFill { mem: memory },
        &[mark, zero, len],
        &[],
    );
    body.add_op(
        clear,
        Operator::GlobalSet { global_index: top },
        &[mark],
        &[],
    );
    body.set_terminator(clear, Terminator::Return { values: vec![] });
    body.convert_to_max_ssa(None);
    body
}
