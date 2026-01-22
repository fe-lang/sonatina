use std::{collections::BTreeMap, fmt::Write};

use sonatina_ir::{BlockId, Function, InstId, ValueId};

use crate::{bitset::BitSet, stackalloc::SpillSlotRef};

use super::{
    super::Action,
    StackifyAlloc,
    slots::TRANSIENT_SLOT_TAG,
    sym_stack::{StackItem, SymStack},
    templates::BlockTemplate,
};

/// Optional observer hooks for tracing stackify planning.
///
/// `StackifyAlloc::for_function_with_trace` is allowed to run multiple fixed-point iterations.
/// Observers must support `checkpoint`/`rollback` so unsuccessful iterations can be discarded.
pub(super) trait StackifyObserver {
    type Checkpoint: Copy;

    fn checkpoint(&mut self) -> Self::Checkpoint;
    fn rollback(&mut self, checkpoint: Self::Checkpoint);

    fn on_block_header(&mut self, _func: &Function, _block: BlockId, _template: &BlockTemplate) {}

    fn on_block_inherited(
        &mut self,
        _func: &Function,
        _block: BlockId,
        _pred: BlockId,
        _inherited_stack: &SymStack,
        _live_future: &BitSet<ValueId>,
        _live_out: &BitSet<ValueId>,
    ) {
    }

    fn on_block_prologue(&mut self, _actions: &[Action]) {}

    fn on_inst_start(
        &mut self,
        _func: &Function,
        _inst: InstId,
        _stack: &SymStack,
        _live_future: &BitSet<ValueId>,
        _live_out: &BitSet<ValueId>,
        _last_use: &BitSet<ValueId>,
    ) {
    }

    fn on_inst_actions(
        &mut self,
        _label: &'static str,
        _actions: &[Action],
        _dest: Option<BlockId>,
    ) {
    }

    fn on_inst_normal(
        &mut self,
        _func: &Function,
        _inst: InstId,
        _args: &[ValueId],
        _res: Option<ValueId>,
    ) {
    }

    fn on_inst_jump(&mut self, _inst: InstId, _dest: BlockId) {}

    fn on_inst_br(&mut self, _func: &Function, _inst: InstId, _cond: ValueId, _dests: &[BlockId]) {}

    fn on_inst_br_table(&mut self, _inst: InstId) {}

    fn on_inst_return(&mut self, _func: &Function, _inst: InstId, _ret: Option<ValueId>) {}
}

pub(super) struct NullObserver;

impl StackifyObserver for NullObserver {
    type Checkpoint = ();

    fn checkpoint(&mut self) -> Self::Checkpoint {}

    fn rollback(&mut self, _checkpoint: Self::Checkpoint) {}
}

/// A snapshot-oriented trace collector for stackify planning.
///
/// The `render` output is intentionally stable and human-oriented: it prints per-block templates,
/// symbolic stacks at each instruction (dead values marked with `x`), and labels action groups
/// such as cleanup, prelude, exit normalization, and internal returns.
#[derive(Default)]
pub(super) struct StackifyTrace {
    out: String,
    action_chunks: Vec<ActionChunk>,
}

struct ActionChunk {
    placeholder: String,
    actions: crate::stackalloc::Actions,
}

impl StackifyTrace {
    pub(super) fn render(self, func: &Function, alloc: &StackifyAlloc) -> String {
        if func.layout.iter_block().next().is_none() {
            return "<empty function>\n".to_string();
        }

        let mut out = String::new();
        let _ = writeln!(&mut out, "STACKIFY");

        // Print spill-set slots in slot order.
        let mut spill_set_by_slot: BTreeMap<(u8, u32), Vec<ValueId>> = BTreeMap::new();
        for (v, slot) in alloc.slot_of_value.iter() {
            if let Some(slot) = *slot {
                let slot = match slot {
                    SpillSlotRef::Scratch(slot) => (0, slot),
                    SpillSlotRef::Persistent(slot) => (1, slot),
                    SpillSlotRef::Transient(slot) => (2, alloc.persistent_frame_slots + slot),
                };
                spill_set_by_slot.entry(slot).or_default().push(v);
            }
        }
        if !spill_set_by_slot.is_empty() {
            let _ = write!(&mut out, "spill_set: ");
            for (i, ((kind, slot), mut values)) in spill_set_by_slot.into_iter().enumerate() {
                values.sort_by_key(|v| v.as_u32());
                if i != 0 {
                    let _ = write!(&mut out, ", ");
                }
                let slot_label = if kind == 0 {
                    format!("s{slot}")
                } else {
                    slot.to_string()
                };
                if values.len() == 1 {
                    let _ = write!(&mut out, "{slot_label}={}", fmt_value(func, values[0]));
                } else {
                    let _ = write!(&mut out, "{slot_label}={}", fmt_values(func, &values));
                }
            }
            let _ = writeln!(&mut out);
        }

        let _ = writeln!(&mut out, "trace:");
        let mut trace = self.out;
        for chunk in self.action_chunks {
            let formatted = fmt_actions(&chunk.actions, alloc.persistent_frame_slots);
            trace = trace.replace(&chunk.placeholder, &formatted);
        }
        out.push_str(&trace);
        out
    }

    fn push_actions_placeholder(&mut self, actions: &[Action]) -> String {
        let idx = self.action_chunks.len();
        let placeholder = format!("@@ACTIONS:{idx}@@");
        let mut stored = crate::stackalloc::Actions::new();
        stored.extend_from_slice(actions);
        self.action_chunks.push(ActionChunk {
            placeholder: placeholder.clone(),
            actions: stored,
        });
        placeholder
    }
}

impl StackifyObserver for StackifyTrace {
    type Checkpoint = (usize, usize);

    fn checkpoint(&mut self) -> Self::Checkpoint {
        (self.out.len(), self.action_chunks.len())
    }

    fn rollback(&mut self, checkpoint: Self::Checkpoint) {
        let (out_len, chunk_len) = checkpoint;
        self.out.truncate(out_len);
        self.action_chunks.truncate(chunk_len);
    }

    fn on_block_header(&mut self, func: &Function, block: BlockId, template: &BlockTemplate) {
        let _ = writeln!(
            &mut self.out,
            "  {block:?} P={} T={}",
            fmt_values(func, &template.params),
            fmt_values(func, &template.transfer)
        );
    }

    fn on_block_inherited(
        &mut self,
        func: &Function,
        _block: BlockId,
        pred: BlockId,
        inherited_stack: &SymStack,
        live_future: &BitSet<ValueId>,
        live_out: &BitSet<ValueId>,
    ) {
        let _ = writeln!(
            &mut self.out,
            "    inherited from {pred:?}: {}",
            fmt_stack(func, inherited_stack, live_future, live_out)
        );
    }

    fn on_block_prologue(&mut self, actions: &[Action]) {
        if actions.is_empty() {
            return;
        }
        let placeholder = self.push_actions_placeholder(actions);
        let _ = writeln!(&mut self.out, "    prologue: {placeholder}");
    }

    fn on_inst_start(
        &mut self,
        func: &Function,
        _inst: InstId,
        stack: &SymStack,
        live_future: &BitSet<ValueId>,
        live_out: &BitSet<ValueId>,
        last_use: &BitSet<ValueId>,
    ) {
        let stack_start = fmt_stack(func, stack, live_future, live_out);
        let last_use_list: Vec<ValueId> = last_use.iter().collect();
        if last_use_list.is_empty() {
            let _ = writeln!(&mut self.out, "    - stack={stack_start}");
        } else {
            let _ = writeln!(
                &mut self.out,
                "    - stack={stack_start}, last_use={}",
                fmt_values(func, &last_use_list)
            );
        }
    }

    fn on_inst_actions(&mut self, label: &'static str, actions: &[Action], dest: Option<BlockId>) {
        if actions.is_empty() {
            return;
        }
        let placeholder = self.push_actions_placeholder(actions);
        match (label, dest) {
            ("exit", Some(dest)) => {
                let _ = writeln!(&mut self.out, "      exit({dest:?}): {placeholder}");
            }
            _ => {
                let _ = writeln!(&mut self.out, "      {label}: {placeholder}");
            }
        }
    }

    fn on_inst_normal(
        &mut self,
        func: &Function,
        inst: InstId,
        args: &[ValueId],
        res: Option<ValueId>,
    ) {
        let op_name = func.dfg.inst(inst).as_text();
        let _ = write!(&mut self.out, "      {op_name} {}", fmt_values(func, args));
        if let Some(r) = res {
            let _ = write!(&mut self.out, " -> {}", fmt_value(func, r));
        }
        let _ = writeln!(&mut self.out);
    }

    fn on_inst_jump(&mut self, _inst: InstId, dest: BlockId) {
        let _ = writeln!(&mut self.out, "      jump -> {dest:?}");
    }

    fn on_inst_br(&mut self, func: &Function, inst: InstId, cond: ValueId, dests: &[BlockId]) {
        let op_name = func.dfg.inst(inst).as_text();
        let _ = writeln!(
            &mut self.out,
            "      {op_name} {} -> {dests:?}",
            fmt_values(func, &[cond])
        );
    }

    fn on_inst_br_table(&mut self, _inst: InstId) {
        let _ = writeln!(&mut self.out, "      br_table");
    }

    fn on_inst_return(&mut self, func: &Function, inst: InstId, ret: Option<ValueId>) {
        let op_name = func.dfg.inst(inst).as_text();
        if let Some(ret) = ret {
            let _ = writeln!(
                &mut self.out,
                "      {op_name} {}",
                fmt_values(func, &[ret])
            );
        } else {
            let _ = writeln!(&mut self.out, "      {op_name} []");
        }
    }
}

fn fmt_immediate(imm: sonatina_ir::Immediate) -> String {
    use sonatina_ir::Immediate::*;
    match imm {
        I1(v) => format!("{v}"),
        I8(v) => format!("{v}"),
        I16(v) => format!("{v}"),
        I32(v) => format!("{v}"),
        I64(v) => format!("{v}"),
        I128(v) => format!("{v}"),
        I256(v) => format!("{v:?}"),
    }
}

fn fmt_value(func: &Function, v: ValueId) -> String {
    if func.dfg.value_is_imm(v) {
        let imm = func.dfg.value_imm(v).expect("imm value missing payload");
        return fmt_immediate(imm);
    }
    format!("v{}", v.as_u32())
}

fn fmt_values(func: &Function, values: &[ValueId]) -> String {
    let mut s = String::new();
    s.push('[');
    for (i, &v) in values.iter().enumerate() {
        if i != 0 {
            s.push_str(", ");
        }
        s.push_str(&fmt_value(func, v));
    }
    s.push(']');
    s
}

fn fmt_stack(
    func: &Function,
    stack: &SymStack,
    live_future: &BitSet<ValueId>,
    live_out: &BitSet<ValueId>,
) -> String {
    let mut s = String::new();
    s.push('[');
    for (i, item) in stack.iter().enumerate() {
        if i != 0 {
            s.push_str(", ");
        }
        match item {
            StackItem::Value(v) => {
                let v = *v;
                let mut v_s = fmt_value(func, v);
                if !func.dfg.value_is_imm(v) && !live_future.contains(v) && !live_out.contains(v) {
                    v_s.push('x');
                }
                s.push_str(&v_s);
            }
            StackItem::FuncRetAddr => s.push_str("<RET>"),
            StackItem::CallRetAddr => s.push_str("<CALLRET>"),
        }
    }
    s.push(']');
    s
}

fn fmt_actions(actions: &[Action], persistent_frame_slots: u32) -> String {
    fn decode_slot(slot: u32, persistent_frame_slots: u32) -> u32 {
        if slot & TRANSIENT_SLOT_TAG != 0 {
            persistent_frame_slots
                .checked_add(slot & !TRANSIENT_SLOT_TAG)
                .expect("frame slot overflow")
        } else {
            slot
        }
    }

    let mut s = String::new();
    s.push('[');
    for (i, a) in actions.iter().enumerate() {
        if i != 0 {
            s.push_str(", ");
        }
        match *a {
            Action::StackDup(n) => {
                let _ = write!(&mut s, "DUP{}", n as u32 + 1);
            }
            Action::StackSwap(n) => {
                let _ = write!(&mut s, "SWAP{n}");
            }
            Action::Push(imm) => {
                let _ = write!(&mut s, "PUSH({})", fmt_immediate(imm));
            }
            Action::PushContinuationOffset => s.push_str("PUSH_CONT"),
            Action::Pop => s.push_str("POP"),
            Action::MemLoadAbs(addr) => {
                let _ = write!(&mut s, "MLOAD_ABS({addr})");
            }
            Action::MemLoadFrameSlot(slot) => {
                let slot = decode_slot(slot, persistent_frame_slots);
                let _ = write!(&mut s, "MLOAD_SLOT({slot})");
            }
            Action::MemStoreAbs(addr) => {
                let _ = write!(&mut s, "MSTORE_ABS({addr})");
            }
            Action::MemStoreFrameSlot(slot) => {
                let slot = decode_slot(slot, persistent_frame_slots);
                let _ = write!(&mut s, "MSTORE_SLOT({slot})");
            }
        }
    }
    s.push(']');
    s
}
