use std::{collections::BTreeMap, fmt::Write};

use rustc_hash::FxHashMap;
use sonatina_ir::{
    BlockId, Function, InstId, ValueId,
    inst::{data, downcast},
    ir_writer::{FuncWriteCtx, InstStatement, IrWrite},
    module::FuncRef,
};

use crate::{
    bitset::BitSet,
    isa::evm::{immediate_u32, static_arena_alloc::StackObjId},
    stackalloc::Actions,
};

use super::{
    super::Action,
    StackifyAlloc,
    alloc::SpillStorage,
    sym_stack::{StackItem, SymStack},
    templates::BlockTemplate,
};

/// Optional observer hooks for tracing stackify planning.
///
/// `StackifyBuilder::compute_with_trace` is allowed to run multiple fixed-point iterations.
/// Observers must support `checkpoint`/`rollback` so unsuccessful iterations can be discarded.
pub(super) trait StackifyObserver {
    fn checkpoint(&mut self) -> usize;
    fn rollback(&mut self, checkpoint: usize);

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
        _results: &[ValueId],
    ) {
    }

    fn on_inst_jump(&mut self, _inst: InstId, _dest: BlockId) {}

    fn on_deferred_inst_jump(&mut self, inst: InstId, dest: BlockId) -> usize {
        self.on_inst_jump(inst, dest);
        0
    }

    fn on_deferred_exit_actions(&mut self, _deferred: usize, _actions: &[Action]) {}

    fn on_inst_br(&mut self, _func: &Function, _inst: InstId, _cond: ValueId, _dests: &[BlockId]) {}

    fn on_inst_br_table(&mut self, _inst: InstId) {}

    fn on_inst_return(&mut self, _func: &Function, _inst: InstId, _rets: &[ValueId]) {}
}

pub(super) struct NullObserver;

impl StackifyObserver for NullObserver {
    fn checkpoint(&mut self) -> usize {
        0
    }

    fn rollback(&mut self, _checkpoint: usize) {}
}

/// A snapshot-oriented trace collector for stackify planning.
///
/// The `render` output is intentionally stable and human-oriented: it prints per-block templates,
/// symbolic stacks at each instruction (dead values marked with `x`), and labels action groups
/// such as cleanup, prelude, exit normalization, and internal returns.
#[derive(Default)]
pub(crate) struct StackifyTrace {
    events: Vec<TraceEvent>,
}

/// One recorded trace line (or line group). Everything that can be formatted at record time is
/// pre-rendered into a `Line`; the two things that cannot are kept structured:
/// - instruction comments need a `FuncWriteCtx` only available at render time (`InstHeader`);
/// - action payloads (`Actions`/`DeferredExit`) are stored raw so downstream object-id remapping
///   can rewrite them before render, and deferred-exit actions are filled in later by index.
enum TraceEvent {
    /// Fully pre-rendered text, including any trailing newline.
    Line(String),
    /// `// <inst comment>` line (rendered at the end) followed by `stack_line` (pre-rendered).
    InstHeader { inst: InstId, stack_line: String },
    /// An action group rendered as `{prefix}{actions}\n`. Only recorded for non-empty groups.
    Actions {
        prefix: String,
        actions: crate::stackalloc::Actions,
    },
    /// A deferred exit whose `actions` are filled in when its edge resolves; renders as
    /// `      exit({dest:?}): {actions}\n`, or nothing when no actions were added.
    DeferredExit {
        dest: BlockId,
        actions: crate::stackalloc::Actions,
    },
}

impl StackifyTrace {
    pub(crate) fn remap_stack_objects(&mut self, remap: &FxHashMap<StackObjId, StackObjId>) {
        fn remap_actions(actions: &mut Actions, remap: &FxHashMap<StackObjId, StackObjId>) {
            for action in actions {
                if let Action::MemLoadObj(obj) | Action::MemStoreObj(obj) = action
                    && let Some(new_obj) = remap.get(obj)
                {
                    *obj = *new_obj;
                }
            }
        }

        for event in &mut self.events {
            match event {
                TraceEvent::Actions { actions, .. } | TraceEvent::DeferredExit { actions, .. } => {
                    remap_actions(actions, remap);
                }
                TraceEvent::Line(_) | TraceEvent::InstHeader { .. } => {}
            }
        }
    }

    pub(crate) fn render(self, func: &Function, alloc: &StackifyAlloc) -> String {
        if func.layout.iter_block().next().is_none() {
            return "<empty function>\n".to_string();
        }

        let mut out = String::new();
        let _ = writeln!(&mut out, "STACKIFY");

        let mut spill_set_by_slot: BTreeMap<(u8, u32), Vec<ValueId>> = BTreeMap::new();
        for (v, storage) in alloc.spill_storage.iter() {
            match storage {
                Some(SpillStorage::Scratch(slot)) => {
                    spill_set_by_slot.entry((0, *slot)).or_default().push(v);
                }
                Some(SpillStorage::Object(obj)) => {
                    spill_set_by_slot
                        .entry((1, obj.as_u32()))
                        .or_default()
                        .push(v);
                }
                Some(SpillStorage::ExactLocal(_)) | None => {}
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
                    format!("o{slot}")
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
        for event in &self.events {
            match event {
                TraceEvent::Line(line) => out.push_str(line),
                TraceEvent::InstHeader { inst, stack_line } => {
                    let _ = writeln!(&mut out, "    // {}", fmt_inst_comment(func, *inst));
                    out.push_str(stack_line);
                }
                TraceEvent::Actions { prefix, actions } => {
                    let _ = writeln!(&mut out, "{prefix}{}", fmt_actions(actions));
                }
                TraceEvent::DeferredExit { dest, actions } => {
                    if !actions.is_empty() {
                        let _ =
                            writeln!(&mut out, "      exit({dest:?}): {}", fmt_actions(actions));
                    }
                }
            }
        }
        out
    }

    fn push_line(&mut self, line: String) {
        self.events.push(TraceEvent::Line(line));
    }

    fn push_actions(&mut self, prefix: String, actions: &[Action]) {
        let mut stored = crate::stackalloc::Actions::new();
        stored.extend_from_slice(actions);
        self.events.push(TraceEvent::Actions {
            prefix,
            actions: stored,
        });
    }
}

impl StackifyObserver for StackifyTrace {
    fn checkpoint(&mut self) -> usize {
        self.events.len()
    }

    fn rollback(&mut self, checkpoint: usize) {
        self.events.truncate(checkpoint);
    }

    fn on_block_header(&mut self, func: &Function, block: BlockId, template: &BlockTemplate) {
        self.push_line(format!(
            "  {block:?} P={} T={}\n",
            fmt_values(func, &template.params),
            fmt_values(func, template.transfer())
        ));
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
        self.push_line(format!(
            "    inherited from {pred:?}: {}\n",
            fmt_stack(func, inherited_stack, live_future, live_out)
        ));
    }

    fn on_block_prologue(&mut self, actions: &[Action]) {
        if actions.is_empty() {
            return;
        }
        self.push_actions("    prologue: ".to_string(), actions);
    }

    fn on_inst_start(
        &mut self,
        func: &Function,
        inst: InstId,
        stack: &SymStack,
        live_future: &BitSet<ValueId>,
        live_out: &BitSet<ValueId>,
        last_use: &BitSet<ValueId>,
    ) {
        let stack_start = fmt_stack(func, stack, live_future, live_out);
        let last_use_list: Vec<ValueId> = last_use.iter().collect();
        let stack_line = if last_use_list.is_empty() {
            format!("    - stack={stack_start}\n")
        } else {
            format!(
                "    - stack={stack_start}, last_use={}\n",
                fmt_values(func, &last_use_list)
            )
        };
        self.events
            .push(TraceEvent::InstHeader { inst, stack_line });
    }

    fn on_inst_actions(&mut self, label: &'static str, actions: &[Action], dest: Option<BlockId>) {
        if actions.is_empty() {
            return;
        }
        let prefix = match (label, dest) {
            ("exit", Some(dest)) => format!("      exit({dest:?}): "),
            _ => format!("      {label}: "),
        };
        self.push_actions(prefix, actions);
    }

    fn on_inst_normal(
        &mut self,
        func: &Function,
        inst: InstId,
        args: &[ValueId],
        results: &[ValueId],
    ) {
        let op_name = func.dfg.inst(inst).as_text();
        let mut line = format!("      {op_name} {}", fmt_trace_operands(func, inst, args));
        match results {
            [] => {}
            [result] => {
                let _ = write!(&mut line, " -> {}", fmt_value(func, *result));
            }
            _ => {
                let _ = write!(&mut line, " -> {}", fmt_values(func, results));
            }
        }
        line.push('\n');
        self.push_line(line);
    }

    fn on_inst_jump(&mut self, _inst: InstId, dest: BlockId) {
        self.push_line(format!("      jump -> {dest:?}\n"));
    }

    fn on_deferred_inst_jump(&mut self, inst: InstId, dest: BlockId) -> usize {
        let token = self.events.len();
        self.events.push(TraceEvent::DeferredExit {
            dest,
            actions: crate::stackalloc::Actions::new(),
        });
        self.on_inst_jump(inst, dest);
        token
    }

    fn on_deferred_exit_actions(&mut self, deferred: usize, actions: &[Action]) {
        let TraceEvent::DeferredExit {
            actions: stored, ..
        } = &mut self.events[deferred]
        else {
            debug_assert!(
                false,
                "deferred exit token does not point at a DeferredExit event"
            );
            return;
        };
        stored.extend_from_slice(actions);
    }

    fn on_inst_br(&mut self, func: &Function, inst: InstId, cond: ValueId, dests: &[BlockId]) {
        let op_name = func.dfg.inst(inst).as_text();
        self.push_line(format!(
            "      {op_name} {} -> {dests:?}\n",
            fmt_values(func, &[cond])
        ));
    }

    fn on_inst_br_table(&mut self, _inst: InstId) {
        self.push_line("      br_table\n".to_string());
    }

    fn on_inst_return(&mut self, func: &Function, inst: InstId, rets: &[ValueId]) {
        let op_name = func.dfg.inst(inst).as_text();
        let line = if rets.is_empty() {
            format!("      {op_name} []\n")
        } else {
            format!("      {op_name} {}\n", fmt_values(func, rets))
        };
        self.push_line(line);
    }
}

fn fmt_inst_comment(func: &Function, inst: InstId) -> String {
    let Some(func_ref) = fallback_func_ref(func) else {
        return fmt_inst_comment_fallback(func, inst);
    };
    let ctx = FuncWriteCtx::new(func, func_ref);
    let mut bytes = Vec::new();
    if InstStatement(inst).write(&mut bytes, &ctx).is_ok()
        && let Ok(comment) = String::from_utf8(bytes)
    {
        return comment;
    }
    fmt_inst_comment_fallback(func, inst)
}

fn fallback_func_ref(func: &Function) -> Option<FuncRef> {
    func.ctx()
        .declared_funcs
        .iter()
        .next()
        .map(|entry| *entry.key())
}

fn fmt_inst_comment_fallback(func: &Function, inst: InstId) -> String {
    format!("{};", func.dfg.inst(inst).as_text())
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
        I256(v) => format!("{v}"),
        EnumTag { value, .. } => format!("{value}"),
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

fn fmt_trace_operands(func: &Function, inst: InstId, args: &[ValueId]) -> String {
    if let Some(gep) = downcast::<&data::Gep>(func.inst_set(), func.dfg.inst(inst)) {
        // Keep alias-canonicalized runtime operands from `args`, while still showing the full
        // static GEP index list by reinserting compile-time immediate-u32 indices.
        let mut runtime = args.iter().copied();
        let mut rendered: Vec<ValueId> = Vec::with_capacity(gep.values().len());
        for (i, &value) in gep.values().as_slice().iter().enumerate() {
            let is_runtime_operand = i == 0
                || !func.dfg.value_is_imm(value)
                || func.dfg.value_imm(value).and_then(immediate_u32).is_none();
            if is_runtime_operand {
                rendered.push(runtime.next().unwrap_or(value));
            } else {
                rendered.push(value);
            }
        }
        debug_assert!(
            runtime.next().is_none(),
            "trace GEP runtime operand reconstruction left extra args"
        );
        return fmt_values(func, &rendered);
    }
    fmt_values(func, args)
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

fn fmt_actions(actions: &[Action]) -> String {
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
                let _ = write!(&mut s, "MLOAD_SLOT({slot})");
            }
            Action::MaterializeLocalAddr {
                alloca,
                offset_bytes,
            } => {
                let _ = write!(
                    &mut s,
                    "MAT_LOCAL_ADDR({}, {offset_bytes})",
                    alloca.as_u32()
                );
            }
            Action::PushFrameAddr {
                offset_words,
                extra_bytes,
            } => {
                let _ = write!(&mut s, "PUSH_FRAME_ADDR({offset_words}, {extra_bytes})");
            }
            Action::MemLoadObj(obj) => {
                let _ = write!(&mut s, "MLOAD_OBJ({})", obj.as_u32());
            }
            Action::MemStoreAbs(addr) => {
                let _ = write!(&mut s, "MSTORE_ABS({addr})");
            }
            Action::MemStoreFrameSlot(slot) => {
                let _ = write!(&mut s, "MSTORE_SLOT({slot})");
            }
            Action::MemStoreObj(obj) => {
                let _ = write!(&mut s, "MSTORE_OBJ({})", obj.as_u32());
            }
        }
    }
    s.push(']');
    s
}

#[cfg(test)]
mod tests {
    use super::{fmt_trace_operands, fmt_values};
    use sonatina_ir::inst::{data, downcast};
    use sonatina_parser::parse_module;

    #[test]
    fn gep_trace_does_not_duplicate_runtime_immediates() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f(v0.*i256) -> *i256 {
block0:
    v1.*i256 = gep v0 -1.i8;
    return v1;
}
"#;

        let parsed = parse_module(SRC).expect("module parses");
        let func_ref = parsed
            .module
            .funcs()
            .into_iter()
            .find(|&f| parsed.module.ctx.func_sig(f, |sig| sig.name() == "f"))
            .expect("function exists");

        parsed.module.func_store.view(func_ref, |func| {
            let block = func.layout.entry_block().expect("entry block exists");
            let inst = func
                .layout
                .iter_inst(block)
                .find(|&inst| {
                    downcast::<&data::Gep>(func.inst_set(), func.dfg.inst(inst)).is_some()
                })
                .expect("gep inst exists");
            let gep =
                downcast::<&data::Gep>(func.inst_set(), func.dfg.inst(inst)).expect("downcast gep");
            let base = gep.values()[0];
            let idx = gep.values()[1];

            // Non-u32 immediates stay runtime operands in stackify planning.
            assert!(func.dfg.value_is_imm(idx));
            assert!(func.dfg.value_imm(idx).expect("imm").is_negative());

            let rendered = fmt_trace_operands(func, inst, &[base, idx]);
            assert_eq!(rendered, fmt_values(func, &[base, idx]));
        });
    }
}
