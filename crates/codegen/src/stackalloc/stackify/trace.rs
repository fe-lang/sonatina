use std::{collections::BTreeMap, fmt::Write};

use rustc_hash::FxHashMap;
use sonatina_ir::{
    BlockId, Function, InstId, ValueId,
    inst::data,
    ir_writer::{FuncWriteCtx, InstStatement, IrWrite},
    module::FuncRef,
};

use crate::{
    bitset::BitSet,
    isa::evm::{
        immediate_u32,
        stack_plan::{InstStack, StackEntry, StackPlan, StackValue},
        static_arena_alloc::StackObjId,
    },
    object::MachineInstId,
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
    /// The stack that the current block inherited from its only predecessor, before the entry
    /// shuffle that the allocator planned for it. Set by `on_block_inherited`.
    inherited: Option<Vec<(StackItem, bool)>>,
    /// The inherited stack of a block whose entry shuffle is not empty. The shuffle is emitted as
    /// the first opcodes of the block's first instruction, so the record of that instruction is
    /// the stack before the shuffle, not the stack that the planner continues from.
    before_entry_shuffle: Option<Vec<(StackItem, bool)>>,
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
    /// `stack` keeps the same stack in structured form, for [`StackifyTrace::stack_plan`].
    InstHeader {
        inst: InstId,
        stack_line: String,
        stack: Vec<(StackItem, bool)>,
    },
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

    pub(crate) fn render(&self, func: &Function, alloc: &StackifyAlloc) -> String {
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
                Some(SpillStorage::Rematerialized) | None => {}
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
                TraceEvent::InstHeader {
                    inst, stack_line, ..
                } => {
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

    /// The structured form of the stacks recorded at each instruction. Reads the labels of
    /// `func`, the function that was planned.
    pub(crate) fn stack_plan(&self, func: &Function) -> StackPlan {
        // An instruction that appears more than once belongs to an iteration that planning
        // discarded and re-ran; the last record is the one that the plan kept.
        let mut by_inst: BTreeMap<u32, InstStack> = BTreeMap::new();
        for event in &self.events {
            let TraceEvent::InstHeader { inst, stack, .. } = event else {
                continue;
            };
            let stack = stack
                .iter()
                .map(|(item, dead)| match item {
                    StackItem::Value(value) => StackEntry::Value(StackValue {
                        value: *value,
                        dead: *dead,
                        constant: func.dfg.value_is_imm(*value),
                        labels: func.dfg.value_labels(*value).to_vec(),
                    }),
                    StackItem::FuncRetAddr => StackEntry::ReturnAddress,
                    StackItem::CallRetAddr => StackEntry::CallContinuation,
                })
                .collect();
            by_inst.insert(
                inst.as_u32(),
                InstStack {
                    inst: MachineInstId(*inst),
                    stack,
                },
            );
        }

        StackPlan {
            insts: by_inst.into_values().collect(),
        }
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
        self.inherited = None;
        self.before_entry_shuffle = None;
    }

    fn on_block_header(&mut self, func: &Function, block: BlockId, template: &BlockTemplate) {
        self.inherited = None;
        self.before_entry_shuffle = None;
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
        self.inherited = Some(structured_stack(
            func,
            inherited_stack,
            live_future,
            live_out,
        ));
        self.push_line(format!(
            "    inherited from {pred:?}: {}\n",
            fmt_stack(func, inherited_stack, live_future, live_out)
        ));
    }

    fn on_block_prologue(&mut self, actions: &[Action]) {
        let inherited = self.inherited.take();
        if actions.is_empty() {
            return;
        }
        self.before_entry_shuffle = inherited;
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
        // The text above shows the stack that planning continues from. The structured record is
        // the stack before the instruction's first emitted opcode, which for the first
        // instruction of a block with an entry shuffle is the stack before that shuffle.
        let stack = self
            .before_entry_shuffle
            .take()
            .unwrap_or_else(|| structured_stack(func, stack, live_future, live_out));
        self.events.push(TraceEvent::InstHeader {
            inst,
            stack_line,
            stack,
        });
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
    if let Some(gep) = func.dfg.downcast::<&data::Gep>(inst) {
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

/// `stack` with the dead flag of each item, in the form that a [`StackPlan`] is built from.
fn structured_stack(
    func: &Function,
    stack: &SymStack,
    live_future: &BitSet<ValueId>,
    live_out: &BitSet<ValueId>,
) -> Vec<(StackItem, bool)> {
    stack
        .iter()
        .map(|item| {
            let dead =
                matches!(item, StackItem::Value(v) if is_dead(func, *v, live_future, live_out));
            (item.clone(), dead)
        })
        .collect()
}

/// Whether `v` is a word that the instruction being planned and everything after it ignores, so
/// the planner pops it. Immediates are never dead: the planner may keep them for later uses.
fn is_dead(
    func: &Function,
    v: ValueId,
    live_future: &BitSet<ValueId>,
    live_out: &BitSet<ValueId>,
) -> bool {
    !func.dfg.value_is_imm(v) && !live_future.contains(v) && !live_out.contains(v)
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
                if is_dead(func, v, live_future, live_out) {
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
            Action::LoadCalldata(offset) => {
                let _ = write!(&mut s, "CALLDATALOAD({})", fmt_immediate(offset));
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
    use crate::{
        domtree::DomTree,
        isa::evm::stack_plan::{StackEntry, StackValue},
        liveness::Liveness,
        object::MachineInstId,
        stackalloc::{Action, Allocator, StackifyBuilder, StackifyEdgeSplitter},
    };
    use sonatina_ir::{ValueId, ValueLabel, cfg::ControlFlowGraph, inst::data};
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
                .find(|&inst| func.dfg.downcast::<&data::Gep>(inst).is_some())
                .expect("gep inst exists");
            let gep = func.dfg.downcast::<&data::Gep>(inst).expect("downcast gep");
            let base = gep.values()[0];
            let idx = gep.values()[1];

            // Non-u32 immediates stay runtime operands in stackify planning.
            assert!(func.dfg.value_is_imm(idx));
            assert!(func.dfg.value_imm(idx).expect("imm").is_negative());

            let rendered = fmt_trace_operands(func, inst, &[base, idx]);
            assert_eq!(rendered, fmt_values(func, &[base, idx]));
        });
    }

    /// A block with one predecessor and a phi. The machine pipeline removes such a phi before
    /// planning (`CfgCleanup`), so only a caller that plans a function directly reaches the
    /// allocator with one.
    const SINGLE_PRED_PHI: &str = r#"
target = "evm-ethereum-osaka"

func public %f(v0.i256, v1.i256) -> i256 {
block0:
    v2.i256 = add v0 v1;
    jump block1;
block1:
    v3.i256 = phi (v1 block0);
    v4.i256 = sub v3 v2;
    return v4;
}
"#;

    #[test]
    fn record_of_a_block_with_an_entry_shuffle_is_the_stack_before_the_shuffle() {
        let parsed = parse_module(SINGLE_PRED_PHI).expect("module parses");
        let fref = parsed.module.funcs()[0];
        let v1 = parsed.debug.value(fref, "v1").expect("v1 exists");
        let v2 = parsed.debug.value(fref, "v2").expect("v2 exists");
        let v4 = parsed.debug.value(fref, "v4").expect("v4 exists");
        parsed.module.func_store.modify(fref, |function| {
            function.dfg.add_value_label(v1, ValueLabel(7));

            let mut cfg = ControlFlowGraph::new();
            cfg.compute(function);
            StackifyEdgeSplitter::run(function, &mut cfg);
            let mut liveness = Liveness::new();
            liveness.compute(function, &cfg);
            let mut dom = DomTree::new();
            dom.compute(&cfg);
            let (alloc, trace) = StackifyBuilder::new(function, &cfg, &dom, &liveness, 16)
                .compute_with_trace_capture();
            let text = trace.render(function, &alloc);
            let plan = trace.stack_plan(function);

            // The first instruction of block1 starts with the allocator's entry shuffle.
            let sub = plan
                .insts
                .iter()
                .map(|record| record.inst.raw())
                .find(|&inst| function.dfg.inst_results(inst) == [v4])
                .expect("record of the sub");
            assert_eq!(
                alloc.pre_inst(sub).as_slice(),
                [Action::StackSwap(1)],
                "{text}"
            );
            // The text shows the stack that planning continues from, after the shuffle.
            assert!(
                text.contains("- stack=[v3, v2, <RET>], last_use=[v2, v3]"),
                "{text}"
            );

            // The record is the stack before the first opcode, which is the shuffle's SWAP1: v1
            // is still a separate, dead word below v2, and it keeps its label.
            let record = plan.stack_before(MachineInstId(sub)).expect("record");
            let value = |value: ValueId, dead: bool, labels: &[ValueLabel]| {
                StackEntry::Value(StackValue {
                    value,
                    dead,
                    constant: false,
                    labels: labels.to_vec(),
                })
            };
            assert_eq!(
                record.stack,
                [
                    value(v2, false, &[]),
                    value(v1, true, &[ValueLabel(7)]),
                    StackEntry::ReturnAddress
                ]
            );

            // Applying the shuffle to the record gives the stack that the text shows: the word of
            // v1 is the phi result v3, on top of v2.
            let mut replayed: Vec<_> = record.stack.clone();
            replayed.swap(0, 1);
            assert!(matches!(&replayed[0], StackEntry::Value(w) if w.value == v1));
            assert!(matches!(&replayed[1], StackEntry::Value(w) if w.value == v2));

            // Instructions without an entry shuffle are recorded as planned: the return reads
            // the sum's result on top of the return address.
            let ret = plan.insts.last().expect("record of the return");
            assert_eq!(
                ret.stack,
                [value(v4, false, &[]), StackEntry::ReturnAddress]
            );
        });
    }
}
