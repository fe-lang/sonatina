use std::{collections::BTreeMap, fmt::Write};

use sonatina_ir::{
    BlockId, Function, InstId, U256, ValueId,
    inst::{data, downcast},
    ir_writer::{FuncWriteCtx, InstStatement, IrWrite},
    module::FuncRef,
};

use crate::bitset::BitSet;

use super::{
    super::Action,
    StackifyAlloc,
    sym_stack::{StackItem, SymStack},
    templates::BlockTemplate,
};

/// Optional observer hooks for tracing stackify planning.
///
/// `StackifyBuilder::compute_with_trace` is allowed to run multiple fixed-point iterations.
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
    inst_chunks: Vec<InstChunk>,
}

struct ActionChunk {
    placeholder: String,
    actions: crate::stackalloc::Actions,
}

struct InstChunk {
    placeholder: String,
    inst: InstId,
}

impl StackifyTrace {
    pub(super) fn render(self, func: &Function, alloc: &StackifyAlloc) -> String {
        if func.layout.iter_block().next().is_none() {
            return "<empty function>\n".to_string();
        }

        let mut out = String::new();
        let _ = writeln!(&mut out, "STACKIFY");

        let mut spill_set_by_slot: BTreeMap<(u8, u32), Vec<ValueId>> = BTreeMap::new();
        for (v, slot) in alloc.scratch_slot_of_value.iter() {
            if let Some(slot) = *slot {
                spill_set_by_slot.entry((0, slot)).or_default().push(v);
            }
        }
        for (v, obj) in alloc.spill_obj.iter() {
            if alloc.scratch_slot_of_value[v].is_some() {
                continue;
            }
            if let Some(obj) = *obj {
                spill_set_by_slot
                    .entry((1, obj.as_u32()))
                    .or_default()
                    .push(v);
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
        let mut trace = self.out;
        for chunk in self.action_chunks {
            let formatted = fmt_actions(&chunk.actions);
            trace = trace.replace(&chunk.placeholder, &formatted);
        }
        for chunk in self.inst_chunks {
            let comment = fmt_inst_comment(func, chunk.inst);
            trace = trace.replace(&chunk.placeholder, &comment);
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

    fn push_inst_placeholder(&mut self, inst: InstId) -> String {
        let idx = self.inst_chunks.len();
        let placeholder = format!("@@INST:{idx}@@");
        self.inst_chunks.push(InstChunk {
            placeholder: placeholder.clone(),
            inst,
        });
        placeholder
    }
}

impl StackifyObserver for StackifyTrace {
    type Checkpoint = (usize, usize, usize);

    fn checkpoint(&mut self) -> Self::Checkpoint {
        (
            self.out.len(),
            self.action_chunks.len(),
            self.inst_chunks.len(),
        )
    }

    fn rollback(&mut self, checkpoint: Self::Checkpoint) {
        let (out_len, action_chunk_len, inst_chunk_len) = checkpoint;
        self.out.truncate(out_len);
        self.action_chunks.truncate(action_chunk_len);
        self.inst_chunks.truncate(inst_chunk_len);
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
        inst: InstId,
        stack: &SymStack,
        live_future: &BitSet<ValueId>,
        live_out: &BitSet<ValueId>,
        last_use: &BitSet<ValueId>,
    ) {
        let comment = self.push_inst_placeholder(inst);
        let _ = writeln!(&mut self.out, "    // {comment}");
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
        let _ = write!(
            &mut self.out,
            "      {op_name} {}",
            fmt_trace_operands(func, inst, args)
        );
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

fn immediate_u32(imm: sonatina_ir::Immediate) -> Option<u32> {
    if imm.is_negative() {
        return None;
    }

    let value = imm.as_i256().to_u256();
    if value > U256::from(u32::MAX) {
        return None;
    }

    Some(value.low_u32())
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
