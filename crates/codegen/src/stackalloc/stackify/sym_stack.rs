use crate::stackalloc::{Action, Actions};
use sonatina_ir::{Function, Immediate, ValueId};
use std::collections::VecDeque;

use super::templates::BlockTemplate;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) enum StackItem {
    Value(ValueId),
    /// Implicit return address for the current function.
    FuncRetAddr,
    /// Temporary continuation address pushed for an internal `call`.
    CallRetAddr,
}

#[derive(Clone, Debug)]
pub(super) struct SymStack {
    /// Top-first.
    items: VecDeque<StackItem>,
}

impl SymStack {
    pub(super) fn entry_stack(func: &Function, has_internal_return: bool) -> Self {
        let mut items: VecDeque<StackItem> = func
            .arg_values
            .iter()
            .copied()
            .map(StackItem::Value)
            .collect();
        if has_internal_return {
            items.push_back(StackItem::FuncRetAddr);
        }
        Self { items }
    }

    pub(super) fn from_template(template: &BlockTemplate, has_internal_return: bool) -> Self {
        let mut items: VecDeque<StackItem> = template
            .params
            .iter()
            .copied()
            .chain(template.transfer.iter().copied())
            .map(StackItem::Value)
            .collect();
        if has_internal_return {
            items.push_back(StackItem::FuncRetAddr);
        }
        Self { items }
    }

    pub(super) fn func_ret_index(&self) -> Option<usize> {
        self.items.iter().position(|i| *i == StackItem::FuncRetAddr)
    }

    pub(super) fn len_above_func_ret(&self) -> usize {
        self.func_ret_index().unwrap_or(self.items.len())
    }

    pub(super) fn common_suffix_len(&self, desired: &[ValueId]) -> usize {
        let limit = self.len_above_func_ret();
        self.items
            .iter()
            .take(limit)
            .rev()
            .zip(desired.iter().rev().copied())
            .take_while(|&(item, want)| item == &StackItem::Value(want))
            .count()
    }

    pub(super) fn len(&self) -> usize {
        self.items.len()
    }

    pub(super) fn top(&self) -> Option<&StackItem> {
        self.items.front()
    }

    pub(super) fn item_at(&self, idx: usize) -> Option<&StackItem> {
        self.items.get(idx)
    }

    pub(super) fn iter(&self) -> impl Iterator<Item = &'_ StackItem> + '_ {
        self.items.iter()
    }

    pub(super) fn find_reachable_value(&self, v: ValueId, max_depth: usize) -> Option<usize> {
        let limit = self.len_above_func_ret().min(max_depth);
        self.items
            .iter()
            .take(limit)
            .position(|item| item == &StackItem::Value(v))
    }

    pub(super) fn find_reachable_value_from(
        &self,
        v: ValueId,
        start: usize,
        max_depth: usize,
    ) -> Option<usize> {
        let limit = self.len_above_func_ret().min(max_depth);
        self.items
            .iter()
            .skip(start)
            .take(limit.saturating_sub(start))
            .position(|item| item == &StackItem::Value(v))
            .map(|off| start + off)
    }

    pub(super) fn push_value(&mut self, v: ValueId) {
        self.items.push_front(StackItem::Value(v));
    }

    pub(super) fn push_imm(&mut self, stack_as: ValueId, imm: Immediate, actions: &mut Actions) {
        actions.push(Action::Push(imm));
        self.push_value(stack_as);
    }

    pub(super) fn rename_top_value(&mut self, v: ValueId) {
        let Some(StackItem::Value(top)) = self.items.front_mut() else {
            panic!("expected StackItem::Value on top of stack")
        };
        *top = v;
    }

    pub(super) fn rename_value_at_depth(&mut self, depth: usize, v: ValueId) {
        debug_assert!(depth < self.len_above_func_ret());
        let Some(StackItem::Value(slot)) = self.items.get_mut(depth) else {
            panic!("expected StackItem::Value at depth {depth}")
        };
        *slot = v;
    }

    /// Duplicate `stack[pos]` to the top (`DUP{pos+1}`).
    pub(super) fn dup(&mut self, pos: usize, actions: &mut Actions) {
        assert!(pos < super::DUP_MAX, "DUP out of range");
        assert!(pos < self.len_above_func_ret(), "DUP past call barrier");

        let item = self.items[pos].clone();
        self.items.push_front(item);
        actions.push(Action::StackDup(pos as u8));
    }

    /// Delete `stack[depth-1]` (1-indexed), preserving the relative order of the remaining items.
    pub(super) fn stable_delete_at_depth(&mut self, depth: usize, actions: &mut Actions) {
        assert!(
            (1..=super::SWAP_WINDOW_MAX).contains(&depth),
            "stable delete out of range"
        );
        assert!(
            depth <= self.len_above_func_ret(),
            "stable delete past call barrier"
        );

        for k in 1..depth {
            self.swap(k, actions);
        }
        self.pop(actions);
    }

    pub(super) fn pop(&mut self, actions: &mut Actions) {
        self.pop_operand();
        actions.push(Action::Pop);
    }

    pub(super) fn pop_n(&mut self, n: usize, actions: &mut Actions) {
        for _ in 0..n {
            self.pop(actions);
        }
    }

    pub(super) fn swap(&mut self, depth: usize, actions: &mut Actions) {
        if depth == 0 {
            return;
        }
        assert!(depth <= super::SWAP_DEPTH_MAX, "SWAP out of range");
        assert!(depth < self.len_above_func_ret(), "SWAP past call barrier");

        actions.push(Action::StackSwap(depth as u8));
        self.items.swap(0, depth);
    }

    pub(super) fn stable_rotate_to_top(&mut self, pos: usize, actions: &mut Actions) {
        if pos == 0 {
            return;
        }
        assert!(pos <= super::SWAP_DEPTH_MAX, "SWAP out of range");
        assert!(pos < self.len_above_func_ret(), "SWAP past call barrier");
        for k in 1..=pos {
            self.swap(k, actions);
        }
    }

    pub(super) fn clear_above_func_ret(&mut self, actions: &mut Actions) {
        while let Some(top) = self.items.front() {
            if *top == StackItem::FuncRetAddr {
                break;
            }
            self.pop(actions);
        }
    }

    pub(super) fn replace_above_func_ret(&mut self, above: Vec<StackItem>) {
        let Some(ret_pos) = self.func_ret_index() else {
            self.items = above.into_iter().collect();
            return;
        };

        let suffix = self.items.split_off(ret_pos);
        let mut items: VecDeque<StackItem> = above.into_iter().collect();
        items.extend(suffix);
        self.items = items;
    }

    pub(super) fn push_call_ret_addr(&mut self) {
        self.items.push_front(StackItem::CallRetAddr);
    }

    pub(super) fn push_call_continuation(&mut self, actions: &mut Actions) {
        actions.push(Action::PushContinuationOffset);
        self.push_call_ret_addr();
    }

    /// Ensure the call continuation address sits immediately below the `operand_count`
    /// call operands at the top of the stack.
    ///
    /// This matches the EVM backend's internal-call ABI, where the callee expects its return
    /// address (`FuncRetAddr`) to sit below its arguments and above any caller values that must
    /// survive the call.
    pub(super) fn position_call_ret_below_operands(
        &mut self,
        operand_count: usize,
        actions: &mut Actions,
    ) {
        if operand_count == 0 {
            return;
        }

        if self.items.front() != Some(&StackItem::CallRetAddr) {
            panic!("expected StackItem::CallRetAddr on top of stack");
        }

        // Stackify planning should keep the call continuation SWAP-reachable.
        assert!(
            operand_count <= super::SWAP_DEPTH_MAX,
            "call operand count exceeds SWAP16"
        );
        assert!(
            operand_count < self.len_above_func_ret(),
            "call operand count exceeds stack depth"
        );

        // During call operand preparation we arrange the operands as a left-rotation of the
        // callee ABI order. With that setup, a single swap with the bottom operand moves the
        // continuation behind the operands and restores the ABI operand order.
        self.swap(operand_count, actions);

        debug_assert_eq!(
            self.items.get(operand_count),
            Some(&StackItem::CallRetAddr),
            "failed to position call return address"
        );
    }

    pub(super) fn remove_call_ret_addr(&mut self) {
        let Some(pos) = self.items.iter().position(|i| *i == StackItem::CallRetAddr) else {
            panic!("expected StackItem::CallRetAddr")
        };
        self.items.remove(pos);
    }

    pub(super) fn pop_operand(&mut self) {
        match self.items.front() {
            Some(StackItem::FuncRetAddr) => {
                panic!("attempted to pop below function return barrier")
            }
            Some(_) => {
                self.items.pop_front();
            }
            None => {
                panic!("stack underflow")
            }
        }
    }

    pub(super) fn pop_n_operands(&mut self, n: usize) {
        for _ in 0..n {
            self.pop_operand();
        }
    }
}
