//! A minimal `State` for interpreting a single instruction in unit tests.
//!
//! Every instruction-family test module needs the same stub: a value table,
//! a throwaway `DataFlowGraph`, and `unreachable!()` for the memory and
//! control-flow hooks that constant folding never reaches.

use std::collections::HashMap;

use super::{Action, EvalResults, EvalValue, State};
use crate::{
    DataFlowGraph, HasInst, Inst, Type, ValueId,
    builder::test_util::test_isa,
    module::{FuncRef, ModuleCtx},
};

pub(crate) struct TestHasInst;

impl<I: Inst> HasInst<I> for TestHasInst {}

pub(crate) struct TestState {
    dfg: DataFlowGraph,
    /// Tests seed this at construction and some rebind entries between
    /// interpreted instructions.
    pub(crate) values: HashMap<ValueId, EvalValue>,
}

impl TestState {
    /// Builds a state over a fresh, empty graph.
    pub(crate) fn new(values: impl IntoIterator<Item = (ValueId, EvalValue)>) -> Self {
        let isa = test_isa();
        Self::with_dfg(DataFlowGraph::new(ModuleCtx::new(&isa)), values)
    }

    /// Builds a state over a graph the caller has already populated, for tests
    /// whose instructions read value types back out of it.
    pub(crate) fn with_dfg(
        dfg: DataFlowGraph,
        values: impl IntoIterator<Item = (ValueId, EvalValue)>,
    ) -> Self {
        Self {
            dfg,
            values: values.into_iter().collect(),
        }
    }
}

impl State for TestState {
    fn lookup_val(&mut self, value: ValueId) -> EvalValue {
        self.values.get(&value).cloned().unwrap_or_default()
    }

    fn call_func(&mut self, _func: FuncRef, _args: Vec<EvalValue>) -> EvalResults {
        unreachable!()
    }

    fn set_action(&mut self, action: Action) {
        assert_eq!(action, Action::Continue);
    }

    fn prev_block(&mut self) -> crate::BlockId {
        unreachable!()
    }

    fn load(&mut self, _addr: EvalValue, _ty: Type) -> EvalValue {
        unreachable!()
    }

    fn store(&mut self, _addr: EvalValue, _value: EvalValue, _ty: Type) -> EvalValue {
        unreachable!()
    }

    fn alloca(&mut self, _ty: Type) -> EvalValue {
        unreachable!()
    }

    fn dfg(&self) -> &DataFlowGraph {
        &self.dfg
    }
}
