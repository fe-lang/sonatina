use cranelift_entity::{entity_impl, PrimaryMap, SecondaryMap};
use dashmap::DashMap;
use rustc_hash::FxHashSet;
use sonatina_ir::{module::FuncRef, Module};

#[derive(Debug, Clone, Default)]
pub struct CallGraph {
    nodes: SecondaryMap<FuncRef, Node>,
}

impl CallGraph {
    /// Build a call graph from a module.
    pub fn build_graph(module: &Module) -> Self {
        let d_nodes = DashMap::new();
        module.func_store.par_for_each(|func_ref, func| {
            let mut callees = FxHashSet::default();
            for block in func.layout.iter_block() {
                for inst_id in func.layout.iter_inst(block) {
                    if let Some(call) = func.dfg.call_info(inst_id) {
                        callees.insert(call.callee());
                    }
                }
            }

            let mut callees: Vec<_> = callees.into_iter().collect();
            callees.sort_unstable();
            let node = Node { callees };

            d_nodes.insert(func_ref, node);
        });

        let mut nodes = SecondaryMap::new();
        for (func_ref, node) in d_nodes {
            nodes[func_ref] = node;
        }
        CallGraph { nodes }
    }

    /// Get the callees of a function.
    pub fn callee_of(&self, func_ref: FuncRef) -> &[FuncRef] {
        &self.nodes[func_ref].callees
    }
}

#[derive(Debug, Clone, Default)]
struct Node {
    callees: Vec<FuncRef>,
}

/// Represents the strongly connected components of a call graph in a module.
pub struct CallGraphSccs {
    scc_map: SecondaryMap<FuncRef, SccRef>,
    scc_store: PrimaryMap<SccRef, SccInfo>,
}

impl CallGraphSccs {
    pub fn scc_of(&self, func_ref: FuncRef) -> &SccInfo {
        let scc_ref = self.scc_map[func_ref];
        &self.scc_store[scc_ref]
    }
}

#[derive(Debug, Clone)]
pub struct SccInfo {
    /// Whether the SCC is a true cycle.
    /// NOTE: The SCC fomes a true cycle if it contains more than one function
    /// or a function that calls itself.
    pub is_cycle: bool,

    /// The functions in the SCC.
    pub scc: FxHashSet<FuncRef>,
}

#[derive(Debug)]
pub struct SccBuilder {
    scc_map: SecondaryMap<FuncRef, SccRef>,
    scc_store: PrimaryMap<SccRef, SccInfo>,
    stack: Vec<FuncRef>,
    nodes: SecondaryMap<FuncRef, NodeState>,
    next_index: usize,
}

impl SccBuilder {
    pub fn compute_scc(mut self, call_graph: &CallGraph) -> CallGraphSccs {
        for func_ref in call_graph.nodes.keys() {
            if !self.nodes[func_ref].visited {
                self.strong_component(func_ref, call_graph);
            }
        }

        CallGraphSccs {
            scc_map: self.scc_map,
            scc_store: self.scc_store,
        }
    }

    fn strong_component(&mut self, func_ref: FuncRef, call_graph: &CallGraph) {
        let index = self.next_index;
        self.next_index += 1;
        let node_info = NodeState {
            index,
            lowlink: index,
            on_stack: true,
            visited: true,
        };
        self.nodes[func_ref] = node_info;
        self.stack.push(func_ref);

        let mut is_trivial_cycle = false;

        for &callee in call_graph.callee_of(func_ref) {
            is_trivial_cycle |= callee == func_ref;

            if !self.nodes[callee].visited {
                self.strong_component(callee, call_graph);
                self.nodes[func_ref].lowlink =
                    self.nodes[func_ref].lowlink.min(self.nodes[callee].lowlink);
            } else if self.nodes[callee].on_stack {
                self.nodes[func_ref].lowlink =
                    self.nodes[func_ref].lowlink.min(self.nodes[callee].index);
            }
        }

        if self.nodes[func_ref].index == self.nodes[func_ref].lowlink {
            let mut scc = FxHashSet::default();

            loop {
                let top = self.stack.pop().unwrap();
                self.nodes[top].on_stack = false;
                scc.insert(top);

                if top == func_ref {
                    break;
                }
            }

            let scc_ref = self.scc_store.push(SccInfo {
                scc: FxHashSet::default(),
                is_cycle: scc.len() > 1 || is_trivial_cycle,
            });

            for &func_ref in &scc {
                self.scc_map[func_ref] = scc_ref;
            }

            self.scc_store[scc_ref].scc = scc;
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct SccRef(u32);
entity_impl!(SccRef);

#[derive(Default, Debug, Clone)]
struct NodeState {
    index: usize,
    lowlink: usize,
    on_stack: bool,
    visited: bool,
}
