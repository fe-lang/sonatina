use dashmap::DashMap;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{module::FuncRef, visitor::Visitor, Module};

#[derive(Debug, Clone, Default)]
pub struct CallGraph {
    nodes: FxHashMap<FuncRef, Node>,
}

impl CallGraph {
    /// Build a call graph from a module.
    pub fn build_graph(module: &Module) -> Self {
        let nodes = DashMap::new();
        module.func_store.par_for_each(|func_ref, func| {
            let mut collector = CalleeCollector::default();
            for block in func.layout.iter_block() {
                for inst_id in func.layout.iter_inst(block) {
                    func.dfg.inst(inst_id).accept(&mut collector);
                }
            }

            let mut callees: Vec<_> = collector.callees.into_iter().collect();
            callees.sort_unstable();
            let node = Node { callee: callees };

            nodes.insert(func_ref, node);
        });

        CallGraph {
            nodes: nodes.into_iter().collect(),
        }
    }

    /// Get the callees of a function.
    pub fn callee_of(&self, func_ref: FuncRef) -> &[FuncRef] {
        &self.nodes[&func_ref].callee
    }
}

#[derive(Debug, Clone, Default)]
struct Node {
    callee: Vec<FuncRef>,
}

#[derive(Debug, Default)]
struct CalleeCollector {
    callees: FxHashSet<FuncRef>,
}

impl Visitor for CalleeCollector {
    fn visit_func_ref(&mut self, item: FuncRef) {
        self.callees.insert(item);
    }
}
