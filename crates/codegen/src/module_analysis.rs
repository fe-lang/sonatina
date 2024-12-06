use cranelift_entity::{entity_impl, PrimaryMap, SecondaryMap};
use dashmap::{DashMap, ReadOnlyView};
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{module::FuncRef, Linkage, Module};

pub fn analyze_module(module: &Module) -> ModuleInfo {
    ModuleAnalyzer::new(module).analyze()
}

#[derive(Debug, Clone)]
pub struct ModuleInfo {
    pub scc: CallGraphSccs,
    pub call_graph: CallGraph,
    pub func_info: ReadOnlyView<FuncRef, FuncInfo>,
    pub access_pattern: ModuleAccessPattern,
}

/// The access pattern of a module with regard to function calls.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModuleAccessPattern {
    /// The module module calls a function from another module, but the module
    /// doesn't expose any function to other modules.
    OutgoingOnly,
    /// The module exposes at least one function to other modules, but the
    /// module doesn't call any function from other modules.
    IncomingOnly,
    /// `Bidirectional`: The module calls a function from another module, and
    /// also exposes at least one function to other modules.
    Bidirectional,
    /// `Closed`: The module doesn't call any function from other modules, and
    /// also doesn't expose any function to other modules.
    Closed,
}

impl ModuleAccessPattern {
    pub fn join(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Self::OutgoingOnly, Self::OutgoingOnly) => Self::OutgoingOnly,
            (Self::IncomingOnly, Self::IncomingOnly) => Self::IncomingOnly,
            (Self::IncomingOnly, Self::OutgoingOnly) | (Self::OutgoingOnly, Self::IncomingOnly) => {
                Self::Bidirectional
            }
            (Self::Bidirectional, _) | (_, Self::Bidirectional) => Self::Bidirectional,
            (Self::Closed, other) | (other, Self::Closed) => other,
        }
    }

    fn from_linkage(linkage: Linkage) -> Self {
        match linkage {
            Linkage::Public => Self::IncomingOnly,
            Linkage::External => Self::OutgoingOnly,
            Linkage::Private => Self::Closed,
        }
    }
}

/// The module-granular information of a function.
#[derive(Debug, Clone, Copy)]
pub struct FuncInfo {
    /// `ture` if the funciton is `NOT` a part of recursive function call. We
    /// take a conservative approach here, i.e., we only mark a function as
    /// non-recursive if we can ensure that the function is not recursive
    /// regardless of how the module is linked to other modules later.
    pub is_non_recursive: bool,
}

#[derive(Debug, Clone, Default)]
pub struct CallGraph {
    nodes: SecondaryMap<FuncRef, Node>,
}

impl CallGraph {
    /// Builds a call graph from a module.
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

    /// Returns `true` if the function is a leaf function.
    pub fn is_leaf(&self, func_ref: FuncRef) -> bool {
        self.nodes[func_ref].callees.is_empty()
    }
}

/// Represents the strongly connected components of a call graph in a module.
#[derive(Debug, Clone)]
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

#[derive(Debug, Default)]
pub struct SccBuilder {
    scc_map: SecondaryMap<FuncRef, SccRef>,
    scc_store: PrimaryMap<SccRef, SccInfo>,
    stack: Vec<FuncRef>,
    nodes: SecondaryMap<FuncRef, NodeState>,
    next_index: usize,
}

impl SccBuilder {
    pub fn new() -> Self {
        Self::default()
    }

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

#[derive(Debug, Clone, Default)]
struct Node {
    callees: Vec<FuncRef>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
struct SccRef(u32);
entity_impl!(SccRef);

#[derive(Default, Debug, Clone)]
struct NodeState {
    index: usize,
    lowlink: usize,
    on_stack: bool,
    visited: bool,
}

struct ModuleAnalyzer<'a> {
    module: &'a Module,
    access_pattern: ModuleAccessPattern,
    scc: CallGraphSccs,
    call_graph: CallGraph,
    func_info: DashMap<FuncRef, FuncInfo>,
}

impl<'a> ModuleAnalyzer<'a> {
    fn new(module: &'a Module) -> Self {
        let call_graph = CallGraph::build_graph(module);
        let scc = SccBuilder::default().compute_scc(&call_graph);
        Self {
            module,
            access_pattern: ModuleAccessPattern::Closed,
            scc,
            call_graph,
            func_info: DashMap::new(),
        }
    }

    fn analyze(mut self) -> ModuleInfo {
        self.determine_access_pattern();
        self.determine_func_info();

        ModuleInfo {
            scc: self.scc,
            call_graph: self.call_graph,
            func_info: self.func_info.into_read_only(),
            access_pattern: self.access_pattern,
        }
    }

    /// Determine the access pattern of the module.
    fn determine_access_pattern(&mut self) {
        let mut seen: FxHashSet<FuncRef> = FxHashSet::default();

        for (func_ref, node) in self.call_graph.nodes.iter() {
            if !seen.insert(func_ref) {
                continue;
            }

            let access_pattern =
                ModuleAccessPattern::from_linkage(self.module.ctx.func_linkage(func_ref));
            self.access_pattern = self.access_pattern.join(access_pattern);
            for &callee in &node.callees {
                if !seen.insert(callee) {
                    continue;
                };
                let access_pattern =
                    ModuleAccessPattern::from_linkage(self.module.ctx.func_linkage(callee));
                self.access_pattern = self.access_pattern.join(access_pattern);
            }
        }
    }

    /// Determine the module-granular information of functions.
    fn determine_func_info(&self) {
        // If the module access pattern is not `Bidirectional`, we can simply use the
        // SCC information to determine whether a function is non-recursive.
        if self.access_pattern != ModuleAccessPattern::Bidirectional {
            for func_ref in self.call_graph.nodes.keys() {
                let scc_info = self.scc.scc_of(func_ref);
                let is_non_recursive = !scc_info.is_cycle
                    || self.module.ctx.func_linkage(func_ref) != Linkage::External;
                self.func_info
                    .insert(func_ref, FuncInfo { is_non_recursive });
            }
        }

        // Traverse the call graph from public functions.
        // If there is the path from a public function to an external function,
        // the all node in the path is marked as recursive.
        // Otherwise, the node is marked as non-recursive if a node doesn't involve in a
        // cycle.
        let mut traversed: FxHashMap<FuncRef, bool> = FxHashMap::default();
        for (func_ref, callees) in self.call_graph.nodes.iter() {
            let sig = self.module.ctx.func_linkage(func_ref);
            if !sig.is_public() | self.func_info.contains_key(&func_ref) {
                continue;
            }

            let mut is_outgoing = false;
            for &callee in callees.callees.iter() {
                if !sig.is_public() | self.func_info.contains_key(&callee) {
                    continue;
                }
                is_outgoing |= self.traverse_incoming_flow(&mut traversed, callee);
            }

            let is_non_recursive = !(self.scc.scc_of(func_ref).is_cycle || is_outgoing);
            self.func_info
                .insert(func_ref, FuncInfo { is_non_recursive });
        }

        for func_ref in self.call_graph.nodes.keys() {
            if self.func_info.contains_key(&func_ref) {
                continue;
            }

            let is_non_recursive = !self.scc.scc_of(func_ref).is_cycle;
            self.func_info
                .insert(func_ref, FuncInfo { is_non_recursive });
        }
    }

    /// Traverse the incoming call flow of a function.
    /// Returns `true` if the function has an outgoing call to another module.
    fn traverse_incoming_flow(
        &self,
        traversed: &mut FxHashMap<FuncRef, bool>,
        func_ref: FuncRef,
    ) -> bool {
        if let Some(&is_outgoing) = traversed.get(&func_ref) {
            return is_outgoing;
        }

        let is_outgoing = self.module.ctx.func_linkage(func_ref).is_external()
            || self
                .call_graph
                .callee_of(func_ref)
                .iter()
                .any(|callee| self.traverse_incoming_flow(traversed, *callee));

        traversed.insert(func_ref, is_outgoing);
        let is_non_recursive = !(is_outgoing || self.scc.scc_of(func_ref).is_cycle);
        self.func_info
            .insert(func_ref, FuncInfo { is_non_recursive });

        is_outgoing
    }
}
