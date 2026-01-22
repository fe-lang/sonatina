use core::fmt;

use cranelift_entity::{PrimaryMap, SecondaryMap, entity_impl};
use dashmap::{DashMap, ReadOnlyView};
use rustc_hash::FxHashSet;
use sonatina_ir::{
    Linkage, Module,
    module::{FuncRef, ModuleCtx},
};

pub fn analyze_module(module: &Module) -> ModuleInfo {
    ModuleAnalyzer::new(module).analyze()
}

#[derive(Debug, Clone)]
pub struct ModuleInfo {
    pub scc: CallGraphSccs,
    pub call_graph: CallGraph,
    pub func_info: ReadOnlyView<FuncRef, FuncInfo>,
    pub access_pattern: DependencyFlow,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DependencyFlow {
    /// The entity depends on external functions but is not depended on by
    /// external functions.
    OutgoingOnly,
    /// The entity is depended on by external functions but does not depend on
    /// any external functions.
    IncomingOnly,
    /// The entity both depends on external functions and is depended on by
    /// external functions.
    Bidirectional,
    /// The entity neither depends on nor is depended on by external functions.
    Closed,
}

impl fmt::Display for DependencyFlow {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::OutgoingOnly => write!(f, "OutgoingOnly"),
            Self::IncomingOnly => write!(f, "IncomingOnly"),
            Self::Bidirectional => write!(f, "Bidirectional"),
            Self::Closed => write!(f, "Closed"),
        }
    }
}

impl DependencyFlow {
    /// Joins two dependency flows.
    /// `Closed` is the bottom, and `Bidirectional` is the top of this lattice.
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

    fn remove_flow(self, flow: Self) -> Self {
        match (self, flow) {
            (Self::OutgoingOnly, Self::OutgoingOnly) => Self::Closed,
            (Self::OutgoingOnly, Self::IncomingOnly) => Self::OutgoingOnly,
            (Self::IncomingOnly, Self::IncomingOnly) => Self::Closed,
            (Self::IncomingOnly, Self::OutgoingOnly) => Self::IncomingOnly,
            (Self::Bidirectional, Self::OutgoingOnly) => Self::IncomingOnly,
            (Self::Bidirectional, Self::IncomingOnly) => Self::OutgoingOnly,
            (_, Self::Bidirectional) => Self::Closed,
            (Self::Closed, _) => Self::Closed,
            (other, Self::Closed) => other,
        }
    }
}

/// The module-granular information of a function.
#[derive(Debug, Clone, Copy)]
pub struct FuncInfo {
    /// `ture` if the funciton is a part of recursive function call. We
    /// take a conservative approach here, i.e., we only mark a function as
    /// non-recursive if we can ensure that the function is not recursive
    /// regardless of how the module is linked to other modules later.
    pub is_recursive: bool,

    /// Indicates the [`DependencyFlow`] of the function.
    pub flow: DependencyFlow,

    /// `true` if the function is a leaf function.
    pub is_leaf: bool,
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

    /// Builds a call graph restricted to `funcs`.
    ///
    /// Any call edges to functions outside `funcs` are ignored.
    pub fn build_graph_subset(module: &Module, funcs: &FxHashSet<FuncRef>) -> Self {
        let mut nodes = SecondaryMap::new();

        let mut ordered: Vec<FuncRef> = funcs.iter().copied().collect();
        ordered.sort_unstable_by_key(|f| f.as_u32());

        for func_ref in ordered {
            let callees = module.func_store.view(func_ref, |func| {
                let mut callees = FxHashSet::default();
                for block in func.layout.iter_block() {
                    for inst_id in func.layout.iter_inst(block) {
                        if let Some(call) = func.dfg.call_info(inst_id) {
                            let callee = call.callee();
                            if funcs.contains(&callee) {
                                callees.insert(callee);
                            }
                        }
                    }
                }

                let mut callees: Vec<_> = callees.into_iter().collect();
                callees.sort_unstable();
                callees
            });

            nodes[func_ref] = Node { callees };
        }

        CallGraph { nodes }
    }

    pub fn funcs(&self) -> impl Iterator<Item = FuncRef> {
        self.nodes.keys()
    }

    /// Get the callees of a function.
    pub fn callee_of(&self, func_ref: FuncRef) -> &[FuncRef] {
        &self.nodes[func_ref].callees
    }

    /// Returns `true` if the function is a leaf function.
    /// If the function is an external functions, it returns always `false`.
    pub fn is_leaf(&self, ctx: &ModuleCtx, func_ref: FuncRef) -> bool {
        !ctx.func_linkage(func_ref).is_external() && self.nodes[func_ref].callees.is_empty()
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
        let scc_ref = self.scc_ref(func_ref);
        self.scc_info(scc_ref)
    }

    pub fn scc_ref(&self, func_ref: FuncRef) -> SccRef {
        self.scc_map[func_ref]
    }

    pub fn scc_info(&self, scc_ref: SccRef) -> &SccInfo {
        &self.scc_store[scc_ref]
    }
}

/// Represents the information of a strongly connected component in a call graph
/// of a module.
#[derive(Debug, Clone)]
pub struct SccInfo {
    /// Whether the SCC is a true cycle.
    /// NOTE: The SCC fomes a true cycle if it contains more than one function
    /// or a function that calls itself.
    pub is_cycle: bool,

    /// The functions in the SCC.
    /// NOTE: In case of the function is an external function, the SCC contains
    /// only one function.
    pub components: FxHashSet<FuncRef>,
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
                components: FxHashSet::default(),
                is_cycle: scc.len() > 1 || is_trivial_cycle,
            });

            for &func_ref in &scc {
                self.scc_map[func_ref] = scc_ref;
            }

            self.scc_store[scc_ref].components = scc;
        }
    }
}

#[derive(Debug, Clone, Default)]
struct Node {
    callees: Vec<FuncRef>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct SccRef(u32);
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
    access_pattern: DependencyFlow,
    sccs: CallGraphSccs,
    call_graph: CallGraph,
    func_info: DashMap<FuncRef, FuncInfo>,
}

impl<'a> ModuleAnalyzer<'a> {
    fn new(module: &'a Module) -> Self {
        let call_graph = CallGraph::build_graph(module);
        let scc = SccBuilder::default().compute_scc(&call_graph);
        Self {
            module,
            access_pattern: DependencyFlow::Closed,
            sccs: scc,
            call_graph,
            func_info: DashMap::new(),
        }
    }

    fn analyze(mut self) -> ModuleInfo {
        self.determine_access_pattern();
        self.determine_func_info();

        // Rewrites external functions info to the most conservative one.
        // In the course of traversing the SCCs, we have assumed that the external
        // function flow is `OutgoingOnly` to ensure that the rest of the internal
        // functions are not too conservative. But in reality, we can't know the actual
        // information of the external functions, so we rewrite the flow of the external
        // functions information to the most conservative one.
        for func_ref in self.module.func_store.funcs() {
            if self.module.ctx.func_linkage(func_ref).is_external() {
                self.func_info.insert(
                    func_ref,
                    FuncInfo {
                        is_recursive: true,
                        flow: DependencyFlow::Bidirectional,
                        is_leaf: false,
                    },
                );
            }
        }

        ModuleInfo {
            scc: self.sccs,
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
                DependencyFlow::from_linkage(self.module.ctx.func_linkage(func_ref));
            self.access_pattern = self.access_pattern.join(access_pattern);
            for &callee in &node.callees {
                if !seen.insert(callee) {
                    continue;
                };
                let access_pattern =
                    DependencyFlow::from_linkage(self.module.ctx.func_linkage(callee));
                self.access_pattern = self.access_pattern.join(access_pattern);
            }
        }
    }

    /// Determine the module-granular information of functions.
    fn determine_func_info(&self) {
        let mut visited: FxHashSet<SccRef> = FxHashSet::default();
        // Traverse the condensation DAG of a call graph to analyze the dependency flow
        // of functions and recursive calls.
        // We start traversing from public functions.
        for func_ref in self.call_graph.nodes.keys() {
            let sig = self.module.ctx.func_linkage(func_ref);
            if !sig.is_public() | self.func_info.contains_key(&func_ref) {
                continue;
            }

            let scc_ref = self.sccs.scc_ref(func_ref);
            self.traverse(scc_ref, DependencyFlow::IncomingOnly, &mut visited);
        }

        // Traverse the rest of the functions.
        for func_ref in self.call_graph.nodes.keys() {
            if self.func_info.contains_key(&func_ref) {
                continue;
            }

            let scc_ref = self.sccs.scc_ref(func_ref);
            self.traverse(scc_ref, DependencyFlow::Closed, &mut visited);
        }
    }

    /// Traverse the condensation DAG of a call graph to analyze the dependency
    /// flow, the recursive calls, and the leaf functions.
    fn traverse(
        &self,
        scc_ref: SccRef,
        initial_flow: DependencyFlow,
        visited: &mut FxHashSet<SccRef>,
    ) -> DependencyFlow {
        assert!(matches!(
            initial_flow,
            DependencyFlow::IncomingOnly | DependencyFlow::Closed,
        ));

        if visited.contains(&scc_ref) {
            // All functions in the same SCC has the same flow.
            let func_ref = self
                .sccs
                .scc_info(scc_ref)
                .components
                .iter()
                .next()
                .unwrap();
            return self.func_info.get(func_ref).unwrap().flow;
        }
        visited.insert(scc_ref);

        let mut flow = initial_flow;
        let mut is_external = false;
        for func_ref in self.sccs.scc_info(scc_ref).components.iter() {
            if self.module.ctx.func_linkage(*func_ref).is_external() {
                assert!(self.sccs.scc_info(scc_ref).components.len() == 1);
                is_external = true;
                flow = DependencyFlow::OutgoingOnly;
                break;
            }
            let mut child_flow = initial_flow;

            // Traverses child SCCs.
            for &callee in self.call_graph.callee_of(*func_ref) {
                // Skip the callee in the same SCC.
                if self.sccs.scc_ref(callee) == scc_ref {
                    continue;
                }

                let scc = self.sccs.scc_ref(callee);
                child_flow = child_flow.join(self.traverse(scc, initial_flow, visited));
            }

            flow = flow.join(child_flow);
        }

        if initial_flow == DependencyFlow::Closed {
            flow = flow.remove_flow(DependencyFlow::IncomingOnly);
        }

        let is_recursive = self.sccs.scc_info(scc_ref).is_cycle
            || flow == DependencyFlow::Bidirectional
            || is_external;
        for &func_ref in self.sccs.scc_info(scc_ref).components.iter() {
            let is_leaf = self.call_graph.is_leaf(&self.module.ctx, func_ref);
            self.func_info.insert(
                func_ref,
                FuncInfo {
                    is_recursive,
                    flow,
                    is_leaf,
                },
            );
        }

        flow
    }
}
