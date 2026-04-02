use super::vcode::{Label, SectionCodeUnitId, SymFixup, VCode, VCodeFixup, VCodeInst};
use crate::stackalloc::Allocator;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    BlockId, Function, GlobalVariableRef, Immediate, Inst, InstDowncast, InstId, Module, Type,
    Value, ValueId,
    inst::data::{GetFunctionPtr, SymAddr, SymSize, SymbolRef},
    module::{FuncRef, ModuleCtx},
    object::EmbedSymbol,
};

pub struct LoweredFunction<Op> {
    pub vcode: VCode<Op>,
    pub block_order: Vec<BlockId>,
}

pub struct SectionCodeUnit<Op> {
    pub id: SectionCodeUnitId,
    pub name: String,
    pub vcode: VCode<Op>,
    pub block_order: Vec<BlockId>,
}

pub struct SectionWorkModule {
    module: Module,
    entry: FuncRef,
    includes: Vec<FuncRef>,
    data: Vec<GlobalVariableRef>,
}

impl SectionWorkModule {
    pub fn from_roots(
        module: &Module,
        entry: FuncRef,
        includes: &[FuncRef],
        data: &[GlobalVariableRef],
    ) -> Self {
        let membership = build_section_membership(module, entry, includes, data);
        let funcs = module
            .funcs()
            .into_iter()
            .filter(|func| membership.funcs.contains(func))
            .collect::<Vec<_>>();
        Self::from_module_subset(module, &funcs, entry, includes, data)
    }

    pub fn from_module_subset(
        module: &Module,
        funcs: &[FuncRef],
        entry: FuncRef,
        includes: &[FuncRef],
        data: &[GlobalVariableRef],
    ) -> Self {
        Self {
            module: module.clone_for_funcs(funcs),
            entry,
            includes: includes.to_vec(),
            data: data.to_vec(),
        }
    }

    pub fn module(&self) -> &Module {
        &self.module
    }

    pub fn module_mut(&mut self) -> &mut Module {
        &mut self.module
    }

    pub fn entry(&self) -> FuncRef {
        self.entry
    }

    pub fn includes(&self) -> &[FuncRef] {
        &self.includes
    }

    pub fn data(&self) -> &[GlobalVariableRef] {
        &self.data
    }

    pub fn membership(&self) -> SectionMembership {
        build_section_membership(&self.module, self.entry, &self.includes, &self.data)
    }

    pub fn function_emission_order(&self, membership: &SectionMembership) -> Vec<FuncRef> {
        compute_section_function_emission_order(
            &self.module,
            self.entry,
            &self.includes,
            membership,
        )
    }
}

#[derive(Default)]
pub struct SectionMembership {
    pub funcs: FxHashSet<FuncRef>,
    pub globals: FxHashSet<GlobalVariableRef>,
    pub used_embed_symbols: FxHashSet<EmbedSymbol>,
}

pub fn build_section_membership(
    module: &Module,
    entry: FuncRef,
    includes: &[FuncRef],
    data: &[GlobalVariableRef],
) -> SectionMembership {
    let mut membership = SectionMembership::default();
    membership.globals.extend(data.iter().copied());

    let mut worklist = Vec::new();
    let roots = std::iter::once(entry).chain(includes.iter().copied());
    for func in roots {
        add_section_func(module, &mut membership, &mut worklist, func);
    }

    while let Some(func_ref) = worklist.pop() {
        module.func_store.try_view(func_ref, |func| {
            let is = func.inst_set();
            for block in func.layout.iter_block() {
                for inst_id in func.layout.iter_inst(block) {
                    if let Some(call) = func.dfg.call_info(inst_id) {
                        add_section_func(module, &mut membership, &mut worklist, call.callee());
                    }

                    let inst = func.dfg.inst(inst_id);

                    if let Some(ptr) = <&GetFunctionPtr as InstDowncast>::downcast(is, inst) {
                        add_section_func(module, &mut membership, &mut worklist, *ptr.func());
                    }

                    if let Some(sym) = <&SymAddr as InstDowncast>::downcast(is, inst) {
                        record_section_symbol(module, sym.sym(), &mut membership, &mut worklist);
                    }
                    if let Some(sym) = <&SymSize as InstDowncast>::downcast(is, inst) {
                        record_section_symbol(module, sym.sym(), &mut membership, &mut worklist);
                    }
                }
            }
        });
    }

    membership
}

pub fn compute_section_function_emission_order(
    module: &Module,
    entry: FuncRef,
    includes: &[FuncRef],
    membership: &SectionMembership,
) -> Vec<FuncRef> {
    let mut include_priority: FxHashMap<FuncRef, usize> = FxHashMap::default();
    for (idx, func) in includes.iter().copied().enumerate() {
        include_priority.entry(func).or_insert(idx);
    }

    let mut func_names: FxHashMap<FuncRef, String> = FxHashMap::default();
    for func in membership.funcs.iter().copied() {
        let name = module.ctx.func_sig(func, |sig| sig.name().to_string());
        func_names.insert(func, name);
    }

    let mut adjacency: FxHashMap<FuncRef, Vec<FuncRef>> = FxHashMap::default();
    for &func_ref in &membership.funcs {
        let mut callees: FxHashSet<FuncRef> = FxHashSet::default();
        module.func_store.view(func_ref, |func| {
            for block in func.layout.iter_block() {
                for inst_id in func.layout.iter_inst(block) {
                    if let Some(call) = func.dfg.call_info(inst_id) {
                        let callee = call.callee();
                        if membership.funcs.contains(&callee) {
                            callees.insert(callee);
                        }
                    }
                }
            }
        });

        let mut callees: Vec<_> = callees.into_iter().collect();
        callees.sort_by(|a, b| compare_section_func(*a, *b, &include_priority, &func_names));
        adjacency.insert(func_ref, callees);
    }

    let mut visited: FxHashSet<FuncRef> = FxHashSet::default();
    let mut order = Vec::new();

    fn dfs(
        node: FuncRef,
        adjacency: &FxHashMap<FuncRef, Vec<FuncRef>>,
        visited: &mut FxHashSet<FuncRef>,
        out: &mut Vec<FuncRef>,
    ) {
        if !visited.insert(node) {
            return;
        }
        out.push(node);
        if let Some(callees) = adjacency.get(&node) {
            for &callee in callees {
                dfs(callee, adjacency, visited, out);
            }
        }
    }

    if membership.funcs.contains(&entry) {
        dfs(entry, &adjacency, &mut visited, &mut order);
    }

    let mut extra_roots: Vec<FuncRef> = includes.to_vec();
    extra_roots.sort_by(|a, b| compare_section_func(*a, *b, &include_priority, &func_names));
    for root in extra_roots {
        if membership.funcs.contains(&root) {
            dfs(root, &adjacency, &mut visited, &mut order);
        }
    }

    let mut remaining: Vec<FuncRef> = membership
        .funcs
        .iter()
        .copied()
        .filter(|f| !visited.contains(f))
        .collect();
    remaining.sort_by(|a, b| compare_section_func(*a, *b, &include_priority, &func_names));
    for root in remaining {
        dfs(root, &adjacency, &mut visited, &mut order);
    }

    debug_assert_eq!(visited.len(), membership.funcs.len());
    order
}

fn add_section_func(
    module: &Module,
    membership: &mut SectionMembership,
    worklist: &mut Vec<FuncRef>,
    func: FuncRef,
) {
    if module.ctx.func_linkage(func).has_definition()
        && module.func_store.contains(func)
        && membership.funcs.insert(func)
    {
        worklist.push(func);
    }
}

fn record_section_symbol(
    module: &Module,
    sym: &SymbolRef,
    membership: &mut SectionMembership,
    worklist: &mut Vec<FuncRef>,
) {
    match sym {
        SymbolRef::Func(func) => add_section_func(module, membership, worklist, *func),
        SymbolRef::Global(gv) => {
            membership.globals.insert(*gv);
        }
        SymbolRef::Embed(sym) => {
            membership.used_embed_symbols.insert(sym.clone());
        }
        SymbolRef::CurrentSection => {}
    }
}

fn compare_section_func(
    a: FuncRef,
    b: FuncRef,
    include_priority: &FxHashMap<FuncRef, usize>,
    func_names: &FxHashMap<FuncRef, String>,
) -> std::cmp::Ordering {
    let a_pri = include_priority.get(&a).copied().unwrap_or(usize::MAX);
    let b_pri = include_priority.get(&b).copied().unwrap_or(usize::MAX);
    let a_name = func_names.get(&a).unwrap();
    let b_name = func_names.get(&b).unwrap();

    (a_pri, a_name, a.as_u32()).cmp(&(b_pri, b_name, b.as_u32()))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FixupUpdate {
    Unchanged,
    ContentChanged,
    LayoutChanged,
}

#[derive(Debug)]
pub struct CodegenError {}
pub type CodegenResult<T> = Result<T, CodegenError>;

pub struct Lower<'a, Op> {
    pub module: &'a ModuleCtx,
    function: &'a Function,
    vcode: VCode<Op>,

    cur_insn: Option<InstId>,
    cur_block: Option<BlockId>,

    // Optional mapping from block -> next block in the final emission layout.
    //
    // When present, `is_next_block` uses this instead of the IR block layout, so
    // fallthrough optimizations match the actual assembled `block_order`.
    next_block_in_layout: Option<FxHashMap<BlockId, BlockId>>,
}

impl<'a, Op: Default> Lower<'a, Op> {
    pub fn new(module: &'a ModuleCtx, function: &'a Function, block_order: &'a [BlockId]) -> Self {
        let mut next_block_in_layout = FxHashMap::default();
        for window in block_order.windows(2) {
            next_block_in_layout.insert(window[0], window[1]);
        }

        Lower {
            module,
            function,
            vcode: VCode::default(),
            cur_insn: None,
            cur_block: None,
            next_block_in_layout: Some(next_block_in_layout),
        }
    }

    pub fn lower(
        mut self,
        alloc: &mut dyn Allocator,
        mut enter_block: impl FnMut(&mut Self, &mut dyn Allocator, BlockId),
        mut enter_function: impl FnMut(&mut Self, &mut dyn Allocator, &Function),
        mut lower_insn: impl FnMut(&mut Self, &mut dyn Allocator, InstId),
    ) -> CodegenResult<VCode<Op>> {
        let function = self.function;
        let entry = function.layout.entry_block();
        for block in function.layout.iter_block() {
            self.cur_block = Some(block);
            self.cur_insn = None;
            enter_block(&mut self, alloc, block);
            if entry == Some(block) {
                enter_function(&mut self, alloc, function);
            }

            for insn in function.layout.iter_inst(block) {
                self.cur_insn = Some(insn);
                lower_insn(&mut self, alloc, insn);
            }
        }

        Ok(self.vcode)
    }

    pub fn push(&mut self, op: Op) -> VCodeInst {
        self.vcode
            .add_inst_to_block(op, self.cur_insn, self.cur_block.unwrap())
    }

    pub fn push_with_imm(&mut self, op: Op, bytes: &[u8]) {
        let i = self.push(op);
        self.add_immediate(i, bytes);
    }

    pub fn push_jump_target(&mut self, op: Op, dest: Label) {
        let op = self.push(op);
        self.add_label_reference(op, dest);
    }

    pub fn next_insn(&self) -> VCodeInst {
        self.vcode.insts.next_key()
    }

    pub fn add_immediate(&mut self, inst: VCodeInst, bytes: &[u8]) {
        self.vcode.inst_imm_bytes.insert((inst, bytes.into()));
    }

    pub fn add_label_reference(&mut self, inst: VCodeInst, dest: Label) {
        let label = self.vcode.labels.push(dest);
        self.vcode.fixups.insert((inst, VCodeFixup::Label(label)));
    }

    pub fn add_sym_fixup(&mut self, inst: VCodeInst, fixup: SymFixup) {
        self.vcode.fixups.insert((inst, VCodeFixup::Sym(fixup)));
    }

    pub fn push_sym_fixup(&mut self, op: Op, fixup: SymFixup) -> VCodeInst {
        let inst = self.push(op);
        self.add_immediate(inst, &[]);
        self.add_sym_fixup(inst, fixup);
        inst
    }

    pub fn insn_data(&self, inst: InstId) -> &dyn Inst {
        self.function.dfg.inst(inst)
    }

    pub fn value_imm(&self, value: ValueId) -> Option<Immediate> {
        self.function.dfg.value_imm(value)
    }

    pub fn value_ty(&self, value: ValueId) -> Type {
        self.function.dfg.value_ty(value)
    }

    pub fn insn_results(&self, inst: InstId) -> &[ValueId] {
        self.function.dfg.inst_results(inst)
    }

    pub fn insn_result_at(&self, inst: InstId, idx: usize) -> Option<ValueId> {
        self.function.dfg.inst_result_at(inst, idx)
    }

    pub fn insn_result(&self, inst: InstId) -> Option<ValueId> {
        self.function.dfg.single_inst_result(inst)
    }

    pub fn value_def_inst(&self, value: ValueId) -> Option<InstId> {
        self.value_def_inst_result(value).map(|(inst, _)| inst)
    }

    pub fn value_def_inst_result(&self, value: ValueId) -> Option<(InstId, usize)> {
        let Value::Inst {
            inst, result_idx, ..
        } = self.function.dfg.value(value)
        else {
            return None;
        };
        Some((*inst, usize::from(*result_idx)))
    }

    pub fn insn_block(&self, inst: InstId) -> BlockId {
        self.function.layout.inst_block(inst)
    }

    pub fn is_entry(&self, block: BlockId) -> bool {
        self.function.layout.entry_block() == Some(block)
    }

    /// Check if the given `BlockId` is next in the layout.
    /// Used for avoiding unnecessary `jump` operations.
    pub fn is_next_block(&self, block: BlockId) -> bool {
        let Some(cur) = self.cur_block else {
            return false;
        };

        if let Some(next_block_in_layout) = &self.next_block_in_layout {
            return next_block_in_layout.get(&cur).copied() == Some(block);
        }

        self.function.layout.next_block_of(cur) == Some(block)
    }
}
