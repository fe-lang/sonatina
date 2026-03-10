use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    BlockId, Function, InstId, InstSetExt, Type, ValueId,
    cfg::ControlFlowGraph,
    inst::{SideEffect, evm::inst_set::EvmInstKind},
    isa::{Isa, evm::Evm},
};

use crate::{
    domtree::DomTree,
    post_domtree::{PDTIdom, PostDomTree},
    stackalloc::{Action, Allocator},
};

use super::{FuncMemPlan, ObjLoc, fold_stack_actions};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum FrameSite {
    BlockEntry(BlockId),
    EnterFunction,
    PreInst(InstId),
    Inst(InstId),
    PostInst(InstId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum FrameInjectionPoint {
    BeforeSite(FrameSite),
    BeforeAction {
        site: FrameSite,
        action_index: usize,
    },
    AfterAction {
        site: FrameSite,
        action_index: usize,
    },
    AfterSite(FrameSite),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LazyFramePlan {
    enter: FrameInjectionPoint,
    exits: Vec<FrameInjectionPoint>,
}

impl LazyFramePlan {
    pub(crate) fn enter_before_site(&self, site: FrameSite) -> bool {
        self.enter == FrameInjectionPoint::BeforeSite(site)
    }

    pub(crate) fn enter_before_action(&self, site: FrameSite, action_index: usize) -> bool {
        self.enter == FrameInjectionPoint::BeforeAction { site, action_index }
    }

    pub(crate) fn exit_before_site(&self, site: FrameSite) -> bool {
        self.exits
            .iter()
            .copied()
            .any(|point| point == FrameInjectionPoint::BeforeSite(site))
    }

    pub(crate) fn exit_after_action(&self, site: FrameSite, action_index: usize) -> bool {
        self.exits
            .iter()
            .copied()
            .any(|point| point == FrameInjectionPoint::AfterAction { site, action_index })
    }

    pub(crate) fn exit_after_site(&self, site: FrameSite) -> bool {
        self.exits
            .iter()
            .copied()
            .any(|point| point == FrameInjectionPoint::AfterSite(site))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum PostNode {
    Real(BlockId),
    DummyExit(BlockId),
    DummyEntry(BlockId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct DepPoint {
    block: BlockId,
    order: PointOrder,
    point: FrameInjectionPoint,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct PointOrder {
    site_rank: u32,
    phase_rank: u32,
    action_rank: u32,
}

struct PointOrderTable {
    entry_block: BlockId,
    inst_order: FxHashMap<InstId, u32>,
}

struct RootUseDepCtx<'a> {
    reachable_returns: &'a FxHashMap<BlockId, Vec<(BlockId, InstId)>>,
    rooted: &'a FxHashSet<ValueId>,
    order: &'a PointOrderTable,
}

pub(crate) fn compute_lazy_frame_plan(
    function: &Function,
    alloc: &dyn Allocator,
    mem_plan: &FuncMemPlan,
    isa: &Evm,
) -> Option<LazyFramePlan> {
    if mem_plan.frame_size_words() == 0 {
        return None;
    }

    function.layout.entry_block()?;

    let mut cfg = ControlFlowGraph::default();
    cfg.compute(function);
    let dep_points = collect_dep_points(function, &cfg, alloc, mem_plan, isa)?;
    if dep_points.is_empty() {
        return None;
    }

    let mut dep_blocks: Vec<BlockId> = dep_points.iter().map(|point| point.block).collect();
    dep_blocks.sort_unstable_by_key(|block| block.as_u32());
    dep_blocks.dedup();

    let mut dom = DomTree::new();
    dom.compute(&cfg);
    let mut post_dom = PostDomTree::new();
    post_dom.compute(function);

    if dep_blocks
        .iter()
        .any(|&block| !dom.is_reachable(block) || !post_dom.is_reachable(block))
    {
        return None;
    }

    let entry_block = nearest_common_dominator(&dom, &dep_blocks)?;
    if !dep_blocks
        .iter()
        .all(|&block| dom.dominates(entry_block, block))
    {
        return None;
    }

    let enter = earliest_point_in_block(&dep_points, entry_block)?;
    let exits = match nearest_common_postdominator(&post_dom, &dep_blocks)? {
        PostNode::Real(exit_block) if dom.dominates(entry_block, exit_block) => {
            vec![latest_point_in_block_or_entry(&dep_points, exit_block)]
        }
        PostNode::DummyExit(_) => {
            let mut return_blocks: Vec<BlockId> = dep_points
                .iter()
                .filter_map(|point| match point.point {
                    FrameInjectionPoint::AfterSite(FrameSite::PreInst(inst))
                        if function.dfg.is_return(inst) =>
                    {
                        Some(point.block)
                    }
                    _ => None,
                })
                .collect();
            return_blocks.sort_unstable_by_key(|block| block.as_u32());
            return_blocks.dedup();
            if return_blocks.is_empty()
                || return_blocks
                    .iter()
                    .any(|&block| !dom.dominates(entry_block, block))
            {
                return None;
            }
            return return_blocks
                .into_iter()
                .map(|block| latest_point_in_block(&dep_points, block))
                .collect::<Option<Vec<_>>>()
                .map(|exits| LazyFramePlan { enter, exits });
        }
        PostNode::Real(_) | PostNode::DummyEntry(_) => return None,
    };

    if exits.contains(&enter) {
        return None;
    }

    Some(LazyFramePlan { enter, exits })
}

fn collect_dep_points(
    function: &Function,
    cfg: &ControlFlowGraph,
    alloc: &dyn Allocator,
    mem_plan: &FuncMemPlan,
    isa: &Evm,
) -> Option<Vec<DepPoint>> {
    let rooted = compute_rooted_frame_values(function, mem_plan, isa);
    let reachable_returns = compute_reachable_returns(function, cfg);
    let order = PointOrderTable::new(function)?;
    let root_use = RootUseDepCtx {
        reachable_returns: &reachable_returns,
        rooted: &rooted,
        order: &order,
    };
    let mut out: Vec<DepPoint> = Vec::new();
    let mut seen: FxHashSet<FrameInjectionPoint> = FxHashSet::default();

    let entry_block = function.layout.entry_block()?;
    collect_action_dep_points(
        &mut out,
        &mut seen,
        &order,
        entry_block,
        FrameSite::EnterFunction,
        &alloc.enter_function(function),
        0,
    );

    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));
            let args = function.dfg.inst(inst).collect_values();

            match &data {
                EvmInstKind::Call(_) => {
                    let mut actions = alloc.read(inst, &args);
                    let cont_pos = actions
                        .iter()
                        .position(|a| matches!(a, Action::PushContinuationOffset))?;
                    let suffix: Vec<Action> = actions.drain(cont_pos + 1..).collect();
                    let marker = actions.remove(cont_pos);
                    if marker != Action::PushContinuationOffset {
                        return None;
                    }
                    let prefix_len = fold_stack_actions(&actions).len();
                    collect_action_dep_points(
                        &mut out,
                        &mut seen,
                        &order,
                        block,
                        FrameSite::PreInst(inst),
                        &actions,
                        0,
                    );
                    collect_action_dep_points(
                        &mut out,
                        &mut seen,
                        &order,
                        block,
                        FrameSite::PreInst(inst),
                        &suffix,
                        prefix_len,
                    );
                }
                EvmInstKind::BrTable(br) => {
                    for (case_val, _) in br.table().iter() {
                        let actions = alloc.read(inst, &[*br.scrutinee(), *case_val]);
                        if fold_stack_actions(&actions).iter().any(|action| {
                            matches!(
                                action,
                                Action::MemLoadFrameSlot(_) | Action::MemStoreFrameSlot(_)
                            )
                        }) {
                            return None;
                        }
                    }
                }
                _ => collect_action_dep_points(
                    &mut out,
                    &mut seen,
                    &order,
                    block,
                    FrameSite::PreInst(inst),
                    &alloc.read(inst, &args),
                    0,
                ),
            }

            if matches!(data, EvmInstKind::Alloca(_))
                && matches!(
                    mem_plan.alloca_loc.get(&inst).copied(),
                    Some(ObjLoc::StableFrame(_))
                )
            {
                push_dep_point(
                    &mut out,
                    &mut seen,
                    &order,
                    block,
                    FrameInjectionPoint::BeforeSite(FrameSite::Inst(inst)),
                );
            }

            collect_root_use_dep_points(
                function, &root_use, block, inst, &data, &mut out, &mut seen,
            );

            collect_action_dep_points(
                &mut out,
                &mut seen,
                &order,
                block,
                FrameSite::PostInst(inst),
                &alloc.write(inst, function.dfg.inst_results(inst)),
                0,
            );
        }
    }

    Some(out)
}

fn compute_rooted_frame_values(
    function: &Function,
    mem_plan: &FuncMemPlan,
    isa: &Evm,
) -> FxHashSet<ValueId> {
    let mut rooted: FxHashSet<ValueId> = FxHashSet::default();
    for (&inst, &loc) in &mem_plan.alloca_loc {
        if matches!(loc, ObjLoc::StableFrame(_))
            && let Some(result) = function.dfg.inst_result(inst)
        {
            rooted.insert(result);
        }
    }

    let mut changed = true;
    while changed {
        changed = false;
        for block in function.layout.iter_block() {
            for inst in function.layout.iter_inst(block) {
                let newly_rooted = if function.dfg.is_phi(inst) {
                    let phi = function.dfg.cast_phi(inst).expect("phi downcast failed");
                    phi.args().iter().any(|(value, _)| rooted.contains(value))
                } else {
                    let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));
                    match data {
                        EvmInstKind::Bitcast(bitcast) => rooted.contains(bitcast.from()),
                        EvmInstKind::IntToPtr(int_to_ptr) => {
                            rooted.contains(int_to_ptr.from())
                                && scalar_bit_width(
                                    function.dfg.value_ty(*int_to_ptr.from()),
                                    &function.dfg.ctx,
                                ) == Some(256)
                        }
                        EvmInstKind::PtrToInt(ptr_to_int) => {
                            rooted.contains(ptr_to_int.from())
                                && scalar_bit_width(*ptr_to_int.ty(), &function.dfg.ctx)
                                    == Some(256)
                        }
                        EvmInstKind::Gep(gep) => gep
                            .values()
                            .first()
                            .is_some_and(|value| rooted.contains(value)),
                        _ => false,
                    }
                };

                if newly_rooted {
                    for &result in function.dfg.inst_results(inst) {
                        changed |= rooted.insert(result);
                    }
                }
            }
        }
    }

    rooted
}

fn collect_root_use_dep_points(
    function: &Function,
    root_use: &RootUseDepCtx<'_>,
    block: BlockId,
    inst: InstId,
    data: &EvmInstKind,
    out: &mut Vec<DepPoint>,
    seen: &mut FxHashSet<FrameInjectionPoint>,
) {
    let operands = function.dfg.inst(inst).collect_values();
    let rooted_operands: FxHashSet<ValueId> = operands
        .into_iter()
        .filter(|value| root_use.rooted.contains(value))
        .collect();
    if rooted_operands.is_empty() {
        return;
    }

    if function.dfg.is_phi(inst)
        || is_alias_preserving_root_use(function, inst, data, &rooted_operands)
    {
        return;
    }

    if function.dfg.is_return(inst) {
        push_dep_point(
            out,
            seen,
            root_use.order,
            block,
            FrameInjectionPoint::AfterSite(FrameSite::PreInst(inst)),
        );
        return;
    }

    push_dep_point(
        out,
        seen,
        root_use.order,
        block,
        FrameInjectionPoint::AfterSite(FrameSite::PostInst(inst)),
    );

    if is_escape_like_root_use(function, inst, data, &rooted_operands) {
        for &(ret_block, ret_inst) in root_use.reachable_returns.get(&block).into_iter().flatten() {
            push_dep_point(
                out,
                seen,
                root_use.order,
                ret_block,
                FrameInjectionPoint::AfterSite(FrameSite::PreInst(ret_inst)),
            );
        }
    }
}

fn is_alias_preserving_root_use(
    function: &Function,
    inst: InstId,
    data: &EvmInstKind,
    rooted_operands: &FxHashSet<ValueId>,
) -> bool {
    if function.dfg.is_phi(inst) {
        return true;
    }
    match data {
        EvmInstKind::Bitcast(_) | EvmInstKind::IntToPtr(_) | EvmInstKind::PtrToInt(_) => true,
        EvmInstKind::Gep(gep) => gep
            .values()
            .first()
            .is_some_and(|value| rooted_operands.contains(value)),
        _ => false,
    }
}

fn is_escape_like_root_use(
    function: &Function,
    inst: InstId,
    data: &EvmInstKind,
    rooted_operands: &FxHashSet<ValueId>,
) -> bool {
    if function.dfg.is_return(inst) {
        return true;
    }

    match data {
        EvmInstKind::Call(call) => call
            .args()
            .iter()
            .any(|value| rooted_operands.contains(value)),
        EvmInstKind::Mstore(mstore) => rooted_operands.contains(mstore.value()),
        EvmInstKind::EvmMstore8(mstore8) => rooted_operands.contains(mstore8.val()),
        EvmInstKind::EvmSstore(sstore) => rooted_operands.contains(sstore.val()),
        EvmInstKind::EvmTstore(tstore) => rooted_operands.contains(tstore.val()),
        _ => function.dfg.inst(inst).side_effect() == SideEffect::Write,
    }
}

fn compute_reachable_returns(
    function: &Function,
    cfg: &ControlFlowGraph,
) -> FxHashMap<BlockId, Vec<(BlockId, InstId)>> {
    let mut out: FxHashMap<BlockId, Vec<(BlockId, InstId)>> = FxHashMap::default();
    for block in function.layout.iter_block() {
        let mut seen: FxHashSet<BlockId> = FxHashSet::default();
        let mut worklist = vec![block];
        let mut returns = Vec::new();
        while let Some(cur) = worklist.pop() {
            if !seen.insert(cur) {
                continue;
            }
            if let Some(term) = function.layout.last_inst_of(cur)
                && function.dfg.is_return(term)
            {
                returns.push((cur, term));
                continue;
            }
            for succ in cfg.succs_of(cur) {
                worklist.push(*succ);
            }
        }
        returns
            .sort_unstable_by_key(|(ret_block, ret_inst)| (ret_block.as_u32(), ret_inst.as_u32()));
        out.insert(block, returns);
    }
    out
}

fn collect_action_dep_points(
    out: &mut Vec<DepPoint>,
    seen: &mut FxHashSet<FrameInjectionPoint>,
    order: &PointOrderTable,
    block: BlockId,
    site: FrameSite,
    actions: &[Action],
    action_index_offset: usize,
) {
    let folded = fold_stack_actions(actions);
    for (index, action) in folded.iter().enumerate() {
        if matches!(
            action,
            Action::MemLoadFrameSlot(_) | Action::MemStoreFrameSlot(_)
        ) {
            push_dep_point(
                out,
                seen,
                order,
                block,
                FrameInjectionPoint::BeforeAction {
                    site,
                    action_index: action_index_offset
                        .checked_add(index)
                        .expect("frame action index overflow"),
                },
            );
        }
    }
}

fn push_dep_point(
    out: &mut Vec<DepPoint>,
    seen: &mut FxHashSet<FrameInjectionPoint>,
    order: &PointOrderTable,
    block: BlockId,
    point: FrameInjectionPoint,
) {
    if !seen.insert(point) {
        return;
    }
    out.push(DepPoint {
        block,
        order: order.key(block, point),
        point,
    });
}

fn earliest_point_in_block(points: &[DepPoint], block: BlockId) -> Option<FrameInjectionPoint> {
    points
        .iter()
        .filter(|point| point.block == block)
        .min_by_key(|point| point.order)
        .map(|point| point.point)
}

fn latest_point_in_block(points: &[DepPoint], block: BlockId) -> Option<FrameInjectionPoint> {
    points
        .iter()
        .filter(|point| point.block == block)
        .max_by_key(|point| point.order)
        .map(|point| point.point)
}

fn latest_point_in_block_or_entry(points: &[DepPoint], block: BlockId) -> FrameInjectionPoint {
    latest_point_in_block(points, block).unwrap_or(FrameInjectionPoint::BeforeSite(
        FrameSite::BlockEntry(block),
    ))
}

impl PointOrderTable {
    fn new(function: &Function) -> Option<Self> {
        let entry_block = function.layout.entry_block()?;
        let mut inst_order = FxHashMap::default();
        for block in function.layout.iter_block() {
            for (index, inst) in function.layout.iter_inst(block).enumerate() {
                inst_order.insert(
                    inst,
                    u32::try_from(index).expect("instruction order overflow"),
                );
            }
        }
        Some(Self {
            entry_block,
            inst_order,
        })
    }

    fn key(&self, block: BlockId, point: FrameInjectionPoint) -> PointOrder {
        let (site, phase_rank, action_rank) = match point {
            FrameInjectionPoint::BeforeSite(site) => (site, 0, 0),
            FrameInjectionPoint::BeforeAction { site, action_index } => (
                site,
                1,
                u32::try_from(action_index)
                    .expect("action index overflow")
                    .checked_mul(2)
                    .expect("action index overflow"),
            ),
            FrameInjectionPoint::AfterAction { site, action_index } => (
                site,
                1,
                u32::try_from(action_index)
                    .expect("action index overflow")
                    .checked_mul(2)
                    .and_then(|rank| rank.checked_add(1))
                    .expect("action index overflow"),
            ),
            FrameInjectionPoint::AfterSite(site) => (site, 2, 0),
        };

        PointOrder {
            site_rank: self.site_rank(block, site),
            phase_rank,
            action_rank,
        }
    }

    fn site_rank(&self, block: BlockId, site: FrameSite) -> u32 {
        let site_base = if block == self.entry_block { 1 } else { 0 };
        match site {
            FrameSite::EnterFunction => {
                debug_assert_eq!(
                    block, self.entry_block,
                    "enter_function site on non-entry block"
                );
                0
            }
            FrameSite::BlockEntry(site_block) => {
                debug_assert_eq!(block, site_block, "block-entry site on wrong block");
                site_base
            }
            FrameSite::PreInst(inst) => self.inst_site_rank(inst, site_base, 0),
            FrameSite::Inst(inst) => self.inst_site_rank(inst, site_base, 1),
            FrameSite::PostInst(inst) => self.inst_site_rank(inst, site_base, 2),
        }
    }

    fn inst_site_rank(&self, inst: InstId, site_base: u32, offset: u32) -> u32 {
        let inst_rank = self
            .inst_order
            .get(&inst)
            .copied()
            .expect("missing instruction order");
        site_base
            .checked_add(1)
            .and_then(|rank| {
                rank.checked_add(inst_rank.checked_mul(3).expect("site rank overflow"))
            })
            .and_then(|rank| rank.checked_add(offset))
            .expect("site rank overflow")
    }
}

fn nearest_common_dominator(dom: &DomTree, blocks: &[BlockId]) -> Option<BlockId> {
    let &first = blocks.first()?;
    dom_chain(dom, first)
        .into_iter()
        .find(|&cand| blocks.iter().all(|&block| dom.dominates(cand, block)))
}

fn dom_chain(dom: &DomTree, mut block: BlockId) -> Vec<BlockId> {
    let mut out = vec![block];
    while let Some(idom) = dom.idom_of(block) {
        out.push(idom);
        block = idom;
    }
    out
}

fn nearest_common_postdominator(post_dom: &PostDomTree, blocks: &[BlockId]) -> Option<PostNode> {
    let &first = blocks.first()?;
    let first_chain = postdom_chain(post_dom, first);
    let other_chains: Vec<FxHashSet<PostNode>> = blocks
        .iter()
        .copied()
        .skip(1)
        .map(|block| postdom_chain(post_dom, block).into_iter().collect())
        .collect();
    first_chain
        .into_iter()
        .find(|cand| other_chains.iter().all(|chain| chain.contains(cand)))
}

fn postdom_chain(post_dom: &PostDomTree, block: BlockId) -> Vec<PostNode> {
    let mut out = vec![PostNode::Real(block)];
    let mut cur = block;
    while let Some(idom) = post_dom.idom_of(cur) {
        let node = match idom {
            PDTIdom::Real(next) => {
                cur = next;
                PostNode::Real(next)
            }
            PDTIdom::DummyExit(dummy) => PostNode::DummyExit(dummy),
            PDTIdom::DummyEntry(dummy) => PostNode::DummyEntry(dummy),
        };
        out.push(node);
        if !matches!(node, PostNode::Real(_)) {
            break;
        }
    }
    out
}

fn scalar_bit_width(ty: Type, module: &sonatina_ir::module::ModuleCtx) -> Option<u16> {
    let bits = match ty {
        Type::I1 => 1,
        Type::I8 => 8,
        Type::I16 => 16,
        Type::I32 => 32,
        Type::I64 => 64,
        Type::I128 => 128,
        Type::I256 => 256,
        Type::Unit => 0,
        Type::Compound(_) if ty.is_pointer(module) => 256,
        Type::Compound(_) => return None,
    };
    Some(bits)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        critical_edge::CriticalEdgeSplitter,
        isa::evm::{
            FinalAlloc,
            memory_plan::{ArenaCostModel, FuncAnalysis, compute_program_memory_plan},
            ptr_escape::compute_ptr_escape_summaries,
        },
        liveness::{InstLiveness, Liveness},
        stackalloc::StackifyBuilder,
    };
    use rustc_hash::FxHashMap;
    use sonatina_parser::parse_module;
    use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

    struct LazyPlanCtx {
        module: sonatina_ir::Module,
        func: sonatina_ir::module::FuncRef,
        plan: LazyFramePlan,
    }

    fn lazy_plan_from_src(src: &str, func_name: &str, cost_model: &ArenaCostModel) -> LazyPlanCtx {
        let parsed = parse_module(src).expect("module parses");
        let funcs = parsed.module.funcs();
        let isa = Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        });
        let ptr_escape = compute_ptr_escape_summaries(&parsed.module, &funcs, &isa);

        let mut analyses: FxHashMap<sonatina_ir::module::FuncRef, FuncAnalysis> =
            FxHashMap::default();
        for &func in &funcs {
            parsed.module.func_store.modify(func, |function| {
                let mut cfg = ControlFlowGraph::default();
                cfg.compute(function);
                let mut splitter = CriticalEdgeSplitter::new();
                splitter.run(function, &mut cfg);

                let mut liveness = Liveness::new();
                liveness.compute(function, &cfg);

                let mut inst_liveness = InstLiveness::new();
                inst_liveness.compute(function, &cfg, &liveness);

                let mut dom = DomTree::new();
                dom.compute(&cfg);

                analyses.insert(
                    func,
                    FuncAnalysis {
                        alloc: StackifyBuilder::new(function, &cfg, &dom, &liveness, 16).compute(),
                        inst_liveness,
                        block_order: dom.rpo().to_vec(),
                    },
                );
            });
        }

        let plan = compute_program_memory_plan(
            &parsed.module,
            &funcs,
            &analyses,
            &ptr_escape,
            &isa,
            cost_model,
        );
        let func = funcs
            .into_iter()
            .find(|&func| {
                parsed
                    .module
                    .ctx
                    .func_sig(func, |sig| sig.name() == func_name)
            })
            .expect("function exists");
        let analysis = analyses.remove(&func).expect("missing analysis");
        let mem_plan = plan
            .funcs
            .get(&func)
            .expect("missing function plan")
            .clone();
        let alloc = FinalAlloc::new(analysis.alloc, mem_plan.clone());
        let lazy_plan = parsed.module.func_store.view(func, |function| {
            compute_lazy_frame_plan(function, &alloc, &mem_plan, &isa)
        });

        LazyPlanCtx {
            module: parsed.module,
            func,
            plan: lazy_plan.expect("expected lazy frame plan"),
        }
    }

    #[test]
    fn visible_recursive_alloca_keeps_frame_live_until_return() {
        let ctx = lazy_plan_from_src(
            r#"
target = "evm-ethereum-osaka"

func public %f(v0.i1, v1.*i256) -> i256 {
block0:
    br v0 block1 block2;

block1:
    return 0.i256;

block2:
    v2.*i256 = alloca i256;
    v3.i256 = call %f 1.i1 v2;
    return v3;
}
"#,
            "f",
            &ArenaCostModel::default(),
        );

        let (alloca_inst, ret_inst) = ctx.module.func_store.view(ctx.func, |function| {
            let mut alloca_inst = None;
            let mut ret_inst = None;
            for block in function.layout.iter_block() {
                for inst in function.layout.iter_inst(block) {
                    if function.dfg.is_return(inst) {
                        ret_inst = Some(inst);
                    } else if matches!(
                        Evm::new(function.dfg.ctx.triple)
                            .inst_set()
                            .resolve_inst(function.dfg.inst(inst)),
                        EvmInstKind::Alloca(_)
                    ) {
                        alloca_inst = Some(inst);
                    }
                }
            }
            (alloca_inst.expect("alloca"), ret_inst.expect("return"))
        });

        assert!(!ctx.plan.enter_before_site(FrameSite::EnterFunction));
        assert!(ctx.plan.enter_before_site(FrameSite::Inst(alloca_inst)));
        assert!(ctx.plan.exit_after_site(FrameSite::PreInst(ret_inst)));
    }

    #[test]
    fn shadow_only_recursive_frame_skips_function_entry() {
        let ctx = lazy_plan_from_src(
            r#"
target = "evm-ethereum-osaka"

func public %f(v0.i1) -> i256 {
block0:
    br v0 block1 block2;

block1:
    return 0.i256;

block2:
    v1.*i256 = alloca i256;
    mstore v1 1.i256 i256;
    v2.i256 = call %f 0.i1;
    v3.i256 = mload v1 i256;
    return v3;
}
"#,
            "f",
            &ArenaCostModel {
                w_save: 0,
                w_code: 0,
                ..ArenaCostModel::default()
            },
        );

        assert!(!ctx.plan.enter_before_site(FrameSite::EnterFunction));
    }

    #[test]
    fn visible_escape_beats_later_local_frame_touches_in_same_block() {
        let ctx = lazy_plan_from_src(
            r#"
target = "evm-ethereum-osaka"

func public %f(v0.i1, v1.*i256) -> i256 {
block0:
    br v0 block1 block2;

block1:
    return 0.i256;

block2:
    v2.*i256 = alloca i256;
    v3.i256 = call %f 1.i1 v2;
    mstore v2 7.i256 i256;
    v4.i256 = mload v2 i256;
    v5.i256 = add v3 v4;
    return v5;
}
"#,
            "f",
            &ArenaCostModel::default(),
        );

        let ret_inst = ctx.module.func_store.view(ctx.func, |function| {
            let mut ret_inst = None;
            for block in function.layout.iter_block() {
                for inst in function.layout.iter_inst(block) {
                    if function.dfg.is_return(inst) {
                        ret_inst = Some(inst);
                    }
                }
            }
            ret_inst.expect("return")
        });

        assert!(ctx.plan.exit_after_site(FrameSite::PreInst(ret_inst)));
    }
}
