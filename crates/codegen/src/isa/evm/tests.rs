use super::*;
use crate::{
    analysis::func_behavior,
    critical_edge::CriticalEdgeSplitter,
    domtree::DomTree,
    liveness::{InstLiveness, Liveness},
    machinst::{
        lower::{LoweredFunction, SectionWorkModule},
        vcode::{Label, VCode, VCodeFixup},
    },
    object::{CompileOptions, SymbolId, link::link_section},
    optim::pipeline::Pipeline,
    stackalloc::{Action, Actions, Allocator, StackifyAlloc, StackifyBuilder},
};
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    BlockId, Function, Immediate, InstId, InstSetBase, InstSetExt, Module, ValueId,
    cfg::ControlFlowGraph, inst::evm::inst_set::EvmInstKind, ir_writer::FuncWriter, isa::Isa,
    module::ModuleCtx, object::SectionName,
};
use sonatina_parser::parse_module;
use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

use self::{
    dyn_sp::DynSpInitKind,
    emit::{
        FinalAlloc, materialize_jumpdests, prune_redundant_opcode_sequences,
        rewrite_evm_local_fallthrough_layout,
    },
    memory_plan::{
        ArenaCostModel, BackendSpillReserve, ProgramMemoryPlan,
        compute_abs_clobber_words_with_extra, compute_semantic_program_memory_plan,
    },
    prepare::compute_return_escape_caller_clamp_words,
};

struct PlanTestCtx {
    module: sonatina_ir::Module,
    funcs: Vec<FuncRef>,
    names: FxHashMap<String, FuncRef>,
    plan: ProgramMemoryPlan,
}

fn plan_test_ctx_from_src(src: &str) -> PlanTestCtx {
    let parsed = parse_module(src).expect("module parses");
    let funcs = parsed.module.funcs();
    let isa = Evm::new(TargetTriple {
        architecture: Architecture::Evm,
        vendor: Vendor::Ethereum,
        operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
    });
    let ptr_escape = compute_ptr_escape_summaries(&parsed.module, &funcs, &isa);
    let backend = EvmBackend::new(isa);

    let mut analyses: FxHashMap<FuncRef, memory_plan::FuncPreAnalysis> = FxHashMap::default();
    for &func in &funcs {
        parsed.module.func_store.modify(func, |function| {
            analyses.insert(
                func,
                compute_test_pre_analysis(function, &parsed.module.ctx, &backend, &ptr_escape),
            );
        });
    }

    let plan = compute_semantic_program_memory_plan(
        &parsed.module,
        &crate::module_analysis::CallGraphSchedule::compute(&parsed.module, &funcs),
        &analyses,
        &ptr_escape,
        &isa,
        &ArenaCostModel::default(),
    );

    let mut names: FxHashMap<String, FuncRef> = FxHashMap::default();
    for &func in &funcs {
        let name = parsed
            .module
            .ctx
            .func_sig(func, |sig| sig.name().to_string());
        names.insert(name, func);
    }

    PlanTestCtx {
        module: parsed.module,
        funcs,
        names,
        plan,
    }
}

fn compute_test_pre_analysis(
    function: &mut Function,
    module: &ModuleCtx,
    backend: &EvmBackend,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
) -> memory_plan::FuncPreAnalysis {
    let mut cfg = ControlFlowGraph::new();
    cfg.compute(function);

    CriticalEdgeSplitter::new().run(function, &mut cfg);

    let mut dom = DomTree::new();
    dom.compute(&cfg);

    let mut liveness = Liveness::new();
    liveness.compute(function, &cfg);

    let mut inst_liveness = InstLiveness::new();
    inst_liveness.compute(function, &cfg, &liveness);

    let prov = crate::isa::evm::ptr_provenance::compute_provenance(
        function,
        module,
        &backend.isa,
        |callee| PtrEscapeSummary::get_or_conservative(ptr_escape, module, callee),
    );
    let prov_conservative_value = crate::isa::evm::ptr_provenance::compute_value_provenance(
        function,
        module,
        &backend.isa,
        |callee| PtrEscapeSummary::conservative_unknown_ctx(module, callee),
    );
    memory_plan::FuncPreAnalysis {
        block_order: dom.rpo().to_owned(),
        value_aliases: backend.compute_high_evm_value_aliases(function, module),
        cfg,
        inst_liveness,
        prov,
        prov_conservative_value,
    }
}

fn compute_test_stackify_alloc(function: &mut Function) -> StackifyAlloc {
    let mut cfg = ControlFlowGraph::new();
    cfg.compute(function);

    CriticalEdgeSplitter::new().run(function, &mut cfg);

    let mut liveness = Liveness::new();
    liveness.compute(function, &cfg);

    let mut dom = DomTree::new();
    dom.compute(&cfg);

    StackifyBuilder::new(function, &cfg, &dom, &liveness, 16).compute()
}

fn find_func(module: &Module, name: &str) -> FuncRef {
    module
        .funcs()
        .into_iter()
        .find(|&func| module.ctx.func_sig(func, |sig| sig.name() == name))
        .expect("function exists")
}

fn work_module_with_entry(
    module: &Module,
    _funcs: &[FuncRef],
    entry: FuncRef,
) -> SectionWorkModule {
    SectionWorkModule::from_roots(module, entry, &[], &[])
}

fn work_module(module: &Module, funcs: &[FuncRef]) -> SectionWorkModule {
    work_module_with_entry(module, funcs, funcs[0])
}

fn test_backend() -> EvmBackend {
    EvmBackend::new(Evm::new(TargetTriple {
        architecture: Architecture::Evm,
        vendor: Vendor::Ethereum,
        operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
    }))
}

fn first_memory_op(lowered: &LoweredFunction<OpCode>) -> Option<u8> {
    lowered
        .block_order
        .iter()
        .flat_map(|&block| lowered.vcode.block_insns(block))
        .map(|inst| lowered.vcode.insts[inst] as u8)
        .find(|op| *op == OpCode::MLOAD as u8 || *op == OpCode::MSTORE as u8)
}

fn lowered_bytes(lowered: &LoweredFunction<OpCode>) -> Vec<u8> {
    let mut bytes = Vec::new();
    for &block in &lowered.block_order {
        for inst in lowered.vcode.block_insns(block) {
            bytes.push(lowered.vcode.insts[inst] as u8);
            if let Some((_, imm)) = lowered.vcode.inst_imm_bytes.get(inst) {
                bytes.extend_from_slice(imm);
            }
        }
    }
    bytes
}

fn contains_subsequence(bytes: &[u8], needle: &[u8]) -> bool {
    bytes.windows(needle.len()).any(|window| window == needle)
}

fn rewrite_local_fallthrough_order_from_src(
    src: &str,
    func_name: &str,
    block_order: &[u32],
) -> Vec<u32> {
    rewrite_local_fallthrough_order_from_src_with_profile(src, func_name, block_order, true)
}

fn rewrite_local_fallthrough_order_from_src_with_profile(
    src: &str,
    func_name: &str,
    block_order: &[u32],
    prefer_speed: bool,
) -> Vec<u32> {
    let parsed = parse_module(src).expect("module parses");
    let func = find_func(&parsed.module, func_name);
    let block_order: Vec<_> = block_order.iter().copied().map(BlockId).collect();

    parsed.module.func_store.view(func, |function| {
        rewrite_evm_local_fallthrough_layout(
            function,
            &FxHashMap::default(),
            block_order,
            prefer_speed,
        )
        .into_iter()
        .map(|block| block.0)
        .collect()
    })
}

const HOT_LOOP_EXIT_LAYOUT_SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %main(v0.i256) -> i256 {
block0:
    jump block3;

block3:
    v1.i256 = phi (0.i256 block0) (v2 block4);
    v3.i1 = gt v1 v0;
    br v3 block1 block4;

block4:
    v2.i256 = add v1 1.i256;
    jump block3;

block1:
    return v1;
}
"#;

const HOT_LOOP_LT_SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %main(v0.i256) -> i256 {
block0:
    jump block3;

block3:
    v1.i256 = phi (0.i256 block0) (v2 block4);
    v3.i1 = lt v1 v0;
    br v3 block4 block1;

block4:
    v2.i256 = add v1 1.i256;
    jump block3;

block1:
    return v1;
}
"#;

const HOT_LOOP_LT_MULTI_BLOCK_BODY_SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %main(v0.i1, v1.i256) -> i256 {
block0:
    jump block3;

block3:
    v2.i256 = phi (0.i256 block0) (v5 block7);
    v3.i1 = lt v2 v1;
    br v3 block4 block5;

block4:
    br v0 block6 block7;

block6:
    v4.i256 = add v2 2.i256;
    jump block7;

block7:
    v5.i256 = phi (v2 block4) (v4 block6);
    v6.i256 = add v5 1.i256;
    jump block3;

block5:
    return v2;
}
"#;

const HOT_LOOP_MULTI_PRED_BODY_SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %main(v0.i1, v1.i256) -> i256 {
block0:
    br v0 block2 block3;

block2:
    jump block4;

block3:
    v4.i256 = phi (0.i256 block0) (v5 block4);
    v6.i1 = gt v4 v1;
    br v6 block1 block4;

block4:
    v5.i256 = add v4 1.i256;
    jump block3;

block1:
    return v4;
}
"#;

const HOT_LOOP_LATCH_SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %main(v0.i256) -> i256 {
block0:
    jump block3;

block3:
    v1.i256 = phi (0.i256 block0) (v2 block5);
    v3.i1 = gt v1 v0;
    br v3 block1 block4;

block4:
    v4.i256 = add v1 1.i256;
    jump block5;

block5:
    v2.i256 = add v4 0.i256;
    jump block3;

block1:
    return v1;
}
"#;

const HOT_LOOP_NONTERMINAL_EXIT_SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %main(v0.i256) -> i256 {
block0:
    jump block3;

block3:
    v1.i256 = phi (0.i256 block0) (v2 block4);
    v3.i1 = gt v1 v0;
    br v3 block1 block4;

block4:
    v2.i256 = add v1 1.i256;
    jump block3;

block1:
    jump block2;

block2:
    return v1;
}
"#;

const HOT_LOOP_NONADJACENT_WINDOW_SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %main(v0.i1, v1.i256) -> i256 {
block0:
    br v0 block2 block3;

block2:
    return 7.i256;

block3:
    v4.i256 = phi (0.i256 block0) (v5 block4);
    v6.i1 = gt v4 v1;
    br v6 block1 block4;

block4:
    v5.i256 = add v4 1.i256;
    jump block3;

block1:
    return v4;
}
"#;

const NON_LOOP_BRANCH_SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %main(v0.i1) -> i256 {
block0:
    br v0 block1 block2;

block1:
    return 1.i256;

block2:
    return 2.i256;
}
"#;

const NON_LOOP_DIAMOND_SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %main(v0.i1, v1.i256) -> i256 {
block0:
    br v0 block1 block2;

block1:
    v2.i256 = add v1 1.i256;
    jump block3;

block2:
    v3.i256 = add v1 2.i256;
    jump block3;

block3:
    v4.i256 = phi (v2 block1) (v3 block2);
    return v4;
}
"#;

#[test]
fn local_fallthrough_layout_rewrites_hot_loop_header_window() {
    let order =
        rewrite_local_fallthrough_order_from_src(HOT_LOOP_EXIT_LAYOUT_SRC, "main", &[0, 3, 1, 4]);

    assert_eq!(order, vec![0, 3, 4, 1]);
}

#[test]
fn local_fallthrough_layout_skips_lt_loop_headers() {
    let order = rewrite_local_fallthrough_order_from_src(HOT_LOOP_LT_SRC, "main", &[0, 3, 1, 4]);

    assert_eq!(order, vec![0, 3, 1, 4]);
}

#[test]
fn local_fallthrough_layout_rewrites_lt_loop_body_fallthrough() {
    let order = rewrite_local_fallthrough_order_from_src(HOT_LOOP_LT_SRC, "main", &[0, 3, 4, 1]);

    assert_eq!(order, vec![0, 3, 1, 4]);
}

#[test]
fn local_fallthrough_layout_rewrites_lt_multi_block_loop_body() {
    let order = rewrite_local_fallthrough_order_from_src(
        HOT_LOOP_LT_MULTI_BLOCK_BODY_SRC,
        "main",
        &[0, 3, 4, 6, 7, 5],
    );

    assert_eq!(order, vec![0, 3, 5, 4, 6, 7]);
}

#[test]
fn local_fallthrough_layout_skips_multi_pred_bodies() {
    let order = rewrite_local_fallthrough_order_from_src(
        HOT_LOOP_MULTI_PRED_BODY_SRC,
        "main",
        &[0, 2, 3, 1, 4],
    );

    assert_eq!(order, vec![0, 2, 3, 1, 4]);
}

#[test]
fn local_fallthrough_layout_skips_non_backedge_body_blocks() {
    let order =
        rewrite_local_fallthrough_order_from_src(HOT_LOOP_LATCH_SRC, "main", &[0, 3, 1, 4, 5]);

    assert_eq!(order, vec![0, 3, 1, 4, 5]);
}

#[test]
fn local_fallthrough_layout_rewrites_nonterminal_loop_exits() {
    let order = rewrite_local_fallthrough_order_from_src(
        HOT_LOOP_NONTERMINAL_EXIT_SRC,
        "main",
        &[0, 3, 1, 4, 2],
    );

    assert_eq!(order, vec![0, 3, 4, 1, 2]);
}

#[test]
fn local_fallthrough_layout_skips_nonadjacent_windows() {
    let order = rewrite_local_fallthrough_order_from_src(
        HOT_LOOP_NONADJACENT_WINDOW_SRC,
        "main",
        &[0, 3, 2, 1, 4],
    );

    assert_eq!(order, vec![0, 3, 2, 1, 4]);
}

#[test]
fn local_fallthrough_layout_skips_already_ideal_order() {
    let order =
        rewrite_local_fallthrough_order_from_src(HOT_LOOP_EXIT_LAYOUT_SRC, "main", &[0, 3, 4, 1]);

    assert_eq!(order, vec![0, 3, 4, 1]);
}

#[test]
fn local_fallthrough_layout_skips_non_loop_branches() {
    let order = rewrite_local_fallthrough_order_from_src(NON_LOOP_BRANCH_SRC, "main", &[0, 1, 2]);

    assert_eq!(order, vec![0, 1, 2]);
}

#[test]
fn local_fallthrough_layout_rewrites_non_loop_diamond() {
    let order = rewrite_local_fallthrough_order_from_src_with_profile(
        NON_LOOP_DIAMOND_SRC,
        "main",
        &[0, 1, 2, 3],
        false,
    );

    assert_eq!(order, vec![0, 2, 1, 3]);
}

#[test]
fn local_fallthrough_layout_skips_non_loop_diamond_for_speed() {
    let order =
        rewrite_local_fallthrough_order_from_src(NON_LOOP_DIAMOND_SRC, "main", &[0, 1, 2, 3]);

    assert_eq!(order, vec![0, 1, 2, 3]);
}

#[test]
fn fold_stack_actions_cancels_swap_self_inverse() {
    let actions = [Action::StackSwap(7), Action::StackSwap(7)];
    let folded = fold_stack_actions(&actions);
    assert!(folded.is_empty());
}

#[test]
fn fold_stack_actions_keeps_nonmatching_dup_swap() {
    let actions = [Action::StackDup(3), Action::StackSwap(3)];
    let folded = fold_stack_actions(&actions);
    assert_eq!(folded.as_slice(), actions.as_slice());
}

#[test]
fn fold_stack_actions_keeps_push_swap1_pop_replacement() {
    let actions = [
        Action::Push(Immediate::I8(7)),
        Action::StackSwap(1),
        Action::Pop,
    ];
    let folded = fold_stack_actions(&actions);
    assert_eq!(folded.as_slice(), actions.as_slice());
}

#[test]
fn fold_stack_actions_cancels_double_push_swap_pop_shuffle_noop() {
    let actions = [
        Action::StackSwap(3),
        Action::Push(Immediate::I1(false)),
        Action::Push(Immediate::I1(true)),
        Action::StackSwap(1),
        Action::StackSwap(2),
        Action::StackSwap(1),
        Action::Pop,
        Action::StackSwap(1),
        Action::Pop,
        Action::StackSwap(4),
    ];
    let folded = fold_stack_actions(&actions);
    assert_eq!(
        folded.as_slice(),
        [Action::StackSwap(3), Action::StackSwap(4)].as_slice()
    );
}

#[test]
fn prune_keeps_push_swap1_pop_replacement() {
    let mut vcode = VCode::<OpCode>::default();
    let block = BlockId(0);

    let push = vcode.add_inst_to_block(OpCode::PUSH1, None, block);
    vcode.inst_imm_bytes.insert((push, smallvec![7u8]));
    vcode.add_inst_to_block(OpCode::SWAP1, None, block);
    vcode.add_inst_to_block(OpCode::POP, None, block);

    prune_redundant_opcode_sequences(&mut vcode, &[block]);

    let ops: Vec<_> = vcode
        .block_insns(block)
        .map(|inst| vcode.insts[inst] as u8)
        .collect();
    assert_eq!(
        ops,
        vec![OpCode::PUSH1 as u8, OpCode::SWAP1 as u8, OpCode::POP as u8]
    );
}

#[test]
fn prune_removes_double_push_swap_pop_shuffle_noop() {
    let mut vcode = VCode::<OpCode>::default();
    let block = BlockId(0);

    let push_false = vcode.add_inst_to_block(OpCode::PUSH1, None, block);
    vcode.inst_imm_bytes.insert((push_false, smallvec![0u8]));
    let push_true = vcode.add_inst_to_block(OpCode::PUSH1, None, block);
    vcode.inst_imm_bytes.insert((push_true, smallvec![1u8]));
    vcode.add_inst_to_block(OpCode::SWAP1, None, block);
    vcode.add_inst_to_block(OpCode::SWAP2, None, block);
    vcode.add_inst_to_block(OpCode::SWAP1, None, block);
    vcode.add_inst_to_block(OpCode::POP, None, block);
    vcode.add_inst_to_block(OpCode::SWAP1, None, block);
    vcode.add_inst_to_block(OpCode::POP, None, block);

    prune_redundant_opcode_sequences(&mut vcode, &[block]);

    assert_eq!(vcode.block_insns(block).count(), 0);
}

#[test]
fn prune_removes_two_inst_stack_noops() {
    for (first, imm) in [(OpCode::DUP1, None), (OpCode::PUSH1, Some(7u8))] {
        let mut vcode = VCode::<OpCode>::default();
        let block = BlockId(0);

        let inst = vcode.add_inst_to_block(first, None, block);
        if let Some(byte) = imm {
            vcode.inst_imm_bytes.insert((inst, smallvec![byte]));
        }
        vcode.add_inst_to_block(OpCode::POP, None, block);

        prune_redundant_opcode_sequences(&mut vcode, &[block]);

        assert_eq!(vcode.block_insns(block).count(), 0);
    }

    let mut vcode = VCode::<OpCode>::default();
    let block = BlockId(0);
    vcode.add_inst_to_block(OpCode::SWAP1, None, block);
    vcode.add_inst_to_block(OpCode::SWAP1, None, block);

    prune_redundant_opcode_sequences(&mut vcode, &[block]);

    assert_eq!(vcode.block_insns(block).count(), 0);
}

#[test]
fn recursive_entry_lowering_uses_lazy_frame() {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

func public %f(v0.i1, v1.i256) -> i256 {
block0:
    br v0 block1 block2;

block1:
    return 0.i256;

block2:
    v2.*i256 = alloca i256;
    mstore v2 v1 i256;
    v3.i256 = call %f 1.i1 v1;
    v4.i256 = mload v2 i256;
    v5.i256 = add v3 v4;
    return v5;
}
"#,
    )
    .unwrap();

    let f = find_func(&parsed.module, "f");
    let backend = test_backend();
    let prepared = backend
        .prepare_section(work_module_with_entry(&parsed.module, &[f], f))
        .expect("prepare should succeed");
    let function_plan = prepared.function_plan(f).expect("missing function plan");
    assert_eq!(
        function_plan.dyn_sp_plan.entry_init,
        Some(DynSpInitKind::Checked)
    );
    assert!(function_plan.dyn_sp_plan.entry_live_frame);
    assert!(function_plan.frame_summary.lowering.is_some());

    let lowered = backend
        .lower_function(&prepared, f)
        .expect("function lowers");
    let first_mem_op = first_memory_op(&lowered).expect("entry lowering should touch dyn_sp");

    assert_eq!(
        first_mem_op,
        OpCode::MLOAD as u8,
        "recursive lazy frame lowering must read dyn_sp before writing it"
    );
}

#[test]
fn nonrecursive_entry_lowering_skips_dyn_sp_init() {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

func public %entry() {
block0:
    evm_return 0.i8 0.i8;
}

object @Contract {
  section runtime {
    entry %entry;
  }
}
"#,
    )
    .unwrap();

    let entry = find_func(&parsed.module, "entry");
    let backend = test_backend();
    let prepared = backend
        .prepare_section(work_module_with_entry(&parsed.module, &[entry], entry))
        .expect("prepare should succeed");
    let function_plan = prepared
        .function_plan(entry)
        .expect("missing function plan");
    assert_eq!(function_plan.dyn_sp_plan.entry_init, None);
    assert!(function_plan.frame_summary.lowering.is_none());

    let lowered = backend
        .lower_function(&prepared, entry)
        .expect("function lowers");
    assert_eq!(
        first_memory_op(&lowered),
        None,
        "entry without dyn-sp init should not emit dyn-sp memory ops"
    );
}

#[test]
fn recursive_entry_without_live_frame_initializes_dyn_sp_directly() {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

func public %f(v0.i1) -> i256 {
block0:
    br v0 block1 block2;
 
block1:
    return 0.i256;
 
block2:
    v1.i256 = call %f 1.i1;
    v2.*i256 = alloca i256;
    mstore v2 5.i256 i256;
    v3.i256 = call %sink v2;
    v4.i256 = mload v2 i256;
    v5.i256 = add v1 v3;
    v6.i256 = add v5 v4;
    return v6;
}

func private %sink(v0.*i256) -> i256 {
block0:
    v1.i256 = mload v0 i256;
    return v1;
}

object @Contract {
  section runtime {
    entry %f;
  }
}
"#,
    )
    .unwrap();

    let f = find_func(&parsed.module, "f");
    let backend = test_backend();
    let prepared = backend
        .prepare_section(work_module_with_entry(&parsed.module, &[f], f))
        .expect("prepare should succeed");
    let function_plan = prepared.function_plan(f).expect("missing function plan");
    assert_eq!(
        function_plan.dyn_sp_plan.entry_init,
        Some(DynSpInitKind::Always)
    );
    assert!(!function_plan.dyn_sp_plan.entry_live_frame);
    assert!(function_plan.frame_summary.lowering.is_some());

    let lowered = backend
        .lower_function(&prepared, f)
        .expect("function lowers");
    let first_mem_op = first_memory_op(&lowered).expect("entry lowering should touch dyn_sp");
    assert_eq!(
        first_mem_op,
        OpCode::MSTORE as u8,
        "entry without live-frame reentry should initialize dyn_sp directly"
    );
}

#[test]
fn fixed_transient_malloc_keccak_lowers_to_machine_zero_buffer() {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i256) -> i256 {
block0:
    v1.*i8 = evm_malloc 32.i256;
    v2.*i256 = bitcast v1 *i256;
    mstore v2 v0 i256;
    v3.i256 = evm_keccak256 v1 32.i256;
    return v3;
}
"#,
    )
    .unwrap();

    let entry = find_func(&parsed.module, "entry");
    let backend = test_backend();
    let prepared = backend
        .prepare_section(work_module_with_entry(&parsed.module, &[entry], entry))
        .expect("prepare should succeed");

    let dumped = prepared.module().func_store.view(entry, |function| {
        FuncWriter::new(entry, function).dump_string()
    });
    assert!(
        dumped.contains("evm_mstore 0.i256"),
        "fixed transient store should use address zero in machine IR:\n{dumped}"
    );
    assert!(
        dumped.contains("evm_keccak256 0.i256 32.i256"),
        "fixed transient keccak should use address zero in machine IR:\n{dumped}"
    );
    assert!(
        !dumped.contains("evm_malloc") && !dumped.contains("bitcast"),
        "machine IR should not retain malloc/cast operations:\n{dumped}"
    );

    let lowered = backend
        .lower_function(&prepared, entry)
        .expect("entry lowers");
    let bytes = lowered_bytes(&lowered);
    assert!(
        contains_subsequence(
            &bytes,
            &[
                OpCode::PUSH0 as u8,
                OpCode::MSTORE as u8,
                OpCode::PUSH1 as u8,
                0x20,
                OpCode::PUSH0 as u8,
                OpCode::KECCAK256 as u8,
            ],
        ),
        "expected PUSH0/MSTORE/PUSH1 0x20/PUSH0/KECCAK256 sequence, got {bytes:?}"
    );
    assert!(
        !contains_subsequence(&bytes, &[OpCode::SWAP1 as u8, OpCode::DUP2 as u8]),
        "fixed zero buffer should not lower through SWAP1 DUP2: {bytes:?}"
    );
}

#[test]
fn fixed_transient_malloc_return_lowers_to_machine_zero_buffer() {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i256) {
block0:
    v1.*i8 = evm_malloc 32.i256;
    v2.*i256 = bitcast v1 *i256;
    mstore v2 v0 i256;
    evm_return v1 32.i256;
}
"#,
    )
    .unwrap();

    let entry = find_func(&parsed.module, "entry");
    let backend = test_backend();
    let prepared = backend
        .prepare_section(work_module_with_entry(&parsed.module, &[entry], entry))
        .expect("prepare should succeed");

    let dumped = prepared.module().func_store.view(entry, |function| {
        FuncWriter::new(entry, function).dump_string()
    });
    assert!(
        dumped.contains("evm_mstore 0.i256"),
        "fixed transient store should use address zero in machine IR:\n{dumped}"
    );
    assert!(
        dumped.contains("evm_return 0.i256 32.i256"),
        "fixed transient return should use address zero in machine IR:\n{dumped}"
    );
    assert!(
        !dumped.contains("evm_malloc") && !dumped.contains("bitcast"),
        "machine IR should not retain malloc/cast operations:\n{dumped}"
    );

    let lowered = backend
        .lower_function(&prepared, entry)
        .expect("entry lowers");
    let bytes = lowered_bytes(&lowered);
    assert!(
        contains_subsequence(
            &bytes,
            &[
                OpCode::PUSH0 as u8,
                OpCode::MSTORE as u8,
                OpCode::PUSH1 as u8,
                0x20,
                OpCode::PUSH0 as u8,
                OpCode::RETURN as u8,
            ],
        ),
        "expected PUSH0/MSTORE/PUSH1 0x20/PUSH0/RETURN sequence, got {bytes:?}"
    );
    assert!(
        !contains_subsequence(&bytes, &[OpCode::SWAP1 as u8, OpCode::DUP2 as u8]),
        "fixed zero buffer should not lower through SWAP1 DUP2: {bytes:?}"
    );
}

fn prepared_func_dump(src: &str, func_name: &str) -> String {
    let parsed = parse_module(src).expect("module parses");
    let funcs = parsed.module.funcs();
    let entry = find_func(&parsed.module, func_name);
    let backend = test_backend();
    let prepared = backend
        .prepare_section(work_module_with_entry(&parsed.module, &funcs, entry))
        .expect("prepare should succeed");

    prepared.module().func_store.view(entry, |function| {
        FuncWriter::new(entry, function).dump_string()
    })
}

#[test]
fn non_terminal_private_transient_malloc_lowers_to_static_slot_with_persistent_heap() {
    let dumped = prepared_func_dump(
        r#"
target = "evm-ethereum-osaka"

func private %mk(v0.i256) -> *i8 {
block0:
    v1.*i8 = evm_malloc 32.i256;
    v2.i256 = ptr_to_int v1 i256;
    mstore v2 v0 i256;
    return v1;
}

func public %entry(v0.i1, v1.i256) -> i256 {
block0:
    br v0 block1 block2;

block1:
    v2.*i8 = evm_malloc 64.i256;
    v3.i256 = ptr_to_int v2 i256;
    mstore v3 v1 i256;
    v4.i256 = add v3 32.i256;
    mstore v4 v1 i256;
    v5.i256 = evm_keccak256 v3 64.i256;
    return v5;

block2:
    v6.*i8 = call %mk v1;
    v7.i256 = ptr_to_int v6 i256;
    return v7;
}
"#,
        "entry",
    );

    assert!(
        dumped.contains("evm_keccak256"),
        "test should contain the private scratch consumer:\n{dumped}"
    );
    assert!(
        !dumped.contains("evm_mload 64.i256"),
        "private transient malloc should not read the heap free pointer:\n{dumped}"
    );
    assert!(
        !dumped.contains("evm_malloc") && !dumped.contains("ptr_to_int"),
        "machine IR should replace the malloc address with a static slot:\n{dumped}"
    );
}

#[test]
fn disjoint_private_transient_mallocs_pack_into_same_static_slot() {
    let dumped = prepared_func_dump(
        r#"
target = "evm-ethereum-osaka"

func private %mk(v0.i256) -> *i8 {
block0:
    v1.*i8 = evm_malloc 32.i256;
    v2.i256 = ptr_to_int v1 i256;
    mstore v2 v0 i256;
    return v1;
}

func public %entry(v0.i256) -> i256 {
block0:
    v1.*i8 = evm_malloc 64.i256;
    v2.i256 = ptr_to_int v1 i256;
    mstore v2 v0 i256;
    v3.i256 = evm_keccak256 v2 64.i256;
    v4.*i8 = evm_malloc 64.i256;
    v5.i256 = ptr_to_int v4 i256;
    mstore v5 v0 i256;
    v6.i256 = evm_keccak256 v5 64.i256;
    v7.i256 = add v3 v6;
    return v7;
}
"#,
        "entry",
    );

    let keccak_bases: Vec<_> = dumped
        .lines()
        .filter_map(|line| {
            line.split("evm_keccak256 ")
                .nth(1)
                .and_then(|tail| tail.split_whitespace().next())
        })
        .collect();
    assert_eq!(
        keccak_bases.len(),
        2,
        "test should contain two private scratch consumers:\n{dumped}"
    );
    assert_eq!(
        keccak_bases[0], keccak_bases[1],
        "disjoint private buffers should share the packed static slot:\n{dumped}"
    );
    assert!(
        !dumped.contains("evm_mload 64.i256"),
        "packed private buffers should not use transient heap bases:\n{dumped}"
    );
}

#[test]
fn dynamic_private_transient_access_len_keeps_heap_base() {
    let dumped = prepared_func_dump(
        r#"
target = "evm-ethereum-osaka"

func private %mk(v0.i256) -> *i8 {
block0:
    v1.*i8 = evm_malloc 32.i256;
    v2.i256 = ptr_to_int v1 i256;
    mstore v2 v0 i256;
    return v1;
}

func public %entry(v0.i1, v1.i256, v2.i256) -> i256 {
block0:
    br v0 block1 block2;

block1:
    v3.*i8 = evm_malloc 64.i256;
    v4.i256 = ptr_to_int v3 i256;
    mstore v4 v2 i256;
    v5.i256 = evm_keccak256 v4 v1;
    return v5;

block2:
    v6.*i8 = call %mk v2;
    v7.i256 = ptr_to_int v6 i256;
    return v7;
}
"#,
        "entry",
    );

    assert!(
        dumped.contains("evm_mload 64.i256"),
        "dynamic private access length must retain the heap-derived base:\n{dumped}"
    );
}

#[test]
fn terminal_private_checked_malloc_lowers_to_fixed_buffer_with_persistent_heap() {
    let dumped = prepared_func_dump(
        r#"
target = "evm-ethereum-osaka"

func private %mk(v0.i256) -> *i8 {
block0:
    v1.*i8 = evm_malloc 32.i256;
    v2.i256 = ptr_to_int v1 i256;
    mstore v2 v0 i256;
    return v1;
}

func public %entry(v0.i1, v1.i256) {
block0:
    br v0 block1 block4;

block1:
    v2.*i8 = evm_malloc 64.i256;
    v3.i256 = ptr_to_int v2 i256;
    mstore v3 v1 i256;
    (v4.i256, v5.i1) = uaddo v3 32.i256;
    br v5 block2 block3;

block2:
    evm_revert 0.i256 0.i256;

block3:
    mstore v4 v1 i256;
    evm_return v3 64.i256;

block4:
    v6.*i8 = call %mk v1;
    v7.i256 = ptr_to_int v6 i256;
    evm_return v7 32.i256;
}
"#,
        "entry",
    );

    assert!(
        !dumped.contains("evm_mload 64.i256"),
        "terminal-private malloc should not lower through the heap free pointer:\n{dumped}"
    );
    assert!(
        !dumped.contains("uaddo") && !dumped.contains(" lt "),
        "fixed terminal buffer should fold checked address arithmetic:\n{dumped}"
    );
}

#[test]
fn terminal_private_malloc_keeps_heap_base_when_pointer_value_escapes_in_payload() {
    let dumped = prepared_func_dump(
        r#"
target = "evm-ethereum-osaka"

func public %entry() {
block0:
    v0.*i8 = evm_malloc 32.i256;
    v1.i256 = ptr_to_int v0 i256;
    mstore v1 v1 i256;
    evm_return v1 32.i256;
}
"#,
        "entry",
    );

    assert!(
        dumped.contains("evm_mload 64.i256"),
        "malloc address stored into returned bytes must remain heap-based:\n{dumped}"
    );
}

#[test]
fn terminal_private_checked_malloc_keeps_heap_base_when_overflow_flag_escapes() {
    let dumped = prepared_func_dump(
        r#"
target = "evm-ethereum-osaka"

func private %mk(v0.i256) -> *i8 {
block0:
    v1.*i8 = evm_malloc 32.i256;
    v2.i256 = ptr_to_int v1 i256;
    mstore v2 v0 i256;
    return v1;
}

func public %entry(v0.i1, v1.i256) {
block0:
    br v0 block1 block2;

block1:
    v2.*i8 = evm_malloc 64.i256;
    v3.i256 = ptr_to_int v2 i256;
    (v4.i256, v5.i1) = uaddo v3 32.i256;
    v6.i256 = zext v5 i256;
    mstore v3 v6 i256;
    evm_return v3 32.i256;

block2:
    v7.*i8 = call %mk v1;
    v8.i256 = ptr_to_int v7 i256;
    evm_return v8 32.i256;
}
"#,
        "entry",
    );

    assert!(
        dumped.contains("evm_mload 64.i256"),
        "observable malloc-derived overflow flag must keep heap-based placement:\n{dumped}"
    );
}

#[test]
fn terminal_return_payload_write_does_not_reserve_arena_base() {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

func private %callee() -> i256 {
block0:
    v0.*i256 = alloca i256;
    mstore v0 3.i256 i256;
    v1.i256 = mload v0 i256;
    return v1;
}

func public %entry() {
block0:
    v0.i256 = call %callee;
    mstore 0.i32 v0 i256;
    evm_return 0.i8 32.i8;
}

object @Contract {
  section runtime {
    entry %entry;
  }
}
"#,
    )
    .unwrap();

    let funcs = parsed.module.funcs();
    let callee = find_func(&parsed.module, "callee");
    let entry = find_func(&parsed.module, "entry");
    let backend = test_backend();
    let prepared = backend
        .prepare_section(work_module_with_entry(&parsed.module, &funcs, entry))
        .expect("prepare should succeed");

    assert_eq!(prepared.section_plan().arena_base, 0);
    assert_eq!(
        prepared
            .function_plan(callee)
            .expect("missing callee plan")
            .mem_plan
            .scratch_words,
        1
    );
}

#[test]
fn terminal_return_payload_read_across_call_reserves_arena_base() {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

func private %callee() -> i256 {
block0:
    v0.*i256 = alloca i256;
    mstore v0 3.i256 i256;
    v1.i256 = mload v0 i256;
    return v1;
}

func public %entry() {
block0:
    mstore 0.i32 7.i256 i256;
    v0.i256 = call %callee;
    evm_return 0.i8 32.i8;
}

object @Contract {
  section runtime {
    entry %entry;
  }
}
"#,
    )
    .unwrap();

    let funcs = parsed.module.funcs();
    let entry = find_func(&parsed.module, "entry");
    let backend = test_backend();
    let prepared = backend
        .prepare_section(work_module_with_entry(&parsed.module, &funcs, entry))
        .expect("prepare should succeed");

    assert_eq!(prepared.section_plan().arena_base, 0x20);
}

#[test]
fn return_escape_clamp_uses_caller_transitive_clobber_bound() {
    let ctx = plan_test_ctx_from_src(
        r#"
target = "evm-ethereum-osaka"

func public %sum8(v0.i256, v1.i256, v2.i256, v3.i256, v4.i256, v5.i256, v6.i256, v7.i256) -> i256 {
block0:
    v8.i256 = add v0 v1;
    v9.i256 = add v2 v3;
    v10.i256 = add v4 v5;
    v11.i256 = add v6 v7;
    v12.i256 = add v8 v9;
    v13.i256 = add v10 v11;
    v14.i256 = add v12 v13;
    return v14;
}

func public %spill(v0.i256, v1.i256, v2.i256, v3.i256, v4.i256, v5.i256, v6.i256, v7.i256) -> i256 {
block1:
    v8.i256 = add v0 v1;
    v9.i256 = add v2 v3;
    v10.i256 = add v4 v5;
    v11.i256 = add v6 v7;
    v12.i256 = add v8 v9;
    v13.i256 = add v10 v11;
    v14.i256 = add v12 v13;
    jump block2;

block2:
    v15.i256 = phi (v14 block1) (v19 block2);
    v16.i256 = call %sum8 v0 v1 v2 v3 v4 v5 v6 v7;
    v17.i256 = call %sum8 v8 v9 v10 v11 v12 v13 v14 v15;
    v18.i256 = add v16 v17;
    v19.i256 = add v7 v18;
    v20.i1 = gt v19 1000.i256;
    br v20 block3 block2;

block3:
    return v18;
}

func public %mk() -> *i256 {
block0:
    v0.*i8 = evm_malloc 32.i256;
    v1.*i256 = bitcast v0 *i256;
    mstore v1 111.i256 i256;
    return v1;
}

func public %main(v0.i256, v1.i256, v2.i256, v3.i256, v4.i256, v5.i256, v6.i256, v7.i256) -> i256 {
block0:
    v8.*i256 = call %mk;
    v9.i256 = call %spill v0 v1 v2 v3 v4 v5 v6 v7;
    v10.i256 = mload v8 i256;
    v11.i256 = add v9 v10;
    return v11;
}
"#,
    );

    let mk = ctx.names["mk"];
    let main = ctx.names["main"];
    let abs_clobber_words = compute_abs_clobber_words_with_extra(
        &crate::module_analysis::CallGraphSchedule::compute(&ctx.module, &ctx.funcs),
        &ctx.plan,
        &FxHashMap::default(),
    );
    let clamp_words = compute_return_escape_caller_clamp_words(
        &crate::module_analysis::CallGraphSchedule::compute(&ctx.module, &ctx.funcs),
        &ctx.plan,
        &FxHashMap::default(),
    );
    let main_clobber_words = abs_clobber_words[&main];

    assert_eq!(clamp_words[&mk], main_clobber_words);

    let extra_reserve = BackendSpillReserve {
        scratch_words: 3,
        stable_words: 0,
    };
    let extra_main_clobber_words = main_clobber_words
        .checked_add(extra_reserve.scratch_words)
        .expect("test clobber overflow");
    let mut extra_clobber_words = FxHashMap::default();
    extra_clobber_words.insert(main, extra_reserve);
    let clamp_words = compute_return_escape_caller_clamp_words(
        &crate::module_analysis::CallGraphSchedule::compute(&ctx.module, &ctx.funcs),
        &ctx.plan,
        &extra_clobber_words,
    );

    assert_eq!(clamp_words[&mk], extra_main_clobber_words);
}

#[test]
fn return_escape_clamp_uses_reserved_static_chain_layout() {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

func public %reserve_anchor() {
block0:
    return;
}

func public %use(v0.*i256) -> i256 {
block0:
    v1.i256 = mload v0 i256;
    return v1;
}

func public %mk() -> *i256 {
block0:
    v0.*i8 = evm_malloc 32.i256;
    v1.*i256 = bitcast v0 *i256;
    mstore v1 111.i256 i256;
    return v1;
}

func public %decode() -> i256 {
block0:
    v0.*i256 = alloca i256;
    mstore v0 7.i256 i256;
    v1.i256 = call %use v0;
    return v1;
}

func public %main() -> i256 {
block0:
    v0.*i256 = call %mk;
    v1.i256 = call %decode;
    v2.i256 = mload v0 i256;
    v3.i256 = add v1 v2;
    return v3;
}
"#,
    )
    .expect("module parses");
    let funcs = parsed.module.funcs();
    let backend = test_backend();
    let ptr_escape = compute_ptr_escape_summaries(&parsed.module, &funcs, &backend.isa);

    let mut analyses = FxHashMap::default();
    for &func in &funcs {
        parsed.module.func_store.modify(func, |function| {
            analyses.insert(
                func,
                compute_test_pre_analysis(function, &parsed.module.ctx, &backend, &ptr_escape),
            );
        });
    }

    let mut names = FxHashMap::default();
    for &func in &funcs {
        let name = parsed
            .module
            .ctx
            .func_sig(func, |sig| sig.name().to_string());
        names.insert(name, func);
    }

    let reserve_words = FxHashMap::from_iter([(
        names["reserve_anchor"],
        BackendSpillReserve {
            scratch_words: 0,
            stable_words: 8,
        },
    )]);
    let schedule = crate::module_analysis::CallGraphSchedule::compute(&parsed.module, &funcs);
    let fixed_reservations =
        prepare::scan_fixed_reservations(&parsed.module, &funcs, &backend, &analyses);
    let placement = machine::placement::compute_semantic_memory_placement(
        &parsed.module,
        machine::placement::MemoryPlacementSection {
            schedule: &schedule,
            fixed_reservations: &fixed_reservations,
            funcs: &funcs,
            entry: names["main"],
            includes: &[],
        },
        &analyses,
        &ptr_escape,
        &FxHashSet::default(),
        &backend,
        &reserve_words,
    );

    let mk = names["mk"];
    let decode = names["decode"];
    let mk_plan = &placement.funcs[&mk].mem_plan;
    let decode_end_words = placement.funcs[&decode].mem_plan.abs_words_end();
    assert!(
        mk_plan.return_escape_caller_abs_words >= decode_end_words,
        "return-escaping malloc clamp must include the post-reserve sibling callee frame"
    );

    let malloc = parsed.module.func_store.view(mk, |function| {
        function
            .layout
            .iter_block()
            .flat_map(|block| function.layout.iter_inst(block))
            .find(|&inst| {
                matches!(
                    backend.isa.inst_set().resolve_inst(function.dfg.inst(inst)),
                    EvmInstKind::EvmMalloc(_)
                )
            })
            .expect("mk has a malloc")
    });
    let min_base = match placement.funcs[&mk].malloc_placements[&malloc] {
        machine::placement::MallocPlacement::Heap { min_base, .. } => min_base,
        machine::placement::MallocPlacement::Fixed { base } => base,
    };
    let min_base_words = min_base
        .checked_sub(mk_plan.arena_base)
        .expect("malloc min base below arena")
        / WORD_BYTES;
    assert!(
        min_base_words >= decode_end_words,
        "malloc min base must not overlap the sibling callee's reserved static frame"
    );
}

#[test]
fn caller_free_ptr_floor_reaches_callee_malloc() {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

func public %clobber_then_read(v0.*i256) -> i256 {
block0:
    v1.*i8 = evm_malloc 32.i256;
    v2.*i256 = bitcast v1 *i256;
    mstore v2 v2 i256;
    v3.i256 = mload v0 i256;
    return v3;
}

func public %main() -> i256 {
block0:
    v0.*i8 = evm_malloc 32.i256;
    v1.*i256 = bitcast v0 *i256;
    mstore v1 111.i256 i256;
    v2.i256 = call %clobber_then_read v1;
    return v2;
}

func public %entry() {
block0:
    v0.i256 = call %main;
    mstore 0.i32 v0 i256;
    evm_return 0.i8 32.i8;
}
"#,
    )
    .expect("module parses");
    let funcs = parsed.module.funcs();
    let backend = test_backend();
    let ptr_escape = compute_ptr_escape_summaries(&parsed.module, &funcs, &backend.isa);

    let mut analyses = FxHashMap::default();
    for &func in &funcs {
        parsed.module.func_store.modify(func, |function| {
            analyses.insert(
                func,
                compute_test_pre_analysis(function, &parsed.module.ctx, &backend, &ptr_escape),
            );
        });
    }

    let clobber = find_func(&parsed.module, "clobber_then_read");
    let entry = find_func(&parsed.module, "entry");
    let schedule = crate::module_analysis::CallGraphSchedule::compute(&parsed.module, &funcs);
    let fixed_reservations =
        prepare::scan_fixed_reservations(&parsed.module, &funcs, &backend, &analyses);
    let placement = machine::placement::compute_semantic_memory_placement(
        &parsed.module,
        machine::placement::MemoryPlacementSection {
            schedule: &schedule,
            fixed_reservations: &fixed_reservations,
            funcs: &funcs,
            entry,
            includes: &[],
        },
        &analyses,
        &ptr_escape,
        &FxHashSet::default(),
        &backend,
        &FxHashMap::default(),
    );
    let malloc = parsed.module.func_store.view(clobber, |function| {
        function
            .layout
            .iter_block()
            .flat_map(|block| function.layout.iter_inst(block))
            .find(|&inst| {
                matches!(
                    backend.isa.inst_set().resolve_inst(function.dfg.inst(inst)),
                    EvmInstKind::EvmMalloc(_)
                )
            })
            .expect("clobber_then_read has a malloc")
    });
    assert_eq!(
        placement.funcs[&clobber].free_ptr_floor_before_malloc[&malloc],
        Some(0xa0)
    );
}

#[test]
fn callee_malloc_exit_floor_reaches_later_callee() {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

func public %alloc() -> i256 {
block0:
    v0.*i8 = evm_malloc 32.i256;
    v1.i256 = ptr_to_int v0 i256;
    return v1;
}

func public %scratch(v0.i256) -> i256 {
block0:
    v1.*i8 = evm_malloc 32.i256;
    v2.i256 = ptr_to_int v1 i256;
    mstore v2 v2 i256;
    return v0;
}

func public %entry() {
block0:
    v0.i256 = call %alloc;
    v1.i256 = call %scratch v0;
    mstore 0.i32 v1 i256;
    evm_return 0.i8 32.i8;
}
"#,
    )
    .expect("module parses");
    let funcs = parsed.module.funcs();
    let backend = test_backend();
    let ptr_escape = compute_ptr_escape_summaries(&parsed.module, &funcs, &backend.isa);

    let mut analyses = FxHashMap::default();
    for &func in &funcs {
        parsed.module.func_store.modify(func, |function| {
            analyses.insert(
                func,
                compute_test_pre_analysis(function, &parsed.module.ctx, &backend, &ptr_escape),
            );
        });
    }

    let entry = find_func(&parsed.module, "entry");
    let scratch = find_func(&parsed.module, "scratch");
    let schedule = crate::module_analysis::CallGraphSchedule::compute(&parsed.module, &funcs);
    let fixed_reservations =
        prepare::scan_fixed_reservations(&parsed.module, &funcs, &backend, &analyses);
    let placement = machine::placement::compute_semantic_memory_placement(
        &parsed.module,
        machine::placement::MemoryPlacementSection {
            schedule: &schedule,
            fixed_reservations: &fixed_reservations,
            funcs: &funcs,
            entry,
            includes: &[],
        },
        &analyses,
        &ptr_escape,
        &FxHashSet::default(),
        &backend,
        &FxHashMap::default(),
    );
    let malloc = parsed.module.func_store.view(scratch, |function| {
        function
            .layout
            .iter_block()
            .flat_map(|block| function.layout.iter_inst(block))
            .find(|&inst| {
                matches!(
                    backend.isa.inst_set().resolve_inst(function.dfg.inst(inst)),
                    EvmInstKind::EvmMalloc(_)
                )
            })
            .expect("scratch has a malloc")
    });
    let min_base = match placement.funcs[&scratch].malloc_placements[&malloc] {
        machine::placement::MallocPlacement::Heap { min_base, .. } => min_base,
        machine::placement::MallocPlacement::Fixed { base } => base,
    };
    assert_eq!(
        placement.funcs[&scratch].free_ptr_floor_before_malloc[&malloc],
        Some(min_base)
    );
}

#[test]
fn noreturn_call_skips_continuation_marker_and_preserve() {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

func private %abort() -> i256 {
block0:
    evm_revert 0.i256 0.i256;
}

func public %caller(v0.i256) -> i256 {
block0:
    v1.*i256 = alloca i256;
    mstore v1 v0 i256;
    v2.i256 = call %abort;
    v3.i256 = mload v1 i256;
    return v3;
}
"#,
    )
    .unwrap();

    func_behavior::analyze_module(&parsed.module);

    let funcs = parsed.module.funcs();
    let isa = Evm::new(TargetTriple {
        architecture: Architecture::Evm,
        vendor: Vendor::Ethereum,
        operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
    });
    let ptr_escape = compute_ptr_escape_summaries(&parsed.module, &funcs, &isa);

    let mut names: FxHashMap<String, FuncRef> = FxHashMap::default();
    for &f in &funcs {
        let name = parsed.module.ctx.func_sig(f, |sig| sig.name().to_string());
        names.insert(name, f);
    }
    let caller = names["caller"];

    let backend = EvmBackend::new(isa);
    let mut pre_analyses: FxHashMap<FuncRef, memory_plan::FuncPreAnalysis> = FxHashMap::default();
    let mut stack_allocs: FxHashMap<FuncRef, StackifyAlloc> = FxHashMap::default();
    for &func in &funcs {
        parsed.module.func_store.modify(func, |function| {
            pre_analyses.insert(
                func,
                compute_test_pre_analysis(function, &parsed.module.ctx, &backend, &ptr_escape),
            );
            stack_allocs.insert(func, compute_test_stackify_alloc(function));
        });
    }

    let (call_inst, call_args) = parsed.module.func_store.view(caller, |function| {
        function
            .layout
            .iter_block()
            .flat_map(|block| function.layout.iter_inst(block))
            .find_map(|inst| {
                function
                    .dfg
                    .cast_call(inst)
                    .map(|call| (inst, call.args().clone()))
            })
            .expect("missing call inst")
    });

    let actions = stack_allocs
        .get(&caller)
        .expect("missing caller analysis")
        .read(call_inst, &call_args);
    assert!(
        !actions
            .iter()
            .any(|a| matches!(a, Action::PushContinuationOffset)),
        "noreturn call should not materialize a local continuation: {actions:?}"
    );

    let plan = compute_semantic_program_memory_plan(
        &parsed.module,
        &crate::module_analysis::CallGraphSchedule::compute(&parsed.module, &funcs),
        &pre_analyses,
        &ptr_escape,
        &isa,
        &ArenaCostModel::default(),
    );
    assert!(
        !plan
            .funcs
            .get(&caller)
            .expect("missing caller plan")
            .call_preserve
            .contains_key(&call_inst),
        "noreturn call should not preserve caller scratch state"
    );
}

#[test]
fn prepare_section_handles_recursive_scratch_barriers_without_oscillation() {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

func public %f(v0.i256) -> i256 {
block0:
    v1.i1 = eq v0 0.i256;
    br v1 block1 block2;

block1:
    return 0.i256;

block2:
    v2.*i256 = alloca i256;
    mstore v2 v0 i256;
    v3.i256 = mload v2 i256;
    v4.i256 = add v3 1.i256;
    v5.i256 = add v3 2.i256;
    v6.i256 = add v3 3.i256;
    v7.i256 = add v3 4.i256;
    mstore v2 v7 i256;
    v8.i256 = sub v3 1.i256;
    v9.i256 = call %f v8;
    v10.i256 = mload v2 i256;
    v11.i256 = add v9 v10;
    v12.i256 = add v11 v4;
    v13.i256 = add v12 v5;
    v14.i256 = add v13 v6;
    return v14;
}

func public %entry() {
block0:
    v0.i256 = call %f 3.i256;
    mstore 0.i32 v0 i256;
    evm_return 0.i8 32.i8;
}

object @Contract {
  section runtime {
    entry %entry;
  }
}
"#,
    )
    .unwrap();

    let funcs = parsed.module.funcs();
    let mut names: FxHashMap<String, FuncRef> = FxHashMap::default();
    for &func in &funcs {
        let name = parsed
            .module
            .ctx
            .func_sig(func, |sig| sig.name().to_string());
        names.insert(name, func);
    }

    let backend = EvmBackend::new(Evm::new(TargetTriple {
        architecture: Architecture::Evm,
        vendor: Vendor::Ethereum,
        operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
    }))
    .with_stackify_reach_depth(4);
    let prepared = backend
        .prepare_section(work_module_with_entry(
            &parsed.module,
            &funcs,
            names["entry"],
        ))
        .expect("prepare should succeed");
    assert!(
        !prepared
            .function_plan(names["f"])
            .expect("function plan for %f")
            .alloc
            .uses_scratch_spills(),
        "recursive caller should treat self-call as a scratch barrier"
    );
}

#[test]
fn prepare_section_scratch_analysis_is_deterministic_across_runs() {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

func private %helper(v0.i256) -> i256 {
block0:
    v1.i256 = add v0 5.i256;
    return v1;
}

func public %f(v0.i256) -> i256 {
block0:
    v1.i1 = eq v0 0.i256;
    br v1 block1 block2;

block1:
    return 0.i256;

block2:
    v2.*i256 = alloca i256;
    mstore v2 v0 i256;
    v3.i256 = mload v2 i256;
    v4.i256 = add v3 1.i256;
    v5.i256 = add v3 2.i256;
    v6.i256 = add v3 3.i256;
    v7.i256 = add v3 4.i256;
    mstore v2 v7 i256;
    v8.i256 = sub v3 1.i256;
    v9.i256 = call %f v8;
    v10.i256 = mload v2 i256;
    v11.i256 = add v9 v10;
    v12.i256 = add v11 v4;
    v13.i256 = add v12 v5;
    v14.i256 = add v13 v6;
    return v14;
}

func public %entry() {
block0:
    v0.i256 = call %helper 7.i256;
    v1.i256 = call %f v0;
    mstore 0.i32 v1 i256;
    evm_return 0.i8 32.i8;
}

object @Contract {
  section runtime {
    entry %entry;
  }
}
"#,
    )
    .unwrap();

    let funcs = parsed.module.funcs();
    let entry = find_func(&parsed.module, "entry");
    let recursive = find_func(&parsed.module, "f");
    let backend = EvmBackend::new(Evm::new(TargetTriple {
        architecture: Architecture::Evm,
        vendor: Vendor::Ethereum,
        operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
    }))
    .with_stackify_reach_depth(4);

    let mut expected_func_order: Option<Vec<FuncRef>> = None;
    let mut expected_spill_summary: Option<Vec<(String, bool)>> = None;
    let mut expected_mem_plan: Option<String> = None;

    for _ in 0..8 {
        let prepared = backend
            .prepare_section(work_module_with_entry(&parsed.module, &funcs, entry))
            .expect("prepare should succeed");
        let func_order = prepared.funcs().to_vec();
        let spill_summary: Vec<_> = prepared
            .funcs()
            .iter()
            .copied()
            .map(|func| {
                (
                    prepared
                        .module()
                        .ctx
                        .func_sig(func, |sig| sig.name().to_string()),
                    prepared
                        .function_plan(func)
                        .expect("function plan should exist")
                        .alloc
                        .uses_scratch_spills(),
                )
            })
            .collect();
        let mem_plan = backend.snapshot_mem_plan_detail(&prepared);

        if let Some(expected) = &expected_func_order {
            assert_eq!(
                func_order.as_slice(),
                expected.as_slice(),
                "function order changed across runs"
            );
        } else {
            expected_func_order = Some(func_order);
        }
        if let Some(expected) = &expected_spill_summary {
            assert_eq!(
                spill_summary.as_slice(),
                expected.as_slice(),
                "scratch spill decisions changed across runs"
            );
        } else {
            expected_spill_summary = Some(spill_summary);
        }
        if let Some(expected) = &expected_mem_plan {
            assert_eq!(
                mem_plan.as_str(),
                expected.as_str(),
                "mem plan changed across runs"
            );
        } else {
            expected_mem_plan = Some(mem_plan);
        }
    }

    assert!(
        !expected_spill_summary
            .expect("spill summary should be recorded")
            .into_iter()
            .find(|(name, _)| name == "f")
            .expect("recursive function should be present")
            .1,
        "recursive caller should still avoid scratch spills"
    );
    assert!(
        !backend
            .prepare_section(work_module_with_entry(&parsed.module, &funcs, entry))
            .expect("prepare should succeed")
            .function_plan(recursive)
            .expect("function plan for %f")
            .alloc
            .uses_scratch_spills(),
        "recursive caller should treat self-call as a scratch barrier"
    );
}

#[test]
fn prepare_section_runs_late_dead_arg_elim_on_helpers() {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

func private %helper(v0.i256, v1.i256) -> i256 {
block0:
    return v1;
}

func public %entry(v0.i256) -> i256 {
block0:
    v1.i256 = call %helper 0.i256 v0;
    return v1;
}

object @Contract {
  section runtime {
    entry %entry;
  }
}
"#,
    )
    .unwrap();

    let funcs = parsed.module.funcs();
    let mut names: FxHashMap<String, FuncRef> = FxHashMap::default();
    for &func in &funcs {
        let name = parsed
            .module
            .ctx
            .func_sig(func, |sig| sig.name().to_string());
        names.insert(name, func);
    }

    let backend = EvmBackend::new(Evm::new(TargetTriple {
        architecture: Architecture::Evm,
        vendor: Vendor::Ethereum,
        operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
    }))
    .with_late_cleanup_profile(LateCleanupProfile::Speed);
    let prepared = backend
        .prepare_section(work_module_with_entry(
            &parsed.module,
            &funcs,
            names["entry"],
        ))
        .expect("prepare should succeed");

    let helper_sig = prepared
        .module()
        .ctx
        .get_sig(names["helper"])
        .expect("helper signature should exist");
    assert_eq!(
        helper_sig.args().len(),
        1,
        "late cleanup should prune dead helper arg"
    );
    prepared
        .module()
        .func_store
        .view(names["entry"], |function| {
            let dumped = FuncWriter::new(names["entry"], function).dump_string();
            assert!(
                dumped.contains("v1.i256 = call %helper v0;"),
                "entry callsite should be rewritten after late dead-arg elim:\n{dumped}"
            );
        });
    let original_helper_sig = parsed
        .module
        .ctx
        .get_sig(names["helper"])
        .expect("original helper signature should exist");
    assert_eq!(
        original_helper_sig.args().len(),
        2,
        "prepare should not mutate the original module"
    );
}

#[test]
fn prepare_section_binds_uniform_const_arg_before_late_dead_arg_elim() {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

func private %helper(v0.i256, v1.i256) -> i256 {
block0:
    v2.i256 = add v0 v1;
    return v2;
}

func public %entry(v0.i256) -> i256 {
block0:
    v1.i256 = add 1.i256 2.i256;
    v2.i256 = call %helper v1 v0;
    v3.i256 = call %helper 3.i256 v2;
    return v3;
}

object @Contract {
  section runtime {
    entry %entry;
  }
}
"#,
    )
    .unwrap();

    let funcs = parsed.module.funcs();
    let mut names: FxHashMap<String, FuncRef> = FxHashMap::default();
    for &func in &funcs {
        let name = parsed
            .module
            .ctx
            .func_sig(func, |sig| sig.name().to_string());
        names.insert(name, func);
    }

    let backend = EvmBackend::new(Evm::new(TargetTriple {
        architecture: Architecture::Evm,
        vendor: Vendor::Ethereum,
        operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
    }))
    .with_late_cleanup_profile(LateCleanupProfile::Speed);
    let prepared = backend
        .prepare_section(work_module_with_entry(
            &parsed.module,
            &funcs,
            names["entry"],
        ))
        .expect("prepare should succeed");

    let helper_sig = prepared
        .module()
        .ctx
        .get_sig(names["helper"])
        .expect("helper signature should exist");
    assert_eq!(
        helper_sig.args().len(),
        1,
        "uniform const arg binding should expose removable helper arg"
    );
    prepared
        .module()
        .func_store
        .view(names["entry"], |function| {
            let dumped = FuncWriter::new(names["entry"], function).dump_string();
            assert!(
                !dumped.contains("call %helper 3.i256"),
                "entry callsites should drop the bound constant:\n{dumped}"
            );
        });
}

#[test]
fn prepare_section_prunes_dead_constref_specialization_original() {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

type @Err = enum {
    #None,
    #Bad,
};

type @Result = { i1, @Err };

global private const [i256; 1] $values = [1];

func private %verify(v0.constref<[i256; 1]>) -> @Result {
block0:
    v1.@Err = enum.make @Err #Bad;
    v2.@Result = insert_value undef.@Result 0.i8 0.i1;
    v3.@Result = insert_value v2 1.i8 v1;
    return v3;
}

func public %entry() -> i256 {
block0:
    v0.constref<[i256; 1]> = const.ref $values;
    v1.@Result = call %verify v0;
    v2.i1 = extract_value v1 0.i8;
    v3.@Err = extract_value v1 1.i8;
    enum.assert_variant v3 #Bad;
    return 1.i256;
}

object @Contract {
  section runtime {
    entry %entry;
  }
}
"#,
    )
    .unwrap();

    let funcs = parsed.module.funcs();
    let verify = find_func(&parsed.module, "verify");
    let entry = find_func(&parsed.module, "entry");
    let backend = test_backend().with_late_cleanup_profile(LateCleanupProfile::Speed);
    let prepared = backend
        .prepare_section(work_module_with_entry(&parsed.module, &funcs, entry))
        .expect("prepare should succeed");

    assert!(
        prepared.module().ctx.get_sig(verify).is_none(),
        "dead unspecialized original should be pruned"
    );
}

#[test]
fn prepare_section_keeps_live_unspecialized_constref_original() {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

global private const [i256; 1] $values = [1];

func private %verify(v0.constref<[i256; 1]>) -> i256 {
block0:
    v1.constref<i256> = const.index v0 0.i8;
    v2.i256 = const.load v1;
    return v2;
}

func private %dispatch(v0.constref<[i256; 1]>) -> i256 {
block0:
    v1.i256 = call %verify v0;
    return v1;
}

func public %entry() -> i256 {
block0:
    v0.constref<[i256; 1]> = const.ref $values;
    v1.i256 = call %verify v0;
    v2.i256 = call %dispatch v0;
    v3.i256 = add v1 v2;
    return v3;
}

object @Contract {
  section runtime {
    entry %entry;
  }
}
"#,
    )
    .unwrap();

    let funcs = parsed.module.funcs();
    let verify = find_func(&parsed.module, "verify");
    let entry = find_func(&parsed.module, "entry");
    let backend = test_backend().with_late_cleanup_profile(LateCleanupProfile::Speed);
    let prepared = backend
        .prepare_section(work_module_with_entry(&parsed.module, &funcs, entry))
        .expect("prepare should succeed");
    let names: FxHashSet<_> = prepared
        .module()
        .funcs()
        .into_iter()
        .map(|func| {
            prepared
                .module()
                .ctx
                .func_sig(func, |sig| sig.name().to_string())
        })
        .collect();

    assert!(
        prepared.module().ctx.get_sig(verify).is_some(),
        "original should remain live through the specialized dispatch clone"
    );
    assert!(
        names
            .iter()
            .any(|name| name.starts_with("verify__constref")),
        "direct static call should still produce a specialized clone: {names:?}"
    );
}

#[test]
fn prepare_section_runs_raw_memory_cleanup_after_memory_legalize() {
    let mut parsed = parse_module(include_str!(
        "../../../test_files/evm/fresh_equivalent_out_param_scalarizes.sntn"
    ))
    .unwrap();
    Pipeline::speed().run(&mut parsed.module);

    let funcs = parsed.module.funcs();
    let off_backend = EvmBackend::new(Evm::new(TargetTriple {
        architecture: Architecture::Evm,
        vendor: Vendor::Ethereum,
        operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
    }))
    .with_late_cleanup_profile(LateCleanupProfile::Off);
    let speed_backend = EvmBackend::new(Evm::new(TargetTriple {
        architecture: Architecture::Evm,
        vendor: Vendor::Ethereum,
        operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
    }))
    .with_late_cleanup_profile(LateCleanupProfile::Speed);
    let entry = find_func(&parsed.module, "entry");
    let count_insts = |prepared: &EvmPreparedSection| {
        prepared.module().func_store.view(entry, |function| {
            function
                .layout
                .iter_block()
                .map(|block| function.layout.iter_inst(block).count())
                .sum::<usize>()
        })
    };
    let dump_entry = |prepared: &EvmPreparedSection| {
        prepared.module().func_store.view(entry, |function| {
            FuncWriter::new(entry, function).dump_string()
        })
    };
    let before = off_backend
        .prepare_section(work_module_with_entry(&parsed.module, &funcs, entry))
        .expect("prepare without optional cleanup should succeed");
    let after = speed_backend
        .prepare_section(work_module_with_entry(&parsed.module, &funcs, entry))
        .expect("prepare with optional cleanup should succeed");
    let before_dump = dump_entry(&before);
    let after_dump = dump_entry(&after);
    let before = count_insts(&before);
    let after = count_insts(&after);

    assert!(
        !before_dump.contains("obj."),
        "mandatory lowering must still remove object IR when optional cleanup is off:\n{before_dump}"
    );
    assert!(
        !after_dump.contains("obj."),
        "mandatory lowering must still remove object IR when optional cleanup is on:\n{after_dump}"
    );
    assert!(
        after <= before,
        "late raw-memory cleanup should not expand prepared machine IR (before={before}, after={after})"
    );
}

#[test]
fn prepare_section_places_zero_sized_callee_visible_alloca_without_cleanup() {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

type @empty = {};
type @wrapper = {@empty};

func private %callee(v0.objref<@wrapper>) {
block0:
    return;
}

func public %entry() {
block0:
    v0.objref<@wrapper> = obj.alloc @wrapper;
    call %callee v0;
    evm_stop;
}
"#,
    )
    .unwrap();
    let funcs = parsed.module.funcs();
    let entry = find_func(&parsed.module, "entry");
    let prepared = test_backend()
        .with_late_cleanup_profile(LateCleanupProfile::Off)
        .prepare_section(work_module_with_entry(&parsed.module, &funcs, entry))
        .expect("zero-sized callee-visible alloca should lower without optional cleanup");
    let plan = prepared.function_plan(entry).expect("entry plan");

    assert_eq!(plan.mem_plan.scratch_words, 0);
    assert_eq!(plan.mem_plan.stable_words, 0);
    assert!(plan.mem_plan.alloca_loc.is_empty());
}

#[test]
fn lowering_elides_section_entry_jumpdest_for_noreturn_call() {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

func private %abort() {
block0:
    evm_revert 0.i256 0.i256;
}

func public %caller() {
block0:
    call %abort;
    unreachable;
}

object @Contract {
  section runtime {
    entry %caller;
  }
}
"#,
    )
    .unwrap();

    let funcs = parsed.module.funcs();
    let mut names: FxHashMap<String, FuncRef> = FxHashMap::default();
    for &f in &funcs {
        let name = parsed.module.ctx.func_sig(f, |sig| sig.name().to_string());
        names.insert(name, f);
    }

    let backend = EvmBackend::new(Evm::new(TargetTriple {
        architecture: Architecture::Evm,
        vendor: Vendor::Ethereum,
        operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
    }));
    let prepared = backend
        .prepare_section(work_module_with_entry(
            &parsed.module,
            &funcs,
            names["caller"],
        ))
        .expect("prepare should succeed");
    let lowered = backend
        .lower_function(&prepared, names["caller"])
        .expect("caller lowers");

    assert_eq!(lowered.block_order.len(), 1, "expected single caller block");
    let block = lowered.block_order[0];
    let jumpdest_count = lowered
        .vcode
        .block_insns(block)
        .filter(|&inst| (lowered.vcode.insts[inst] as u8) == (OpCode::JUMPDEST as u8))
        .count();
    assert_eq!(
        jumpdest_count, 0,
        "section-entry caller should not need a JUMPDEST without incoming jumps"
    );

    let lowered_abort = backend
        .lower_function(&prepared, names["abort"])
        .expect("abort lowers");
    let abort_block = lowered_abort.block_order[0];
    let abort_jumpdest_count = lowered_abort
        .vcode
        .block_insns(abort_block)
        .filter(|&inst| (lowered_abort.vcode.insts[inst] as u8) == (OpCode::JUMPDEST as u8))
        .count();
    assert_eq!(
        abort_jumpdest_count, 1,
        "direct call target should still materialize an entry JUMPDEST"
    );
}

#[test]
fn lowering_materializes_jumpdest_for_nonfallthrough_block_target() {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

func public %main(v0.i1) -> i256 {
block0:
    br v0 block2 block1;

block1:
    return 1.i256;

block2:
    return 2.i256;
}

object @Contract {
  section runtime {
    entry %main;
  }
}
"#,
    )
    .unwrap();

    let func = parsed.module.funcs()[0];
    let backend = EvmBackend::new(Evm::new(TargetTriple {
        architecture: Architecture::Evm,
        vendor: Vendor::Ethereum,
        operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
    }));
    let prepared = backend
        .prepare_section(work_module(&parsed.module, &[func]))
        .expect("prepare should succeed");
    let lowered = backend
        .lower_function(&prepared, func)
        .expect("main lowers");

    let block2 = lowered
        .block_order
        .iter()
        .copied()
        .find(|block| block.0 == 2)
        .expect("missing block2");
    assert!(
        lowered
            .vcode
            .block_insns(block2)
            .next()
            .is_some_and(|inst| { (lowered.vcode.insts[inst] as u8) == (OpCode::JUMPDEST as u8) }),
        "non-fallthrough branch target should start with JUMPDEST"
    );
}

#[test]
fn lowering_skips_trunc_mask_after_logical_shr() {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

func public %entry() {
block0:
    v0.i256 = evm_calldata_load 0.i256;
    v1.i256 = shr 224.i256 v0;
    v2.i32 = trunc v1 i32;
    v3.i1 = eq v2 305419896.i32;
    br v3 block1 block2;

block1:
    evm_return 0.i256 0.i256;

block2:
    evm_revert 0.i256 0.i256;
}

object @Contract {
  section runtime {
    entry %entry;
  }
}
"#,
    )
    .unwrap();

    let func = find_func(&parsed.module, "entry");
    let backend = EvmBackend::new(Evm::new(TargetTriple {
        architecture: Architecture::Evm,
        vendor: Vendor::Ethereum,
        operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
    }));
    let prepared = backend
        .prepare_section(work_module(&parsed.module, &[func]))
        .expect("prepare should succeed");
    let lowered = backend
        .lower_function(&prepared, func)
        .expect("entry lowers");
    let ops: Vec<_> = lowered
        .block_order
        .iter()
        .flat_map(|&block| lowered.vcode.block_insns(block))
        .map(|inst| lowered.vcode.insts[inst] as u8)
        .collect();

    assert!(
        ops.contains(&(OpCode::SHR as u8)),
        "expected the calldata selector path to lower through SHR"
    );
    assert!(
        !ops.contains(&(OpCode::AND as u8)),
        "trunc after SHR should not materialize a redundant mask: {ops:?}"
    );
}

#[test]
fn materialize_jumpdests_uses_final_block_fixups() {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

func public %main() -> i256 {
block0:
    return 0.i256;

block1:
    return 1.i256;
}
"#,
    )
    .unwrap();

    let func = parsed.module.funcs()[0];
    parsed.module.func_store.view(func, |function| {
        let block_order: Vec<_> = function.layout.iter_block().collect();
        assert_eq!(block_order.len(), 2, "expected two blocks");

        let mut vcode = VCode::<OpCode>::default();
        let push = vcode.add_inst_to_block(OpCode::PUSH1, None, block_order[0]);
        let label = vcode.labels.push(Label::Block(block_order[1]));
        vcode.fixups.insert((push, VCodeFixup::Label(label)));
        vcode.add_inst_to_block(OpCode::JUMP, None, block_order[0]);
        vcode.add_inst_to_block(OpCode::STOP, None, block_order[1]);

        materialize_jumpdests(&mut vcode, function, &block_order, false);

        assert!(
            vcode
                .block_insns(block_order[1])
                .next()
                .is_some_and(|inst| (vcode.insts[inst] as u8) == (OpCode::JUMPDEST as u8)),
            "final block fixup should force a block-entry JUMPDEST"
        );
        assert!(
            vcode
                .block_insns(block_order[0])
                .next()
                .is_some_and(|inst| (vcode.insts[inst] as u8) != (OpCode::JUMPDEST as u8)),
            "entry block should remain unpadded without function-entry targeting"
        );
    });
}

#[test]
fn lowering_elides_pure_jump_alias_blocks() {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

func public %main(v0.i1) {
block0:
    br v0 block1 block2;

block1:
    jump block3;

block2:
    v1.i256 = add 1.i256 2.i256;
    jump block3;

block3:
    evm_revert 0.i256 0.i256;
}

object @Contract {
  section runtime {
    entry %main;
  }
}
"#,
    )
    .unwrap();

    let func = parsed.module.funcs()[0];
    let backend = EvmBackend::new(Evm::new(TargetTriple {
        architecture: Architecture::Evm,
        vendor: Vendor::Ethereum,
        operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
    }));
    let prepared = backend
        .prepare_section(work_module(&parsed.module, &[func]))
        .expect("prepare should succeed");
    let lowered = backend
        .lower_function(&prepared, func)
        .expect("main lowers");

    assert!(
        lowered.block_order.iter().all(|block| block.0 != 1),
        "pure trampoline block should be omitted from final block order"
    );
    assert!(
        lowered
            .vcode
            .blocks
            .get(BlockId(1))
            .is_none_or(|block| block.is_empty()),
        "late alias block should not lower any instructions"
    );
    assert!(
        lowered.block_order.iter().all(|block| {
            let insts: Vec<_> = lowered.vcode.block_insns(*block).collect();
            !matches!(
                insts.as_slice(),
                [jumpdest, push, jump]
                    if (lowered.vcode.insts[*jumpdest] as u8) == (OpCode::JUMPDEST as u8)
                        && is_push_opcode(lowered.vcode.insts[*push])
                        && matches!(
                            lowered.vcode.fixups.get(*push),
                            Some((_, VCodeFixup::Label(_)))
                        )
                        && (lowered.vcode.insts[*jump] as u8) == (OpCode::JUMP as u8)
            )
        }),
        "late lowering should not leave pure jump trampoline blocks behind"
    );
}

#[test]
fn lowering_folds_branch_with_same_canonical_dest() {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

func public %main(v0.i1) {
block0:
    br v0 block1 block2;

block1:
    jump block3;

block2:
    jump block3;

block3:
    evm_revert 0.i256 0.i256;
}

object @Contract {
  section runtime {
    entry %main;
  }
}
"#,
    )
    .unwrap();

    let func = parsed.module.funcs()[0];
    let backend = EvmBackend::new(Evm::new(TargetTriple {
        architecture: Architecture::Evm,
        vendor: Vendor::Ethereum,
        operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
    }));
    let prepared = backend
        .prepare_section(work_module(&parsed.module, &[func]))
        .expect("prepare should succeed");
    let lowered = backend
        .lower_function(&prepared, func)
        .expect("main lowers");
    let entry = lowered.block_order[0];
    let ops: Vec<_> = lowered
        .vcode
        .block_insns(entry)
        .map(|inst| lowered.vcode.insts[inst] as u8)
        .collect();

    assert!(
        !ops.contains(&(OpCode::JUMPI as u8)),
        "branch with one canonical destination should not lower to JUMPI: {ops:?}"
    );
}

#[test]
fn prepared_section_is_reusable_across_lower_calls() {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

func public %main(v0.i256) -> i256 {
block0:
    v1.i256 = add v0 1.i256;
    return v1;
}

object @Contract {
  section runtime {
    entry %main;
  }
}
"#,
    )
    .unwrap();

    let func = parsed.module.funcs()[0];
    let backend = EvmBackend::new(Evm::new(TargetTriple {
        architecture: Architecture::Evm,
        vendor: Vendor::Ethereum,
        operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
    }));
    let prepared = backend
        .prepare_section(work_module(&parsed.module, &[func]))
        .expect("prepare should succeed");
    assert!(
        prepared.function_plan(func).is_some(),
        "prepared section should retain the per-function lowering plan"
    );

    backend
        .lower_function(&prepared, func)
        .expect("first lower succeeds");

    backend
        .lower_function(&prepared, func)
        .expect("second lower succeeds");
}

#[test]
fn reprepare_after_module_mutation_updates_lowering() {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

func public %main() {
block0:
    evm_return 0.i256 0.i256;
}

object @Contract {
  section runtime {
    entry %main;
  }
}
"#,
    )
    .unwrap();

    let func = parsed.module.funcs()[0];
    let backend = EvmBackend::new(Evm::new(TargetTriple {
        architecture: Architecture::Evm,
        vendor: Vendor::Ethereum,
        operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
    }));
    let _prepared = backend
        .prepare_section(work_module(&parsed.module, &[func]))
        .expect("initial prepare should succeed");

    parsed.module.func_store.modify(func, |function| {
        let block = function.layout.entry_block().expect("entry block exists");
        let term = function
            .layout
            .last_inst_of(block)
            .expect("entry block terminator exists");
        let (addr, len) = match backend.isa.inst_set().resolve_inst(function.dfg.inst(term)) {
            EvmInstKind::EvmReturn(ret) => (*ret.addr(), *ret.len()),
            _ => panic!("terminator should be evm_return"),
        };
        function.dfg.replace_inst(
            term,
            Box::new(sonatina_ir::inst::evm::EvmRevert::new(
                backend
                    .isa
                    .inst_set()
                    .has_evm_revert()
                    .expect("evm_revert supported"),
                addr,
                len,
            )),
        );
    });

    let prepared = backend
        .prepare_section(work_module(&parsed.module, &[func]))
        .expect("re-prepare after mutation should succeed");

    let lowered = backend
        .lower_function(&prepared, func)
        .expect("lower after mutation succeeds");
    assert!(
        lowered
            .vcode
            .insts
            .values()
            .any(|&op| (op as u8) == (OpCode::REVERT as u8)),
        "updated lowering should reflect the mutated terminator"
    );
    assert!(
        !lowered
            .vcode
            .insts
            .values()
            .any(|&op| (op as u8) == (OpCode::RETURN as u8)),
        "stale prepared lowering should not survive module mutation"
    );
}

#[test]
fn call_save_pre_tucks_saved_words_below_operands() {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

func public %caller(v0.i256, v1.i256) -> i256 {
block0:
    v2.*i256 = alloca i256;
    mstore v2 1.i256 i256;
    v3.i256 = mload v2 i256;
    v4.i256 = add v3 v0;
    mstore v2 v4 i256;
    v5.i256 = call %caller 11.i256 22.i256;
    v6.i256 = mload v2 i256;
    v7.i256 = add v5 v6;
    return v7;
}
"#,
    )
    .unwrap();

    let funcs = parsed.module.funcs();
    let isa = Evm::new(TargetTriple {
        architecture: Architecture::Evm,
        vendor: Vendor::Ethereum,
        operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
    });
    let ptr_escape = compute_ptr_escape_summaries(&parsed.module, &funcs, &isa);

    let backend = EvmBackend::new(isa);
    let mut pre_analyses: FxHashMap<FuncRef, memory_plan::FuncPreAnalysis> = FxHashMap::default();
    let mut stack_allocs: FxHashMap<FuncRef, StackifyAlloc> = FxHashMap::default();
    for &func in &funcs {
        parsed.module.func_store.modify(func, |function| {
            pre_analyses.insert(
                func,
                compute_test_pre_analysis(function, &parsed.module.ctx, &backend, &ptr_escape),
            );
            stack_allocs.insert(func, compute_test_stackify_alloc(function));
        });
    }

    let cost_model = ArenaCostModel {
        w_save: 0,
        w_code: 0,
        ..ArenaCostModel::default()
    };
    let plan = compute_semantic_program_memory_plan(
        &parsed.module,
        &crate::module_analysis::CallGraphSchedule::compute(&parsed.module, &funcs),
        &pre_analyses,
        &ptr_escape,
        &isa,
        &cost_model,
    );

    let mut names: FxHashMap<String, FuncRef> = FxHashMap::default();
    for &f in &funcs {
        let name = parsed.module.ctx.func_sig(f, |sig| sig.name().to_string());
        names.insert(name, f);
    }
    let caller = names["caller"];

    let (call_inst, call_args): (InstId, SmallVec<[ValueId; 8]>) =
        parsed.module.func_store.view(caller, |function| {
            for block in function.layout.iter_block() {
                for inst in function.layout.iter_inst(block) {
                    let Some(call) = function.dfg.cast_call(inst) else {
                        continue;
                    };
                    return (inst, call.args().clone());
                }
            }
            panic!("missing call inst");
        });

    assert_eq!(call_args.len(), 2, "test expects a 2-arg call");

    let stack_alloc = stack_allocs
        .remove(&caller)
        .expect("missing caller analysis");
    let semantic_plan = plan.funcs.get(&caller).expect("missing caller plan");
    // These tests run on source IR with an identity inst mapping, so the
    // semantic call_preserve keys are already the "machine" keys.
    let mem_plan = memory_plan::MachineFuncPlan {
        arena_base: semantic_plan.arena_base,
        scratch_words: semantic_plan.scratch_words,
        stable_words: semantic_plan.stable_words,
        stable_mode: semantic_plan.stable_mode,
        entry_abs_words: semantic_plan.entry_abs_words,
        obj_loc: semantic_plan.obj_loc.clone(),
        alloca_loc: semantic_plan.alloca_loc.clone(),
        spill_obj: Default::default(),
        call_preserve: semantic_plan.call_preserve.clone(),
    };
    let alloc = FinalAlloc::new(stack_alloc, mem_plan);

    let save_plan = alloc
        .mem_plan
        .call_preserve
        .get(&call_inst)
        .expect("expected non-empty call preserve entry for call");
    let (shadow_obj, runs) = (&save_plan.shadow_obj, &save_plan.runs);
    assert!(!runs.is_empty(), "expected at least one saved run");

    let actions = alloc.read(call_inst, &call_args);
    let cont_pos = actions
        .iter()
        .position(|a| matches!(a, Action::PushContinuationOffset))
        .expect("missing continuation marker");

    let expected_len = runs
        .iter()
        .map(|run| usize::try_from(run.len_words).expect("run length overflow"))
        .sum::<usize>()
        .checked_mul(2)
        .expect("expected injected length overflow");
    assert!(
        cont_pos >= expected_len,
        "expected injected actions immediately before continuation marker"
    );
    let injected = &actions[cont_pos - expected_len..cont_pos];
    let shadow_loc = alloc.obj_loc_for_id(*shadow_obj);
    let mut expected = Actions::new();
    for run in runs {
        for word in 0..run.len_words {
            expected
                .push(alloc.action_load_for_loc(ObjLoc::ScratchAbs(run.scratch_src_word), word));
            expected.push(
                alloc.action_store_for_loc(
                    shadow_loc,
                    run.shadow_dst_word
                        .checked_add(word)
                        .expect("shadow save offset overflow"),
                ),
            );
        }
    }
    assert_eq!(injected, expected.as_slice());
}

#[test]
fn call_save_post_preserves_two_results_above_saved_words() {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

func public %caller(v0.i256, v1.i256) -> (i256, i1) {
block0:
    v2.*i256 = alloca i256;
    mstore v2 1.i256 i256;
    v3.i256 = mload v2 i256;
    v4.i256 = add v3 v0;
    mstore v2 v4 i256;
    (v5.i256, v6.i1) = call %caller 11.i256 22.i256;
    v7.i256 = mload v2 i256;
    br v6 block1 block2;

block1:
    v8.i256 = add v5 v7;
    return (v8, v6);

block2:
    v9.i256 = add v7 1.i256;
    return (v9, v6);
}
"#,
    )
    .unwrap();

    let funcs = parsed.module.funcs();
    let isa = Evm::new(TargetTriple {
        architecture: Architecture::Evm,
        vendor: Vendor::Ethereum,
        operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
    });
    let ptr_escape = compute_ptr_escape_summaries(&parsed.module, &funcs, &isa);

    let backend = EvmBackend::new(isa);
    let mut pre_analyses: FxHashMap<FuncRef, memory_plan::FuncPreAnalysis> = FxHashMap::default();
    let mut stack_allocs: FxHashMap<FuncRef, StackifyAlloc> = FxHashMap::default();
    for &func in &funcs {
        parsed.module.func_store.modify(func, |function| {
            pre_analyses.insert(
                func,
                compute_test_pre_analysis(function, &parsed.module.ctx, &backend, &ptr_escape),
            );
            stack_allocs.insert(func, compute_test_stackify_alloc(function));
        });
    }

    let cost_model = ArenaCostModel {
        w_save: 0,
        w_code: 0,
        ..ArenaCostModel::default()
    };
    let plan = compute_semantic_program_memory_plan(
        &parsed.module,
        &crate::module_analysis::CallGraphSchedule::compute(&parsed.module, &funcs),
        &pre_analyses,
        &ptr_escape,
        &isa,
        &cost_model,
    );

    let mut names: FxHashMap<String, FuncRef> = FxHashMap::default();
    for &f in &funcs {
        let name = parsed.module.ctx.func_sig(f, |sig| sig.name().to_string());
        names.insert(name, f);
    }
    let caller = names["caller"];

    let (call_inst, call_results): (InstId, SmallVec<[ValueId; 8]>) =
        parsed.module.func_store.view(caller, |function| {
            for block in function.layout.iter_block() {
                for inst in function.layout.iter_inst(block) {
                    if function.dfg.call_info(inst).is_none() {
                        continue;
                    }
                    return (
                        inst,
                        function.dfg.inst_results(inst).iter().copied().collect(),
                    );
                }
            }
            panic!("missing call inst");
        });

    let stack_alloc = stack_allocs
        .remove(&caller)
        .expect("missing caller analysis");
    let semantic_plan = plan.funcs.get(&caller).expect("missing caller plan");
    // These tests run on source IR with an identity inst mapping, so the
    // semantic call_preserve keys are already the "machine" keys.
    let mem_plan = memory_plan::MachineFuncPlan {
        arena_base: semantic_plan.arena_base,
        scratch_words: semantic_plan.scratch_words,
        stable_words: semantic_plan.stable_words,
        stable_mode: semantic_plan.stable_mode,
        entry_abs_words: semantic_plan.entry_abs_words,
        obj_loc: semantic_plan.obj_loc.clone(),
        alloca_loc: semantic_plan.alloca_loc.clone(),
        spill_obj: Default::default(),
        call_preserve: semantic_plan.call_preserve.clone(),
    };
    let alloc = FinalAlloc::new(stack_alloc, mem_plan);

    let save_plan = alloc
        .mem_plan
        .call_preserve
        .get(&call_inst)
        .expect("expected non-empty call preserve entry for call");
    assert_eq!(save_plan.result_count, 2);
    let (shadow_obj, runs) = (&save_plan.shadow_obj, &save_plan.runs);
    assert!(!runs.is_empty(), "expected at least one saved run");

    let actions = alloc.write(call_inst, &call_results);
    let mut expected = Actions::new();
    let shadow_loc = alloc.obj_loc_for_id(*shadow_obj);
    for run in runs.iter().rev() {
        for word in (0..run.len_words).rev() {
            expected.push(
                alloc.action_load_for_loc(
                    shadow_loc,
                    run.shadow_dst_word
                        .checked_add(word)
                        .expect("shadow restore offset overflow"),
                ),
            );
            expected
                .push(alloc.action_store_for_loc(ObjLoc::ScratchAbs(run.scratch_src_word), word));
        }
    }
    assert_eq!(
        actions.as_slice(),
        expected.as_slice(),
        "multi-result call preserve restore must copy saved scratch words back after post-actions"
    );
}

#[test]
fn prune_removes_and_one_after_bool_producer() {
    let mut vcode = VCode::<OpCode>::default();
    let block = BlockId(0);

    vcode.add_inst_to_block(OpCode::LT, None, block);
    let push = vcode.add_inst_to_block(OpCode::PUSH1, None, block);
    vcode.inst_imm_bytes.insert((push, smallvec![1u8]));
    vcode.add_inst_to_block(OpCode::AND, None, block);

    prune_redundant_opcode_sequences(&mut vcode, &[block]);

    let ops: Vec<_> = vcode
        .block_insns(block)
        .map(|inst| vcode.insts[inst] as u8)
        .collect();
    assert_eq!(ops, vec![OpCode::LT as u8]);
}

#[test]
fn prune_keeps_and_mask_when_not_bool_producer() {
    let mut vcode = VCode::<OpCode>::default();
    let block = BlockId(0);

    vcode.add_inst_to_block(OpCode::ADD, None, block);
    let push = vcode.add_inst_to_block(OpCode::PUSH1, None, block);
    vcode.inst_imm_bytes.insert((push, smallvec![1u8]));
    vcode.add_inst_to_block(OpCode::AND, None, block);

    prune_redundant_opcode_sequences(&mut vcode, &[block]);

    let ops: Vec<_> = vcode
        .block_insns(block)
        .map(|inst| vcode.insts[inst] as u8)
        .collect();
    assert_eq!(
        ops,
        vec![OpCode::ADD as u8, OpCode::PUSH1 as u8, OpCode::AND as u8]
    );
}

#[test]
fn prune_keeps_and_mask_when_mask_not_one() {
    let mut vcode = VCode::<OpCode>::default();
    let block = BlockId(0);

    vcode.add_inst_to_block(OpCode::EQ, None, block);
    let push = vcode.add_inst_to_block(OpCode::PUSH1, None, block);
    vcode.inst_imm_bytes.insert((push, smallvec![3u8]));
    vcode.add_inst_to_block(OpCode::AND, None, block);

    prune_redundant_opcode_sequences(&mut vcode, &[block]);

    let ops: Vec<_> = vcode
        .block_insns(block)
        .map(|inst| vcode.insts[inst] as u8)
        .collect();
    assert_eq!(
        ops,
        vec![OpCode::EQ as u8, OpCode::PUSH1 as u8, OpCode::AND as u8]
    );
}

#[test]
fn prune_removes_iszero_iszero_before_labeled_jumpi() {
    let mut vcode = VCode::<OpCode>::default();
    let block = BlockId(0);

    vcode.add_inst_to_block(OpCode::ISZERO, None, block);
    vcode.add_inst_to_block(OpCode::ISZERO, None, block);
    let push = vcode.add_inst_to_block(OpCode::PUSH1, None, block);
    vcode.add_inst_to_block(OpCode::JUMPI, None, block);

    let label = vcode.labels.push(Label::Block(BlockId(1)));
    vcode.fixups.insert((push, VCodeFixup::Label(label)));

    prune_redundant_opcode_sequences(&mut vcode, &[block]);

    let ops: Vec<_> = vcode
        .block_insns(block)
        .map(|inst| vcode.insts[inst] as u8)
        .collect();
    assert_eq!(ops, vec![OpCode::PUSH1 as u8, OpCode::JUMPI as u8]);
}

#[test]
fn prune_keeps_iszero_iszero_before_non_labeled_jumpi() {
    let mut vcode = VCode::<OpCode>::default();
    let block = BlockId(0);

    vcode.add_inst_to_block(OpCode::ISZERO, None, block);
    vcode.add_inst_to_block(OpCode::ISZERO, None, block);
    let push = vcode.add_inst_to_block(OpCode::PUSH1, None, block);
    vcode.inst_imm_bytes.insert((push, smallvec![7u8]));
    vcode.add_inst_to_block(OpCode::JUMPI, None, block);

    prune_redundant_opcode_sequences(&mut vcode, &[block]);

    let ops: Vec<_> = vcode
        .block_insns(block)
        .map(|inst| vcode.insts[inst] as u8)
        .collect();
    assert_eq!(
        ops,
        vec![
            OpCode::ISZERO as u8,
            OpCode::ISZERO as u8,
            OpCode::PUSH1 as u8,
            OpCode::JUMPI as u8
        ]
    );
}

#[test]
fn link_section_resolves_sym_fixups_in_late_outlined_helper() {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

func private %a(v0.i1) {
block0:
    br v0 block1 block2;

block1:
    jump block3;

block2:
    evm_invalid;

block3:
    v1.i256 = sym_addr .;
    v2.i256 = sym_size .;
    mstore 0.i256 v1 i256;
    mstore 32.i256 v2 i256;
    evm_return 0.i256 64.i256;
}

func private %b(v0.i1) {
block0:
    br v0 block1 block2;

block1:
    jump block3;

block2:
    evm_invalid;

block3:
    v3.i256 = sym_addr .;
    v4.i256 = sym_size .;
    mstore 0.i256 v3 i256;
    mstore 32.i256 v4 i256;
    evm_return 0.i256 64.i256;
}

func public %main(v0.i1) {
block0:
    br v0 block1 block2;

block1:
    call %a 1.i1;
    return;

block2:
    call %b 1.i1;
    return;
}
"#,
    )
    .expect("module parses");
    let backend = test_backend().with_late_cleanup_profile(LateCleanupProfile::Speed);
    let entry = find_func(&parsed.module, "main");
    let prepared = backend
        .prepare_section(work_module_with_entry(&parsed.module, &[entry], entry))
        .expect("prepare should succeed");
    let mut lowered_funcs: Vec<_> = prepared
        .funcs()
        .iter()
        .map(|&func| {
            (
                func,
                backend
                    .lower_function(&prepared, func)
                    .expect("lowering should succeed"),
            )
        })
        .collect();
    let section_units = backend
        .post_lower_section(&prepared, &mut lowered_funcs)
        .expect("late outlining should succeed");

    assert_eq!(section_units.len(), 1, "expected one outlined helper");
    let helper_fixups: Vec<_> = section_units[0]
        .vcode
        .fixups
        .values()
        .filter_map(|(_, fixup)| match fixup {
            VCodeFixup::Sym(sym) => Some((sym.kind.clone(), sym.sym.clone())),
            VCodeFixup::Label(_) => None,
        })
        .collect();
    assert!(
        helper_fixups.iter().any(
            |(kind, sym)| *kind == crate::machinst::vcode::SymFixupKind::Addr
                && *sym == sonatina_ir::inst::data::SymbolRef::CurrentSection
        ),
        "outlined helper must retain current-section address fixup: {helper_fixups:?}"
    );
    assert!(
        helper_fixups.iter().any(
            |(kind, sym)| *kind == crate::machinst::vcode::SymFixupKind::Size
                && *sym == sonatina_ir::inst::data::SymbolRef::CurrentSection
        ),
        "outlined helper must retain current-section size fixup: {helper_fixups:?}"
    );

    let artifact = link_section(
        &backend,
        &prepared,
        &[],
        &[],
        &SectionName("runtime".into()),
        &CompileOptions {
            fixup_policy: PushWidthPolicy::Push4,
            emit_symtab: true,
            ..CompileOptions::default()
        },
    )
    .expect("linking should resolve outlined helper symbol fixups");
    let current = artifact
        .symtab
        .get(&SymbolId::CurrentSection)
        .expect("current-section symbol missing");
    let offset = current.offset.to_be_bytes();
    let size = current.size.to_be_bytes();
    assert!(
        artifact
            .bytes
            .windows(offset.len())
            .any(|window| window == offset),
        "linked section must contain the resolved current-section address"
    );
    assert!(
        artifact
            .bytes
            .windows(size.len())
            .any(|window| window == size),
        "linked section must contain the resolved current-section size"
    );
}
