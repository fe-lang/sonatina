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
    stackalloc::{Action, Actions, Allocator, StackifyBuilder},
};
use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    BlockId, Directive, Immediate, InstId, InstSetBase, InstSetExt, Module, ValueId,
    cfg::ControlFlowGraph, inst::evm::inst_set::EvmInstKind, ir_writer::FuncWriter, isa::Isa,
    object::SectionName,
};
use sonatina_parser::parse_module;
use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

use self::{
    dyn_sp::{DynSpInitKind, DynSpPlan, compute_dyn_sp_plan},
    emit::{
        FinalAlloc, materialize_jumpdests, prune_redundant_opcode_sequences,
        rewrite_evm_local_fallthrough_layout,
    },
    memory_plan::{
        ArenaCostModel, ProgramMemoryPlan, compute_abs_clobber_words, compute_program_memory_plan,
    },
    prepare::compute_return_escape_caller_clamp_words,
};

struct PlanTestCtx {
    module: sonatina_ir::Module,
    funcs: Vec<FuncRef>,
    names: FxHashMap<String, FuncRef>,
    plan: ProgramMemoryPlan,
    analyses: FxHashMap<FuncRef, memory_plan::FuncAnalysis>,
}

struct DynSpTestCtx {
    module: sonatina_ir::Module,
    names: FxHashMap<String, FuncRef>,
    plan: DynSpPlan,
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

    let mut analyses: FxHashMap<FuncRef, memory_plan::FuncAnalysis> = FxHashMap::default();
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
                memory_plan::FuncAnalysis {
                    alloc: StackifyBuilder::new(function, &cfg, &dom, &liveness, 16).compute(),
                    inst_liveness,
                    block_order: dom.rpo().to_vec(),
                    value_aliases: {
                        let mut value_aliases = SecondaryMap::new();
                        for value in function.dfg.value_ids() {
                            value_aliases[value] = Some(value);
                        }
                        value_aliases
                    },
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
        analyses,
    }
}

fn dyn_sp_plan_from_src(src: &str) -> DynSpTestCtx {
    let ctx = plan_test_ctx_from_src(src);
    let isa = Evm::new(TargetTriple {
        architecture: Architecture::Evm,
        vendor: Vendor::Ethereum,
        operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
    });
    let section_entry = ctx
        .module
        .objects
        .values()
        .find_map(|object| {
            object.sections.iter().find_map(|section| {
                section
                    .directives
                    .iter()
                    .find_map(|directive| match directive {
                        Directive::Entry(func) => Some(*func),
                        Directive::Include(_) | Directive::Data(_) | Directive::Embed(_) => None,
                    })
            })
        })
        .unwrap_or(ctx.funcs[0]);
    let dyn_sp_plan = compute_dyn_sp_plan(
        &ctx.module,
        &ctx.funcs,
        section_entry,
        &ctx.plan,
        &ctx.analyses,
        &isa,
    );

    DynSpTestCtx {
        module: ctx.module,
        names: ctx.names,
        plan: dyn_sp_plan,
    }
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

fn rewrite_local_fallthrough_order_from_src(
    src: &str,
    func_name: &str,
    block_order: &[u32],
) -> Vec<u32> {
    let parsed = parse_module(src).expect("module parses");
    let func = find_func(&parsed.module, func_name);
    let block_order: Vec<_> = block_order.iter().copied().map(BlockId).collect();

    parsed.module.func_store.view(func, |function| {
        rewrite_evm_local_fallthrough_layout(function, &FxHashMap::default(), block_order)
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
fn local_fallthrough_layout_skips_nonterminal_exits() {
    let order = rewrite_local_fallthrough_order_from_src(
        HOT_LOOP_NONTERMINAL_EXIT_SRC,
        "main",
        &[0, 3, 1, 4, 2],
    );

    assert_eq!(order, vec![0, 3, 1, 4, 2]);
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
fn fold_stack_actions_cancels_push_swap1_pop_noop() {
    let actions = [
        Action::Push(Immediate::I8(7)),
        Action::StackSwap(1),
        Action::Pop,
    ];
    let folded = fold_stack_actions(&actions);
    assert!(folded.is_empty());
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
fn dyn_sp_entry_init_covers_ready_recursive_entry_scc() {
    let ctx = dyn_sp_plan_from_src(
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
    );

    let f = ctx.names["f"];
    assert_eq!(ctx.plan.entry_init, Some(DynSpInitKind::Checked));
    assert!(
        ctx.plan
            .frontier_init_calls
            .get(&f)
            .is_none_or(FxHashSet::is_empty)
    );
    assert!(ctx.plan.entry_live_frame[&f]);
}

#[test]
fn recursive_entry_lowering_checks_dyn_sp_before_reinit() {
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

    let lowered = backend
        .lower_function(&prepared, f)
        .expect("function lowers");
    let first_mem_op = first_memory_op(&lowered).expect("entry lowering should touch dyn_sp");

    assert_eq!(
        first_mem_op,
        OpCode::MLOAD as u8,
        "recursive entry lowering must guard dyn_sp init before writing it"
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
    let abs_clobber_words = compute_abs_clobber_words(&ctx.module, &ctx.funcs, &ctx.plan);
    let clamp_words = compute_return_escape_caller_clamp_words(&ctx.module, &ctx.funcs, &ctx.plan);
    let main_active_words = ctx.plan.funcs[&main].active_abs_words();
    let main_clobber_words = abs_clobber_words[&main];

    assert!(
        main_clobber_words > main_active_words,
        "test setup requires a caller whose future callee clobber exceeds its own active frame"
    );
    assert_eq!(clamp_words[&mk], main_clobber_words);
}

#[test]
fn dyn_sp_frontier_init_marks_call_from_non_ready_entry_into_ready_scc() {
    let ctx = dyn_sp_plan_from_src(
        r#"
target = "evm-ethereum-osaka"

func public %dispatch(v0.i1, v1.i256) -> i256 {
block0:
    br v0 block1 block2;

block1:
    v2.*i8 = evm_malloc 32.i256;
    v3.*i256 = bitcast v2 *i256;
    mstore v3 111.i256 i256;
    v4.i256 = mload v3 i256;
    return v4;

block2:
    v5.i256 = call %ready v1;
    return v5;
}

func private %ready(v0.i256) -> i256 {
block0:
    v1.i1 = eq v0 0.i256;
    br v1 block1 block2;

block1:
    return 7.i256;

block2:
    v2.*i256 = alloca i256;
    mstore v2 v0 i256;
    v3.i256 = sub v0 1.i256;
    v4.i256 = call %ready v3;
    v5.i256 = mload v2 i256;
    v6.i256 = add v4 v5;
    return v6;
}
"#,
    );

    let dispatch = ctx.names["dispatch"];
    let ready = ctx.names["ready"];
    let frontier_calls = ctx
        .plan
        .frontier_init_calls
        .get(&dispatch)
        .expect("dispatch should have a frontier init call");
    let call_inst = ctx.module.func_store.view(dispatch, |function| {
        function
            .layout
            .iter_block()
            .flat_map(|block| function.layout.iter_inst(block))
            .find(|&inst| {
                function
                    .dfg
                    .call_info(inst)
                    .is_some_and(|call| call.callee() == ready)
            })
            .expect("call to ready")
    });

    assert_eq!(ctx.plan.entry_init, None);
    assert!(frontier_calls.contains(&call_inst));
    assert!(
        ctx.plan
            .checked_frontier_init_calls
            .get(&dispatch)
            .is_none_or(|calls| !calls.contains(&call_inst))
    );
}

#[test]
fn dyn_sp_entry_live_frame_propagates_only_from_active_callsites() {
    let ctx = dyn_sp_plan_from_src(
        r#"
target = "evm-ethereum-osaka"

func public %ready(v0.i1, v1.i256) -> i256 {
block0:
    br v0 block1 block2;

block1:
    v2.i256 = call %helper;
    return v2;

block2:
    v3.i1 = eq v1 0.i256;
    br v3 block3 block4;

block3:
    return 0.i256;

block4:
    v4.*i256 = alloca i256;
    mstore v4 v1 i256;
    v5.i256 = call %helper;
    v6.i256 = sub v1 1.i256;
    v7.i256 = call %ready 0.i1 v6;
    v8.i256 = mload v4 i256;
    v9.i256 = add v5 v8;
    return v9;
}

func private %helper() -> i256 {
block0:
    v0.*i8 = evm_malloc 32.i256;
    v1.*i256 = bitcast v0 *i256;
    mstore v1 111.i256 i256;
    v2.i256 = mload v1 i256;
    return v2;
}
"#,
    );

    let ready = ctx.names["ready"];
    let helper = ctx.names["helper"];
    let helper_calls: Vec<InstId> = ctx.module.func_store.view(ready, |function| {
        function
            .layout
            .iter_block()
            .flat_map(|block| function.layout.iter_inst(block))
            .filter(|&inst| {
                function
                    .dfg
                    .call_info(inst)
                    .is_some_and(|call| call.callee() == helper)
            })
            .collect()
    });
    assert_eq!(
        helper_calls.len(),
        2,
        "expected one cold and one hot helper call"
    );

    let summary = ctx
        .plan
        .frame_summaries
        .get(&ready)
        .expect("missing ready summary");
    let active_count = helper_calls
        .iter()
        .copied()
        .filter(|&inst| summary.local_frame_active_before_inst(inst))
        .count();

    assert_eq!(
        active_count, 1,
        "only the hot helper call should be frame-active"
    );
    assert!(ctx.plan.entry_live_frame[&helper]);
}

#[test]
fn dyn_sp_helper_before_lazy_enter_stays_not_live() {
    let ctx = dyn_sp_plan_from_src(
        r#"
target = "evm-ethereum-osaka"

func public %helper() -> i256 {
block0:
    v0.*i8 = evm_malloc 32.i256;
    v1.*i256 = bitcast v0 *i256;
    mstore v1 111.i256 i256;
    v2.i256 = mload v1 i256;
    return v2;
}

func public %ready(v0.i1, v1.i256) -> i256 {
block0:
    br v0 block1 block2;

block1:
    v2.i256 = call %helper;
    return v2;

block2:
    v3.*i256 = alloca i256;
    mstore v3 v1 i256;
    v4.i256 = mload v3 i256;
    return v4;
}

func public %entry(v0.i1, v1.i256) -> i256 {
block0:
    v2.i256 = call %ready v0 v1;
    return v2;
}

object @Contract {
  section runtime {
    entry %entry;
  }
}
"#,
    );

    let helper = ctx.names["helper"];
    let ready = ctx.names["ready"];
    let ready_summary = ctx
        .plan
        .frame_summaries
        .get(&ready)
        .expect("missing ready summary");
    let helper_call = ctx.module.func_store.view(ready, |function| {
        function
            .layout
            .iter_block()
            .flat_map(|block| function.layout.iter_inst(block))
            .find(|&inst| {
                function
                    .dfg
                    .call_info(inst)
                    .is_some_and(|call| call.callee() == helper)
            })
            .expect("call to helper")
    });

    assert!(
        !ready_summary.local_frame_active_before_inst(helper_call),
        "helper call should stay before lazy frame entry"
    );
    assert!(!ctx.plan.entry_live_frame[&helper]);
}

#[test]
fn dyn_sp_mixed_entry_helper_uses_checked_frontier_init() {
    let ctx = dyn_sp_plan_from_src(
        r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i1, v1.i256) -> i256 {
block0:
    br v0 block1 block2;

block1:
    v2.i256 = call %helper v1;
    return v2;

block2:
    v3.i256 = call %ready_caller v1;
    return v3;
}

func private %helper(v0.i256) -> i256 {
block0:
    v1.i256 = call %target v0;
    return v1;
}

func private %ready_caller(v0.i256) -> i256 {
block0:
    v1.i1 = eq v0 0.i256;
    br v1 block1 block2;

block1:
    return 0.i256;

block2:
    v2.*i256 = alloca i256;
    mstore v2 v0 i256;
    v3.i256 = call %helper 0.i256;
    v4.i256 = sub v0 1.i256;
    v5.i256 = call %ready_caller v4;
    v6.i256 = mload v2 i256;
    v7.i256 = add v3 v5;
    v8.i256 = add v7 v6;
    return v8;
}

func private %target(v0.i256) -> i256 {
block0:
    v1.i1 = eq v0 0.i256;
    br v1 block1 block2;

block1:
    return 0.i256;

block2:
    v2.*i256 = alloca i256;
    mstore v2 v0 i256;
    v3.i256 = sub v0 1.i256;
    v4.i256 = call %target v3;
    v5.i256 = mload v2 i256;
    v6.i256 = add v4 v5;
    return v6;
}
"#,
    );

    let helper = ctx.names["helper"];
    let target = ctx.names["target"];
    let helper_call = ctx.module.func_store.view(helper, |function| {
        function
            .layout
            .iter_block()
            .flat_map(|block| function.layout.iter_inst(block))
            .find(|&inst| {
                function
                    .dfg
                    .call_info(inst)
                    .is_some_and(|call| call.callee() == target)
            })
            .expect("helper call to target")
    });

    assert!(
        ctx.plan
            .frontier_init_calls
            .get(&helper)
            .is_some_and(|calls| calls.contains(&helper_call))
    );
    assert!(
        ctx.plan
            .checked_frontier_init_calls
            .get(&helper)
            .is_some_and(|calls| calls.contains(&helper_call))
    );
}

#[test]
fn dyn_sp_plan_is_deterministic_across_runs() {
    let src = r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i256) -> i256 {
block0:
    v1.i1 = eq v0 0.i256;
    br v1 block1 block2;

block1:
    v2.i256 = call %helper 4.i256;
    return v2;

block2:
    v3.i256 = call %ready_caller v0;
    return v3;
}

func private %helper(v0.i256) -> i256 {
block0:
    v1.i1 = eq v0 0.i256;
    br v1 block1 block2;

block1:
    return 0.i256;

block2:
    v2.*i256 = alloca i256;
    mstore v2 v0 i256;
    v3.i256 = call %ready_caller v0;
    v4.i256 = sub v0 1.i256;
    v5.i256 = call %target v4;
    v6.i256 = mload v2 i256;
    v7.i256 = add v3 v5;
    v8.i256 = add v7 v6;
    return v8;
}

func private %ready_caller(v0.i256) -> i256 {
block0:
    v1.i1 = eq v0 0.i256;
    br v1 block1 block2;

block1:
    return 0.i256;

block2:
    v2.*i256 = alloca i256;
    mstore v2 v0 i256;
    v3.i256 = call %target v0;
    v4.i256 = mload v2 i256;
    v5.i256 = add v3 v4;
    return v5;
}

func private %target(v0.i256) -> i256 {
block0:
    v1.i1 = eq v0 0.i256;
    br v1 block1 block2;

block1:
    return 0.i256;

block2:
    v2.*i256 = alloca i256;
    mstore v2 v0 i256;
    v3.i256 = sub v0 1.i256;
    v4.i256 = call %target v3;
    v5.i256 = mload v2 i256;
    v6.i256 = add v4 v5;
    return v6;
}

object @Contract {
  section runtime {
    entry %entry;
  }
}
"#;

    let mut expected_frontier_init_calls = None;
    let mut expected_checked_frontier_init_calls = None;
    let mut expected_entry_init = None;
    let mut expected_entry_live_frame = None;
    let mut expected_frame_summaries = None;

    for _ in 0..8 {
        let plan = dyn_sp_plan_from_src(src).plan;
        if let Some(expected) = &expected_frontier_init_calls {
            assert_eq!(
                &plan.frontier_init_calls, expected,
                "frontier init calls changed across runs"
            );
        } else {
            expected_frontier_init_calls = Some(plan.frontier_init_calls.clone());
        }
        if let Some(expected) = &expected_checked_frontier_init_calls {
            assert_eq!(
                &plan.checked_frontier_init_calls, expected,
                "checked frontier init calls changed across runs"
            );
        } else {
            expected_checked_frontier_init_calls = Some(plan.checked_frontier_init_calls.clone());
        }
        if let Some(expected) = expected_entry_init {
            assert_eq!(plan.entry_init, expected, "entry init changed across runs");
        } else {
            expected_entry_init = Some(plan.entry_init);
        }
        if let Some(expected) = &expected_entry_live_frame {
            assert_eq!(
                &plan.entry_live_frame, expected,
                "entry live frame changed across runs"
            );
        } else {
            expected_entry_live_frame = Some(plan.entry_live_frame.clone());
        }
        if let Some(expected) = &expected_frame_summaries {
            assert_eq!(
                &plan.frame_summaries, expected,
                "frame summaries changed across runs"
            );
        } else {
            expected_frame_summaries = Some(plan.frame_summaries.clone());
        }
    }
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

    let mut analyses: FxHashMap<FuncRef, memory_plan::FuncAnalysis> = FxHashMap::default();
    for &func in &funcs {
        parsed.module.func_store.modify(func, |function| {
            let mut cfg = ControlFlowGraph::new();
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
                memory_plan::FuncAnalysis {
                    alloc: StackifyBuilder::new(function, &cfg, &dom, &liveness, 16).compute(),
                    inst_liveness,
                    block_order: dom.rpo().to_vec(),
                    value_aliases: {
                        let mut value_aliases = SecondaryMap::new();
                        for value in function.dfg.value_ids() {
                            value_aliases[value] = Some(value);
                        }
                        value_aliases
                    },
                },
            );
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

    let actions = analyses
        .get(&caller)
        .expect("missing caller analysis")
        .alloc
        .read(call_inst, &call_args);
    assert!(
        !actions
            .iter()
            .any(|a| matches!(a, Action::PushContinuationOffset)),
        "noreturn call should not materialize a local continuation: {actions:?}"
    );

    let plan = compute_program_memory_plan(
        &parsed.module,
        &funcs,
        &analyses,
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
    let before = count_insts(&before);
    let after = count_insts(&after);

    assert!(
        !before_dump.contains("obj."),
        "mandatory lowering must still remove object IR when optional cleanup is off:\n{before_dump}"
    );
    assert!(
        after < before,
        "late raw-memory cleanup should reduce prepared IR after memory legalization (before={before}, after={after})"
    );
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

    let mut analyses: FxHashMap<FuncRef, memory_plan::FuncAnalysis> = FxHashMap::default();
    for &func in &funcs {
        parsed.module.func_store.modify(func, |function| {
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(function);

            let mut splitter = CriticalEdgeSplitter::new();
            splitter.run(function, &mut cfg);

            let mut liveness = Liveness::new();
            liveness.compute(function, &cfg);

            let mut inst_liveness = InstLiveness::new();
            inst_liveness.compute(function, &cfg, &liveness);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let block_order = dom.rpo().to_owned();
            let alloc = StackifyBuilder::new(function, &cfg, &dom, &liveness, 16).compute();

            analyses.insert(
                func,
                memory_plan::FuncAnalysis {
                    alloc,
                    inst_liveness,
                    block_order,
                    value_aliases: {
                        let mut value_aliases = SecondaryMap::new();
                        for value in function.dfg.value_ids() {
                            value_aliases[value] = Some(value);
                        }
                        value_aliases
                    },
                },
            );
        });
    }

    let cost_model = ArenaCostModel {
        w_save: 0,
        w_code: 0,
        ..ArenaCostModel::default()
    };
    let plan = compute_program_memory_plan(
        &parsed.module,
        &funcs,
        &analyses,
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

    let analysis = analyses.remove(&caller).expect("missing caller analysis");
    let mem_plan = plan
        .funcs
        .get(&caller)
        .expect("missing caller plan")
        .clone();
    let alloc = FinalAlloc::new(analysis.alloc, mem_plan);

    let save_plan = alloc
        .mem_plan
        .call_preserve
        .get(&call_inst)
        .expect("expected non-empty call preserve entry for call");
    let PreserveMode::ShadowRuns { shadow_obj, runs } = &save_plan.mode else {
        panic!("expected shadow preserve plan for caller");
    };
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

    let mut analyses: FxHashMap<FuncRef, memory_plan::FuncAnalysis> = FxHashMap::default();
    for &func in &funcs {
        parsed.module.func_store.modify(func, |function| {
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(function);

            let mut splitter = CriticalEdgeSplitter::new();
            splitter.run(function, &mut cfg);

            let mut liveness = Liveness::new();
            liveness.compute(function, &cfg);

            let mut inst_liveness = InstLiveness::new();
            inst_liveness.compute(function, &cfg, &liveness);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let block_order = dom.rpo().to_owned();
            let alloc = StackifyBuilder::new(function, &cfg, &dom, &liveness, 16).compute();

            analyses.insert(
                func,
                memory_plan::FuncAnalysis {
                    alloc,
                    inst_liveness,
                    block_order,
                    value_aliases: {
                        let mut value_aliases = SecondaryMap::new();
                        for value in function.dfg.value_ids() {
                            value_aliases[value] = Some(value);
                        }
                        value_aliases
                    },
                },
            );
        });
    }

    let cost_model = ArenaCostModel {
        w_save: 0,
        w_code: 0,
        ..ArenaCostModel::default()
    };
    let plan = compute_program_memory_plan(
        &parsed.module,
        &funcs,
        &analyses,
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

    let analysis = analyses.remove(&caller).expect("missing caller analysis");
    let mem_plan = plan
        .funcs
        .get(&caller)
        .expect("missing caller plan")
        .clone();
    let alloc = FinalAlloc::new(analysis.alloc, mem_plan);

    let save_plan = alloc
        .mem_plan
        .call_preserve
        .get(&call_inst)
        .expect("expected non-empty call preserve entry for call");
    assert_eq!(save_plan.result_count, 2);
    let PreserveMode::ShadowRuns { shadow_obj, runs } = &save_plan.mode else {
        panic!("expected shadow preserve plan for caller");
    };
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
    let backend = test_backend();
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
        &CompileOptions::default(),
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
