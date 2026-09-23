use sonatina_codegen::{domtree::DomTree, loop_analysis::LoopTree, optim::code_sink::CodeSink};
use sonatina_ir::{
    ControlFlowGraph,
    inst::{downcast, evm::EvmCalldataLoad},
    ir_writer::ModuleWriter,
};
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module_or_panic};

#[test]
fn calldata_sinking_preserves_effects_and_is_idempotent() {
    let parsed = sonatina_parser::parse_module(include_str!(
        "../../filecheck/fixtures/code_sink/calldata.sntn"
    ))
    .unwrap();
    let module = parsed.module;
    let config = VerifierConfig::for_level(VerificationLevel::Full);
    verify_module_or_panic(&module, &config);
    let before = ModuleWriter::new(&module).dump_string();
    for func_ref in module.funcs() {
        module.func_store.modify(func_ref, |func| {
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);
            let mut domtree = DomTree::new();
            domtree.compute(&cfg);
            let mut loops = LoopTree::new();
            loops.compute(&cfg, &domtree);
            let instructions = func
                .layout
                .iter_block()
                .flat_map(|block| func.layout.iter_inst(block))
                .count();
            let mut sink = CodeSink::new();
            sink.run(func, &cfg, &domtree, &loops);
            assert!(
                !sink.run(func, &cfg, &domtree, &loops),
                "sinking must converge in one run"
            );
            assert_eq!(
                instructions,
                func.layout
                    .iter_block()
                    .flat_map(|block| func.layout.iter_inst(block))
                    .count()
            );
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    if downcast::<&EvmCalldataLoad>(func.inst_set(), func.dfg.inst(inst)).is_some()
                    {
                        assert!(func.dfg.effect_summary(inst).may_read_memory());
                        assert!(!func.dfg.can_speculate(inst));
                    }
                }
            }
        });
    }
    verify_module_or_panic(&module, &config);
    assert_ne!(
        before,
        ModuleWriter::new(&module).dump_string(),
        "the fixture must exercise sinking"
    );
}
