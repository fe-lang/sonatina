use std::{hint::black_box, time::Instant};

use sonatina_codegen::{
    domtree::DomTree,
    optim::{
        aggregate::{AggregateCombine, AggregateScalarize},
        gvn::GvnSolver,
        sccp::SccpSolver,
    },
};
use sonatina_ir::{ControlFlowGraph, Module, ir_writer::ModuleWriter};
use sonatina_parser::parse_module;
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module_or_panic};

fn insert_chain_module(
    length: usize,
    stages: usize,
    reconstruct: bool,
    reverse_layout: bool,
) -> Module {
    let mut source = format!(
        "target = \"evm-ethereum-osaka\"\nfunc private %f(v0.[i8; {length}], v1.i8) -> [i8; {length}] {{\nblock0:\njump block1;\n"
    );
    let mut previous = "v0".to_string();
    let mut blocks = Vec::new();
    let mut next = 2;
    for stage in 0..stages {
        let block = stage + 1;
        let mut body = format!("block{block}:\n");
        let mut aggregate = format!("undef.[i8; {length}]");
        for index in 0..length {
            let field = next;
            let result = next + 1;
            next += 2;
            if reconstruct {
                body.push_str(&format!(
                    "v{field}.i8 = extract_value {previous} {index}.i64;\n"
                ));
            } else {
                body.push_str(&format!("v{field}.i8 = add v1 {}.i8;\n", index % 251));
            }
            body.push_str(&format!(
                "v{result}.[i8; {length}] = insert_value {aggregate} {index}.i64 v{field};\n"
            ));
            aggregate = format!("v{result}");
        }
        if stage + 1 == stages {
            body.push_str(&format!("return {aggregate};\n"));
        } else {
            body.push_str(&format!("jump block{};\n", block + 1));
        }
        previous = aggregate;
        blocks.push(body);
    }
    if reverse_layout {
        blocks.reverse();
    }
    source.extend(blocks);
    source.push_str("}\n");
    parse_module(&source)
        .expect("valid insertion-chain IR")
        .module
}

#[test]
fn reconstruction_tracks_replaced_sources_across_layout_orders() {
    for length in [3, 1024] {
        for reverse_layout in [false, true] {
            let module = insert_chain_module(length, 3, true, reverse_layout);
            let config = VerifierConfig::for_level(VerificationLevel::Full);
            verify_module_or_panic(&module, &config);
            for func_ref in module.funcs() {
                module.func_store.modify(func_ref, |func| {
                    assert!(AggregateCombine::default().run(func));
                });
            }
            verify_module_or_panic(&module, &config);
            let text = ModuleWriter::new(&module).dump_string();
            assert!(text.contains("return v0;"), "{text}");
        }
    }
}

#[test]
#[ignore = "manual scaling measurement; run with --release --ignored --nocapture"]
fn insertion_chain_scaling() {
    if cfg!(debug_assertions) {
        panic!("measure a release-built compiler");
    }
    for (pass, reconstruct) in ["combine", "sccp", "scalarize", "gvn"]
        .into_iter()
        .flat_map(|pass| [false, true].map(|reconstruct| (pass, reconstruct)))
    {
        for length in [64, 256, 1024, 4096] {
            let mut samples = Vec::new();
            for sample in 0..6 {
                let module = insert_chain_module(length, 1, reconstruct, false);
                let start = Instant::now();
                for func_ref in module.funcs() {
                    module.func_store.modify(func_ref, |func| {
                        let mut cfg = ControlFlowGraph::default();
                        cfg.compute(func);
                        black_box(match pass {
                            "combine" => AggregateCombine::default().run(func),
                            "sccp" => SccpSolver::new().run(func, &mut cfg),
                            "scalarize" => AggregateScalarize::default().run(func),
                            "gvn" => GvnSolver::new().run(func, &mut cfg, &mut DomTree::default()),
                            _ => unreachable!(),
                        });
                    });
                }
                if sample != 0 {
                    samples.push(start.elapsed());
                }
            }
            samples.sort();
            println!(
                "pass={pass}, reconstruct={reconstruct}, elements={length}, median={:?}",
                samples[samples.len() / 2]
            );
        }
    }
}
