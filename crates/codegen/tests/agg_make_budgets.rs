//! A fresh array built by an `insert_value` chain on undef and by an
//! `agg.make` weighs the same in the size budgets of loop rotation, loop
//! unrolling, jump threading and insert chain placement: each pass applies to
//! both spellings or to neither.
use sonatina_codegen::{
    optim::{Pass, Pipeline, Step},
    transform::aggregate::fold_fresh_aggregates,
};
use sonatina_ir::ir_writer::ModuleWriter;

/// `vN.[i256; len] = ...` built from `elem` in every field.
fn build(result: &str, len: usize, elem: &str, make: bool) -> String {
    let ty = format!("[i256; {len}]");
    if make {
        let elems: String = (0..len).map(|_| format!(" {elem}")).collect();
        return format!("{result}.{ty} = agg.make {ty}{elems};\n");
    }
    let mut text = String::new();
    let mut current = format!("undef.{ty}");
    for index in 0..len {
        let next = if index + 1 == len {
            result.to_string()
        } else {
            format!("v{}", 100 + index)
        };
        text.push_str(&format!(
            "{next}.{ty} = insert_value {current} {index}.i8 {elem};\n"
        ));
        current = next;
    }
    text
}

/// Whether `pass` changes `source`, other than by spelling a chain as an
/// `agg.make`, which hoist does first.
fn applies(pass: Pass, source: &str) -> bool {
    let mut module = sonatina_parser::parse_module(source).unwrap().module;
    let input = sonatina_parser::parse_module(source).unwrap().module;
    fold_fresh_aggregates(&input);
    let mut pipeline = Pipeline::new();
    pipeline.add_step(Step::FuncPasses(vec![pass]));
    pipeline.run(&mut module);
    fold_fresh_aggregates(&module);
    ModuleWriter::new(&module).dump_string() != ModuleWriter::new(&input).dump_string()
}

fn same_decision(pass: Pass, source: impl Fn(bool) -> String, expected: bool) {
    for make in [false, true] {
        assert_eq!(applies(pass, &source(make)), expected, "{}", source(make));
    }
}

#[test]
fn jump_threading_weighs_agg_make_as_its_chain() {
    // The threaded block's body is the array: four fields fit, five do not.
    for (len, threads) in [(4, true), (5, false)] {
        same_decision(
            Pass::JumpThread,
            |make| {
                format!(
                    "target = \"evm-ethereum-osaka\"
func public %f(v0.i1, v1.i256) -> [i256; {len}] {{
block0:
    br v0 block1 block2;
block1:
    jump block3;
block2:
    jump block3;
block3:
    v3.i1 = phi (1.i1 block1) (0.i1 block2);
{}    br v3 block4 block5;
block4:
    return v9;
block5:
    return v9;
}}
",
                    build("v9", len, "v1", make)
                )
            },
            threads,
        );
    }
}

#[test]
fn loop_rotation_weighs_agg_make_as_its_chain() {
    // The header copies the array and its test: seven fields fit, eight do
    // not.
    for (len, rotates) in [(7, true), (8, false)] {
        same_decision(
            Pass::LoopRotate,
            |make| {
                format!(
                    "target = \"evm-ethereum-osaka\"
func public %g(v0.i256, v1.objref<[i256; {len}]>) {{
block0:
    jump block1;
block1:
    v2.i256 = phi (0.i256 block0) (v20 block2);
{}    v3.i1 = lt v2 v0;
    br v3 block2 block3;
block2:
    obj.store v1 v9;
    v20.i256 = add v2 1.i256;
    jump block1;
block3:
    return;
}}
",
                    build("v9", len, "v2", make)
                )
            },
            rotates,
        );
    }
}

#[test]
fn loop_unrolling_weighs_agg_make_as_its_chain() {
    // Four trips of a body that stores a 10-element array fit the budget, of
    // one that stores 200 elements do not.
    for (len, unrolls) in [(10, true), (200, false)] {
        same_decision(
            Pass::LoopUnroll,
            |make| {
                format!(
                    "target = \"evm-ethereum-osaka\"
func public %h(v1.objref<[i256; {len}]>) {{
block0:
    jump block1;
block1:
    v2.i256 = phi (0.i256 block0) (v20 block2);
    v3.i1 = lt v2 4.i256;
    br v3 block2 block3;
block2:
{}    obj.store v1 v9;
    v20.i256 = add v2 1.i256;
    jump block1;
block3:
    return;
}}
",
                    build("v9", len, "v2", make)
                )
            },
            unrolls,
        );
    }
}

#[test]
fn rebuilding_at_uses_weighs_agg_make_as_its_chain() {
    // A value stored in a later block is built again at its uses when its
    // construction is small: sixteen fields are, seventeen are not.
    for (len, rebuilds) in [(16, true), (17, false)] {
        same_decision(
            Pass::HoistInsertChains,
            |make| {
                format!(
                    "target = \"evm-ethereum-osaka\"
declare external %grow() -> i1;
declare external %undo([i256; {len}]);
func public %push(v0.objref<[i256; {len}]>, v1.i256) {{
block0:
{}    v6.i1 = call %grow;
    br v6 block1 block2;
block1:
    obj.store v0 v9;
    return;
block2:
    call %undo v9;
    return;
}}
",
                    build("v9", len, "v1", make)
                )
            },
            rebuilds,
        );
    }
}
