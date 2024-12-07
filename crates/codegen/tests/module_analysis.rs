mod common;

use std::fmt::Write;

use dir_test::{dir_test, Fixture};
use indexmap::IndexSet;
use sonatina_codegen::module_analysis::{analyze_module, ModuleInfo, SccRef};
use sonatina_ir::module::ModuleCtx;
use sonatina_parser::ParsedModule;

#[dir_test(
    dir: "$CARGO_MANIFEST_DIR/test_files/module_analysis/",
    glob: "*.sntn"
    loader: common::parse_module,
)]
fn test(fixture: Fixture<ParsedModule>) {
    let module = &fixture.content().module;
    let module_info = analyze_module(module);
    let info_string = dump_module_info(&module.ctx, &module_info);

    snap_test!(info_string, fixture.path());
}

fn dump_module_info(ctx: &ModuleCtx, info: &ModuleInfo) -> String {
    let mut s = String::new();
    // Write access pattern.
    writeln!(&mut s, "ModuleDependency: {}\n", info.access_pattern).unwrap();

    let mut sccs: IndexSet<SccRef> = IndexSet::default();

    // Write SCCs.
    for func_ref in info.call_graph.funcs() {
        let scc_ref = info.scc.scc_ref(func_ref);
        if sccs.insert(info.scc.scc_ref(func_ref)) {
            write!(&mut s, "SCC: [").unwrap();
            let mut components: Vec<_> = info
                .scc
                .scc_info(scc_ref)
                .components
                .iter()
                .copied()
                .collect();
            components.sort_unstable();
            let mut components = components.into_iter();

            if let Some(func_ref) = components.next() {
                ctx.func_sig(func_ref, |sig| {
                    write!(&mut s, "`%{}`", sig.name()).unwrap();
                });
            }

            for func_ref in components {
                ctx.func_sig(func_ref, |sig| {
                    write!(&mut s, ", `%{}`", sig.name()).unwrap();
                });
            }

            writeln!(&mut s, "]").unwrap();
        }
    }
    writeln!(&mut s).unwrap();

    for func_ref in info.call_graph.funcs() {
        let func_info = info.func_info.get(&func_ref).unwrap();
        ctx.func_sig(func_ref, |sig| {
            writeln!(&mut s, "`%{}` = {:?}", sig.name(), func_info).unwrap();
        });
    }

    s
}
