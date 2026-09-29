//! Shared scaffolding for the crate's unit tests.
//!
//! Parsing a module, looking a function up by name, and dumping one back to
//! text are needed by nearly every pass test, so they live here instead of
//! being redefined in each `mod tests`.

use sonatina_ir::{Module, ir_writer::FuncWriter, module::FuncRef};
use sonatina_parser::parse_module;

pub(crate) fn parse_test_module(src: &str) -> Module {
    parse_module(src).expect("parse should succeed").module
}

pub(crate) fn lookup_func(module: &Module, name: &str) -> FuncRef {
    module
        .funcs()
        .into_iter()
        .find(|&func_ref| module.ctx.func_sig(func_ref, |sig| sig.name() == name))
        .expect("function should exist")
}

pub(crate) fn dump_func(module: &Module, func_ref: FuncRef) -> String {
    module.func_store.view(func_ref, |func| {
        FuncWriter::new(func_ref, func).dump_string()
    })
}

pub(crate) fn dump_func_by_name(module: &Module, name: &str) -> String {
    dump_func(module, lookup_func(module, name))
}
