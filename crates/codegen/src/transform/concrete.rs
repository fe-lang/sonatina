//! The last IR phase on every backend, and what backends assume of its result.
//!
//! [`concretize`] folds residual fresh `insert_value` chains into `agg.make`.
//! Backends check its result with [`check_concrete`].

use sonatina_ir::{Function, Module};

use super::aggregate::fresh::{fold_fresh_aggregates_in, is_fresh_insert};

/// Finalizes every function of `module` ([`concretize_function`]).
pub fn concretize(module: &Module) {
    for func in module.funcs() {
        module.func_store.modify(func, concretize_function);
    }
}

/// Folds each fresh insert chain into an `agg.make`.
pub fn concretize_function(func: &mut Function) {
    fold_fresh_aggregates_in(func);
}

/// Checks that `func` has no constant-index insert into an `agg.make` or
/// `zero` aggregate that `concretize` would have folded.
pub fn check_concrete(func: &Function) -> Result<(), String> {
    for block in func.layout.iter_block() {
        for inst in func.layout.iter_inst(block) {
            if is_fresh_insert(func, inst) {
                let data = func.dfg.inst(inst);
                return Err(format!(
                    "inst{} ({}) is an insert into an `agg.make` that `concretize` folds",
                    inst.as_u32(),
                    data.as_text()
                ));
            }
        }
    }
    Ok(())
}

/// [`check_concrete`] on every function of `module`, naming the function.
pub fn check_concrete_module(module: &Module) -> Result<(), String> {
    for func in module.funcs() {
        module
            .func_store
            .view(func, check_concrete)
            .map_err(|error| {
                let name = module.ctx.func_sig(func, |sig| sig.name().to_string());
                format!("function %{name} is not concrete: {error}")
            })?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use sonatina_ir::ir_writer::FuncWriter;
    use sonatina_parser::parse_module;

    use super::{check_concrete, concretize_function};

    const TYPES: &str = "target = \"evm-ethereum-osaka\"\ntype @pair = { i64, i64 };\n";

    /// The one function of `body`, checked, then concretized and checked
    /// again: the check's verdict before, and the function's text after.
    fn concretize(body: &str) -> (Result<(), String>, String) {
        let module = parse_module(&format!("{TYPES}{body}")).unwrap().module;
        let func = module.funcs()[0];
        let before = module.func_store.view(func, check_concrete);
        module.func_store.modify(func, concretize_function);
        module.func_store.view(func, |function| {
            assert_eq!(check_concrete(function), Ok(()));
            (before, FuncWriter::new(func, function).dump_string())
        })
    }

    #[test]
    fn fresh_chains_fold_and_an_unfolded_one_is_rejected() {
        let body = "func private %f(v0.i64) -> @pair {\nblock0:\n    v1.@pair = agg.make @pair v0 v0;\n    v2.@pair = insert_value v1 1.i8 7.i64;\n    return v2;\n}";
        let (before, text) = concretize(body);
        assert!(
            before.is_err_and(|error| error.contains("insert into an `agg.make`")),
            "{text}"
        );
        assert!(text.contains("agg.make @pair v0 7.i64"), "{text}");
        assert!(!text.contains("insert_value"), "{text}");
    }
}
