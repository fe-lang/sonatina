//! The last IR phase on every backend, and what backends assume of its result.
//!
//! [`concretize`] makes every value concrete: the final IR it leaves, which
//! each backend's lowering consumes, has no `undef` and no `freeze`. It is the
//! one place that says what an unspecified value becomes: `zero.T`, the value
//! of `T` whose bits are all zero, but for a frozen pointer (see
//! [`lower_frozen_undef`]). Until it runs, `docs/undef.md` holds. Backends
//! check its result with [`check_concrete`].

use rustc_hash::FxHashSet;
use sonatina_ir::{
    Function, I256, Immediate, InstId, Module, Value, ValueId,
    inst::{cast::IntToPtr, data::Freeze, logic::And},
};

use super::aggregate::fresh::{fold_fresh_aggregates_in, is_fresh_insert};

/// Makes every function of `module` concrete ([`concretize_function`]).
pub fn concretize(module: &Module) {
    for func in module.funcs() {
        module.func_store.modify(func, concretize_function);
    }
}

/// Folds each fresh insert chain into an `agg.make`, lowers each `freeze` of
/// a literal `undef` ([`lower_frozen_undef`]), makes every other literal
/// `undef` the `zero` of its type, and then, every value being concrete,
/// replaces each remaining `freeze x` with `x`. Last, it folds each `and` of a
/// value it made constant, and each `and` of one it folded, when the result is
/// constant: on EVM a narrow `freeze` and a narrow effect operand are masks of
/// their word, and a word that is constant once the freeze is gone needs none.
/// Any other `and` stays; folding the input's constants is the optimizer's.
pub fn concretize_function(func: &mut Function) {
    fold_fresh_aggregates_in(func);
    let unconcrete = |value: ValueId| {
        matches!(func.dfg.value(value), Value::Undef { .. })
            || func
                .dfg
                .value_inst(value)
                .is_some_and(|inst| func.dfg.downcast::<&Freeze>(inst).is_some())
    };
    let mut masks: FxHashSet<InstId> = func
        .layout
        .iter_block()
        .flat_map(|block| func.layout.iter_inst(block))
        .filter(|&inst| {
            func.dfg
                .downcast::<&And>(inst)
                .is_some_and(|and| unconcrete(*and.lhs()) || unconcrete(*and.rhs()))
        })
        .collect();
    let freezes: Vec<InstId> = func
        .layout
        .iter_block()
        .flat_map(|block| func.layout.iter_inst(block))
        .filter(|&inst| func.dfg.downcast::<&Freeze>(inst).is_some())
        .collect();
    let left: Vec<InstId> = freezes
        .into_iter()
        .filter(|&inst| lower_frozen_undef(func, inst).is_none())
        .collect();
    let undefs: Vec<ValueId> = func
        .dfg
        .value_ids()
        .filter(|&value| matches!(func.dfg.value(value), Value::Undef { .. }))
        .collect();
    for value in undefs {
        let ty = func.dfg.value_ty(value);
        if let Some(&canonical) = func.dfg.zeros.get(&ty) {
            func.dfg.change_to_alias(value, canonical);
            func.dfg.delete_value(value);
        } else {
            func.dfg.values[value] = Value::Zero { ty };
            func.dfg.zeros.insert(ty, value);
        }
    }
    for inst in left {
        let arg = *func.dfg.downcast::<&Freeze>(inst).expect("a freeze").arg();
        let result = func.dfg.inst_result(inst).expect("freeze has a result");
        func.dfg.change_to_alias(result, arg);
        func.layout.remove_inst(inst);
        func.erase_inst(inst);
    }
    // In layout order, so a mask of a mask that became constant folds too.
    let ands: Vec<InstId> = func
        .layout
        .iter_block()
        .flat_map(|block| func.layout.iter_inst(block))
        .filter(|&inst| func.dfg.downcast::<&And>(inst).is_some())
        .collect();
    for inst in ands {
        if !masks.contains(&inst) {
            continue;
        }
        let and = func.dfg.downcast::<&And>(inst).expect("an and");
        let constant = |value: ValueId| match func.dfg.value(value) {
            Value::Zero { .. } => Some(I256::zero()),
            Value::Immediate { imm, .. } => Some(imm.as_i256()),
            _ => None,
        };
        let folded = match (constant(*and.lhs()), constant(*and.rhs())) {
            (Some(lhs), Some(rhs)) => lhs & rhs,
            (Some(zero), _) | (_, Some(zero)) if zero.is_zero() => I256::zero(),
            _ => continue,
        };
        let result = func.dfg.inst_result(inst).expect("an and has a result");
        let ty = func.dfg.value_ty(result);
        let value = func.dfg.make_imm_value(Immediate::from_i256(folded, ty));
        masks.extend(func.dfg.change_to_alias(result, value));
        func.layout.remove_inst(inst);
        func.erase_inst(inst);
    }
}

/// Lowers `freeze undef` to zero, and leaves a freeze of any other value
/// alone. A frozen pointer is a defined one that a program may use as an
/// address, so it becomes `int_to_ptr 0`, whose provenance is unknown, not
/// `zero.*T`, through which an access is undefined behavior. Returns the value
/// that now stands for the freeze's result, or `None` if the freeze stays.
pub(crate) fn lower_frozen_undef(func: &mut Function, inst: InstId) -> Option<ValueId> {
    let arg = *func.dfg.downcast::<&Freeze>(inst).expect("a freeze").arg();
    let result = func.dfg.inst_result(inst).expect("freeze has a result");
    let replacement = match *func.dfg.value(arg) {
        Value::Undef { ty } if ty.is_pointer(func.ctx()) => {
            let int_ty = func.ctx().type_layout.pointer_repl();
            let zero = func.dfg.make_imm_value(Immediate::zero(int_ty));
            let null = IntToPtr::new_unchecked(func.inst_set(), zero, ty);
            func.dfg.replace_inst(inst, Box::new(null));
            return Some(result);
        }
        Value::Undef { ty } => func.dfg.make_imm_value(Immediate::zero(ty)),
        _ => return None,
    };
    func.dfg.change_to_alias(result, replacement);
    func.layout.remove_inst(inst);
    func.erase_inst(inst);
    Some(replacement)
}

/// Checks that `func` is concrete, as [`concretize`] leaves it: no instruction
/// has an `undef` operand, in any position the instruction's own value
/// visitor reaches (phi inputs, branch conditions, call arguments, returned
/// values, ...), none is a `freeze`, and none is a constant-index insert into
/// an `agg.make` that the fold would have taken.
pub fn check_concrete(func: &Function) -> Result<(), String> {
    for block in func.layout.iter_block() {
        for inst in func.layout.iter_inst(block) {
            let data = func.dfg.inst(inst);
            let problem = if func.dfg.downcast::<&Freeze>(inst).is_some() {
                "is a `freeze`".to_string()
            } else if let Some(value) = data
                .collect_values()
                .into_iter()
                .find(|&value| matches!(func.dfg.value(value), Value::Undef { .. }))
            {
                format!("has an `undef` operand v{}", value.as_u32())
            } else if is_fresh_insert(func, inst) {
                "is an insert into an `agg.make` that `concretize` folds".to_string()
            } else {
                continue;
            };
            return Err(format!(
                "inst{} ({}) {problem}",
                inst.as_u32(),
                data.as_text()
            ));
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
    fn every_operand_position_is_checked_and_made_zero() {
        for body in [
            // A phi input.
            "func private %f(v0.i1) -> i64 {\nblock0:\n    br v0 block1 block2;\nblock1:\n    jump block3;\nblock2:\n    jump block3;\nblock3:\n    v1.i64 = phi (undef.i64 block1) (3.i64 block2);\n    return v1;\n}",
            // A branch condition.
            "func private %f() -> i64 {\nblock0:\n    br undef.i1 block1 block2;\nblock1:\n    return 1.i64;\nblock2:\n    return 2.i64;\n}",
            // A call argument.
            "func private %f() -> i64 {\nblock0:\n    v0.i64 = call %g undef.i64;\n    return v0;\n}\nfunc private %g(v0.i64) -> i64 {\nblock0:\n    return v0;\n}",
            // A returned value.
            "func private %f() -> @pair {\nblock0:\n    return undef.@pair;\n}",
            // A stored value and an address.
            "func private %f(v0.*i64) {\nblock0:\n    mstore v0 undef.i64 i64;\n    mstore undef.*i64 1.i64 i64;\n    return;\n}",
            // An `agg.make` operand.
            "func private %f(v0.i64) -> @pair {\nblock0:\n    v1.@pair = agg.make @pair v0 undef.i64;\n    return v1;\n}",
        ] {
            let (before, text) = concretize(body);
            assert!(before.is_err(), "{body}");
            assert!(!text.contains("undef"), "{text}");
            assert!(text.contains("zero."), "{text}");
        }
    }

    #[test]
    fn freezes_go() {
        let (before, text) = concretize(
            "func private %f(v0.i64) -> i64 {\nblock0:\n    v1.i64 = freeze v0;\n    v2.i64 = freeze undef.i64;\n    v3.*i8 = freeze undef.*i8;\n    v4.i64 = ptr_to_int v3 i64;\n    v5.i64 = add v1 v2;\n    v6.i64 = add v5 v4;\n    return v6;\n}",
        );
        assert!(before.is_err());
        assert!(!text.contains("freeze"), "{text}");
        // A frozen pointer is a defined one, not the null `zero`.
        assert!(text.contains("int_to_ptr 0.i256 *i8"), "{text}");
        assert!(text.contains("add v0 0.i64"), "{text}");
    }

    #[test]
    fn masks_of_a_zero_word_fold() {
        // EVM legalization makes a narrow `freeze` `and (freeze w) mask` and a
        // narrow effect operand `and w mask`; here `w` is a literal `undef`.
        let (_, text) = concretize(
            "func private %f() -> i256 {\nblock0:\n    v0.i256 = freeze undef.i256;\n    v1.i256 = and v0 255.i256;\n    v2.i256 = and undef.i256 255.i256;\n    v3.i256 = and v1 v2;\n    return v3;\n}",
        );
        assert!(!text.contains("and "), "{text}");
        assert!(text.contains("return 0.i256;"), "{text}");
        // A frozen constant, as -O0 leaves one, is masked as it is.
        let (_, text) = concretize(
            "func private %f() -> i256 {\nblock0:\n    v0.i256 = freeze 300.i256;\n    v1.i256 = and v0 255.i256;\n    return v1;\n}",
        );
        assert!(!text.contains("and "), "{text}");
        assert!(text.contains("return 44.i256;"), "{text}");
        // The input's own constant `and` is the optimizer's to fold.
        let (_, text) = concretize(
            "func private %f() -> i256 {\nblock0:\n    v0.i256 = and 240.i256 204.i256;\n    return v0;\n}",
        );
        assert!(text.contains("and 240.i256 204.i256"), "{text}");
    }

    #[test]
    fn a_frozen_value_with_an_undef_part_is_its_concrete_argument() {
        let (_, text) = concretize(
            "func private %f(v0.i1) -> *i8 {\nblock0:\n    br v0 block1 block2;\nblock1:\n    jump block3;\nblock2:\n    jump block3;\nblock3:\n    v1.*i8 = phi (undef.*i8 block1) (undef.*i8 block2);\n    v2.*i8 = freeze v1;\n    return v2;\n}",
        );
        assert!(
            text.contains("phi (zero.*i8 block1) (zero.*i8 block2)"),
            "{text}"
        );
        assert!(text.contains("return v1;"), "{text}");
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
