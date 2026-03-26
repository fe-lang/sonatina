use sonatina_ir::{
    Function, InstId, Type, ValueId,
    inst::{BinaryInstKind, InstClassKind},
};

use crate::analysis::known_bits::{KnownBits, KnownBitsQuery};

pub struct KnownBitsSimplify {
    plans: Vec<RewritePlan>,
}

#[derive(Clone, Copy)]
struct RewritePlan {
    inst: InstId,
    replacement: ValueId,
}

impl KnownBitsSimplify {
    pub fn new() -> Self {
        Self { plans: Vec::new() }
    }

    pub fn run(&mut self, func: &mut Function) -> bool {
        self.plans.clear();

        let mut known_bits = KnownBitsQuery::new(func);
        let blocks: Vec<_> = func.layout.iter_block().collect();
        for block in blocks {
            for inst in func.layout.iter_inst(block) {
                if let Some(plan) = self.plan_inst(func, &mut known_bits, inst) {
                    self.plans.push(plan);
                }
            }
        }

        if self.plans.is_empty() {
            return false;
        }

        for plan in self.plans.drain(..) {
            apply_plan(func, plan);
        }

        true
    }

    fn plan_inst(
        &self,
        func: &Function,
        known_bits: &mut KnownBitsQuery<'_>,
        inst: InstId,
    ) -> Option<RewritePlan> {
        if !matches!(
            func.dfg.inst(inst).kind(),
            InstClassKind::Binary(BinaryInstKind::And)
        ) {
            return None;
        }

        let result = func.dfg.inst_result(inst)?;
        let ty = func.dfg.value_ty(result);
        if !supports_mask_simplify(ty) {
            return None;
        }

        let args = func.dfg.inst(inst).collect_values();
        let [lhs, rhs] = args.as_slice() else {
            return None;
        };

        match (func.dfg.value_imm(*lhs), func.dfg.value_imm(*rhs)) {
            (Some(mask), None) => self.plan_masked_and(known_bits, ty, *rhs, mask, inst),
            (None, Some(mask)) => self.plan_masked_and(known_bits, ty, *lhs, mask, inst),
            _ => None,
        }
    }

    fn plan_masked_and(
        &self,
        known_bits: &mut KnownBitsQuery<'_>,
        ty: Type,
        value: ValueId,
        mask_imm: sonatina_ir::Immediate,
        inst: InstId,
    ) -> Option<RewritePlan> {
        let type_mask = !KnownBits::unknown(ty).known_zero;
        let mask = KnownBits::from_imm(mask_imm).known_one & type_mask;
        let outside = type_mask & !mask;
        known_bits
            .for_value(value)
            .all_zero_in(outside)
            .then_some(RewritePlan {
                inst,
                replacement: value,
            })
    }
}

impl Default for KnownBitsSimplify {
    fn default() -> Self {
        Self::new()
    }
}

fn apply_plan(func: &mut Function, plan: RewritePlan) {
    if !func.layout.is_inst_inserted(plan.inst) {
        return;
    }

    let Some(result) = func.dfg.inst_result(plan.inst) else {
        return;
    };

    func.dfg.change_to_alias(result, plan.replacement);
    func.layout.remove_inst(plan.inst);
    func.erase_inst(plan.inst);
}

fn supports_mask_simplify(ty: Type) -> bool {
    matches!(
        ty,
        Type::I1 | Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::I128 | Type::I256
    )
}

#[cfg(test)]
mod tests {
    use sonatina_ir::{Module, ir_writer::FuncWriter, module::FuncRef};
    use sonatina_parser::parse_module;

    use super::KnownBitsSimplify;

    #[test]
    fn folds_redundant_mask_after_logical_shr() {
        let (module, func_ref) = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

func public %f(v0.i256) -> i256 {
block0:
    v1.i256 = shr 224.i256 v0;
    v2.i256 = and v1 4294967295.i256;
    return v2;
}
"#,
        );

        module.func_store.modify(func_ref, |func| {
            assert!(KnownBitsSimplify::new().run(func));
        });

        let dumped = dump_func(&module, func_ref);
        assert!(dumped.contains("v1.i256 = shr 224.i256 v0;"), "{dumped}");
        assert!(!dumped.contains(" and "), "{dumped}");
        assert!(dumped.contains("return v1;"), "{dumped}");
    }

    #[test]
    fn does_not_fold_mask_after_arithmetic_sar_without_known_sign() {
        let (module, func_ref) = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

func public %f(v0.i256) -> i256 {
block0:
    v1.i256 = sar 224.i256 v0;
    v2.i256 = and v1 4294967295.i256;
    return v2;
}
"#,
        );

        module.func_store.modify(func_ref, |func| {
            assert!(!KnownBitsSimplify::new().run(func));
        });

        let dumped = dump_func(&module, func_ref);
        assert!(
            dumped.contains("v2.i256 = and v1 4294967295.i256;"),
            "{dumped}"
        );
    }

    #[test]
    fn folds_all_ones_mask_with_immediate_on_lhs() {
        let (module, func_ref) = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

func public %f(v0.i8) -> i8 {
block0:
    v1.i8 = and -1.i8 v0;
    return v1;
}
"#,
        );

        module.func_store.modify(func_ref, |func| {
            assert!(KnownBitsSimplify::new().run(func));
        });

        let dumped = dump_func(&module, func_ref);
        assert!(!dumped.contains(" and "), "{dumped}");
        assert!(dumped.contains("return v0;"), "{dumped}");
    }

    #[test]
    fn leaves_non_immediate_masks_alone() {
        let (module, func_ref) = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

func public %f(v0.i256, v1.i256) -> i256 {
block0:
    v2.i256 = and v0 v1;
    return v2;
}
"#,
        );

        module.func_store.modify(func_ref, |func| {
            assert!(!KnownBitsSimplify::new().run(func));
        });

        let dumped = dump_func(&module, func_ref);
        assert!(dumped.contains("v2.i256 = and v0 v1;"), "{dumped}");
    }

    fn parse_test_module(src: &str) -> (Module, FuncRef) {
        let parsed = parse_module(src).expect("module parses");
        let func_ref = parsed
            .module
            .funcs()
            .into_iter()
            .find(|&func| parsed.module.ctx.func_sig(func, |sig| sig.name() == "f"))
            .expect("missing f");
        (parsed.module, func_ref)
    }

    fn dump_func(module: &Module, func_ref: FuncRef) -> String {
        module.func_store.view(func_ref, |func| {
            FuncWriter::new(func_ref, func).dump_string()
        })
    }
}
