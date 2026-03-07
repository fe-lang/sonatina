use sonatina_ir::{
    Function, Type, Value,
    inst::{
        arith::{Add, Uaddo},
        cmp::Lt,
        downcast,
    },
};

pub fn legalize_multi_result(func: &mut Function) {
    let blocks: Vec<_> = func.layout.iter_block().collect();
    for block in blocks {
        let insts: Vec<_> = func.layout.iter_inst(block).collect();
        for inst in insts {
            let Some(uaddo) = downcast::<&Uaddo>(func.inst_set(), func.dfg.inst(inst)) else {
                continue;
            };

            let results = func.dfg.inst_results(inst).to_vec();
            assert_eq!(
                results.len(),
                2,
                "uaddo must have exactly two results before legalization"
            );

            let lhs = *uaddo.lhs();
            let rhs = *uaddo.rhs();
            let lhs_ty = func.dfg.value_ty(lhs);
            let rhs_ty = func.dfg.value_ty(rhs);
            let sum_ty = func.dfg.value_ty(results[0]);
            let overflow_ty = func.dfg.value_ty(results[1]);
            assert!(lhs_ty.is_integral(), "uaddo operands must be integral");
            assert_eq!(lhs_ty, rhs_ty, "uaddo operands must have matching types");
            assert_eq!(
                sum_ty, lhs_ty,
                "uaddo sum result type must match operand type"
            );
            assert_eq!(overflow_ty, Type::I1, "uaddo overflow result must be i1");

            let is = func.inst_set();

            let add_inst = func
                .dfg
                .make_inst(Add::new(is.has_add().unwrap(), lhs, rhs));
            func.layout.insert_inst_before(add_inst, inst);
            let add_result = func.dfg.make_value(Value::Inst {
                inst: add_inst,
                result_idx: 0,
                ty: sum_ty,
            });
            func.dfg.attach_result(add_inst, add_result);

            let lt_inst = func
                .dfg
                .make_inst(Lt::new(is.has_lt().unwrap(), add_result, lhs));
            func.layout.insert_inst_before(lt_inst, inst);
            let lt_result = func.dfg.make_value(Value::Inst {
                inst: lt_inst,
                result_idx: 0,
                ty: overflow_ty,
            });
            func.dfg.attach_result(lt_inst, lt_result);

            func.dfg.change_to_alias(results[0], add_result);
            func.dfg.change_to_alias(results[1], lt_result);
            func.dfg.untrack_inst(inst);
            func.layout.remove_inst(inst);
        }
    }
}
