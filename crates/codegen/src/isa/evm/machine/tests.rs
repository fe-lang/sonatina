use std::{collections::BTreeSet, sync::Arc};

use crate::{
    domtree::DomTree,
    isa::evm::test_util::osaka_triple,
    loop_analysis::LoopTree,
    optim::{gvn::GvnSolver, known_bits_simplify::KnownBitsSimplify},
    range_analysis::{RangeAnalysis, RangeFact},
};
use sonatina_ir::{
    ControlFlowGraph, I256, Immediate, Linkage, Signature, Type,
    builder::ModuleBuilder,
    func_cursor::InstInserter,
    inst::{
        arith::{Add, Mul, Sub},
        cmp::{Eq, IsZero, Lt},
        control_flow::{Br, BrTable, BranchKind, Jump, Phi, Return},
        data::Alloca,
        evm::{EvmMload, EvmMstore, EvmMstore8},
        logic::{And, Not, Or},
    },
    ir_writer::FuncWriter,
    isa::{
        Isa,
        evm::{Evm, EvmMachine},
    },
    module::ModuleCtx,
};
use sonatina_parser::parse_module;
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_function};

use super::{
    super::{LateCleanupProfile, SwitchLoweringStrategy},
    branch::canonicalize_machine_branch_conditions,
    pipeline::run_machine_opt_pipeline,
    switch::lower_switches,
    verify::verify_machine_function,
};

fn machine_builder() -> ModuleBuilder {
    ModuleBuilder::new(ModuleCtx::new(&EvmMachine::new(osaka_triple())))
}

#[test]
fn machine_switch_tree_preserves_phi_inputs_and_attribution() {
    let mb = machine_builder();
    let func_ref = mb
        .declare_function(Signature::new_single(
            "switch_phi",
            Linkage::Public,
            &[Type::I256],
            Type::I256,
        ))
        .unwrap();
    let machine = EvmMachine::new(mb.triple());
    let is = machine.inst_set();
    let mut builder = mb.func_builder::<InstInserter>(func_ref);
    let entry = builder.append_block();
    let root = builder.append_block();
    let other = builder.append_block();
    let shared = builder.append_block();
    let input = builder.func.arg_values[0];
    let zero = builder.make_imm_value(Immediate::zero(Type::I256));
    let one = builder.make_imm_value(Immediate::one(Type::I256));
    builder.switch_to_block(entry);
    builder.insert_inst_no_result(Jump::new(is, root));
    builder.switch_to_block(root);
    let carried = builder.insert_inst(Phi::new(is, vec![(input, entry)].into()), Type::I256);
    let next = builder.insert_inst(Add::new(is, carried, one), Type::I256);
    let root_phi = builder.func.dfg.value_inst(carried).unwrap();
    builder.func.dfg.replace_inst(
        root_phi,
        Box::new(Phi::new(is, vec![(input, entry), (next, root)].into())),
    );
    let cases = (0..16)
        .map(|key| {
            let value = builder.make_imm_value(Immediate::from_i256(key.into(), Type::I256));
            let dest = match key % 3 {
                0 => root,
                1 => shared,
                _ => other,
            };
            (value, dest)
        })
        .collect();
    builder.insert_inst_no_result(BrTable::new(is, input, Some(shared), cases));
    let term = builder.func.layout.last_inst_of(root).unwrap();
    builder
        .func
        .set_inst_frontend_origin(term, Arc::from("selector-source"));
    builder
        .func
        .set_inst_provenance(term, "selector-provenance".into());
    builder.switch_to_block(other);
    builder.insert_inst_no_result(Jump::new(is, shared));
    builder.switch_to_block(shared);
    let merged = builder.insert_inst(
        Phi::new(is, vec![(next, root), (zero, other)].into()),
        Type::I256,
    );
    builder.insert_inst_no_result(Return::new_single(is, merged));
    builder.seal_all();
    builder.finish();
    let module = mb.build();
    module.func_store.modify(func_ref, |func| {
        let old_insts: BTreeSet<_> = func
            .layout
            .iter_block()
            .flat_map(|block| func.layout.iter_inst(block))
            .collect();
        lower_switches(func, 16);
        verify_machine_function(func_ref, func).unwrap();
        // General SSA/dominance/user checks apply to machine IR too; its target-specific
        // word result types are checked above instead of using high-level type rules.
        let cfg = VerifierConfig {
            level: VerificationLevel::Fast,
            ..VerifierConfig::for_level(VerificationLevel::Full)
        };
        let report = verify_function(&module.ctx, func_ref, func, &cfg);
        assert!(!report.has_errors(), "{report:?}");
        let phi = func.dfg.cast_phi(root_phi).unwrap();
        assert!(
            phi.args()
                .iter()
                .any(|&(value, pred)| value == input && pred == entry)
        );
        assert!(
            phi.args()
                .iter()
                .filter(|&&(_, pred)| pred != entry)
                .all(|&(value, pred)| value == next && pred != root)
        );
        let shared_phi = func
            .dfg
            .cast_phi(func.dfg.value_inst(merged).unwrap())
            .unwrap();
        assert!(
            shared_phi
                .args()
                .iter()
                .filter(|&&(_, pred)| pred != other)
                .all(|&(value, pred)| value == next && pred != root)
        );
        for inst in func
            .layout
            .iter_block()
            .flat_map(|block| func.layout.iter_inst(block))
            .filter(|inst| !old_insts.contains(inst))
        {
            assert_eq!(func.inst_frontend_origin(inst), Some("selector-source"));
            assert_eq!(func.inst_provenance(inst), Some("selector-provenance"));
        }
        let once = FuncWriter::new(func_ref, func).dump_string();
        lower_switches(func, 16);
        assert_eq!(FuncWriter::new(func_ref, func).dump_string(), once);
    });
}

#[test]
fn machine_switch_pressure_includes_phi_edges_and_respects_reach() {
    // Payloads are defined in the switch block and used only through successor
    // phis, so ordinary block live-outs alone cannot detect their pressure.
    for (payload_count, reach, keep_input_live, cases, expected_pivots) in [
        (13, 16, false, 6, 1),
        (14, 16, false, 6, 0),
        (13, 15, false, 6, 0),
        (13, 16, true, 6, 1),
        (13, 16, false, 9, 2),
        (14, 16, false, 9, 1),
    ] {
        let mb = machine_builder();
        let func_ref = mb
            .declare_function(Signature::new_single(
                "switch_pressure",
                Linkage::Public,
                &[Type::I256],
                Type::I256,
            ))
            .unwrap();
        let machine = EvmMachine::new(mb.triple());
        let is = machine.inst_set();
        let mut builder = mb.func_builder::<InstInserter>(func_ref);
        let root = builder.append_block();
        let destinations = [builder.append_block(), builder.append_block()];
        let input = builder.func.arg_values[0];
        let one = builder.make_imm_value(Immediate::one(Type::I256));
        builder.switch_to_block(root);
        let payloads: Vec<_> = (0..payload_count)
            .map(|index| {
                let offset = builder.make_imm_value(Immediate::from_i256(index.into(), Type::I256));
                builder.insert_inst(Add::new(is, input, offset), Type::I256)
            })
            .collect();
        let table = (0..cases)
            .map(|key| {
                let value = builder.make_imm_value(Immediate::from_i256(key.into(), Type::I256));
                (value, destinations[key as usize % destinations.len()])
            })
            .collect();
        builder.insert_inst_no_result(BrTable::new(is, input, Some(destinations[0]), table));
        for dest in destinations {
            builder.switch_to_block(dest);
            // Repeated sources across destinations and immediate phi inputs must
            // not inflate the distinct live-word count.
            let merged: Vec<_> = payloads
                .iter()
                .copied()
                .chain([one])
                .map(|value| {
                    builder.insert_inst(Phi::new(is, vec![(value, root)].into()), Type::I256)
                })
                .collect();
            let mut sum = if keep_input_live { input } else { one };
            for value in merged {
                sum = builder.insert_inst(Add::new(is, sum, value), Type::I256);
            }
            builder.insert_inst_no_result(Return::new_single(is, sum));
        }
        builder.seal_all();
        builder.finish();
        let module = mb.build();
        module.func_store.modify(func_ref, |func| {
            lower_switches(func, reach);
            verify_machine_function(func_ref, func).unwrap();
            let pivots = func
                .layout
                .iter_block()
                .filter_map(|block| func.layout.last_inst_of(block))
                .filter_map(|inst| func.dfg.branch_info(inst))
                .filter(|branch| matches!(branch.branch_kind(), BranchKind::Br(_)))
                .count();
            assert_eq!(
                pivots, expected_pivots,
                "payloads={payload_count}, reach={reach}, live_input={keep_input_live}, cases={cases}"
            );
        });
    }
}

#[test]
fn machine_switch_without_default_is_unchanged() {
    let mb = machine_builder();
    let func_ref = mb
        .declare_function(Signature::new_single(
            "switch_no_default",
            Linkage::Public,
            &[Type::I256],
            Type::I256,
        ))
        .unwrap();
    let machine = EvmMachine::new(mb.triple());
    let is = machine.inst_set();
    let mut builder = mb.func_builder::<InstInserter>(func_ref);
    let entry = builder.append_block();
    let left = builder.append_block();
    let right = builder.append_block();
    builder.switch_to_block(entry);
    let input = builder.func.arg_values[0];
    let cases = (0..16)
        .map(|key| {
            let value = builder.make_imm_value(Immediate::from_i256(key.into(), Type::I256));
            (value, if key % 2 == 0 { left } else { right })
        })
        .collect();
    builder.insert_inst_no_result(BrTable::new(is, input, None, cases));
    for block in [left, right] {
        builder.switch_to_block(block);
        builder.insert_inst_no_result(Return::new_single(is, input));
    }
    builder.seal_all();
    builder.finish();
    let module = mb.build();
    module.func_store.modify(func_ref, |func| {
        let before = FuncWriter::new(func_ref, func).dump_string();
        lower_switches(func, 16);
        assert_eq!(FuncWriter::new(func_ref, func).dump_string(), before);
    });
}

fn expect_machine_rejects(src: &str) {
    let parsed = parse_module(src).expect("module parses");
    let func = parsed.module.funcs()[0];
    parsed.module.func_store.view(func, |function| {
        let err = verify_machine_function(func, function)
            .expect_err("high-level IR should be rejected by machine verifier");
        assert!(
            err.contains("unsupported instruction") || err.contains("must be i256,"),
            "{err}"
        );
    });
}

#[test]
fn machine_verify_accepts_word_machine_ir() {
    let mb = machine_builder();
    let func_ref = mb
        .declare_function(Signature::new_single(
            "machine_ok",
            Linkage::Public,
            &[],
            Type::I256,
        ))
        .unwrap();
    let machine = EvmMachine::new(mb.triple());
    let is = machine.inst_set();
    let mut builder = mb.func_builder::<InstInserter>(func_ref);

    let block = builder.append_block();
    builder.switch_to_block(block);
    let addr = builder.make_imm_value(Immediate::from_i256(I256::from(0), Type::I256));
    let value = builder.make_imm_value(Immediate::from_i256(I256::from(7), Type::I256));
    builder.insert_inst_no_result(EvmMstore::new(is, addr, value));
    let loaded = builder.insert_inst(EvmMload::new(is, addr), Type::I256);
    builder.insert_inst_no_result(Return::new_single(is, loaded));
    builder.seal_all();
    builder.finish();

    let module = mb.build();
    module.func_store.view(func_ref, |function| {
        verify_machine_function(func_ref, function).expect("valid machine IR should verify");
    });
}

#[test]
fn machine_verify_rejects_i1_compare_result() {
    let mb = machine_builder();
    let func_ref = mb
        .declare_function(Signature::new_single(
            "machine_i1_cmp",
            Linkage::Public,
            &[Type::I256, Type::I256],
            Type::I256,
        ))
        .unwrap();
    let machine = EvmMachine::new(mb.triple());
    let is = machine.inst_set();
    let mut builder = mb.func_builder::<InstInserter>(func_ref);

    let block = builder.append_block();
    builder.switch_to_block(block);
    let lhs = builder.func.arg_values[0];
    let rhs = builder.func.arg_values[1];
    let cmp = builder.insert_inst(Lt::new(is, lhs, rhs), Type::I1);
    let sum = builder.insert_inst(Add::new(is, lhs, cmp), Type::I256);
    builder.insert_inst_no_result(Return::new_single(is, sum));
    builder.seal_all();
    builder.finish();

    let module = mb.build();
    module.func_store.view(func_ref, |function| {
        let err = verify_machine_function(func_ref, function)
            .expect_err("machine IR should reject i1 compare results");
        assert!(err.contains("must be i256,"), "{err}");
    });
}

#[test]
fn machine_verify_rejects_i1_word_operand() {
    let mb = machine_builder();
    let func_ref = mb
        .declare_function(Signature::new_single(
            "machine_i1_word",
            Linkage::Public,
            &[Type::I256, Type::I1],
            Type::I256,
        ))
        .unwrap();
    let machine = EvmMachine::new(mb.triple());
    let is = machine.inst_set();
    let mut builder = mb.func_builder::<InstInserter>(func_ref);

    let block = builder.append_block();
    builder.switch_to_block(block);
    let lhs = builder.func.arg_values[0];
    let rhs = builder.func.arg_values[1];
    let sum = builder.insert_inst(Add::new(is, lhs, rhs), Type::I256);
    builder.insert_inst_no_result(Return::new_single(is, sum));
    builder.seal_all();
    builder.finish();

    let module = mb.build();
    module.func_store.view(func_ref, |function| {
        let err = verify_machine_function(func_ref, function)
            .expect_err("machine IR should reject i1 operands");
        assert!(err.contains("must be i256,"), "{err}");
    });
}

#[test]
fn machine_verify_accepts_word_typed_comparison() {
    let mb = machine_builder();
    let func_ref = mb
        .declare_function(Signature::new_single(
            "machine_word_cmp",
            Linkage::Public,
            &[Type::I256, Type::I256],
            Type::I256,
        ))
        .unwrap();
    let machine = EvmMachine::new(mb.triple());
    let is = machine.inst_set();
    let mut builder = mb.func_builder::<InstInserter>(func_ref);

    let block = builder.append_block();
    builder.switch_to_block(block);
    let lhs = builder.func.arg_values[0];
    let rhs = builder.func.arg_values[1];
    let cmp = builder.insert_inst(Lt::new(is, lhs, rhs), Type::I256);
    builder.insert_inst_no_result(Return::new_single(is, cmp));
    builder.seal_all();
    builder.finish();

    let module = mb.build();
    module.func_store.view(func_ref, |function| {
        verify_machine_function(func_ref, function)
            .expect("word-typed compare result is the machine zext-free form");
    });
}

#[test]
fn machine_gvn_folds_word_bool_constant_without_zext() {
    let mb = machine_builder();
    let func_ref = mb
        .declare_function(Signature::new_single(
            "machine_gvn_word_bool_const",
            Linkage::Public,
            &[],
            Type::I256,
        ))
        .unwrap();
    let machine = EvmMachine::new(mb.triple());
    let is = machine.inst_set();
    let mut builder = mb.func_builder::<InstInserter>(func_ref);

    let block = builder.append_block();
    builder.switch_to_block(block);
    let lhs = builder.make_imm_value(Immediate::from_i256(I256::from(1), Type::I256));
    let rhs = builder.make_imm_value(Immediate::from_i256(I256::from(1), Type::I256));
    let masked = builder.insert_inst(And::new(is, lhs, rhs), Type::I256);
    builder.insert_inst_no_result(Return::new_single(is, masked));
    builder.seal_all();
    builder.finish();

    let module = mb.build();
    run_machine_opt_pipeline(
        &module,
        &[func_ref],
        LateCleanupProfile::Off,
        SwitchLoweringStrategy::Auto,
        16,
        None,
    )
    .expect("GVN should fold word bool constants without panicking");
    module.func_store.view(func_ref, |function| {
        let dumped = FuncWriter::new(func_ref, function).dump_string();
        assert!(dumped.contains("return 1.i256;"), "{dumped}");
        assert!(!dumped.contains(" and "), "{dumped}");
    });
}

#[test]
fn machine_known_bits_drops_mask_on_mstore8_value() {
    let mb = machine_builder();
    let func_ref = mb
        .declare_function(Signature::new(
            "machine_mstore8_mask",
            Linkage::Public,
            &[Type::I256, Type::I256],
            &[],
        ))
        .unwrap();
    let machine = EvmMachine::new(mb.triple());
    let is = machine.inst_set();
    let mut builder = mb.func_builder::<InstInserter>(func_ref);

    let block = builder.append_block();
    builder.switch_to_block(block);
    let addr = builder.func.arg_values[0];
    let value = builder.func.arg_values[1];
    let byte = builder.make_imm_value(Immediate::from_i256(I256::from(255), Type::I256));
    let masked = builder.insert_inst(And::new(is, value, byte), Type::I256);
    builder.insert_inst_no_result(EvmMstore8::new(is, addr, masked));
    builder.insert_inst_no_result(Return::new_unit(is));
    builder.seal_all();
    builder.finish();

    let module = mb.build();
    run_machine_opt_pipeline(
        &module,
        &[func_ref],
        LateCleanupProfile::Speed,
        SwitchLoweringStrategy::Auto,
        16,
        None,
    )
    .expect("machine pipeline should run");
    module.func_store.view(func_ref, |function| {
        let dumped = FuncWriter::new(func_ref, function).dump_string();
        assert!(!dumped.contains(" and "), "{dumped}");
    });
}

#[test]
fn machine_known_bits_drops_mask_on_mstore8_value_in_loop() {
    // for i in 0..n { mstore8(dst + i, mload(src + i) & 0xff) }: the mask
    // depends on the loop counter.
    let mb = machine_builder();
    let func_ref = mb
        .declare_function(Signature::new(
            "machine_mstore8_mask_loop",
            Linkage::Public,
            &[Type::I256, Type::I256, Type::I256],
            &[],
        ))
        .unwrap();
    let machine = EvmMachine::new(mb.triple());
    let is = machine.inst_set();
    let mut builder = mb.func_builder::<InstInserter>(func_ref);

    let entry = builder.append_block();
    let body = builder.append_block();
    let exit = builder.append_block();
    let [src, dst, n] = builder.func.arg_values[..] else {
        unreachable!()
    };
    let zero = builder.make_imm_value(Immediate::from_i256(I256::from(0), Type::I256));
    let one = builder.make_imm_value(Immediate::from_i256(I256::from(1), Type::I256));
    let byte = builder.make_imm_value(Immediate::from_i256(I256::from(255), Type::I256));

    builder.switch_to_block(entry);
    builder.insert_inst_no_result(Jump::new(is, body));

    builder.switch_to_block(body);
    let i = builder.insert_inst(Phi::new(is, vec![(zero, entry)].into()), Type::I256);
    let from = builder.insert_inst(Add::new(is, src, i), Type::I256);
    let loaded = builder.insert_inst(EvmMload::new(is, from), Type::I256);
    let masked = builder.insert_inst(And::new(is, loaded, byte), Type::I256);
    let to = builder.insert_inst(Add::new(is, dst, i), Type::I256);
    builder.insert_inst_no_result(EvmMstore8::new(is, to, masked));
    let next = builder.insert_inst(Add::new(is, i, one), Type::I256);
    builder.append_phi_arg(i, next, body);
    let more = builder.insert_inst(Lt::new(is, next, n), Type::I256);
    builder.insert_inst_no_result(Br::new(is, more, body, exit));

    builder.switch_to_block(exit);
    builder.insert_inst_no_result(Return::new_unit(is));
    builder.seal_all();
    builder.finish();

    let module = mb.build();
    run_machine_opt_pipeline(
        &module,
        &[func_ref],
        LateCleanupProfile::Speed,
        SwitchLoweringStrategy::Auto,
        16,
        None,
    )
    .expect("machine pipeline should run");
    module.func_store.view(func_ref, |function| {
        let dumped = FuncWriter::new(func_ref, function).dump_string();
        assert!(!dumped.contains(" and "), "{dumped}");
    });
}

#[test]
fn machine_verify_accepts_word_branch_condition() {
    let mb = machine_builder();
    let func_ref = mb
        .declare_function(Signature::new_single(
            "machine_word_branch",
            Linkage::Public,
            &[Type::I256],
            Type::I256,
        ))
        .unwrap();
    let machine = EvmMachine::new(mb.triple());
    let is = machine.inst_set();
    let mut builder = mb.func_builder::<InstInserter>(func_ref);

    let entry = builder.append_block();
    let nz = builder.append_block();
    let z = builder.append_block();
    builder.switch_to_block(entry);
    let cond = builder.func.arg_values[0];
    builder.insert_inst_no_result(Br::new(is, cond, nz, z));
    builder.switch_to_block(nz);
    builder.insert_inst_no_result(Return::new_single(is, cond));
    builder.switch_to_block(z);
    builder.insert_inst_no_result(Return::new_single(is, cond));
    builder.seal_all();
    builder.finish();

    let module = mb.build();
    module.func_store.view(func_ref, |function| {
        verify_machine_function(func_ref, function)
            .expect("machine branches can test any word-shaped EVM stack value");
    });
}

#[test]
fn machine_gvn_accepts_truthy_word_branch_condition() {
    let mb = machine_builder();
    let func_ref = mb
        .declare_function(Signature::new_single(
            "machine_gvn_word_branch",
            Linkage::Public,
            &[Type::I256],
            Type::I256,
        ))
        .unwrap();
    let machine = EvmMachine::new(mb.triple());
    let is = machine.inst_set();
    let mut builder = mb.func_builder::<InstInserter>(func_ref);

    let entry = builder.append_block();
    let nz = builder.append_block();
    let z = builder.append_block();
    builder.switch_to_block(entry);
    let cond = builder.func.arg_values[0];
    builder.insert_inst_no_result(Br::new(is, cond, nz, z));
    builder.switch_to_block(nz);
    builder.insert_inst_no_result(Return::new_single(is, cond));
    builder.switch_to_block(z);
    let zero = builder.make_imm_value(Immediate::zero(Type::I256));
    builder.insert_inst_no_result(Return::new_single(is, zero));
    builder.seal_all();
    builder.finish();

    let module = mb.build();
    run_machine_opt_pipeline(
        &module,
        &[func_ref],
        LateCleanupProfile::Off,
        SwitchLoweringStrategy::Auto,
        16,
        None,
    )
    .expect("GVN should accept truthy word branch conditions");
}

#[test]
fn machine_branch_canonicalize_folds_is_zero_into_branch_polarity() {
    let mb = machine_builder();
    let func_ref = mb
        .declare_function(Signature::new_single(
            "machine_branch_is_zero",
            Linkage::Public,
            &[Type::I256],
            Type::I256,
        ))
        .unwrap();
    let machine = EvmMachine::new(mb.triple());
    let is = machine.inst_set();
    let mut builder = mb.func_builder::<InstInserter>(func_ref);

    let entry = builder.append_block();
    let nz = builder.append_block();
    let z = builder.append_block();
    builder.switch_to_block(entry);
    let arg = builder.func.arg_values[0];
    let cond = builder.insert_inst(IsZero::new(is, arg), Type::I256);
    builder.insert_inst_no_result(Br::new(is, cond, nz, z));
    builder.switch_to_block(nz);
    builder.insert_inst_no_result(Jump::new(is, z));
    builder.switch_to_block(z);
    builder.insert_inst_no_result(Return::new_single(is, arg));
    builder.seal_all();
    builder.finish();

    let module = mb.build();
    module.func_store.modify(func_ref, |function| {
        assert!(canonicalize_machine_branch_conditions(function));
        let term = function
            .layout
            .last_inst_of(entry)
            .expect("entry has terminator");
        let branch = function
            .dfg
            .branch_info(term)
            .expect("entry terminator is branch");
        let BranchKind::Br(br) = branch.branch_kind() else {
            panic!("expected branch terminator");
        };
        assert_eq!(*br.cond(), arg);
        assert_eq!(*br.nz_dest(), z);
        assert_eq!(*br.z_dest(), nz);
        assert!(
            function.layout.iter_inst(entry).all(|inst| !matches!(
                function.dfg.inst(inst).kind(),
                sonatina_ir::inst::InstClassKind::Unary(sonatina_ir::inst::UnaryInstKind::IsZero)
            )),
            "dead is_zero should be removed"
        );
        verify_machine_function(func_ref, function).expect("rewritten machine IR should verify");
    });
}

#[test]
fn machine_verify_rejects_high_level_ops_and_pointer_values() {
    let mb = machine_builder();
    let ptr_ty = mb.ptr_type(Type::I256);
    let func_ref = mb
        .declare_function(Signature::new_single(
            "machine_bad",
            Linkage::Public,
            &[],
            ptr_ty,
        ))
        .unwrap();
    let machine = EvmMachine::new(mb.triple());
    let machine_is = machine.inst_set();
    let evm = Evm::new(mb.triple());
    let evm_is = evm.inst_set();
    let mut builder = mb.func_builder::<InstInserter>(func_ref);

    let block = builder.append_block();
    builder.switch_to_block(block);
    let ptr = builder.insert_inst(Alloca::new(evm_is, Type::I256), ptr_ty);
    builder.insert_inst_no_result(Return::new_single(machine_is, ptr));
    builder.seal_all();
    builder.finish();

    let module = mb.build();
    module.func_store.view(func_ref, |function| {
        let err = verify_machine_function(func_ref, function)
            .expect_err("pointer-typed high-level IR should be rejected");
        assert!(
            err.contains("must be i256,") || err.contains("unsupported instruction"),
            "{err}"
        );
    });
}

#[test]
fn machine_verify_rejects_high_level_instruction_families() {
    let cases = [
        r#"
target = "evm-ethereum-osaka"

func public %bad() -> *i8 {
block0:
    v0.*i8 = evm_malloc 32.i256;
    return v0;
}
"#,
        r#"
target = "evm-ethereum-osaka"

func public %bad() -> *i256 {
block0:
    v0.*i256 = alloca i256;
    return v0;
}
"#,
        r#"
target = "evm-ethereum-osaka"

func public %bad(v0.*i256) -> *i256 {
block0:
    v1.*i256 = gep v0 1.i256;
    return v1;
}
"#,
        r#"
target = "evm-ethereum-osaka"

func public %bad(v0.i256) -> i256 {
block0:
    v1.i256 = bitcast v0 i256;
    return v1;
}
"#,
        r#"
target = "evm-ethereum-osaka"

func public %bad(v0.i256) -> *i256 {
block0:
    v1.*i256 = int_to_ptr v0 *i256;
    return v1;
}
"#,
        r#"
target = "evm-ethereum-osaka"

func public %bad(v0.*i256) -> i256 {
block0:
    v1.i256 = ptr_to_int v0 i256;
    return v1;
}
"#,
        r#"
target = "evm-ethereum-osaka"

func public %bad(v0.i1) -> i256 {
block0:
    v1.i256 = zext v0 i256;
    return v1;
}
"#,
        r#"
target = "evm-ethereum-osaka"

func public %bad(v0.i1) -> i256 {
block0:
    v1.i256 = sext v0 i256;
    return v1;
}
"#,
        r#"
target = "evm-ethereum-osaka"

func public %bad(v0.i256) -> i256 {
block0:
    v1.i8 = trunc v0 i8;
    v2.i256 = zext v1 i256;
    return v2;
}
"#,
        r#"
target = "evm-ethereum-osaka"

func private %bad() -> objref<i256> {
block0:
    v0.objref<i256> = obj.alloc i256;
    return v0;
}
"#,
        r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

func private %bad() -> @OptionI256 {
block0:
    v0.@OptionI256 = enum.make @OptionI256 #Some (1.i256);
    return v0;
}
"#,
    ];

    for src in cases {
        expect_machine_rejects(src);
    }
}

/// `lt (and y 15) (or z 16)` is always 1, so `eq` of it with 1 is 1, `mul` of that with `x`
/// is `x`, and the result is `x & 255`.
fn build_decided_compare_mask(name: &str) -> (sonatina_ir::Module, sonatina_ir::module::FuncRef) {
    let mb = machine_builder();
    let func_ref = mb
        .declare_function(Signature::new_single(
            name,
            Linkage::Public,
            &[Type::I256, Type::I256, Type::I256],
            Type::I256,
        ))
        .unwrap();
    let machine = EvmMachine::new(mb.triple());
    let is = machine.inst_set();
    let mut builder = mb.func_builder::<InstInserter>(func_ref);

    let entry = builder.append_block();
    let [y, z, x] = builder.func.arg_values[..] else {
        unreachable!()
    };
    let imm = |builder: &mut sonatina_ir::builder::FunctionBuilder<InstInserter>, value: u32| {
        builder.make_imm_value(Immediate::from_i256(I256::from(value), Type::I256))
    };
    let fifteen = imm(&mut builder, 15);
    let sixteen = imm(&mut builder, 16);
    let one = imm(&mut builder, 1);
    let byte = imm(&mut builder, 255);

    builder.switch_to_block(entry);
    let low = builder.insert_inst(And::new(is, y, fifteen), Type::I256);
    let high = builder.insert_inst(Or::new(is, z, sixteen), Type::I256);
    let lt = builder.insert_inst(Lt::new(is, low, high), Type::I256);
    let is_one = builder.insert_inst(Eq::new(is, lt, one), Type::I256);
    let scaled = builder.insert_inst(Mul::new(is, is_one, x), Type::I256);
    let masked = builder.insert_inst(And::new(is, scaled, byte), Type::I256);
    builder.insert_inst_no_result(Return::new_single(is, masked));
    builder.seal_all();
    builder.finish();
    (mb.build(), func_ref)
}

#[test]
fn machine_known_bits_keeps_mask_after_decided_word_compare() {
    let (module, func_ref) = build_decided_compare_mask("machine_kb_decided_cmp");
    module.func_store.modify(func_ref, |function| {
        KnownBitsSimplify::new().run(function);
        let dumped = FuncWriter::new(func_ref, function).dump_string();
        assert!(dumped.contains("255.i256"), "{dumped}");
    });
}

#[test]
fn machine_pipeline_keeps_mask_after_decided_word_compare() {
    let (module, func_ref) = build_decided_compare_mask("machine_pipeline_decided_cmp");
    run_machine_opt_pipeline(
        &module,
        &[func_ref],
        LateCleanupProfile::Speed,
        SwitchLoweringStrategy::Auto,
        16,
        None,
    )
    .expect("machine pipeline should run");
    module.func_store.view(func_ref, |function| {
        let dumped = FuncWriter::new(func_ref, function).dump_string();
        assert!(dumped.contains("255.i256"), "{dumped}");
    });
}

#[test]
fn machine_range_of_decided_word_compare_is_one() {
    let (module, func_ref) = build_decided_compare_mask("machine_range_decided_cmp");
    module.func_store.view(func_ref, |function| {
        let mut cfg = ControlFlowGraph::default();
        cfg.compute(function);
        let mut domtree = DomTree::default();
        domtree.compute(&cfg);
        let mut loops = LoopTree::new();
        loops.compute(&cfg, &domtree);
        let mut analysis = RangeAnalysis::default();
        analysis.compute(function, &cfg, &domtree, &loops);

        let entry = function.layout.entry_block().unwrap();
        let results: Vec<_> = function
            .layout
            .iter_inst(entry)
            .filter_map(|inst| function.dfg.inst_result(inst))
            .collect();
        let [_, _, lt, is_one, ..] = results[..] else {
            unreachable!()
        };
        // Replay the block as `KnownBitsSimplify` does: the stored exit env keeps only the
        // values later blocks read.
        let mut env = analysis.entry_env(entry).clone();
        for inst in function.layout.iter_inst(entry) {
            analysis.transfer_inst(function, &mut env, inst);
        }
        let one = RangeFact::singleton(Immediate::one(Type::I256));
        assert_eq!(env.get(&lt), Some(&one));
        assert_eq!(env.get(&is_one), Some(&one));
    });
}

/// `br (not (is_zero (lt a b)))`: `is_zero` gives 0 or 1, so the word `not` is never zero and the
/// branch always goes to `nz`. There `sub (lt a b) 1` is `2**256 - 1` when `a >= b`.
fn build_word_not_branch(name: &str) -> (sonatina_ir::Module, sonatina_ir::module::FuncRef) {
    let mb = machine_builder();
    let func_ref = mb
        .declare_function(Signature::new_single(
            name,
            Linkage::Public,
            &[Type::I256, Type::I256],
            Type::I256,
        ))
        .unwrap();
    let machine = EvmMachine::new(mb.triple());
    let is = machine.inst_set();
    let mut builder = mb.func_builder::<InstInserter>(func_ref);

    let entry = builder.append_block();
    let nz = builder.append_block();
    let z = builder.append_block();
    let [a, b] = builder.func.arg_values[..] else {
        unreachable!()
    };
    let one = builder.make_imm_value(Immediate::from_i256(I256::from(1), Type::I256));
    let zero = builder.make_imm_value(Immediate::zero(Type::I256));

    builder.switch_to_block(entry);
    let lt = builder.insert_inst(Lt::new(is, a, b), Type::I256);
    let is_zero = builder.insert_inst(IsZero::new(is, lt), Type::I256);
    let not = builder.insert_inst(Not::new(is, is_zero), Type::I256);
    builder.insert_inst_no_result(Br::new(is, not, nz, z));

    builder.switch_to_block(nz);
    let diff = builder.insert_inst(Sub::new(is, lt, one), Type::I256);
    builder.insert_inst_no_result(Return::new_single(is, diff));

    builder.switch_to_block(z);
    builder.insert_inst_no_result(Return::new_single(is, zero));
    builder.seal_all();
    builder.finish();
    (mb.build(), func_ref)
}

#[test]
fn machine_gvn_keeps_compare_under_word_not_branch() {
    let (module, func_ref) = build_word_not_branch("machine_gvn_word_not");
    module.func_store.modify(func_ref, |function| {
        let mut cfg = ControlFlowGraph::default();
        cfg.compute(function);
        let mut domtree = DomTree::default();
        domtree.compute(&cfg);
        GvnSolver::new().run(function, &mut cfg, &mut domtree);
        let dumped = FuncWriter::new(func_ref, function).dump_string();
        assert!(dumped.contains(" sub "), "{dumped}");
    });
}

#[test]
fn machine_pipeline_keeps_compare_under_word_not_branch() {
    let (module, func_ref) = build_word_not_branch("machine_pipeline_word_not");
    run_machine_opt_pipeline(
        &module,
        &[func_ref],
        LateCleanupProfile::Speed,
        SwitchLoweringStrategy::Auto,
        16,
        None,
    )
    .expect("machine pipeline should run");
    module.func_store.view(func_ref, |function| {
        let dumped = FuncWriter::new(func_ref, function).dump_string();
        assert!(dumped.contains(" sub "), "{dumped}");
    });
}

/// `block1` defines `v` and jumps to `block3`, which `block2` also reaches. `block3` returns
/// `v` itself, which `block1` does not dominate, or a phi of `v` from `block1`.
fn build_join_of_branch_value(
    name: &str,
    through_phi: bool,
) -> (sonatina_ir::Module, sonatina_ir::module::FuncRef) {
    let mb = machine_builder();
    let func_ref = mb
        .declare_function(Signature::new_single(
            name,
            Linkage::Public,
            &[Type::I256],
            Type::I256,
        ))
        .unwrap();
    let machine = EvmMachine::new(mb.triple());
    let is = machine.inst_set();
    let mut builder = mb.func_builder::<InstInserter>(func_ref);

    let entry = builder.append_block();
    let then_block = builder.append_block();
    let else_block = builder.append_block();
    let join = builder.append_block();
    let arg = builder.func.arg_values[0];
    let one = builder.make_imm_value(Immediate::one(Type::I256));

    builder.switch_to_block(entry);
    builder.insert_inst_no_result(Br::new(is, arg, then_block, else_block));
    builder.switch_to_block(then_block);
    let value = builder.insert_inst(Add::new(is, arg, one), Type::I256);
    builder.insert_inst_no_result(Jump::new(is, join));
    builder.switch_to_block(else_block);
    builder.insert_inst_no_result(Jump::new(is, join));
    builder.switch_to_block(join);
    let result = if through_phi {
        builder.insert_inst(
            Phi::new(is, vec![(value, then_block), (arg, else_block)].into()),
            Type::I256,
        )
    } else {
        value
    };
    builder.insert_inst_no_result(Return::new_single(is, result));
    builder.seal_all();
    builder.finish();
    (mb.build(), func_ref)
}

#[test]
fn machine_verify_accepts_phi_of_branch_value() {
    let (module, func_ref) = build_join_of_branch_value("machine_phi_join", true);
    module.func_store.view(func_ref, |function| {
        verify_machine_function(func_ref, function).expect("valid machine IR should verify");
    });
}

#[test]
fn machine_verify_rejects_use_not_dominated_by_its_definition() {
    let (module, func_ref) = build_join_of_branch_value("machine_bad_join", false);
    module.func_store.view(func_ref, |function| {
        let err = verify_machine_function(func_ref, function)
            .expect_err("a use outside its definition's dominance should be rejected");
        assert!(
            err.contains("value definition does not dominate its use"),
            "{err}"
        );
    });
}

#[test]
fn machine_verify_rejects_use_of_detached_definition() {
    let (module, func_ref) = build_join_of_branch_value("machine_detached_def", true);
    module.func_store.modify(func_ref, |function| {
        // Take the `add` out of the layout; the phi still uses its result.
        let add = function
            .layout
            .iter_block()
            .flat_map(|block| function.layout.iter_inst(block))
            .find(|&inst| {
                function.dfg.cast_phi(inst).is_none() && function.dfg.inst_result(inst).is_some()
            })
            .unwrap();
        function.layout.remove_inst(add);
        let err = verify_machine_function(func_ref, function)
            .expect_err("a use of a definition outside the layout should be rejected");
        assert!(err.contains("detached value definition"), "{err}");
    });
}
