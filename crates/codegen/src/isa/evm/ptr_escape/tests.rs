use super::*;
use sonatina_ir::{InstSetExt, inst::evm::inst_set::EvmInstKind, isa::Isa};
use sonatina_parser::parse_module;
use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

fn arg_may_escape(summary: &PtrEscapeSummary) -> Vec<bool> {
    (0..summary.arg_count())
        .map(|idx| summary.arg_may_escape(idx))
        .collect()
}

fn arg_may_be_returned(summary: &PtrEscapeSummary) -> Vec<bool> {
    (0..summary.arg_count())
        .map(|idx| summary.arg_may_be_returned(idx))
        .collect()
}

fn ret_args(summary: &PtrEscapeSummary, ret_idx: usize) -> Vec<u32> {
    summary.returned_arg_indices(ret_idx).to_vec()
}

fn arg_store_targets(summary: &PtrEscapeSummary, idx: usize) -> Vec<u32> {
    summary.arg_store_targets(idx).to_vec()
}

fn compute(
    src: &str,
) -> (
    FxHashMap<String, PtrEscapeSummary>,
    FxHashMap<String, FuncRef>,
) {
    let parsed = parse_module(src).unwrap();
    let funcs: Vec<FuncRef> = parsed.module.funcs();
    let mut names: FxHashMap<String, FuncRef> = FxHashMap::default();
    for f in funcs.iter().copied() {
        let name = parsed.module.ctx.func_sig(f, |sig| sig.name().to_string());
        names.insert(name, f);
    }

    let isa = Evm::new(TargetTriple {
        architecture: Architecture::Evm,
        vendor: Vendor::Ethereum,
        operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
    });

    let summaries = compute_ptr_escape_summaries(&parsed.module, &funcs, &isa);

    let mut out: FxHashMap<String, PtrEscapeSummary> = FxHashMap::default();
    for (name, f) in &names {
        if let Some(sum) = summaries.get(f) {
            out.insert(name.clone(), sum.clone());
        }
    }

    (out, names)
}

fn call_arg_may_escape_from_src(src: &str, func_name: &str, arg_index: usize) -> bool {
    let parsed = parse_module(src).expect("module parses");
    let funcs: Vec<FuncRef> = parsed.module.funcs();
    let isa = Evm::new(TargetTriple {
        architecture: Architecture::Evm,
        vendor: Vendor::Ethereum,
        operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
    });
    let summaries = compute_ptr_escape_summaries(&parsed.module, &funcs, &isa);
    let func_ref = parsed
        .module
        .funcs()
        .into_iter()
        .find(|&func| {
            parsed
                .module
                .ctx
                .func_sig(func, |sig| sig.name() == func_name)
        })
        .expect("function exists");

    parsed.module.func_store.view(func_ref, |function| {
        let prov = compute_provenance(function, &parsed.module.ctx, &isa, |callee| {
            PtrEscapeSummary::get_or_conservative(&summaries, &parsed.module.ctx, callee)
        })
        .value;
        let call_inst = function
            .layout
            .iter_block()
            .flat_map(|block| function.layout.iter_inst(block))
            .find(|&inst| function.dfg.call_info(inst).is_some())
            .expect("call exists");
        let EvmInstKind::Call(call) = isa.inst_set().resolve_inst(function.dfg.inst(call_inst))
        else {
            panic!("expected internal call");
        };
        let callee_sum =
            PtrEscapeSummary::get_or_conservative(&summaries, &parsed.module.ctx, *call.callee());

        callee_sum.call_arg_may_escape_nonlocal(arg_index, call.args(), &prov)
    })
}

fn ret_provenance_from_src(src: &str, func_name: &str) -> Provenance {
    let parsed = parse_module(src).expect("module parses");
    let funcs: Vec<FuncRef> = parsed.module.funcs();
    let isa = Evm::new(TargetTriple {
        architecture: Architecture::Evm,
        vendor: Vendor::Ethereum,
        operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
    });
    let summaries = compute_ptr_escape_summaries(&parsed.module, &funcs, &isa);
    let func_ref = parsed
        .module
        .funcs()
        .into_iter()
        .find(|&func| {
            parsed
                .module
                .ctx
                .func_sig(func, |sig| sig.name() == func_name)
        })
        .expect("function exists");

    parsed.module.func_store.view(func_ref, |function| {
        let prov = compute_provenance(function, &parsed.module.ctx, &isa, |callee| {
            PtrEscapeSummary::get_or_conservative(&summaries, &parsed.module.ctx, callee)
        })
        .value;

        for block in function.layout.iter_block() {
            for inst in function.layout.iter_inst(block) {
                let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));
                if let EvmInstKind::Return(_) = data
                    && let Some(ret_val) = function
                        .dfg
                        .return_args(inst)
                        .and_then(|args| args.first().copied())
                {
                    return prov[ret_val].clone();
                }
            }
        }

        panic!("no return value in function");
    })
}

#[test]
fn ptr_escape_direct_return() {
    let (summaries, _) = compute(
        r#"
target = "evm-ethereum-osaka"

func public %g(v0.*i8) -> *i8 {
block0:
return v0;
}
"#,
    );

    let g = &summaries["g"];
    assert_eq!(ret_args(g, 0), vec![0]);
    assert!(!g.return_may_be_non_arg_pointer(0));
    assert_eq!(arg_may_be_returned(g), vec![true]);
    assert_eq!(arg_may_escape(g), vec![false]);
}

#[test]
fn ptr_escape_propagates_through_calls() {
    let (summaries, _) = compute(
        r#"
target = "evm-ethereum-osaka"

func public %sink(v0.*i8) {
block0:
mstore 0.i32 v0 *i8;
return;
}

func public %f(v0.*i8) {
block0:
call %sink v0;
return;
}
"#,
    );

    let sink = &summaries["sink"];
    assert_eq!(arg_may_escape(sink), vec![true]);

    let f = &summaries["f"];
    assert_eq!(arg_may_escape(f), vec![true]);
}

#[test]
fn ptr_escape_call_return_flow() {
    let (summaries, _) = compute(
        r#"
target = "evm-ethereum-osaka"

func public %id(v0.*i8) -> *i8 {
block0:
return v0;
}

func public %f(v0.*i8) -> *i8 {
block0:
v1.*i8 = call %id v0;
return v1;
}
"#,
    );

    let f = &summaries["f"];
    assert_eq!(ret_args(f, 0), vec![0]);
    assert!(!f.return_may_be_non_arg_pointer(0));
    assert_eq!(arg_may_be_returned(f), vec![true]);
    assert_eq!(arg_may_escape(f), vec![false]);
}

#[test]
fn ptr_escape_tracks_i256_arg_returned_in_aggregate() {
    let (summaries, _) = compute(
        r#"
target = "evm-ethereum-osaka"

type @Box = {i256};

func public %box(v0.i256) -> @Box {
block0:
v1.@Box = insert_value undef.@Box 0.i256 v0;
return v1;
}
"#,
    );

    let boxed = &summaries["box"];
    assert_eq!(ret_args(boxed, 0), vec![0]);
    assert_eq!(arg_may_be_returned(boxed), vec![true]);
    assert_eq!(arg_may_escape(boxed), vec![false]);
}

#[test]
fn ptr_escape_tracks_i256_store_into_i256_out_param_conditionally() {
    let (summaries, _) = compute(
        r#"
target = "evm-ethereum-osaka"

func public %capture(v0.i256, v1.i256) {
block0:
mstore v1 v0 i256;
return;
}
"#,
    );

    let capture = &summaries["capture"];
    assert_eq!(arg_may_escape(capture), vec![false, false]);
    assert_eq!(arg_store_targets(capture, 0), vec![1]);
    assert!(capture.arg_store_lattice(0).may_store_to_arg());
    assert!(!capture.arg_store_lattice(0).may_store_nonlocal());
}

#[test]
fn ptr_escape_tracks_i256_malloc_return_as_non_arg_pointer() {
    let (summaries, _) = compute(
        r#"
target = "evm-ethereum-osaka"

func public %mk() -> i256 {
block0:
v0.*i8 = evm_malloc 32.i256;
v1.i256 = ptr_to_int v0 i256;
return v1;
}
"#,
    );

    let mk = &summaries["mk"];
    assert!(mk.return_may_be_non_arg_pointer(0));
    assert!(ret_args(mk, 0).is_empty());
    assert_eq!(arg_may_be_returned(mk), Vec::<bool>::new());
}

#[test]
fn ptr_escape_keeps_i256_arg_store_into_local_malloc_local() {
    let (summaries, _) = compute(
        r#"
target = "evm-ethereum-osaka"

func public %scratch(v0.i256) {
block0:
v1.*i8 = evm_malloc 32.i256;
v2.i256 = ptr_to_int v1 i256;
mstore v2 v0 i256;
return;
}
"#,
    );

    let scratch = &summaries["scratch"];
    assert_eq!(arg_may_escape(scratch), vec![false]);
    assert!(scratch.arg_store_lattice(0).may_store_local());
    assert!(!scratch.arg_store_lattice(0).may_store_nonlocal());
}

#[test]
fn ptr_escape_marks_i256_arg_stored_into_returned_malloc_as_escaping() {
    let (summaries, _) = compute(
        r#"
target = "evm-ethereum-osaka"

func public %box(v0.i256) -> i256 {
block0:
v1.*i8 = evm_malloc 32.i256;
v2.i256 = ptr_to_int v1 i256;
mstore v2 v0 i256;
return v2;
}
"#,
    );

    let boxed = &summaries["box"];
    assert!(boxed.return_may_be_non_arg_pointer(0));
    assert_eq!(arg_may_escape(boxed), vec![true]);
    assert_eq!(arg_may_be_returned(boxed), vec![false]);
}

#[test]
fn ptr_escape_closes_escaping_malloc_contents() {
    let (summaries, _) = compute(
        r#"
target = "evm-ethereum-osaka"

func public %box(v0.i256) -> i256 {
block0:
v1.*i8 = evm_malloc 32.i256;
v2.i256 = ptr_to_int v1 i256;
mstore v2 v0 i256;
v3.*i8 = evm_malloc 32.i256;
v4.i256 = ptr_to_int v3 i256;
mstore v4 v2 i256;
return v4;
}
"#,
    );

    let boxed = &summaries["box"];
    assert!(boxed.return_may_be_non_arg_pointer(0));
    assert_eq!(arg_may_escape(boxed), vec![true]);
    assert_eq!(arg_may_be_returned(boxed), vec![false]);
}

#[test]
fn conservative_unknown_i256_return_is_not_pointer_provenance() {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

func public %f(v0.i256) -> i256 {
block0:
return 0.i256;
}
"#,
    )
    .expect("module parses");
    let f = parsed
        .module
        .funcs()
        .into_iter()
        .find(|&func| parsed.module.ctx.func_sig(func, |sig| sig.name() == "f"))
        .expect("function exists");

    let summary = PtrEscapeSummary::conservative_unknown_ctx(&parsed.module.ctx, f);
    assert!(!summary.return_may_be_non_arg_pointer(0));
    assert_eq!(ret_args(&summary, 0), Vec::<u32>::new());
}

#[test]
fn conservative_unknown_i256_args_do_not_create_pointer_store_effects() {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

func public %scalar(v0.i256, v1.i256) {
block0:
return;
}

func public %ptr(v0.*i8, v1.*i8) {
block0:
return;
}
"#,
    )
    .expect("module parses");
    let scalar = parsed
        .module
        .funcs()
        .into_iter()
        .find(|&func| {
            parsed
                .module
                .ctx
                .func_sig(func, |sig| sig.name() == "scalar")
        })
        .expect("function exists");
    let ptr = parsed
        .module
        .funcs()
        .into_iter()
        .find(|&func| parsed.module.ctx.func_sig(func, |sig| sig.name() == "ptr"))
        .expect("function exists");

    let scalar = PtrEscapeSummary::conservative_unknown_ctx(&parsed.module.ctx, scalar);
    assert_eq!(arg_may_escape(&scalar), vec![false, false]);
    assert_eq!(arg_store_targets(&scalar, 0), Vec::<u32>::new());
    assert_eq!(arg_store_targets(&scalar, 1), Vec::<u32>::new());

    let ptr = PtrEscapeSummary::conservative_unknown_ctx(&parsed.module.ctx, ptr);
    assert_eq!(arg_may_escape(&ptr), vec![true, true]);
    assert_eq!(arg_store_targets(&ptr, 0), vec![0, 1]);
    assert_eq!(arg_store_targets(&ptr, 1), vec![0, 1]);
}

#[test]
fn ptr_escape_does_not_forward_i256_arg_after_narrowing_to_noncarrier() {
    let (summaries, _) = compute(
        r#"
target = "evm-ethereum-osaka"

func public %capture(v0.i256, v1.i256) {
block0:
v2.i8 = trunc v0 i8;
mstore v1 v2 i8;
return;
}
"#,
    );

    let capture = &summaries["capture"];
    assert_eq!(arg_may_escape(capture), vec![false, false]);
    assert_eq!(arg_store_targets(capture, 0), Vec::<u32>::new());
}

#[test]
fn ptr_escape_non_arg_unknown_return_does_not_mark_all_args_returned() {
    let (summaries, _) = compute(
        r#"
target = "evm-ethereum-osaka"

func public %f(v0.*i8, v1.*i8) -> *i8 {
block0:
v2.*i8 = int_to_ptr 0.i32 *i8;
return v2;
}
"#,
    );

    let f = &summaries["f"];
    assert!(f.return_may_be_non_arg_pointer(0));
    assert_eq!(arg_may_be_returned(f), vec![false, false]);
    assert_eq!(arg_may_escape(f), vec![false, false]);
}

#[test]
fn ptr_escape_non_arg_unknown_store_does_not_mark_all_args_escape() {
    let (summaries, _) = compute(
        r#"
target = "evm-ethereum-osaka"

func public %f(v0.*i8, v1.*i8) {
block0:
v2.*i8 = int_to_ptr 0.i32 *i8;
mstore 0.i32 v2 *i8;
return;
}
"#,
    );

    let f = &summaries["f"];
    assert_eq!(arg_may_be_returned(f), vec![false, false]);
    assert_eq!(arg_may_escape(f), vec![false, false]);
}

#[test]
fn ptr_escape_tracks_pointer_store_into_out_param_arg_conditionally() {
    let (summaries, _) = compute(
        r#"
target = "evm-ethereum-osaka"

func public %capture(v0.*i8, v1.**i8) {
block0:
mstore v1 v0 *i8;
return;
}
"#,
    );

    let capture = &summaries["capture"];
    assert_eq!(arg_may_escape(capture), vec![false, false]);
    assert_eq!(arg_may_be_returned(capture), vec![false, false]);
    assert_eq!(
        arg_store_targets(capture, 0),
        vec![1],
        "arg 0 should only escape through arg 1"
    );
    assert!(
        capture.arg_store_targets(1).is_empty(),
        "out-param itself should not be marked as forwarded"
    );
    assert!(capture.arg_store_lattice(0).may_store_to_arg());
    assert!(!capture.arg_store_lattice(0).may_store_nonlocal());
}

#[test]
fn ptr_escape_preserves_self_target_arg_stores() {
    let (summaries, _) = compute(
        r#"
target = "evm-ethereum-osaka"

func public %capture(v0.**i8) {
block0:
mstore v0 v0 **i8;
return;
}
"#,
    );

    let capture = &summaries["capture"];
    assert_eq!(arg_may_escape(capture), vec![false]);
    assert_eq!(arg_may_be_returned(capture), vec![false]);
    assert_eq!(
        arg_store_targets(capture, 0),
        vec![0],
        "self-target out-param stores must stay modeled"
    );
    assert!(capture.arg_store_lattice(0).may_store_to_arg());
    assert!(!capture.arg_store_lattice(0).may_store_nonlocal());
}

#[test]
fn ptr_escape_self_target_call_preserves_local_roundtrip_provenance() {
    let ret_prov = ret_provenance_from_src(
        r#"
target = "evm-ethereum-osaka"

func public %capture(v0.**i8) {
block0:
mstore v0 v0 **i8;
return;
}

func public %wrapper() -> **i8 {
block0:
v0.**i8 = alloca *i8;
call %capture v0;
v1.**i8 = mload v0 **i8;
return v1;
}
"#,
        "wrapper",
    );

    assert!(ret_prov.is_local_addr(), "{ret_prov:?}");
    assert_eq!(ret_prov.alloca_insts().count(), 1);
}

#[test]
fn ptr_escape_keeps_nonlocal_outparam_destinations_context_sensitive() {
    let src = r#"
target = "evm-ethereum-osaka"

func public %capture(v0.*i8, v1.**i8) {
block0:
mstore v1 v0 *i8;
mstore 0.i32 v1 **i8;
return;
}

func public %top_arg(v0.*i8, v1.**i8) {
block0:
call %capture v0 v1;
return;
}

func public %top_local(v0.*i8) {
block0:
v1.**i8 = alloca *i8;
call %capture v0 v1;
return;
}
"#;
    let (summaries, _) = compute(src);

    let capture = &summaries["capture"];
    assert_eq!(arg_may_escape(capture), vec![false, true]);
    assert_eq!(
        arg_store_targets(capture, 0),
        vec![1],
        "source arg should keep only the forwarded out-param target"
    );
    assert!(!capture.arg_store_lattice(0).may_store_nonlocal());
    assert!(capture.arg_store_lattice(0).may_store_to_arg());
    assert!(capture.arg_store_lattice(1).may_store_nonlocal());

    assert!(
        call_arg_may_escape_from_src(src, "top_arg", 0),
        "arg-backed out-param should still make the source escape"
    );
    assert!(
        !call_arg_may_escape_from_src(src, "top_local", 0),
        "caller-local out-param should remain non-escaping"
    );
}

#[test]
fn ptr_escape_local_out_param_capture_does_not_mark_caller_arg_escape() {
    let (summaries, _) = compute(
        r#"
target = "evm-ethereum-osaka"

type @Take = {i256, *[i256; 8]};

func public %take(v7.*@Take, v0.i256, v1.*[i256; 8]) {
block0:
v3.*i256 = bitcast v7 *i256;
mstore v3 v0 i256;
v4.**[i256; 8] = gep v7 0.i256 1.i256;
mstore v4 v1 *[i256; 8];
return;
}

func public %take_get(v0.*@Take, v1.i256) -> i256 {
block0:
v3.**[i256; 8] = gep v0 0.i256 1.i256;
v4.*[i256; 8] = mload v3 *[i256; 8];
v5.*i256 = gep v4 0.i256 v1;
v6.i256 = mload v5 i256;
return v6;
}

func public %sum_last4(v0.*[i256; 8]) -> i256 {
block0:
v1.*@Take = alloca @Take;
call %take v1 4.i256 v0;
v2.i256 = call %take_get v1 0.i256;
return v2;
}
"#,
    );

    let take = &summaries["take"];
    assert_eq!(arg_may_escape(take), vec![false, false, false]);
    assert_eq!(
        arg_store_targets(take, 2),
        vec![0],
        "take should forward arg 2 only into the synthetic out-param"
    );

    let sum_last4 = &summaries["sum_last4"];
    assert_eq!(
        arg_may_escape(sum_last4),
        vec![false],
        "caller-local synthetic out-param must not count as an escape"
    );
}

#[test]
fn ptr_escape_resolves_outparam_arg_escapes_through_callers() {
    let src = r#"
target = "evm-ethereum-osaka"

func public %capture(v0.*i8, v1.**i8) {
block0:
mstore v1 v0 *i8;
return;
}

func public %wrapper(v0.*i8, v1.**i8) {
block0:
call %capture v0 v1;
return;
}

func public %through_arg(v0.*i8, v1.**i8) {
block0:
call %wrapper v0 v1;
return;
}

func public %top_arg(v0.*i8, v1.**i8) {
block0:
call %through_arg v0 v1;
return;
}

func public %top_local(v0.*i8) {
block0:
v1.**i8 = alloca *i8;
call %through_arg v0 v1;
return;
}
"#;
    let (summaries, _) = compute(src);

    let wrapper = &summaries["wrapper"];
    assert_eq!(arg_may_escape(wrapper), vec![false, false]);
    assert_eq!(
        arg_store_targets(wrapper, 0),
        vec![1],
        "wrapper should still record that arg 0 flows into arg 1"
    );

    let through_arg = &summaries["through_arg"];
    assert_eq!(
        arg_may_escape(through_arg),
        vec![false, false],
        "intermediate wrappers should keep arg-backed stores contextual"
    );

    assert!(
        call_arg_may_escape_from_src(src, "top_arg", 0),
        "argument-backed out-param should mark the source arg as escaping at the caller boundary"
    );

    assert!(
        !call_arg_may_escape_from_src(src, "top_local", 0),
        "caller-local synthetic out-param must stay non-escaping"
    );
}

#[test]
fn ptr_escape_store_lattice_covers_direct_and_mixed_destinations() {
    type PtrEscapeCase = (&'static str, &'static str, fn(&PtrEscapeSummary));

    let cases: [PtrEscapeCase; 4] = [
        (
            "direct_nonlocal",
            r#"
target = "evm-ethereum-osaka"

func public %f(v0.*i8) {
block0:
mstore 0.i32 v0 *i8;
return;
}
"#,
            |summary: &PtrEscapeSummary| {
                assert_eq!(arg_may_escape(summary), vec![true]);
                assert!(summary.arg_store_lattice(0).may_store_nonlocal());
                assert!(!summary.arg_store_lattice(0).may_store_local());
                assert!(!summary.arg_store_lattice(0).may_store_to_arg());
            },
        ),
        (
            "wrapper_arg",
            r#"
target = "evm-ethereum-osaka"

func public %capture(v0.*i8, v1.**i8) {
block0:
mstore v1 v0 *i8;
return;
}

func public %f(v0.*i8, v1.**i8) {
block0:
call %capture v0 v1;
return;
}
"#,
            |summary: &PtrEscapeSummary| {
                assert_eq!(arg_may_escape(summary), vec![false, false]);
                assert!(!summary.arg_store_lattice(0).may_store_local());
                assert!(summary.arg_store_lattice(0).may_store_to_arg());
                assert!(!summary.arg_store_lattice(0).may_store_nonlocal());
                assert_eq!(arg_store_targets(summary, 0), vec![1]);
            },
        ),
        (
            "wrapper_local",
            r#"
target = "evm-ethereum-osaka"

func public %capture(v0.*i8, v1.**i8) {
block0:
mstore v1 v0 *i8;
return;
}

func public %f(v0.*i8) {
block0:
v1.**i8 = alloca *i8;
call %capture v0 v1;
return;
}
"#,
            |summary: &PtrEscapeSummary| {
                assert_eq!(arg_may_escape(summary), vec![false]);
                assert!(summary.arg_store_lattice(0).may_store_local());
                assert!(!summary.arg_store_lattice(0).may_store_nonlocal());
                assert!(!summary.arg_store_lattice(0).may_store_to_arg());
            },
        ),
        (
            "mixed_destinations",
            r#"
target = "evm-ethereum-osaka"

func public %f(v0.*i8, v1.**i8, v2.i1) {
block0:
br v2 block1 block2;

block1:
mstore v1 v0 *i8;
return;

block2:
v3.**i8 = alloca *i8;
mstore v3 v0 *i8;
return;
}
"#,
            |summary: &PtrEscapeSummary| {
                assert_eq!(arg_may_escape(summary), vec![false, false, false]);
                assert!(summary.arg_store_lattice(0).may_store_local());
                assert!(summary.arg_store_lattice(0).may_store_to_arg());
                assert!(!summary.arg_store_lattice(0).may_store_nonlocal());
                assert_eq!(arg_store_targets(summary, 0), vec![1]);
            },
        ),
    ];

    for (name, src, check) in cases {
        let (summaries, _) = compute(src);
        check(
            summaries
                .get("f")
                .unwrap_or_else(|| panic!("missing summary for case {name}")),
        );
    }
}

#[test]
fn ptr_escape_no_transitive_closure_over_arg_store_targets() {
    let (summaries, _) = compute(
        r#"
target = "evm-ethereum-osaka"

func public %capture(v0.*i8, v1.**i8) {
block0:
mstore v1 v0 *i8;
return;
}

func public %forward(v0.*i8, v1.**i8, v2.***i8) {
block0:
call %capture v0 v1;
call %capture v1 v2;
return;
}
"#,
    );

    let forward = &summaries["forward"];
    assert_eq!(
        arg_store_targets(forward, 0),
        vec![1],
        "arg 0 stores to arg 1 only; no transitive closure to arg 2"
    );
    assert_eq!(
        arg_store_targets(forward, 1),
        vec![2],
        "arg 1 stores to arg 2 only"
    );
    assert_eq!(
        arg_may_escape(forward),
        vec![false, false, false],
        "no arg should be unconditionally nonlocal"
    );
}

#[test]
fn ptr_escape_mcopy_from_arg_attributes_stored_content_not_source_address() {
    let src = r#"
target = "evm-ethereum-osaka"

func public %relay(v0.*i8, v1.**i8, v2.**i8) {
block0:
mstore v1 v0 *i8;
evm_mcopy v2 v1 32.i256;
return;
}

func public %top_local(v0.*i8) {
block0:
v1.**i8 = alloca *i8;
v2.**i8 = alloca *i8;
call %relay v0 v1 v2;
return;
}

func public %top_nonlocal_dest(v0.*i8, v1.**i8) {
block0:
v2.**i8 = alloca *i8;
call %relay v0 v2 v1;
return;
}
"#;
    let (summaries, _) = compute(src);

    let relay = &summaries["relay"];
    // arg 0's value was stored at *arg1, then mcopy'd to *arg2.
    // The summary should attribute the escape to arg 0 (the content),
    // NOT to arg 1 (the source address).
    assert_eq!(
        arg_store_targets(relay, 0),
        vec![1, 2],
        "arg 0 should flow to both arg 1 (via mstore) and arg 2 (via mcopy of *arg1)"
    );
    assert!(
        !relay.arg_store_targets(1).contains(&2),
        "arg 1 (source address) should NOT be recorded as storing to arg 2"
    );
    assert_eq!(
        arg_may_escape(relay),
        vec![false, false, false],
        "no arg should be unconditionally nonlocal"
    );

    // When both the mstore dest and mcopy dest are caller-local,
    // no escape should be reported.
    assert!(
        !call_arg_may_escape_from_src(src, "top_local", 0),
        "arg 0 should not escape when all destinations are caller-local"
    );

    // When the mcopy destination is nonlocal, arg 0 should escape.
    assert!(
        call_arg_may_escape_from_src(src, "top_nonlocal_dest", 0),
        "arg 0 should escape when mcopy destination is nonlocal"
    );
}

#[test]
fn ptr_escape_mcopy_from_local_to_arg_tracks_content() {
    let (summaries, _) = compute(
        r#"
target = "evm-ethereum-osaka"

func public %copy_out(v0.*i8, v1.**i8) {
block0:
v2.**i8 = alloca *i8;
mstore v2 v0 *i8;
evm_mcopy v1 v2 32.i256;
return;
}
"#,
    );

    let f = &summaries["copy_out"];
    // arg 0 was stored to local memory, then mcopy'd to *arg 1.
    // The local branch of mcopy should attribute this to arg 0.
    assert_eq!(
        arg_store_targets(f, 0),
        vec![1],
        "arg 0 should escape through arg 1 via local-to-arg mcopy"
    );
    assert_eq!(
        arg_may_escape(f),
        vec![false, false],
        "no arg should be unconditionally nonlocal"
    );
}

#[test]
fn ptr_escape_mcopy_from_arg_to_local_keeps_escape_local() {
    let (summaries, _) = compute(
        r#"
target = "evm-ethereum-osaka"

func public %copy_local(v0.*i8, v1.**i8) {
block0:
mstore v1 v0 *i8;
v2.**i8 = alloca *i8;
evm_mcopy v2 v1 32.i256;
return;
}
"#,
    );

    let f = &summaries["copy_local"];
    assert_eq!(arg_store_targets(f, 0), vec![1]);
    assert!(f.arg_store_lattice(0).may_store_local());
    assert!(f.arg_store_lattice(0).may_store_to_arg());
    assert!(!f.arg_store_lattice(0).may_store_nonlocal());
    assert_eq!(arg_may_escape(f), vec![false, false]);
}

#[test]
fn ptr_escape_mstore8_uses_destination_provenance_like_mstore() {
    let (summaries, _) = compute(
        r#"
target = "evm-ethereum-osaka"

func public %f(v0.*i8, v1.*i8, v2.i1) {
block0:
v3.i256 = ptr_to_int v0 i256;
br v2 block1 block2;

block1:
evm_mstore8 v1 v3;
return;

block2:
v4.*i8 = alloca i8;
evm_mstore8 v4 v3;
return;
}
"#,
    );

    let f = &summaries["f"];
    assert_eq!(arg_store_targets(f, 0), vec![1]);
    assert!(f.arg_store_lattice(0).may_store_local());
    assert!(f.arg_store_lattice(0).may_store_to_arg());
    assert!(!f.arg_store_lattice(0).may_store_nonlocal());
    assert_eq!(arg_may_escape(f), vec![false, false, false]);
}
