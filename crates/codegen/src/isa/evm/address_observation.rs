use std::iter;

use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use sonatina_ir::{
    AccessLoc, Function, InstId, InstSetExt, Module, Type, ValueId,
    inst::evm::inst_set::EvmInstKind,
    isa::{
        Isa,
        evm::{Evm, space::MEMORY},
    },
    module::FuncRef,
};

use super::fixed_slots::func_address_taken;
use crate::bitset::BitSet;

/// Whether the section may read an allocation's address as a number.
///
/// No allocation is at address 0, where its pointer would be null. A section that reserves no
/// memory would start its arena there, and keeps the word at 0 unless no program can tell.
/// Moving every allocation up a word changes nothing a program sees if each value derived from
/// an allocation's address only addresses memory, once per access: no other memory is reserved
/// that the allocations could move onto, and `msize` and gas are unspecified.
///
/// A value is derived if it is an `alloca` or `evm_malloc`, a cast of a derived value to `i256`
/// or a pointer (a narrower type, `i1` included, drops address bits), a `gep` from one, the sum
/// of one and an underived value, one minus an underived value, a phi of one, a parameter some
/// call passes one, or a call result whose callee returns one. Any other use reads the address:
/// a compare, other arithmetic, a branch, a stored value, a non-address operand of an external
/// call, an argument of a call to a function outside the section, or a return to a caller this
/// cannot see.
pub(crate) fn observes_allocation_address(
    module: &Module,
    funcs: &[FuncRef],
    entry: FuncRef,
    includes: &[FuncRef],
    isa: &Evm,
) -> bool {
    let mut scan = AddressScan {
        // The section entry, its includes and functions whose address is taken have callers
        // this cannot see.
        unseen_callers: iter::once(entry).chain(includes.iter().copied()).collect(),
        ..AddressScan::default()
    };
    for &func in funcs {
        module.func_store.view(func, |function| {
            scan.params.insert(func, function.arg_values.clone());
            for inst in function.layout.iter_all_insts() {
                scan.unseen_callers
                    .extend(func_address_taken(function, inst));
                let results = function.dfg.inst_results(inst);
                match isa.inst_set().resolve_inst(function.dfg.inst(inst)) {
                    EvmInstKind::Alloca(_) | EvmInstKind::EvmMalloc(_) => {
                        for &result in results {
                            scan.derive(func, result);
                        }
                    }
                    EvmInstKind::Call(call) => {
                        for (idx, &result) in results.iter().enumerate() {
                            scan.call_results
                                .entry((*call.callee(), idx))
                                .or_default()
                                .push((func, result));
                        }
                    }
                    _ => {}
                }
            }
        });
    }

    // Each use of a newly derived value is checked again, so an instruction is last checked
    // once all of its derived operands are.
    while let Some((func, value)) = scan.work.pop() {
        let observed = module.func_store.view(func, |function| {
            function
                .dfg
                .users(value)
                .copied()
                .filter(|&inst| function.layout.is_inst_inserted(inst))
                .any(|inst| scan.observes(func, function, inst, isa))
        });
        if observed {
            return true;
        }
    }
    false
}

#[derive(Default)]
struct AddressScan {
    unseen_callers: FxHashSet<FuncRef>,
    params: FxHashMap<FuncRef, SmallVec<[ValueId; 8]>>,
    /// The results of calls, by callee and return index, until the callee returns a derived
    /// value there.
    call_results: FxHashMap<(FuncRef, usize), Vec<(FuncRef, ValueId)>>,
    derived: FxHashMap<FuncRef, BitSet<ValueId>>,
    /// Derived values whose uses are not yet checked.
    work: Vec<(FuncRef, ValueId)>,
}

impl AddressScan {
    fn derive(&mut self, func: FuncRef, value: ValueId) {
        if self.derived.entry(func).or_default().insert(value) {
            self.work.push((func, value));
        }
    }

    fn is_derived(&self, func: FuncRef, value: ValueId) -> bool {
        self.derived
            .get(&func)
            .is_some_and(|derived| derived.contains(value))
    }

    /// Whether `inst`, which uses a derived value, reads it as a number. Derives its results
    /// and the values it passes them to otherwise.
    fn observes(&mut self, func: FuncRef, function: &Function, inst: InstId, isa: &Evm) -> bool {
        let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));
        let results = function.dfg.inst_results(inst);
        let is_derived = |value: &ValueId| self.is_derived(func, *value);
        match data {
            EvmInstKind::Call(call) => {
                let callee = *call.callee();
                let args = call.args();
                // A callee outside the section may do anything with an address.
                let Some(params) = self
                    .params
                    .get(&callee)
                    .filter(|params| params.len() == args.len())
                else {
                    return args.iter().any(is_derived);
                };
                let derived_params: SmallVec<[ValueId; 4]> = args
                    .iter()
                    .zip(params)
                    .filter(|(arg, _)| is_derived(arg))
                    .map(|(_, &param)| param)
                    .collect();
                for param in derived_params {
                    self.derive(callee, param);
                }
                return false;
            }
            EvmInstKind::Return(ret) => {
                let derived_rets: SmallVec<[usize; 2]> = ret
                    .args()
                    .as_slice()
                    .iter()
                    .enumerate()
                    .filter(|(_, value)| is_derived(value))
                    .map(|(idx, _)| idx)
                    .collect();
                if !derived_rets.is_empty() && self.unseen_callers.contains(&func) {
                    return true;
                }
                for idx in derived_rets {
                    for (caller, result) in
                        self.call_results.remove(&(func, idx)).unwrap_or_default()
                    {
                        self.derive(caller, result);
                    }
                }
                return false;
            }
            _ => {}
        }

        let values = function.dfg.inst(inst).collect_values();
        let transparent = match data {
            EvmInstKind::Bitcast(_) | EvmInstKind::PtrToInt(_) => results.iter().all(|&result| {
                let ty = function.dfg.value_ty(result);
                ty == Type::I256 || ty.is_pointer(function.ctx())
            }),
            EvmInstKind::IntToPtr(_) | EvmInstKind::Phi(_) => true,
            EvmInstKind::Gep(gep) => !gep.values().iter().skip(1).any(is_derived),
            EvmInstKind::Add(add) => !(is_derived(add.lhs()) && is_derived(add.rhs())),
            EvmInstKind::Sub(sub) => !is_derived(sub.rhs()),
            _ => false,
        };
        if transparent {
            for &result in results {
                self.derive(func, result);
            }
            return false;
        }

        // Each derived operand must be the address of its own memory access. A zero-length
        // `evm_mload_bytes`, `evm_mcopy` or `memcopy` accesses no memory, so its address counts
        // as read, which is conservative.
        let mut addrs: SmallVec<[ValueId; 4]> = function
            .dfg
            .effects(inst)
            .accesses
            .iter()
            .filter(|access| access.space == MEMORY)
            .filter_map(|access| match &access.loc {
                AccessLoc::LinearExact { addr, .. } | AccessLoc::LinearRange { addr, .. } => {
                    Some(*addr)
                }
                _ => None,
            })
            .collect();
        values
            .iter()
            .filter(|value| is_derived(value))
            .any(|value| {
                let Some(idx) = addrs.iter().position(|addr| addr == value) else {
                    return true;
                };
                addrs.swap_remove(idx);
                false
            })
    }
}

#[cfg(test)]
mod tests {
    use sonatina_parser::parse_module;
    use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

    use super::*;

    /// Whether the section rooted at `%entry` of `funcs`, with `includes`, observes an
    /// allocation's address.
    fn observes(funcs: &str, includes: &[&str]) -> bool {
        observes_without(funcs, includes, &[])
    }

    /// As [`observes`], with the functions `outside` left out of the section.
    fn observes_without(funcs: &str, includes: &[&str], outside: &[&str]) -> bool {
        let source = format!("target = \"evm-ethereum-osaka\"\ntype @empty = {{}};\n{funcs}");
        let module = parse_module(&source).expect("parse").module;
        let report = verify_module(&module, &VerifierConfig::for_level(VerificationLevel::Full));
        assert!(!report.has_errors(), "{report}");
        let funcs = module.funcs();
        let named = |name: &str| {
            funcs
                .iter()
                .copied()
                .find(|&func| module.ctx.func_sig(func, |sig| sig.name() == name))
                .expect("function")
        };
        let includes: Vec<_> = includes.iter().map(|&name| named(name)).collect();
        let section: Vec<_> = funcs
            .iter()
            .copied()
            .filter(|&func| !outside.iter().any(|&name| func == named(name)))
            .collect();
        observes_allocation_address(
            &module,
            &section,
            named("entry"),
            &includes,
            &Evm::new(module.ctx.triple),
        )
    }

    /// `%entry` with `body`, whose statements are separated by `;` and whose blocks are
    /// labelled `blockN: `.
    fn entry(body: &str) -> String {
        let body = body.replace(';', ";\n").replace(": ", ":\n");
        format!("func public %entry() {{\nblock0:\n{body}\n}}")
    }

    const ALLOCA: &str = "v0.*i256 = alloca i256; v1.i256 = ptr_to_int v0 i256;";

    #[test]
    fn address_only_uses_are_unobserved() {
        for body in [
            "mstore v1 7.i256 i256; v2.i256 = mload v0 i256; mstore 0.i256 v2 i256; \
             evm_return 0.i256 32.i256;",
            "v2.i256 = add 32.i256 v1; v3.i256 = sub v2 32.i256; v4.*i256 = int_to_ptr v3 *i256; \
             v5.*i8 = bitcast v4 *i8; v6.*i8 = gep v5 1.i256; evm_mstore8 v6 1.i256; \
             evm_return v1 32.i256;",
            "v2.i256 = evm_keccak256 v1 32.i256; evm_mcopy v1 v1 32.i256; \
             evm_calldata_copy v1 0.i256 32.i256; \
             v3.i256 = evm_call 0.i256 0.i256 0.i256 v1 32.i256 v1 32.i256; \
             evm_log1 v1 32.i256 v2; evm_revert v1 32.i256;",
            "v2.i256 = evm_calldata_load 0.i256; v9.i1 = is_zero v2; br v9 block1 block2; \
             block1: v3.*i256 = alloca i256; jump block2; \
             block2: v4.*i256 = phi (v0 block0) (v3 block1); mstore v4 1.i256 i256; evm_stop;",
            "v2.*@empty = alloca @empty; v3.*i8 = evm_malloc 32.i256; mstore v3 1.i256 i256; \
             evm_return v3 32.i256;",
            "v2.i256 = evm_calldata_load 0.i256; v9.i1 = is_zero v2; jump block1; \
             block1: v3.i256 = phi (v1 block0) (v4 block1); v4.i256 = add v3 32.i256; \
             mstore v3 1.i256 i256; br v9 block1 block2; block2: evm_stop;",
        ] {
            assert!(
                !observes(&entry(&format!("{ALLOCA} {body}")), &[]),
                "{body}"
            );
        }
    }

    #[test]
    fn address_passed_to_and_returned_from_callees_is_unobserved() {
        let funcs = format!(
            "{}
func private %store(v0.*i256) {{
block0:
    mstore v0 1.i256 i256;
    return;
}}
func private %forward(v0.i256) -> i256 {{
block0:
    return v0;
}}
func private %make() -> *i256 {{
block0:
    v0.*i256 = alloca i256;
    return v0;
}}",
            entry(&format!(
                "{ALLOCA} call %store v0; v2.i256 = call %forward v1; \
                 v3.*i256 = int_to_ptr v2 *i256; v4.*i256 = call %make; \
                 v5.i256 = mload v3 i256; mstore v4 v5 i256; evm_return v4 32.i256;"
            ))
        );
        assert!(!observes(&funcs, &[]));
    }

    #[test]
    fn numeric_uses_of_an_address_are_observed() {
        for body in [
            "v2.i1 = is_zero v1; br v2 block1 block2; block1: evm_stop; block2: evm_stop;",
            "v2.i1 = is_zero v0; br v2 block1 block2; block1: evm_stop; block2: evm_stop;",
            "v2.i1 = eq v1 0.i256; br v2 block1 block2; block1: evm_stop; block2: evm_stop;",
            "(v2.i256, v3.i1) = uaddo v1 -1.i256; br v3 block1 block2; \
             block1: evm_stop; block2: evm_stop;",
            "v2.i256 = evm_uaddsat v1 0.i256 i32; mstore v2 1.i256 i256; evm_stop;",
            "v2.i64 = ptr_to_int v0 i64; evm_sstore 0.i256 0.i256; evm_stop;",
            "v2.i1 = bitcast v1 i1; v3.i256 = bitcast v2 i256; mstore v3 1.i256 i256; evm_stop;",
            "v2.i256 = add v1 v1; mstore v2 1.i256 i256; evm_stop;",
            "v2.i256 = sub 64.i256 v1; mstore v2 1.i256 i256; evm_stop;",
            "v2.*i256 = gep v0 v1; mstore v2 1.i256 i256; evm_stop;",
            "mstore 0.i256 v1 i256; evm_return 0.i256 32.i256;",
            "mstore v1 v1 i256; evm_return v1 32.i256;",
            "evm_return v1 v1;",
            "evm_sstore v1 0.i256; evm_stop;",
            "evm_sstore 0.i256 v1; evm_stop;",
            "v2.i256 = evm_keccak256 0.i256 v1; evm_stop;",
            "evm_calldata_copy v1 v1 32.i256; evm_stop;",
            "v2.i256 = evm_call v1 0.i256 0.i256 0.i256 0.i256 0.i256 0.i256; evm_stop;",
            "v2.*i8 = evm_malloc v1; evm_stop;",
            "v2.*i8 = evm_malloc 32.i256; v3.i256 = ptr_to_int v2 i256; \
             (v4.i256, v5.i1) = uaddo v3 -1.i256; br v5 block1 block2; \
             block1: evm_stop; block2: evm_stop;",
            "v2.i256 = evm_calldata_load 0.i256; v9.i1 = is_zero v2; br v9 block1 block2; \
             block1: jump block2; \
             block2: v3.*i256 = phi (v0 block0) (zero.*i256 block1); \
             v4.i256 = ptr_to_int v3 i256; v5.i1 = is_zero v4; br v5 block3 block4; \
             block3: evm_stop; block4: evm_stop;",
        ] {
            assert!(observes(&entry(&format!("{ALLOCA} {body}")), &[]), "{body}");
        }
    }

    #[test]
    fn callee_null_test_of_an_address_is_observed() {
        let funcs = format!(
            "{}
func private %is_null(v0.*i256) -> i1 {{
block0:
    v1.i256 = ptr_to_int v0 i256;
    v2.i1 = is_zero v1;
    return v2;
}}",
            entry(&format!(
                "{ALLOCA} v2.i1 = call %is_null v0; br v2 block1 block2; \
                 block1: evm_stop; block2: evm_stop;"
            ))
        );
        assert!(observes(&funcs, &[]));
    }

    #[test]
    fn null_test_of_a_callee_allocation_is_observed() {
        let funcs = format!(
            "{}
func private %make() -> *i256 {{
block0:
    v0.*i256 = alloca i256;
    return v0;
}}",
            entry(
                "v0.*i256 = call %make; v1.i256 = ptr_to_int v0 i256; v2.i1 = is_zero v1; \
                 br v2 block1 block2; block1: evm_stop; block2: evm_stop;"
            )
        );
        assert!(observes(&funcs, &[]));
    }

    #[test]
    fn address_returned_from_a_function_whose_address_is_taken_is_observed() {
        let make = "func private %make() -> i256 {\nblock0:\n    v0.*i256 = alloca i256;\n    \
                    v1.i256 = ptr_to_int v0 i256;\n    return v1;\n}";
        for take in [
            "v0.*() -> i256 = get_function_ptr %make;",
            "v0.i256 = sym_addr %make;",
            "",
        ] {
            let funcs = format!(
                "{make}\n{}",
                entry(&format!(
                    "{take} v2.i256 = call %make; v3.*i256 = int_to_ptr v2 *i256; \
                     mstore v3 1.i256 i256; evm_stop;"
                ))
            );
            assert_eq!(observes(&funcs, &[]), !take.is_empty(), "{take}");
        }
    }

    #[test]
    fn address_passed_outside_the_section_is_observed() {
        let funcs = format!(
            "{}
func private %store(v0.*i256) {{
block0:
    mstore v0 1.i256 i256;
    return;
}}",
            entry(&format!("{ALLOCA} call %store v0; evm_stop;"))
        );
        assert!(!observes(&funcs, &[]));
        assert!(observes_without(&funcs, &[], &["store"]));
    }

    #[test]
    fn difference_of_addresses_is_observed() {
        for body in [
            "v2.i256 = sub v1 v1; mstore v2 1.i256 i256; evm_stop;",
            "v2.*i256 = alloca i256; v3.i256 = ptr_to_int v2 i256; v4.i256 = sub v1 v3; \
             mstore v4 1.i256 i256; evm_stop;",
        ] {
            assert!(observes(&entry(&format!("{ALLOCA} {body}")), &[]), "{body}");
        }
    }

    /// `%entry` passes an address through `%a`, which passes it on to `%b`, and `%b` back to
    /// `%a` until its counter runs out; each returns what it gets. `use_in_b` is what `%b` does
    /// with it first.
    fn mutually_recursive_forwarding(use_in_b: &str) -> String {
        format!(
            "{}
func private %a(v0.i256, v1.i256) -> i256 {{
block0:
    v2.i256 = call %b v0 v1;
    return v2;
}}
func private %b(v0.i256, v1.i256) -> i256 {{
block0:
    {use_in_b}
    v2.i1 = is_zero v1;
    br v2 block1 block2;
block1:
    return v0;
block2:
    v3.i256 = sub v1 1.i256;
    v4.i256 = call %a v0 v3;
    return v4;
}}",
            entry(
                "v1.i256 = evm_calldata_load 0.i256; v2.*i256 = alloca i256; \
                 v3.i256 = ptr_to_int v2 i256; v4.i256 = call %a v3 v1; \
                 v5.*i256 = int_to_ptr v4 *i256; mstore v5 1.i256 i256; evm_stop;"
            )
        )
    }

    #[test]
    fn address_through_recursive_calls_is_observed_only_where_read() {
        assert!(!observes(&mutually_recursive_forwarding(""), &[]));
        assert!(!observes(
            &mutually_recursive_forwarding("mstore v0 2.i256 i256;"),
            &[]
        ));
        assert!(observes(
            &mutually_recursive_forwarding("v9.i1 = is_zero v0;"),
            &[]
        ));
    }

    #[test]
    fn address_returned_from_a_recursive_callee_is_observed_where_read() {
        let funcs = |use_in_entry: &str| {
            format!(
                "{}
func private %make(v0.i256) -> i256 {{
block0:
    v1.i1 = is_zero v0;
    br v1 block1 block2;
block1:
    v2.*i256 = alloca i256;
    v3.i256 = ptr_to_int v2 i256;
    return v3;
block2:
    v4.i256 = sub v0 1.i256;
    v5.i256 = call %make v4;
    return v5;
}}",
                entry(&format!(
                    "v1.i256 = evm_calldata_load 0.i256; v2.i256 = call %make v1; {use_in_entry}"
                ))
            )
        };
        assert!(!observes(
            &funcs("v3.*i256 = int_to_ptr v2 *i256; mstore v3 1.i256 i256; evm_stop;"),
            &[]
        ));
        assert!(observes(
            &funcs("v3.i1 = is_zero v2; br v3 block1 block2; block1: evm_stop; block2: evm_stop;"),
            &[]
        ));
    }

    #[test]
    fn address_returned_to_an_unseen_caller_is_observed() {
        let returns = |name: &str| {
            format!(
                "func public %{name}() -> i256 {{\nblock0:\n{}\nreturn v1;\n}}",
                ALLOCA.replace(';', ";\n")
            )
        };
        assert!(observes(&returns("entry"), &[]));
        let funcs = format!("{}\n{}", entry("evm_stop;"), returns("included"));
        assert!(!observes(&funcs, &[]));
        assert!(observes(&funcs, &["included"]));
    }
}
