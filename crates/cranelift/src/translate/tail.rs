//! Tail calls: a call whose results its function returns at once becomes a
//! Cranelift `return_call` when the callee cannot reach the caller's frame,
//! which the call then replaces.
//!
//! Only functions in a recursive cycle make tail calls, which keep that
//! recursion in constant stack. Cranelift tail-calls only between functions
//! of its `tail` calling convention, which saves no registers. The functions
//! on either side of a tail call use it; the rest keep the platform
//! convention, as external code calls public functions.

use std::collections::{HashMap, HashSet};

use sonatina_ir::{Module, inst::InstId, module::FuncRef};

use sonatina_codegen::analysis::tail_position::{
    TailSwitch, tail_callers, tail_calls, tail_switches,
};

/// The tail calls of a module.
#[derive(Default)]
pub(super) struct TailCalls {
    sites: HashMap<FuncRef, HashSet<InstId>>,
    functions: HashSet<FuncRef>,
    switches: HashMap<(FuncRef, InstId), TailSwitch>,
}

impl TailCalls {
    pub(super) fn new(module: &Module) -> Self {
        let mut calls = Self::default();
        for func_ref in tail_callers(module) {
            module.func_store.view(func_ref, |function| {
                let sites = tail_calls(func_ref, function);
                if sites.is_empty() {
                    return;
                }
                calls
                    .functions
                    .extend(sites.iter().flat_map(|&(_, callee)| [func_ref, callee]));
                let sites: HashSet<_> = sites.into_iter().map(|(call, _)| call).collect();
                for (br_table, switch) in tail_switches(function, &sites) {
                    calls.switches.insert((func_ref, br_table), switch);
                }
                calls.sites.insert(func_ref, sites);
            });
        }
        calls
    }

    pub(super) fn tail_switch(&self, func: FuncRef, br_table: InstId) -> Option<&TailSwitch> {
        self.switches.get(&(func, br_table))
    }

    /// Whether `func` takes part in a tail call, and so uses the `tail`
    /// calling convention.
    pub(super) fn uses_tail_convention(&self, func: FuncRef) -> bool {
        self.functions.contains(&func)
    }

    pub(super) fn is_tail_call(&self, func: FuncRef, call: InstId) -> bool {
        self.sites
            .get(&func)
            .is_some_and(|sites| sites.contains(&call))
    }
}

#[cfg(test)]
mod tests {
    use sonatina_ir::Module;

    use super::TailCalls;
    use sonatina_ir::module::FuncRef;
    use sonatina_parser::parse_module;

    fn parse_test_module(source: &str) -> Module {
        parse_module(source).expect("parse should succeed").module
    }

    fn lookup_func(module: &Module, name: &str) -> FuncRef {
        module
            .funcs()
            .into_iter()
            .find(|&func| module.ctx.func_sig(func, |sig| sig.name() == name))
            .expect("function should exist")
    }

    fn tail_calls(source: &str) -> (Module, TailCalls) {
        let module = parse_test_module(&format!("target = \"x86_64-unknown-native\"\n{source}"));
        let tail_calls = TailCalls::new(&module);
        (module, tail_calls)
    }

    /// How many of `name`'s calls are tail calls.
    fn tail_call_count(module: &Module, tail_calls: &TailCalls, name: &str) -> usize {
        let func = lookup_func(module, name);
        module.func_store.view(func, |function| {
            function
                .layout
                .iter_block()
                .flat_map(|block| function.layout.iter_inst(block))
                .filter(|&inst| tail_calls.is_tail_call(func, inst))
                .count()
        })
    }

    #[test]
    fn recursive_calls_returning_their_results_are_tail_calls() {
        let (module, tail_calls) = tail_calls(
            r#"
func private %f(v0.i64) -> i64 {
    block0:
        v1.i1 = eq v0 0.i64;
        br v1 block1 block2;
    block1:
        return v0;
    block2:
        v2.i64 = sub v0 1.i64;
        v3.i64 = call %g v2;
        return v3;
}

func private %g(v0.i64) -> i64 {
    block0:
        v1.i64 = call %f v0;
        return v1;
}

func private %helper(v0.i64) -> i64 {
    block0:
        v1.i64 = call %leaf v0;
        return v1;
}

func private %leaf(v0.i64) -> i64 {
    block0:
        return v0;
}

func public %entry(v0.i64) -> i64 {
    block0:
        v1.i64 = call %f v0;
        v2.i64 = call %helper v1;
        return v2;
}
"#,
        );
        let tail = |name| tail_calls.uses_tail_convention(lookup_func(&module, name));
        assert!(tail("f") && tail("g"));
        // Outside a cycle, and from a public caller, calls stay calls.
        assert!(!tail("helper") && !tail("leaf") && !tail("entry"));
    }

    #[test]
    fn calls_joining_a_returning_block_are_tail_calls() {
        let (module, tail_calls) = tail_calls(
            r#"
func private %dispatch(v0.i64, v1.i64) -> i64 {
    block0:
        br_table v0 block3 (0.i64 block1) (1.i64 block2);
    block1:
        v2.i64 = call %inc v1;
        jump block4;
    block2:
        v3.i64 = call %dec v1;
        v5.i64 = add v3 1.i64;
        jump block4;
    block3:
        jump block4;
    block4:
        v4.i64 = phi (v2 block1) (v5 block2) (v1 block3);
        return v4;
}

func private %inc(v0.i64) -> i64 {
    block0:
        v1.i64 = add v0 1.i64;
        v2.i64 = call %dispatch v1 v1;
        return v2;
}

func private %dec(v0.i64) -> i64 {
    block0:
        v1.i64 = sub v0 1.i64;
        return v1;
}
"#,
        );
        // `dec`'s result is used before the join.
        assert_eq!(tail_call_count(&module, &tail_calls, "dispatch"), 1);
        assert!(tail_calls.uses_tail_convention(lookup_func(&module, "inc")));
        assert!(!tail_calls.uses_tail_convention(lookup_func(&module, "dec")));
    }

    #[test]
    fn used_results_and_frame_arguments_are_not_tail_calls() {
        let (module, tail_calls) = tail_calls(
            r#"
func private %adds(v0.i64) -> i64 {
    block0:
        v1.i64 = call %adds v0;
        v2.i64 = add v1 1.i64;
        return v2;
}

func private %wide(v0.i256) -> i256 {
    block0:
        v1.i256 = call %wide v0;
        return v1;
}

func private %narrows(v0.i64) -> i32 {
    block0:
        v1.i32 = call %narrows v0;
        v2.i64 = zext v1 i64;
        v3.i32 = trunc v2 i32;
        return v3;
}
"#,
        );
        for name in ["adds", "wide", "narrows"] {
            assert_eq!(tail_call_count(&module, &tail_calls, name), 0, "{name}");
        }
    }

    #[test]
    fn constrefs_from_arguments_pass_on() {
        let (module, tail_calls) = tail_calls(
            r#"
type @pair = { i64, i64 };

declare external %make(i64) -> constref<@pair>;

func private %passes_argument(v0.constref<@pair>, v1.i64) -> i64 {
    block0:
        v2.i64 = call %first v0 v1;
        return v2;
}

func private %passes_result(v0.i64) -> i64 {
    block0:
        v1.constref<@pair> = call %make v0;
        v2.i64 = call %first v1 v0;
        return v2;
}

func private %first(v0.constref<@pair>, v1.i64) -> i64 {
    block0:
        v2.i1 = eq v1 0.i64;
        br v2 block1 block2;
    block1:
        v3.i64 = call %passes_argument v0 v1;
        return v3;
    block2:
        v4.i64 = call %passes_result v1;
        return v4;
}
"#,
        );
        assert_eq!(tail_call_count(&module, &tail_calls, "passes_argument"), 1);
        assert_eq!(tail_call_count(&module, &tail_calls, "passes_result"), 0);
    }

    #[test]
    fn switches_of_like_tail_calls_are_tail_switches() {
        let source = |scrutinee: &str, second_args: &str, default: &str| {
            format!(
                r#"
func private %switch(v0.i64, v1.i64) -> i64 {{
    block0:
        v5.i64 = and v0 3.i64;
        br_table {scrutinee} {default} (0.i64 block1) (2.i64 block2);
    block1:
        v2.i64 = call %f v0 v1;
        return v2;
    block2:
        v3.i64 = call %g {second_args};
        return v3;
    block3:
        v4.i64 = call %f v0 v1;
        return v4;
    block4:
        return 0.i64;
}}

func private %f(v0.i64, v1.i64) -> i64 {{
    block0:
        v2.i64 = sub v0 1.i64;
        v3.i64 = call %switch v2 v1;
        return v3;
}}

func private %g(v0.i64, v1.i64) -> i64 {{
    block0:
        return v0;
}}
"#
            )
        };
        let switch_of = |source: String| {
            let (module, tail_calls) = tail_calls(&source);
            let switch = lookup_func(&module, "switch");
            let br_table = module.func_store.view(switch, |function| {
                let entry = function.layout.entry_block().unwrap();
                function.layout.last_inst_of(entry).unwrap()
            });
            tail_calls.tail_switch(switch, br_table).map(|switch| {
                let keys: Vec<_> = switch.keys.iter().map(|&(key, _)| key).collect();
                (keys, switch.bits)
            })
        };
        assert_eq!(
            switch_of(source("v5", "v0 v1", "block3")),
            Some((vec![0, 2], 2))
        );
        // Different arguments, a default that is no tail call, or an index
        // too wide for a table.
        assert_eq!(switch_of(source("v5", "v1 v0", "block3")), None);
        assert_eq!(switch_of(source("v5", "v0 v1", "block4")), None);
        assert_eq!(switch_of(source("v0", "v0 v1", "block3")), None);
    }

    #[test]
    fn escaped_allocations_keep_calls() {
        let (module, tail_calls) = tail_calls(
            r#"
func private %passes_reference(v0.i64) -> i64 {
    block0:
        v1.objref<i64> = obj.alloc i64;
        obj.store v1 v0;
        v2.i64 = call %read v1;
        return v2;
}

func private %local_only(v0.i64) -> i64 {
    block0:
        v1.objref<[i64; 2]> = obj.alloc [i64; 2];
        v2.objref<i64> = obj.index v1 1.i8;
        obj.store v2 v0;
        v3.i64 = obj.load v2;
        v4.i64 = call %g v3;
        return v4;
}

func private %read(v0.objref<i64>) -> i64 {
    block0:
        v1.i64 = obj.load v0;
        v2.i64 = call %passes_reference v1;
        return v2;
}

func private %g(v0.i64) -> i64 {
    block0:
        v1.i64 = call %local_only v0;
        return v1;
}
"#,
        );
        assert_eq!(tail_call_count(&module, &tail_calls, "passes_reference"), 0);
        assert_eq!(tail_call_count(&module, &tail_calls, "local_only"), 1);
    }
}
