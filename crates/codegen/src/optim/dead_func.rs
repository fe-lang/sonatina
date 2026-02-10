use rustc_hash::FxHashSet;
use sonatina_ir::{
    InstDowncast, Module,
    inst::data::{GetFunctionPtr, SymAddr, SymSize, SymbolRef},
    module::FuncRef,
    object::Directive,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ExportMode {
    #[default]
    Conservative,
    WholeProgram,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DeadFuncElimConfig {
    pub export_mode: ExportMode,
    pub keep_external_decls: bool,
}

impl Default for DeadFuncElimConfig {
    fn default() -> Self {
        Self {
            export_mode: ExportMode::Conservative,
            keep_external_decls: true,
        }
    }
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct DeadFuncElimStats {
    pub reachable_count: usize,
    pub removed_defs: usize,
    pub kept_public: usize,
    pub kept_external: usize,
    pub addr_taken_roots: usize,
}

#[derive(Default)]
struct Reachability {
    funcs: FxHashSet<FuncRef>,
    kept_public: usize,
    kept_external: usize,
    addr_taken_roots: usize,
}

pub fn collect_object_roots(module: &Module) -> Vec<FuncRef> {
    let mut roots = FxHashSet::default();
    for object in module.objects.values() {
        for section in &object.sections {
            for directive in &section.directives {
                if let Directive::Entry(func) | Directive::Include(func) = directive {
                    roots.insert(*func);
                }
            }
        }
    }

    let mut roots: Vec<_> = roots.into_iter().collect();
    roots.sort_unstable();
    roots
}

pub fn run_dead_func_elim(
    module: &mut Module,
    roots: &[FuncRef],
    config: DeadFuncElimConfig,
) -> DeadFuncElimStats {
    let reachability = collect_reachable(module, roots, config);
    let mut removed_defs = 0;

    for func_ref in module.funcs() {
        let linkage = module.ctx.func_linkage(func_ref);
        if !linkage.has_definition() || reachability.funcs.contains(&func_ref) {
            continue;
        }

        module.func_store.remove(func_ref);
        module.ctx.declared_funcs.remove(&func_ref);
        removed_defs += 1;
    }

    DeadFuncElimStats {
        reachable_count: reachability.funcs.len(),
        removed_defs,
        kept_public: reachability.kept_public,
        kept_external: reachability.kept_external,
        addr_taken_roots: reachability.addr_taken_roots,
    }
}

fn collect_reachable(
    module: &Module,
    roots: &[FuncRef],
    config: DeadFuncElimConfig,
) -> Reachability {
    let mut reachability = Reachability::default();
    let mut worklist = Vec::new();

    if matches!(config.export_mode, ExportMode::Conservative) {
        for func_ref in module.funcs() {
            if !module.ctx.func_linkage(func_ref).is_public() {
                continue;
            }

            reachability.kept_public += 1;
            enqueue_func(module, func_ref, &mut reachability.funcs, &mut worklist);
        }
    }

    if config.keep_external_decls {
        for func_ref in module.funcs() {
            if !module.ctx.func_linkage(func_ref).is_external() {
                continue;
            }

            reachability.kept_external += 1;
            reachability.funcs.insert(func_ref);
        }
    }

    for &func_ref in roots {
        enqueue_func(module, func_ref, &mut reachability.funcs, &mut worklist);
    }

    while let Some(func_ref) = worklist.pop() {
        if !module.ctx.func_linkage(func_ref).has_definition() {
            continue;
        }

        module.func_store.view(func_ref, |func| {
            let is = func.inst_set();
            for block in func.layout.iter_block() {
                for inst_id in func.layout.iter_inst(block) {
                    if let Some(call) = func.dfg.call_info(inst_id) {
                        enqueue_func(
                            module,
                            call.callee(),
                            &mut reachability.funcs,
                            &mut worklist,
                        );
                    }

                    let inst = func.dfg.inst(inst_id);
                    if let Some(ptr) = <&GetFunctionPtr as InstDowncast>::downcast(is, inst)
                        && enqueue_func(module, *ptr.func(), &mut reachability.funcs, &mut worklist)
                    {
                        reachability.addr_taken_roots += 1;
                    }

                    if let Some(sym) = <&SymAddr as InstDowncast>::downcast(is, inst)
                        && let SymbolRef::Func(func_ref) = sym.sym()
                        && enqueue_func(module, *func_ref, &mut reachability.funcs, &mut worklist)
                    {
                        reachability.addr_taken_roots += 1;
                    }

                    if let Some(sym) = <&SymSize as InstDowncast>::downcast(is, inst)
                        && let SymbolRef::Func(func_ref) = sym.sym()
                        && enqueue_func(module, *func_ref, &mut reachability.funcs, &mut worklist)
                    {
                        reachability.addr_taken_roots += 1;
                    }
                }
            }
        });
    }

    reachability
}

fn enqueue_func(
    module: &Module,
    func_ref: FuncRef,
    reachable: &mut FxHashSet<FuncRef>,
    worklist: &mut Vec<FuncRef>,
) -> bool {
    if !module.ctx.declared_funcs.contains_key(&func_ref) || !reachable.insert(func_ref) {
        return false;
    }

    worklist.push(func_ref);
    true
}

#[cfg(test)]
mod tests {
    use sonatina_ir::Module;

    use super::{DeadFuncElimConfig, ExportMode, collect_object_roots, run_dead_func_elim};

    fn parse_module(input: &str) -> sonatina_parser::ParsedModule {
        sonatina_parser::parse_module(input).unwrap_or_else(|errs| panic!("parse failed: {errs:?}"))
    }

    fn function_names(module: &Module) -> Vec<String> {
        let mut names = module
            .funcs()
            .into_iter()
            .map(|func_ref| module.ctx.func_sig(func_ref, |sig| sig.name().to_string()))
            .collect::<Vec<_>>();
        names.sort();
        names
    }

    #[test]
    fn removes_unreachable_private_defs_from_object_roots() {
        let source = r#"
target = "evm-ethereum-london"

func private %entry() {
    block0:
        call %used;
        return;
}

func private %used() {
    block0:
        return;
}

func private %dead() {
    block0:
        return;
}

object @O {
    section runtime {
        entry %entry;
    }
}
"#;

        let mut parsed = parse_module(source);
        let roots = collect_object_roots(&parsed.module);
        let stats = run_dead_func_elim(&mut parsed.module, &roots, DeadFuncElimConfig::default());

        let names = function_names(&parsed.module);
        assert_eq!(names, vec!["entry".to_string(), "used".to_string()]);
        assert_eq!(stats.removed_defs, 1);
    }

    #[test]
    fn keeps_include_roots() {
        let source = r#"
target = "evm-ethereum-london"

func private %entry() {
    block0:
        return;
}

func private %included() {
    block0:
        return;
}

func private %dead() {
    block0:
        return;
}

object @O {
    section runtime {
        entry %entry;
        include %included;
    }
}
"#;

        let mut parsed = parse_module(source);
        let roots = collect_object_roots(&parsed.module);
        run_dead_func_elim(&mut parsed.module, &roots, DeadFuncElimConfig::default());

        let names = function_names(&parsed.module);
        assert_eq!(names, vec!["entry".to_string(), "included".to_string()]);
    }

    #[test]
    fn keeps_addr_taken_functions() {
        let source = r#"
target = "evm-ethereum-london"

func private %entry() {
    block0:
        v0.i256 = sym_addr %target_fn;
        return;
}

func private %target_fn() {
    block0:
        return;
}

func private %dead() {
    block0:
        return;
}

object @O {
    section runtime {
        entry %entry;
    }
}
"#;

        let mut parsed = parse_module(source);
        let roots = collect_object_roots(&parsed.module);
        let stats = run_dead_func_elim(&mut parsed.module, &roots, DeadFuncElimConfig::default());

        let names = function_names(&parsed.module);
        assert_eq!(names, vec!["entry".to_string(), "target_fn".to_string()]);
        assert_eq!(stats.addr_taken_roots, 1);
    }

    #[test]
    fn conservative_mode_keeps_unreachable_public() {
        let source = r#"
target = "evm-ethereum-london"

func private %entry() {
    block0:
        return;
}

func public %exported() {
    block0:
        return;
}

func private %dead() {
    block0:
        return;
}

object @O {
    section runtime {
        entry %entry;
    }
}
"#;

        let mut parsed = parse_module(source);
        let roots = collect_object_roots(&parsed.module);
        run_dead_func_elim(&mut parsed.module, &roots, DeadFuncElimConfig::default());

        let names = function_names(&parsed.module);
        assert_eq!(names, vec!["entry".to_string(), "exported".to_string(),]);
    }

    #[test]
    fn whole_program_mode_drops_unreachable_public() {
        let source = r#"
target = "evm-ethereum-london"

func private %entry() {
    block0:
        return;
}

func public %exported() {
    block0:
        return;
}

object @O {
    section runtime {
        entry %entry;
    }
}
"#;

        let mut parsed = parse_module(source);
        let roots = collect_object_roots(&parsed.module);
        run_dead_func_elim(
            &mut parsed.module,
            &roots,
            DeadFuncElimConfig {
                export_mode: ExportMode::WholeProgram,
                keep_external_decls: true,
            },
        );

        let names = function_names(&parsed.module);
        assert_eq!(names, vec!["entry".to_string()]);
    }
}
