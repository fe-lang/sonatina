//! A fresh aggregate has two spellings: an `insert_value` chain on `zero` and
//! one `agg.make`. Every fixture that builds one is compiled as written and
//! respelled the other way, at every optimization level, on EVM, wasm and
//! Cranelift, and the two must give the same bytes. A fixture written with
//! chains is respelled with `agg.make`, and one written with `agg.make` with
//! chains, so the check keeps working while fixtures move from one spelling to
//! the other. `i1` members are among what must match: each is stored and
//! read as a word. Every compile folds chains into `agg.make` before
//! optimizing (`fold_fresh_aggregates`), so both spellings reach every pass
//! alike.
//!
//! `AGG_MAKE_SPELLING_DIRS` adds directories of `.sntn` or `.sona` modules
//! (such as Fe's `--emit ir` output), separated by `:`. With
//! `AGG_MAKE_SPELLING_DUMP` set to a directory, each difference writes both
//! spellings' optimized IR there.

use std::{
    fmt::Write as _,
    fs,
    path::{Path, PathBuf},
};

use sonatina_codegen::{Compile, EvmCompiler, OptLevel, object::SymbolId};
use sonatina_cranelift::CraneliftObjectBackend;
use sonatina_ir::{
    Function, InstId, Module, Type, ValueId,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::data::{AggMake, InsertValue},
    ir_writer::ModuleWriter,
};
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};
use sonatina_wasm::WasmBackend;

/// Arrays longer than this keep their spelling: respelled, a sparse chain
/// into a large array would take one operand per element.
const MAX_FIELDS: usize = 64;

const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::Os];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Backend {
    Evm,
    Wasm,
    Cranelift,
}

impl Backend {
    fn target(self) -> Option<&'static str> {
        match self {
            Self::Evm => None,
            Self::Wasm => Some("wasm32-unknown-native"),
            Self::Cranelift => Some(if cfg!(target_arch = "aarch64") {
                "aarch64-unknown-native"
            } else {
                "x86_64-unknown-native"
            }),
        }
    }

    /// `module` after the optimizer of this backend at `level`.
    fn optimized_ir(self, module: Module, level: OptLevel) -> String {
        let dump = |module: &Module| ModuleWriter::new(module).dump_string();
        match self {
            Self::Evm => dump(
                Compile::new(module, EvmCompiler::default())
                    .with_opt_level(level)
                    .optimize(),
            ),
            Self::Wasm => dump(
                Compile::new(module, WasmBackend::new())
                    .with_opt_level(level)
                    .optimize(),
            ),
            Self::Cranelift => dump(
                Compile::new(module, CraneliftObjectBackend::new())
                    .with_opt_level(level)
                    .optimize(),
            ),
        }
    }

    /// The code size of each function `module` compiles to on EVM at `level`,
    /// one line each, to find what differs.
    fn evm_function_sizes(module: Module, level: OptLevel) -> String {
        let names: Vec<_> = module
            .funcs()
            .into_iter()
            .map(|func| {
                (
                    func,
                    module.ctx.func_sig(func, |sig| sig.name().to_string()),
                )
            })
            .collect();
        let Ok(artifacts) = Compile::new(module, EvmCompiler::default().with_symbol_table(true))
            .with_opt_level(level)
            .compile()
        else {
            return String::new();
        };
        let mut lines = Vec::new();
        for artifact in artifacts {
            for (section, data) in artifact.sections {
                for (symbol, def) in data.symtab {
                    if let SymbolId::Func(func) = symbol {
                        let name = &names.iter().find(|(f, _)| *f == func).unwrap().1;
                        lines.push(format!(
                            "{} {} {name} {}",
                            artifact.object.0, section.0, def.size
                        ));
                    }
                }
            }
        }
        lines.sort();
        lines.join("\n")
    }

    /// The bytes `module` compiles to at `level`, or why it does not compile.
    fn compile(self, module: Module, level: OptLevel) -> Result<Vec<Vec<u8>>, String> {
        match self {
            Self::Evm => Compile::new(module, EvmCompiler::default())
                .with_opt_level(level)
                .compile()
                .map(|artifacts| {
                    artifacts
                        .into_iter()
                        .flat_map(|artifact| artifact.sections)
                        .map(|(_, section)| section.bytes)
                        .collect()
                })
                .map_err(|errors| format!("{errors:?}")),
            Self::Wasm => Compile::new(module, WasmBackend::new())
                .with_opt_level(level)
                .compile()
                .map(|artifact| vec![artifact.into_bytes()])
                .map_err(|errors| format!("{errors:?}")),
            Self::Cranelift => Compile::new(module, CraneliftObjectBackend::new())
                .with_opt_level(level)
                .compile()
                .map(|artifact| vec![artifact.into_bytes()])
                .map_err(|errors| format!("{errors:?}")),
        }
    }
}

/// The field types of struct or array `ty`, unless it is too long an array.
fn field_tys(func: &Function, ty: Type) -> Option<Vec<Type>> {
    func.ctx().with_ty_store(|store| {
        if let Some(data) = store.struct_def(ty) {
            return Some(data.fields.clone());
        }
        let (elem, len) = store.array_def(ty)?;
        (len <= MAX_FIELDS).then(|| vec![elem; len])
    })
}

fn const_index(func: &Function, value: ValueId) -> Option<usize> {
    func.dfg.value_imm(value)?.to_nonnegative_usize()
}

fn is_zero_const(func: &Function, value: ValueId) -> bool {
    func.dfg.value_is_zero(value) || func.dfg.value_imm(value).is_some_and(|imm| imm.is_zero())
}

/// Whether the insert `user` continues the chain ending in `value`: it is the
/// only use of `value`, as its destination, at a constant index.
fn continues(func: &Function, value: ValueId) -> bool {
    let mut users = func.dfg.users(value);
    let (Some(&user), None) = (users.next(), users.next()) else {
        return false;
    };
    func.dfg.downcast::<&InsertValue>(user).is_some_and(|next| {
        *next.dest() == value && *next.value() != value && const_index(func, *next.idx()).is_some()
    })
}

/// What respelling a module did.
#[derive(Default)]
struct Respelled {
    /// Aggregates respelled, and the functions and fixtures with any.
    aggregates: usize,
    funcs: usize,
    fixtures: usize,
    /// Chains on `zero` kept: with a dynamic index, or into an array longer
    /// than `MAX_FIELDS`.
    dynamic: usize,
    long: usize,
}

impl Respelled {
    fn add(&mut self, other: &Self) {
        self.aggregates += other.aggregates;
        self.funcs += other.funcs;
        self.fixtures += other.fixtures;
        self.dynamic += other.dynamic;
        self.long += other.long;
    }
}

/// Rewrites each `insert_value` chain on `zero` with constant indices whose
/// inner results have no other use into one `agg.make` at the chain's last
/// insert, with zero for the fields no insert writes.
fn chains_to_agg_make(func: &mut Function, stats: &mut Respelled) {
    func.rebuild_users();
    let tops: Vec<InstId> = func
        .layout
        .iter_block()
        .flat_map(|block| func.layout.iter_inst(block))
        .filter(|&inst| {
            func.dfg.downcast::<&InsertValue>(inst).is_some()
                && !continues(func, func.dfg.inst_result(inst).unwrap())
        })
        .collect();
    for top in tops {
        // The chain from its last insert down to `zero`: (inst, index, value).
        let mut chain = Vec::new();
        let mut inst = top;
        let on_zero = loop {
            let insert = func.dfg.downcast::<&InsertValue>(inst).unwrap().clone();
            let Some(index) = const_index(func, *insert.idx()) else {
                // A chain on `zero` below a dynamic index is its own top.
                stats.dynamic += usize::from(is_zero_const(func, *insert.dest()));
                break false;
            };
            chain.push((inst, index, *insert.value()));
            let dest = *insert.dest();
            if is_zero_const(func, dest) {
                break true;
            }
            match func.dfg.value_inst(dest) {
                Some(prev)
                    if func.dfg.downcast::<&InsertValue>(prev).is_some()
                        && func.dfg.users_num(dest) == 1 =>
                {
                    inst = prev;
                }
                _ => break false,
            }
        };
        if !on_zero {
            continue;
        }
        let ty = func.dfg.value_ty(func.dfg.inst_result(top).unwrap());
        let Some(tys) = field_tys(func, ty) else {
            stats.long += 1;
            continue;
        };
        // The last insert of a field wins.
        let mut fields = vec![None; tys.len()];
        for &(_, index, value) in &chain {
            fields[index].get_or_insert(value);
        }
        let values = fields
            .into_iter()
            .zip(tys)
            .map(|(field, ty)| field.unwrap_or_else(|| func.dfg.make_zero_const(ty)))
            .collect();
        let make = AggMake::new_unchecked(func.inst_set(), ty, values);
        func.dfg.replace_inst(top, Box::new(make));
        for &(inst, ..) in &chain[1..] {
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
        }
        stats.aggregates += 1;
    }
}

/// Rewrites each `agg.make` into an `insert_value` chain on `zero` that
/// inserts its non-zero operands in order. Returns how many.
fn agg_make_to_chains(func: &mut Function) -> usize {
    func.rebuild_users();
    let makes: Vec<InstId> = func
        .layout
        .iter_block()
        .flat_map(|block| func.layout.iter_inst(block))
        .filter(|&inst| func.dfg.downcast::<&AggMake>(inst).is_some())
        .collect();
    for &inst in &makes {
        let make = func.dfg.downcast::<&AggMake>(inst).unwrap().clone();
        let ty = *make.ty();
        let mut fields: Vec<(i32, ValueId)> = (0..)
            .zip(make.values().iter().copied())
            .filter(|&(_, value)| !is_zero_const(func, value))
            .collect();
        if fields.is_empty() {
            let Some(&first) = make.values().first() else {
                continue;
            };
            fields.push((0, first));
        }
        let (last_index, last_value) = fields.pop().unwrap();
        let mut dest = func.dfg.make_zero_const(ty);
        let mut cursor = InstInserter::at_location(func.layout.prev_inst_of(inst).map_or(
            CursorLocation::BlockTop(func.layout.inst_block(inst)),
            CursorLocation::At,
        ));
        for (index, value) in fields {
            let index = func.dfg.make_imm_value(index);
            let insert = InsertValue::new_unchecked(func.inst_set(), dest, index, value);
            let new = cursor.insert_inst_data(func, insert);
            dest = cursor.make_result(func, new, ty);
            cursor.attach_result(func, new, dest);
            cursor.set_location(CursorLocation::At(new));
        }
        let index = func.dfg.make_imm_value(last_index);
        let insert = InsertValue::new_unchecked(func.inst_set(), dest, index, last_value);
        func.dfg.replace_inst(inst, Box::new(insert));
    }
    makes.len()
}

/// Respells `module`: its chains as `agg.make`s if it has any to convert,
/// else its `agg.make`s as chains.
fn respell(module: &Module) -> Respelled {
    let mut stats = Respelled::default();
    for func in module.funcs() {
        let before = stats.aggregates;
        module
            .func_store
            .modify(func, |function| chains_to_agg_make(function, &mut stats));
        stats.funcs += usize::from(stats.aggregates > before);
    }
    if stats.aggregates == 0 {
        for func in module.funcs() {
            let count = module.func_store.modify(func, agg_make_to_chains);
            stats.aggregates += count;
            stats.funcs += usize::from(count > 0);
        }
    }
    stats.fixtures = usize::from(stats.aggregates > 0);
    stats
}

fn retarget(source: &str, target: Option<&str>) -> String {
    let Some(target) = target else {
        return source.to_string();
    };
    source
        .lines()
        .map(|line| {
            if line.trim_start().starts_with("target = ") {
                format!("target = \"{target}\"")
            } else {
                line.to_string()
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn fixtures() -> Vec<PathBuf> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let mut files = Vec::new();
    let mut pending = vec![
        root.join("codegen/test_files"),
        root.join("codegen/tests/fixtures"),
        root.join("filecheck/fixtures"),
    ];
    if let Some(dirs) = std::env::var_os("AGG_MAKE_SPELLING_DIRS") {
        pending.extend(std::env::split_paths(&dirs));
    }
    while let Some(dir) = pending.pop() {
        for entry in fs::read_dir(&dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                pending.push(path);
            } else if path
                .extension()
                .is_some_and(|ext| ext == "sntn" || ext == "sona")
            {
                files.push(path);
            }
        }
    }
    files.sort();
    files
}

#[test]
fn both_spellings_of_a_fresh_aggregate_compile_alike() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let verifier = VerifierConfig::for_level(VerificationLevel::Full);
    let mut report = String::new();
    let mut differences = Vec::new();
    let mut evm_compared = Vec::new();
    for backend in [Backend::Evm, Backend::Wasm, Backend::Cranelift] {
        let mut total = Respelled::default();
        let (mut compared, mut unparsed, mut uncompiled) = (0, 0, 0);
        for path in fixtures() {
            let relative = path.strip_prefix(&root).unwrap_or(&path);
            let name = relative.display().to_string();
            let source = retarget(&fs::read_to_string(&path).unwrap(), backend.target());
            let parse = || sonatina_parser::parse_module(&source).map(|parsed| parsed.module);
            let Ok(probe) = parse() else {
                unparsed += 1;
                continue;
            };
            let stats = respell(&probe);
            if stats.aggregates == 0 {
                total.add(&stats);
                continue;
            }
            let check = verify_module(&probe, &verifier);
            assert!(
                !check.has_errors(),
                "{name}: respelled module is invalid: {check}"
            );
            for level in LEVELS {
                let Ok(expected) = backend.compile(parse().unwrap(), level) else {
                    uncompiled += 1;
                    break;
                };
                let other = parse().unwrap();
                respell(&other);
                let actual = backend.compile(other, level);
                compared += 1;
                if backend == Backend::Evm {
                    evm_compared.push(name.clone());
                }
                if actual.as_ref() != Ok(&expected) {
                    let size = |bytes: &[Vec<u8>]| bytes.iter().map(Vec::len).sum::<usize>();
                    let detail = match &actual {
                        Ok(actual) => format!("{} -> {} bytes", size(&expected), size(actual)),
                        Err(error) => format!("respelled fails: {error}"),
                    };
                    if let Ok(dir) = std::env::var("AGG_MAKE_SPELLING_DUMP") {
                        let parts: Vec<_> =
                            relative.iter().map(|part| part.to_string_lossy()).collect();
                        let file = format!("{}.{backend:?}.{level:?}", parts.join("__"));
                        let respelled = parse().unwrap();
                        respell(&respelled);
                        let input = ModuleWriter::new(&respelled).dump_string();
                        fs::write(
                            Path::new(&dir).join(format!("{file}.respelled.input.sntn")),
                            input,
                        )
                        .unwrap();
                        fs::write(
                            Path::new(&dir).join(format!("{file}.written.input.sntn")),
                            &source,
                        )
                        .unwrap();
                        let bytes = [
                            ("written", Ok(expected.clone())),
                            ("respelled", actual.clone()),
                        ];
                        for (suffix, bytes) in bytes {
                            for (index, section) in bytes.into_iter().flatten().enumerate() {
                                fs::write(
                                    Path::new(&dir).join(format!("{file}.{suffix}.{index}.bin")),
                                    section,
                                )
                                .unwrap();
                            }
                        }
                        if backend == Backend::Evm {
                            let respelled = parse().unwrap();
                            respell(&respelled);
                            for (suffix, module) in
                                [("written", parse().unwrap()), ("respelled", respelled)]
                            {
                                let sizes = Backend::evm_function_sizes(module, level);
                                fs::write(
                                    Path::new(&dir).join(format!("{file}.{suffix}.sizes")),
                                    sizes,
                                )
                                .unwrap();
                            }
                        }
                        for (suffix, module) in
                            [("written", parse().unwrap()), ("respelled", respelled)]
                        {
                            let ir = backend.optimized_ir(module, level);
                            fs::write(Path::new(&dir).join(format!("{file}.{suffix}.sntn")), ir)
                                .unwrap();
                        }
                    }
                    differences.push((
                        name.clone(),
                        format!("{backend:?}"),
                        format!("{level:?}"),
                        detail,
                    ));
                }
            }
            total.add(&stats);
        }
        writeln!(
            report,
            "{backend:?}: respelled {} aggregates in {} functions of {} fixtures; kept {} chains with a dynamic index and {} into long arrays; {compared} fixture levels compared; {unparsed} fixtures do not parse and {uncompiled} do not compile for this target",
            total.aggregates, total.funcs, total.fixtures, total.dynamic, total.long
        )
        .unwrap();
    }
    for difference in &differences {
        writeln!(report, "differs: {difference:?}").unwrap();
    }
    eprintln!("{report}");
    assert!(differences.is_empty(), "{report}");
    let agg_make_levels = evm_compared
        .iter()
        .filter(|name| Path::new(name).ends_with("evm/agg_make.sntn"))
        .count();
    assert_eq!(
        agg_make_levels,
        LEVELS.len(),
        "evm/agg_make.sntn was not compared on EVM"
    );
}
