use std::{
    cmp::Reverse,
    collections::{HashMap, HashSet},
    fs,
    io::{self, IsTerminal},
    path::{Path, PathBuf},
    process,
    sync::{Arc, Mutex},
    time::{Duration, Instant},
};

use clap::{Parser, Subcommand};
use sonatina_codegen::{
    isa::evm::{EvmBackend, PushWidthPolicy},
    object::{CompileOptions, ObjectArtifact, compile_all_objects},
    optim::pipeline::Pipeline,
};
use sonatina_ir::{ir_writer::ModuleWriter, isa::evm::Evm, module::Module};
use sonatina_parser::{ParsedModule, parse_module};
use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};
use tracing::span::Id;
use tracing_subscriber::{
    Registry,
    layer::{Context, Layer, SubscriberExt},
    registry::LookupSpan,
};

#[derive(Debug, Parser)]
#[command(name = "sonatina")]
#[command(about = "Sonatina command-line tool")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Debug, Subcommand)]
enum Command {
    /// Parse and verify Sonatina IR
    Verify {
        /// Input Sonatina IR file
        input: PathBuf,
    },

    /// Optimize Sonatina IR and write <input>.opt.sntn
    Optimize {
        /// Emit profile timing from tracing spans
        #[arg(short = 'p', long = "profile")]
        profile: bool,

        /// Input Sonatina IR file
        input: PathBuf,
    },

    /// Build EVM bytecode and write <input>.evm.bin
    Build {
        /// Emit profile timing from tracing spans
        #[arg(short = 'p', long = "profile")]
        profile: bool,

        /// Input Sonatina IR file
        input: PathBuf,
    },
}

fn main() {
    let cli = Cli::parse();
    let exit_code = match cli.command {
        Command::Verify { input } => run_verify(&input),
        Command::Optimize { input, profile } => run_optimize(&input, profile),
        Command::Build { input, profile } => run_build(&input, profile),
    };
    process::exit(exit_code);
}

fn run_verify(input: &Path) -> i32 {
    let source = match read_source(input) {
        Ok(source) => source,
        Err(code) => return code,
    };
    let parsed = match parse_or_report(input, &source) {
        Ok(parsed) => parsed,
        Err(code) => return code,
    };

    let report = verify_module(
        &parsed.module,
        &VerifierConfig::for_level(VerificationLevel::Full),
    );
    if report.diagnostics.is_empty() {
        println!("ok");
        return 0;
    }

    println!("{report}");
    if report.has_errors() { 1 } else { 0 }
}

fn run_optimize(input: &Path, profile: bool) -> i32 {
    let profiler = Profiler::start(profile);
    let total_start = Instant::now();
    let mut stages = Vec::new();

    let source = match measure_stage(&mut stages, "read", || read_source(input)) {
        Ok(source) => source,
        Err(code) => return code,
    };
    let mut parsed = match measure_stage(&mut stages, "parse", || parse_or_report(input, &source)) {
        Ok(parsed) => parsed,
        Err(code) => return code,
    };
    if let Err(code) = measure_stage(&mut stages, "verify", || {
        verify_or_report(&parsed.module, VerificationLevel::Fast)
    }) {
        return code;
    }

    measure_stage(&mut stages, "optimize", || {
        Pipeline::size().run(&mut parsed.module);
    });

    let optimized = measure_stage(&mut stages, "emit_ir", || {
        ModuleWriter::with_debug_provider(&parsed.module, &parsed.debug).dump_string()
    });

    let output_path = optimized_output_path(input);
    if let Err(err) = measure_stage(&mut stages, "write", || {
        fs::write(&output_path, optimized.as_bytes())
    }) {
        eprintln!("error: failed to write `{}`: {err}", output_path.display(),);
        return 2;
    }

    println!("wrote {}", output_path.display());
    profiler.print("optimize", &stages, total_start.elapsed());
    0
}

fn run_build(input: &Path, profile: bool) -> i32 {
    let profiler = Profiler::start(profile);
    let total_start = Instant::now();
    let mut stages = Vec::new();

    let source = match measure_stage(&mut stages, "read", || read_source(input)) {
        Ok(source) => source,
        Err(code) => return code,
    };
    let mut parsed = match measure_stage(&mut stages, "parse", || parse_or_report(input, &source)) {
        Ok(parsed) => parsed,
        Err(code) => return code,
    };
    if let Err(code) = measure_stage(&mut stages, "verify", || {
        verify_or_report(&parsed.module, VerificationLevel::Fast)
    }) {
        return code;
    }

    measure_stage(&mut stages, "optimize", || {
        Pipeline::size().run(&mut parsed.module);
    });

    let artifacts =
        match measure_stage(&mut stages, "codegen", || compile_artifacts(&parsed.module)) {
            Ok(artifacts) => artifacts,
            Err(code) => return code,
        };
    let artifact = match select_artifact(&artifacts) {
        Ok(artifact) => artifact,
        Err(err) => {
            eprintln!("error: {err}");
            return 1;
        }
    };
    let (section_name, bytes) = match select_section(artifact) {
        Ok(selection) => selection,
        Err(err) => {
            eprintln!("error: {err}");
            return 1;
        }
    };

    let output_path = bytecode_output_path(input);
    if let Err(err) = measure_stage(&mut stages, "write", || fs::write(&output_path, bytes)) {
        eprintln!("error: failed to write `{}`: {err}", output_path.display(),);
        return 2;
    }

    println!(
        "wrote {} (object `{}`, section `{}`, {} bytes)",
        output_path.display(),
        artifact.object.0,
        section_name,
        bytes.len()
    );
    profiler.print("build", &stages, total_start.elapsed());
    0
}

fn read_source(input: &Path) -> Result<String, i32> {
    fs::read_to_string(input).map_err(|err| {
        eprintln!("error: failed to read `{}`: {err}", input.display());
        2
    })
}

fn parse_or_report(input: &Path, source: &str) -> Result<ParsedModule, i32> {
    match parse_module(source) {
        Ok(parsed) => Ok(parsed),
        Err(errors) => {
            let mut stderr = io::stderr();
            let use_colors = stderr.is_terminal();
            let path = input.display().to_string();
            for error in errors {
                if error.print(&mut stderr, &path, source, use_colors).is_err() {
                    eprintln!("parse error: {error:?}");
                }
            }
            Err(1)
        }
    }
}

fn verify_or_report(module: &Module, level: VerificationLevel) -> Result<(), i32> {
    let report = verify_module(module, &VerifierConfig::for_level(level));
    if report.diagnostics.is_empty() {
        return Ok(());
    }

    eprintln!("{report}");
    if report.has_errors() { Err(1) } else { Ok(()) }
}

fn compile_artifacts(module: &Module) -> Result<Vec<ObjectArtifact>, i32> {
    let triple = TargetTriple::new(
        Architecture::Evm,
        Vendor::Ethereum,
        OperatingSystem::Evm(EvmVersion::Osaka),
    );
    let backend = EvmBackend::new(Evm::new(triple));
    let opts = CompileOptions {
        fixup_policy: PushWidthPolicy::MinimalRelax,
        emit_symtab: false,
        emit_observability: false,
        verifier_cfg: VerifierConfig::for_level(VerificationLevel::Fast),
    };

    compile_all_objects(module, &backend, &opts).map_err(|errors| {
        eprintln!("error: object compilation failed:");
        for error in errors {
            eprintln!("  {error:?}");
        }
        1
    })
}

fn select_artifact(artifacts: &[ObjectArtifact]) -> Result<&ObjectArtifact, String> {
    if artifacts.is_empty() {
        return Err("no objects were compiled".to_string());
    }
    if artifacts.len() == 1 {
        return Ok(&artifacts[0]);
    }

    let mut matching = artifacts
        .iter()
        .filter(|artifact| artifact.object.0.as_str() == "Contract");
    match (matching.next(), matching.next()) {
        (Some(artifact), None) => Ok(artifact),
        _ => {
            let names = artifacts
                .iter()
                .map(|artifact| artifact.object.0.as_str().to_string())
                .collect::<Vec<_>>()
                .join(", ");
            Err(format!(
                "multiple objects found ({names}); unable to choose output object"
            ))
        }
    }
}

fn select_section(artifact: &ObjectArtifact) -> Result<(&str, &[u8]), String> {
    if let Some((name, section)) = artifact
        .sections
        .iter()
        .find(|(name, _)| name.0.as_str() == "init")
    {
        return Ok((name.0.as_str(), section.bytes.as_slice()));
    }
    if let Some((name, section)) = artifact
        .sections
        .iter()
        .find(|(name, _)| name.0.as_str() == "runtime")
    {
        return Ok((name.0.as_str(), section.bytes.as_slice()));
    }
    if artifact.sections.len() == 1
        && let Some((name, section)) = artifact.sections.iter().next()
    {
        return Ok((name.0.as_str(), section.bytes.as_slice()));
    }

    let names = artifact
        .sections
        .keys()
        .map(|name| name.0.as_str().to_string())
        .collect::<Vec<_>>()
        .join(", ");
    Err(format!(
        "object `{}` has multiple sections ({names}); unable to choose output section",
        artifact.object.0
    ))
}

fn optimized_output_path(input: &Path) -> PathBuf {
    with_suffix_before_ext(input, ".opt", "sntn")
}

fn bytecode_output_path(input: &Path) -> PathBuf {
    let parent = input.parent().unwrap_or_else(|| Path::new("."));
    let stem = input
        .file_stem()
        .and_then(|stem| stem.to_str())
        .unwrap_or("output");
    parent.join(format!("{stem}.evm.bin"))
}

fn with_suffix_before_ext(input: &Path, suffix: &str, fallback_ext: &str) -> PathBuf {
    let parent = input.parent().unwrap_or_else(|| Path::new("."));
    let stem = input
        .file_stem()
        .and_then(|stem| stem.to_str())
        .unwrap_or("output");
    let ext = input.extension().and_then(|ext| ext.to_str());
    match ext {
        Some(ext) => parent.join(format!("{stem}{suffix}.{ext}")),
        None => parent.join(format!("{stem}{suffix}.{fallback_ext}")),
    }
}

#[derive(Debug)]
struct StageTiming {
    name: &'static str,
    elapsed: Duration,
}

fn measure_stage<T>(stages: &mut Vec<StageTiming>, name: &'static str, f: impl FnOnce() -> T) -> T {
    let start = Instant::now();
    let result = f();
    stages.push(StageTiming {
        name,
        elapsed: start.elapsed(),
    });
    result
}

struct Profiler {
    enabled: bool,
    layer: SpanStatsLayer,
}

impl Profiler {
    fn start(enabled: bool) -> Self {
        let layer = SpanStatsLayer::default();
        if enabled {
            let subscriber = Registry::default().with(layer.clone());
            if let Err(err) = tracing::subscriber::set_global_default(subscriber) {
                eprintln!("warning: failed to install tracing subscriber for profile mode: {err}");
                return Self {
                    enabled: false,
                    layer,
                };
            }
        }
        Self { enabled, layer }
    }

    fn print(&self, command: &str, stages: &[StageTiming], total: Duration) {
        if !self.enabled {
            return;
        }

        println!("profile `{command}`:");
        println!("  total {:>12.3} ms", to_ms(total));
        for stage in stages {
            println!("  {:<8} {:>12.3} ms", stage.name, to_ms(stage.elapsed));
        }

        let mut snapshot = self.layer.snapshot();
        snapshot.stats.sort_by_key(|right| Reverse(right.1.total));

        println!("  top spans:");
        for (name, stat) in snapshot
            .stats
            .iter()
            .filter(|(name, _)| name.starts_with("sonatina."))
            .take(20)
        {
            println!(
                "    {:<52} total={:>10.3} ms count={:>6} avg={:>8.3} ms max={:>8.3} ms",
                name,
                to_ms(stat.total),
                stat.count,
                to_ms(stat.avg()),
                to_ms(stat.max),
            );
        }

        let mut pass_stats = snapshot
            .stats
            .iter()
            .filter(|(name, _)| name.starts_with("sonatina.optim.pipeline.pass."))
            .collect::<Vec<_>>();
        pass_stats.sort_by_key(|right| Reverse(right.1.total));

        if !pass_stats.is_empty() {
            println!("  optimization passes:");
            for (name, stat) in pass_stats {
                println!(
                    "    {:<52} total={:>10.3} ms count={:>6} avg={:>8.3} ms max={:>8.3} ms",
                    name,
                    to_ms(stat.total),
                    stat.count,
                    to_ms(stat.avg()),
                    to_ms(stat.max),
                );
            }
        }

        print_span_timeline(&snapshot.spans);
    }
}

fn to_ms(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1000.0
}

#[derive(Default, Clone)]
struct SpanStatsLayer {
    state: Arc<Mutex<SpanState>>,
}

impl SpanStatsLayer {
    fn snapshot(&self) -> ProfileSnapshot {
        let state = self.state.lock().unwrap();
        ProfileSnapshot {
            stats: state
                .stats
                .iter()
                .map(|(name, stat)| (name.clone(), *stat))
                .collect(),
            spans: state.spans.clone(),
        }
    }
}

#[derive(Default)]
struct SpanState {
    next_serial: u64,
    live: HashMap<Id, SpanOpen>,
    stats: HashMap<String, SpanStat>,
    spans: Vec<CompletedSpan>,
}

struct ProfileSnapshot {
    stats: Vec<(String, SpanStat)>,
    spans: Vec<CompletedSpan>,
}

#[derive(Debug)]
struct SpanOpen {
    serial: u64,
    parent_serial: Option<u64>,
    name: String,
    opened: Instant,
}

#[derive(Debug, Clone)]
struct CompletedSpan {
    serial: u64,
    parent_serial: Option<u64>,
    name: String,
    opened: Instant,
    elapsed: Duration,
}

#[derive(Debug, Default, Clone, Copy)]
struct SpanStat {
    count: u64,
    total: Duration,
    max: Duration,
}

impl SpanStat {
    fn add_sample(&mut self, sample: Duration) {
        self.count += 1;
        self.total += sample;
        if sample > self.max {
            self.max = sample;
        }
    }

    fn avg(self) -> Duration {
        if self.count == 0 {
            return Duration::ZERO;
        }
        Duration::from_secs_f64(self.total.as_secs_f64() / self.count as f64)
    }
}

impl<S> Layer<S> for SpanStatsLayer
where
    S: tracing::Subscriber + for<'span> LookupSpan<'span>,
{
    fn on_new_span(&self, attrs: &tracing::span::Attributes<'_>, id: &Id, ctx: Context<'_, S>) {
        let parent_id = attrs.parent().cloned().or_else(|| {
            if attrs.is_contextual() {
                ctx.current_span().id().cloned()
            } else {
                None
            }
        });

        let mut state = self.state.lock().unwrap();
        let parent_serial = parent_id
            .as_ref()
            .and_then(|parent_id| state.live.get(parent_id).map(|span| span.serial));
        let serial = state.next_serial;
        state.next_serial += 1;
        let span = SpanOpen {
            serial,
            parent_serial,
            name: attrs.metadata().name().to_string(),
            opened: Instant::now(),
        };
        state.live.insert(id.clone(), span);
    }

    fn on_close(&self, id: Id, _ctx: Context<'_, S>) {
        let mut state = self.state.lock().unwrap();
        let Some(open) = state.live.remove(&id) else {
            return;
        };
        let elapsed = open.opened.elapsed();
        state
            .stats
            .entry(open.name.clone())
            .or_default()
            .add_sample(elapsed);
        state.spans.push(CompletedSpan {
            serial: open.serial,
            parent_serial: open.parent_serial,
            name: open.name,
            opened: open.opened,
            elapsed,
        });
    }
}

fn print_span_timeline(spans: &[CompletedSpan]) {
    let mut ordered = spans
        .iter()
        .filter(|span| span.name.starts_with("sonatina."))
        .cloned()
        .collect::<Vec<_>>();
    ordered.sort_by(|left, right| {
        left.opened
            .cmp(&right.opened)
            .then(left.serial.cmp(&right.serial))
    });
    if ordered.is_empty() {
        return;
    }

    let parent_map = spans
        .iter()
        .map(|span| (span.serial, span.parent_serial))
        .collect::<HashMap<_, _>>();
    let included = ordered
        .iter()
        .map(|span| span.serial)
        .collect::<HashSet<_>>();
    let start = ordered[0].opened;

    println!(
        "  span timeline (execution order, {} spans):",
        ordered.len()
    );
    for span in ordered {
        let depth = span_depth(span.serial, &parent_map, &included);
        let indent = "  ".repeat(depth);
        let start_offset = to_ms(span.opened.duration_since(start));
        println!(
            "    +{:>10.3} ms {}{} ({:>9.3} ms)",
            start_offset,
            indent,
            span.name,
            to_ms(span.elapsed),
        );
    }
}

fn span_depth(
    serial: u64,
    parent_map: &HashMap<u64, Option<u64>>,
    included: &HashSet<u64>,
) -> usize {
    let mut depth = 0;
    let mut parent = parent_map.get(&serial).copied().flatten();
    while let Some(current) = parent {
        if included.contains(&current) {
            depth += 1;
        }
        parent = parent_map.get(&current).copied().flatten();
    }
    depth
}
