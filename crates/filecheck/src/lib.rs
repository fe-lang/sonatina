pub mod adce;
pub mod gvn;
pub mod insn_simplify;
pub mod licm;
pub mod sccp;

use std::{
    fs,
    io::{self, Write},
    path::{Path, PathBuf},
    time,
};

use sonatina_ir::{ir_writer::FuncWriter, module::FuncRef, Function};
use sonatina_parser::{parse_module, ParsedModule};
use termcolor::{Color, ColorChoice, ColorSpec, StandardStream, WriteColor};
use walkdir::WalkDir;

pub(crate) const FIXTURE_ROOT: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/fixtures");

pub trait FuncTransform {
    fn transform(&mut self, func: &mut Function);

    fn test_root(&self) -> PathBuf;
}

pub struct FileCheckRunner {
    transformer: Box<dyn FuncTransform>,
    results: Vec<FileCheckResult>,
    timer: time::Instant,
}

impl FileCheckRunner {
    pub fn new(transformer: impl FuncTransform + 'static) -> Self {
        Self {
            transformer: Box::new(transformer),
            results: Vec::new(),
            timer: time::Instant::now(),
        }
    }

    pub fn attach_transformer(&mut self, transformer: impl FuncTransform + 'static) {
        self.transformer = Box::new(transformer);
    }

    pub fn run(&mut self) {
        for ent in WalkDir::new(self.transformer.test_root())
            .into_iter()
            .filter_map(|e| match e {
                Ok(ent) => {
                    if ent.file_type().is_file()
                        && ent.path().extension().is_some_and(|ext| ext == "sntn")
                    {
                        Some(ent)
                    } else {
                        None
                    }
                }
                _ => None,
            })
        {
            let mut checker = FileChecker::new(self.transformer.as_mut(), ent.path());
            self.results.extend(checker.check());
        }
    }

    pub fn print_results(&self) {
        let tests_num = self.results.len();
        let failed_num = self.failed_num();
        let is_success = failed_num == 0;

        let mut stdout = StandardStream::stdout(ColorChoice::Always);
        writeln!(stdout, "\nrunning {tests_num} tests").unwrap();
        for res in &self.results {
            res.print_result(&mut stdout).unwrap();
        }

        write!(stdout, "\ntest result: ").unwrap();
        if is_success {
            stdout
                .set_color(ColorSpec::new().set_fg(Color::Green.into()))
                .unwrap();
            write!(stdout, "ok").unwrap();
        } else {
            stdout
                .set_color(ColorSpec::new().set_fg(Color::Red.into()))
                .unwrap();
            write!(stdout, "FAILED").unwrap();
        }
        stdout.reset().unwrap();

        let elapsed = self.timer.elapsed();

        writeln!(
            stdout,
            ". {} passed; {} failed; 0 ignored; 0 measured; 0 filtered out; finished in {}.{:02}s\n",
            tests_num - failed_num,
            failed_num,
            elapsed.as_secs(),
            elapsed.subsec_millis() / 10,
        )
        .unwrap();
    }

    pub fn failed_num(&self) -> usize {
        self.results.iter().filter(|res| !res.is_ok()).count()
    }

    pub fn is_ok(&self) -> bool {
        self.failed_num() == 0
    }
}

pub struct FileChecker<'a> {
    transformer: &'a mut dyn FuncTransform,
    file_path: &'a Path,
}

impl<'a> FileChecker<'a> {
    fn new(transformer: &'a mut dyn FuncTransform, file_path: &'a Path) -> Self {
        Self {
            transformer,
            file_path,
        }
    }

    fn check(&mut self) -> Vec<FileCheckResult> {
        let parsed_module = match self.parse_file() {
            Ok(module) => module,
            Err(msg) => return vec![FileCheckResult::new(self.file_path.to_owned(), Err(msg))],
        };

        let module = &parsed_module.module;

        module
            .funcs()
            .into_iter()
            .map(|func_ref| self.check_func(&parsed_module, func_ref))
            .collect()
    }

    fn check_func(&mut self, parsed_module: &ParsedModule, func_ref: FuncRef) -> FileCheckResult {
        let comments = &parsed_module.debug.func_comments[func_ref];

        let (func_ir, func_name) = parsed_module.module.func_store.modify(func_ref, |func| {
            self.transformer.transform(func);
            (
                FuncWriter::with_debug_provider(func, func_ref, &parsed_module.debug).dump_string(),
                parsed_module
                    .module
                    .ctx
                    .func_sig(func_ref, |sig| sig.name().to_string()),
            )
        });
        let checker = self.build_checker(comments);

        let result = match checker.explain(&func_ir, &()) {
            Ok((true, _)) => Ok(()),
            Ok((false, err)) => Err(err),
            Err(err) => Err(format!("{err}")),
        };

        let mut test_path = self.file_path.to_owned();
        test_path.push(func_name);
        FileCheckResult::new(test_path, result)
    }

    fn parse_file(&self) -> Result<ParsedModule, String> {
        let input = fs::read_to_string(self.file_path).unwrap();

        match parse_module(&input) {
            Ok(module) => Ok(module),
            Err(errs) => {
                let mut v = vec![];
                for e in errs {
                    e.print(&mut v, self.file_path.to_str().unwrap(), &input, true)
                        .unwrap()
                }
                Err(String::from_utf8(v).unwrap())
            }
        }
    }

    fn build_checker(&self, directives: &[String]) -> filecheck::Checker {
        let mut builder = filecheck::CheckerBuilder::new();
        for d in directives {
            if !builder.directive(d).unwrap() && d.contains("nextln") {
                panic!("not a directive: `{d}`");
            }
        }
        builder.finish()
    }
}

#[derive(Debug)]
pub struct FileCheckResult {
    path: PathBuf,
    result: Result<(), String>,
}

impl FileCheckResult {
    fn new(path: PathBuf, result: Result<(), String>) -> Self {
        Self { path, result }
    }

    fn print_result(&self, stdout: &mut StandardStream) -> io::Result<()> {
        let path = self.path.strip_prefix(FIXTURE_ROOT).unwrap();
        write!(
            stdout,
            "test {} ...",
            path.to_string_lossy()
                .replace('/', "::")
                .replace(".sntn", "")
        )?;
        match &self.result {
            Ok(()) => {
                stdout.set_color(ColorSpec::new().set_fg(Color::Green.into()))?;
                writeln!(stdout, " ok")?;
                stdout.reset()?;
            }
            Err(err) => {
                stdout.set_color(ColorSpec::new().set_fg(Color::Red.into()))?;
                writeln!(stdout, " FAILED")?;
                stdout.reset()?;
                writeln!(stdout, "{err}")?;
            }
        }
        Ok(())
    }

    fn is_ok(&self) -> bool {
        self.result.is_ok()
    }
}
