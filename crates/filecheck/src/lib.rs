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

use sonatina_parser::{
    parser::{ParsedModule, Parser},
    ErrorKind,
};
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
                        && ent.path().extension().map_or(false, |ext| ext == "sntn")
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
        writeln!(stdout, "\nrunning {} tests", tests_num).unwrap();
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
        let mut parsed_module = match self.parse_file() {
            Ok(module) => module,
            Err(msg) => return vec![FileCheckResult::new(self.file_path.to_owned(), Err(msg))],
        };

        let module = &parsed_module.module;

        module
            .iter_functions()
            .map(|func_ref| self.check_func(&mut parsed_module, func_ref))
            .collect()
    }

    fn check_func(
        &mut self,
        parsed_module: &mut ParsedModule,
        func_ref: FuncRef,
    ) -> FileCheckResult {
        let func = &mut parsed_module.module.funcs[func_ref];
        let comments = &parsed_module.func_comments[func_ref];

        self.transformer.transform(func);
        let func_ir = FuncWriter::new(func).dump_string().unwrap();

        let checker = self.build_checker(comments);

        let result = match checker.explain(&func_ir, &()) {
            Ok((true, _)) => Ok(()),
            Ok((false, err)) => Err(err),
            Err(err) => Err(format!("{}", err)),
        };

        let mut test_path = self.file_path.to_owned();
        test_path.push(func.sig.name());
        FileCheckResult::new(test_path, result)
    }

    fn parse_file(&self) -> Result<ParsedModule, String> {
        let input = fs::read_to_string(self.file_path).unwrap();
        let parser = Parser::default();
        match parser.parse(&input) {
            Ok(module) => Ok(module),
            Err(err) => match err.kind {
                ErrorKind::InvalidToken(msg) => Err(format!(
                    "failed to parse file: invalid token: {}. line: {}",
                    msg, err.line
                )),

                ErrorKind::SyntaxError(msg) => Err(format!(
                    "failed to parse file: invalid syntax: {}. line: {}",
                    msg, err.line
                )),

                ErrorKind::SemanticError(msg) => Err(format!(
                    "failed to parse file: invalid semantics: {}. line: {}",
                    msg, err.line
                )),
            },
        }
    }

    fn build_checker(&self, directives: &[String]) -> filecheck::Checker {
        let mut builder = filecheck::CheckerBuilder::new();
        for d in directives {
            builder.directive(d).unwrap();
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
                writeln!(stdout, "{}", err)?;
            }
        }
        Ok(())
    }

    fn is_ok(&self) -> bool {
        self.result.is_ok()
    }
}
