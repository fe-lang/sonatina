//! Static linking for RV64IM SP1 objects, separate from code generation.
//!
//! The object must export `main() -> i32` using the RV64 C ABI. The upstream
//! runtime initializes the guest, calls main, and finalizes public values at
//! halt. This crate contains no executor or prover dependencies.
#![doc = include_str!("../README.md")]

use std::{
    env, fs, io,
    path::{Path, PathBuf},
    process::{Command, Output},
};

use object::{Object, ObjectSection, ObjectSymbol};
use tempfile::TempDir;
use thiserror::Error;

pub const SP1_VERSION: &str = "6.8.0";
pub const TOOLCHAIN_RELEASE: &str = "succinct-1.96.0-64bit-v2";
pub const TARGET: &str = "riscv64im-succinct-zkvm-elf";
const IMAGE_BASE: u64 = 0x7800_0000;

#[derive(Debug, Error)]
pub enum Sp1Error {
    #[error("SP1 toolchain: {0}")]
    Toolchain(String),
    #[error("SP1 artifact: {0}")]
    Artifact(String),
    #[error("SP1 {operation} failed ({status}):\n{stdout}{stderr}")]
    Command {
        operation: &'static str,
        status: String,
        stdout: String,
        stderr: String,
    },
    #[error("SP1 I/O: {0}")]
    Io(#[from] io::Error),
}

#[derive(Debug)]
pub struct Sp1Toolchain {
    rustc: PathBuf,
    linker: PathBuf,
}

impl Sp1Toolchain {
    /// Locate the pinned installation without modifying rustup or downloading.
    pub fn from_env() -> Result<Self, Sp1Error> {
        let directory = env::var_os("SONATINA_SP1_TOOLCHAIN").ok_or_else(|| {
            Sp1Error::Toolchain(format!(
                "set SONATINA_SP1_TOOLCHAIN to the extracted {TOOLCHAIN_RELEASE} directory"
            ))
        })?;
        Self::from_directory(directory)
    }

    /// Use an installation of [`TOOLCHAIN_RELEASE`]. These checks detect an
    /// incompatible compiler; use the published archive checksum to establish
    /// the installation's identity (rustc reports an unknown commit hash).
    pub fn from_directory(directory: impl AsRef<Path>) -> Result<Self, Sp1Error> {
        let directory = directory.as_ref().canonicalize()?;
        let rustc = directory.join("bin/rustc");
        let output = run(Command::new(&rustc).arg("-vV"), "toolchain inspection")?;
        let version = String::from_utf8_lossy(&output.stdout);
        if !version.lines().any(|line| line == "release: 1.96.0-dev")
            || !version.lines().any(|line| line == "LLVM version: 22.1.2")
        {
            return Err(Sp1Error::Toolchain(format!(
                "expected {TOOLCHAIN_RELEASE}, found:\n{version}"
            )));
        }
        let host = version
            .lines()
            .find_map(|line| line.strip_prefix("host: "))
            .ok_or_else(|| Sp1Error::Toolchain("rustc did not report a host".into()))?;
        let linker = directory
            .join("lib/rustlib")
            .join(host)
            .join("bin/rust-lld");
        if !linker.is_file()
            || !directory
                .join("lib/rustlib")
                .join(TARGET)
                .join("lib")
                .is_dir()
        {
            return Err(Sp1Error::Toolchain(format!(
                "{TOOLCHAIN_RELEASE} is missing rust-lld or the {TARGET} standard library"
            )));
        }
        Ok(Self { rustc, linker })
    }
}

/// A reusable, pinned runtime archive. Build once, then link multiple objects.
pub struct Sp1Runtime {
    toolchain: Sp1Toolchain,
    directory: TempDir,
    archive: PathBuf,
}

impl Sp1Runtime {
    /// Build the embedded, locked guest package. Cargo may fetch its pinned
    /// dependencies; installing the Succinct toolchain remains explicit.
    pub fn build(toolchain: Sp1Toolchain) -> Result<Self, Sp1Error> {
        let directory = tempfile::Builder::new()
            .prefix("sonatina-sp1-runtime-")
            .tempdir()?;
        fs::create_dir(directory.path().join("src"))?;
        fs::write(
            directory.path().join("Cargo.toml"),
            include_str!("../runtime/Cargo.toml.in"),
        )?;
        fs::write(
            directory.path().join("Cargo.lock"),
            include_str!("../runtime/Cargo.lock"),
        )?;
        fs::write(
            directory.path().join("src/lib.rs"),
            include_str!("../runtime/src/lib.rs"),
        )?;
        let flags = [
            "-C",
            "passes=lower-atomic",
            "-C",
            "panic=abort",
            "--cfg",
            "getrandom_backend=\"custom\"",
            "-C",
            "llvm-args=-misched-prera-direction=bottomup",
            "-C",
            "llvm-args=-misched-postra-direction=bottomup",
        ]
        .join("\x1f");
        let mut command = Command::new("cargo");
        command
            .current_dir(directory.path())
            .args([
                "build",
                "--locked",
                "--release",
                "--lib",
                "--target",
                TARGET,
            ])
            .env("RUSTC", &toolchain.rustc)
            .env("CARGO_TARGET_DIR", directory.path().join("target"))
            .env("CARGO_ENCODED_RUSTFLAGS", flags)
            .env_remove("RUSTFLAGS")
            .env_remove("RUSTC_WRAPPER")
            .env_remove("RUSTC_WORKSPACE_WRAPPER");
        for (name, _) in env::vars_os() {
            if name.to_str().is_some_and(|name| {
                name.starts_with("CARGO_FEATURE_") || name.starts_with("CARGO_CFG_")
            }) {
                command.env_remove(name);
            }
        }
        run(&mut command, "runtime build")?;
        let archive = directory
            .path()
            .join("target")
            .join(TARGET)
            .join("release/libsonatina_sp1_runtime.a");
        Ok(Self {
            toolchain,
            directory,
            archive,
        })
    }

    /// Statically link RV64IM objects, exactly one of which must export
    /// `main() -> i32`. Undefined symbols and out-of-range PC-relative
    /// relocations are errors, not far-call fallbacks. Callers are responsible
    /// for instruction-set compliance and C-compatible external signatures;
    /// ELF headers cannot establish those properties.
    pub fn link_objects(&self, objects: &[&[u8]]) -> Result<Vec<u8>, Sp1Error> {
        let mut main_count = 0;
        for bytes in objects {
            let object = read_rv64_elf(bytes)?;
            if object.kind() != object::ObjectKind::Relocatable {
                return Err(Sp1Error::Artifact("expected a relocatable object".into()));
            }
            main_count += object
                .symbols()
                .filter(|symbol| {
                    symbol.is_global()
                        && symbol.is_definition()
                        && symbol.kind() == object::SymbolKind::Text
                        && symbol.name() == Ok("main")
                })
                .count();
            for section in object
                .sections()
                .filter(|section| section.kind() == object::SectionKind::Text)
            {
                if section.relocations().any(|(_, relocation)| {
                    matches!(
                        relocation.flags(),
                        object::RelocationFlags::Elf {
                            r_type: object::elf::R_RISCV_64
                        }
                    )
                }) {
                    return Err(Sp1Error::Artifact(
                        "absolute address literals in executable text are not supported".into(),
                    ));
                }
            }
        }
        if main_count != 1 {
            return Err(Sp1Error::Artifact(
                "expected exactly one object exporting main() -> i32".into(),
            ));
        }
        let link_dir = tempfile::Builder::new()
            .prefix("link-")
            .tempdir_in(self.directory.path())?;
        let output = link_dir.path().join("program.elf");
        let mut command = Command::new(&self.toolchain.linker);
        command
            .args([
                "-flavor",
                "gnu",
                "-m",
                "elf64lriscv",
                "--entry=_start",
                "--gc-sections",
                "-static",
            ])
            .arg(format!("--image-base={IMAGE_BASE}"));
        for (index, bytes) in objects.iter().enumerate() {
            let input = link_dir.path().join(format!("module-{index}.o"));
            fs::write(&input, bytes)?;
            command.arg(input);
        }
        run(
            command.arg(&self.archive).arg("-o").arg(&output),
            "ELF link",
        )?;
        let bytes = fs::read(output)?;
        let elf = read_rv64_elf(&bytes)?;
        if elf.kind() != object::ObjectKind::Executable || elf.entry() < IMAGE_BASE {
            return Err(Sp1Error::Artifact(
                "linker did not produce an SP1 executable".into(),
            ));
        }
        Ok(bytes)
    }
}

fn read_rv64_elf(bytes: &[u8]) -> Result<object::File<'_>, Sp1Error> {
    let file = object::File::parse(bytes).map_err(|error| Sp1Error::Artifact(error.to_string()))?;
    if file.format() != object::BinaryFormat::Elf
        || file.architecture() != object::Architecture::Riscv64
        || !file.is_little_endian()
        || !matches!(file.flags(), object::FileFlags::Elf { e_flags: 0, .. })
    {
        return Err(Sp1Error::Artifact(
            "expected little-endian RV64 ELF with soft-float ABI and no compressed instructions"
                .into(),
        ));
    }
    Ok(file)
}

fn run(command: &mut Command, operation: &'static str) -> Result<Output, Sp1Error> {
    let output = command.output()?;
    if !output.status.success() {
        return Err(Sp1Error::Command {
            operation,
            status: output.status.to_string(),
            stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
            stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        });
    }
    Ok(output)
}

#[cfg(test)]
mod tests {
    use object::{
        Architecture, BinaryFormat, Endianness, FileFlags, RelocationFlags, SectionKind,
        SymbolFlags, SymbolKind, SymbolScope,
        write::{Object, Relocation, Symbol, SymbolSection},
    };

    use super::*;

    #[test]
    fn rejects_other_object_formats_architectures_and_abi_flags() {
        for (format, architecture, flags) in [
            (BinaryFormat::Elf, Architecture::Riscv64, 0),
            (BinaryFormat::Elf, Architecture::Riscv64, 1),
            (BinaryFormat::Elf, Architecture::Riscv64, 4),
            (BinaryFormat::Elf, Architecture::Riscv32, 0),
            (BinaryFormat::Elf, Architecture::X86_64, 0),
            (BinaryFormat::Coff, Architecture::X86_64, 0),
        ] {
            let mut object = Object::new(format, architecture, Endianness::Little);
            if format == BinaryFormat::Elf {
                object.flags = FileFlags::Elf {
                    os_abi: 0,
                    abi_version: 0,
                    e_flags: flags,
                };
            }
            let bytes = object.write().unwrap();
            assert_eq!(
                read_rv64_elf(&bytes).is_ok(),
                format == BinaryFormat::Elf && architecture == Architecture::Riscv64 && flags == 0
            );
        }
        assert!(read_rv64_elf(b"not an object").is_err());
    }

    #[test]
    fn rejects_missing_duplicate_main_and_inline_addresses_before_linking() {
        // All cases fail preflight: no toolchain or subprocess is needed.
        let runtime = Sp1Runtime {
            toolchain: Sp1Toolchain {
                rustc: PathBuf::new(),
                linker: PathBuf::new(),
            },
            directory: tempfile::tempdir().unwrap(),
            archive: PathBuf::new(),
        };
        let mut object = Object::new(BinaryFormat::Elf, Architecture::Riscv64, Endianness::Little);
        let section = object.add_section(Vec::new(), b".text".to_vec(), SectionKind::Text);
        object.append_section_data(section, &[0; 8], 4);
        let no_main = object.write().unwrap();
        let main = object.add_symbol(Symbol {
            name: b"main".to_vec(),
            value: 0,
            size: 8,
            kind: SymbolKind::Text,
            scope: SymbolScope::Linkage,
            weak: false,
            section: SymbolSection::Section(section),
            flags: SymbolFlags::None,
        });
        let valid = object.write().unwrap();
        object
            .add_relocation(
                section,
                Relocation {
                    offset: 0,
                    symbol: main,
                    addend: 0,
                    flags: RelocationFlags::Elf {
                        r_type: object::elf::R_RISCV_64,
                    },
                },
            )
            .unwrap();
        let literal = object.write().unwrap();
        for objects in [
            &[][..],
            &[no_main.as_slice()][..],
            &[valid.as_slice(), valid.as_slice()][..],
            &[literal.as_slice()][..],
        ] {
            assert!(matches!(
                runtime.link_objects(objects),
                Err(Sp1Error::Artifact(_))
            ));
        }
    }
}
