use std::{env, fs, process};

use sonatina_parser::parse_module;
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

fn main() {
    let mut args = env::args().skip(1);
    let mut input_path = None;
    let mut level = VerificationLevel::Full;

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--level" => {
                let Some(value) = args.next() else {
                    eprintln!("error: --level requires one of: fast, standard, full");
                    process::exit(2);
                };

                level = match value.as_str() {
                    "fast" => VerificationLevel::Fast,
                    "standard" => VerificationLevel::Standard,
                    "full" => VerificationLevel::Full,
                    _ => {
                        eprintln!("error: unknown verification level `{value}`");
                        process::exit(2);
                    }
                };
            }
            "--help" | "-h" => {
                print_help();
                return;
            }
            other if other.starts_with('-') => {
                eprintln!("error: unknown flag `{other}`");
                process::exit(2);
            }
            path => {
                if input_path.replace(path.to_string()).is_some() {
                    eprintln!("error: expected exactly one input file path");
                    process::exit(2);
                }
            }
        }
    }

    let Some(path) = input_path else {
        print_help();
        process::exit(2);
    };

    let source = match fs::read_to_string(&path) {
        Ok(source) => source,
        Err(err) => {
            eprintln!("error: failed to read `{path}`: {err}");
            process::exit(2);
        }
    };

    let parsed = match parse_module(&source) {
        Ok(parsed) => parsed,
        Err(errors) => {
            eprintln!("parse failed:");
            for error in errors {
                eprintln!("  {error:?}");
            }
            process::exit(1);
        }
    };

    let cfg = VerifierConfig::for_level(level);
    let report = verify_module(&parsed.module, &cfg);

    println!("{report}");

    process::exit(if report.has_errors() { 1 } else { 0 });
}

fn print_help() {
    println!(
        "Usage: sonatina-verify <file> [--level fast|standard|full]\n\
         Verifies Sonatina IR and exits non-zero when verification errors are found."
    );
}
