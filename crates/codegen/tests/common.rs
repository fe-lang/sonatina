use std::io::Write;

use sonatina_parser::ParsedModule;

pub fn parse_module(file_path: &str) -> ParsedModule {
    let content = std::fs::read_to_string(file_path).unwrap();

    match sonatina_parser::parse_module(&content) {
        Ok(r) => r,
        Err(errs) => {
            let mut v: Vec<u8> = Vec::new();
            for err in errs {
                err.print(&mut v, file_path, &content, false).unwrap();
                writeln!(&mut v).unwrap();
            }
            let err_str = String::from_utf8(v).unwrap();

            panic!("{err_str}");
        }
    }
}
