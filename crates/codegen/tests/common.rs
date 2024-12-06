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

// copied from fe test-utils
/// A macro to assert that a value matches a snapshot.
/// If the snapshot does not exist, it will be created in the same directory as
/// the test file.
#[macro_export]
macro_rules! snap_test {
    ($value:expr, $fixture_path: expr) => {
        snap_test!($value, $fixture_path, None)
    };

    ($value:expr, $fixture_path: expr, $suffix: expr) => {
        let mut settings = insta::Settings::new();
        let fixture_path = ::std::path::Path::new($fixture_path);
        let fixture_dir = fixture_path.parent().unwrap();
        let fixture_name = fixture_path.file_stem().unwrap().to_str().unwrap();

        settings.set_snapshot_path(fixture_dir);
        settings.set_input_file($fixture_path);
        settings.set_prepend_module_to_snapshot(false);
        settings.set_omit_expression(true);

        let suffix: Option<&str> = $suffix;
        let name = if let Some(suffix) = suffix {
            format!("{fixture_name}.{suffix}")
        } else {
            fixture_name.into()
        };
        settings.bind(|| {
            insta::_macro_support::assert_snapshot(
                (name, $value.as_str()).into(),
                std::path::Path::new(env!("CARGO_MANIFEST_DIR")),
                fixture_name,
                module_path!(),
                file!(),
                line!(),
                &$value,
            )
            .unwrap()
        })
    };
}
