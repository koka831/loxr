use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn buf_to_string(buf: Vec<u8>) -> String {
    String::from_utf8(buf).unwrap()
}

fn print_output(output: Output) {
    eprintln!("info: [stdout]\n{}", buf_to_string(output.stdout));
    eprintln!("info: [stderr]\n{}", buf_to_string(output.stderr));
}

fn compile<P: AsRef<Path>>(program: &P) -> Output {
    let program = program.as_ref().display().to_string();
    match Command::new("cargo")
        .env("CLICOLOR", "0")
        .args(["run", "--quiet", "--", &program])
        .output()
    {
        Ok(output) => output,
        Err(e) => panic!("compile error occured: {e:?}"),
    }
}

fn collect_path(dir: PathBuf) -> Vec<PathBuf> {
    dir.read_dir()
        .unwrap()
        .map(|p| p.unwrap().path())
        .filter(|p| p.extension().is_some_and(|ext| ext == "lox"))
        .collect()
}

#[test]
fn ui_compile_ok() {
    let mut testcases = std::env::current_dir().unwrap();
    testcases.push("tests/ui/success");

    for entry in collect_path(testcases) {
        let output = compile(&entry);
        print_output(output.clone());
        assert!(output.status.success(), "test failed {}", entry.display());
    }
}

#[test]
fn ui_compile_warning() {
    let mut testcases = std::env::current_dir().unwrap();
    testcases.push("tests/ui/warning");

    for entry in collect_path(testcases) {
        let output = compile(&entry);
        print_output(output.clone());
        assert!(output.status.success(), "test failed {}", entry.display());
        let stderr = entry.join("stderr");
        let expected = std::fs::read_to_string(stderr).expect("could not read .stderr file");
        similar_asserts::assert_eq!(
            buf_to_string(output.stderr),
            expected,
            "{}",
            entry.display()
        );
    }
}

#[test]
fn ui_compile_err() {
    let mut testcases = std::env::current_dir().unwrap();
    testcases.push("tests/ui/error");

    for entry in collect_path(testcases) {
        dbg!(&entry);
        let output = compile(&entry);
        print_output(output.clone());
        assert!(
            !output.status.success(),
            "expected to be failed, but it succeeded: {}",
            entry.display()
        );

        let stderr = entry.with_extension("stderr");
        dbg!(&stderr);
        let expected = std::fs::read_to_string(stderr).expect("could not read .stderr file");
        similar_asserts::assert_eq!(
            buf_to_string(output.stderr),
            expected,
            "{}",
            entry.display()
        );
    }
}
