use std::process::Command;
use std::sync::atomic::{AtomicU32, Ordering};

use axion_parser;
use axion_resolve;
use axion_types;
use axion_types::unify::UnifyContext;

use crate::compile_to_ir;
use crate::compile_to_object;

static TEST_COUNTER: AtomicU32 = AtomicU32::new(0);

struct RunResult {
    exit_code: i32,
    stdout: String,
}

fn compile_and_run(src: &str) -> RunResult {
    let (sf, parse_diags) = axion_parser::parse(src, "test.ax");
    assert!(parse_diags.is_empty(), "Parse errors: {:?}", parse_diags);

    let (resolved, diags) = axion_resolve::resolve_single(&sf, "test.ax", src);
    assert!(diags.is_empty(), "Resolve errors: {:?}", diags);

    let (type_out, diags) = axion_types::type_check(&sf, &resolved, "test.ax", src);
    assert!(diags.is_empty(), "Type check errors: {:?}", diags);

    let mut unify = UnifyContext::new();
    let type_env = axion_types::env::TypeEnv::build(&sf, &resolved, &mut unify);

    let obj_bytes =
        compile_to_object(&sf, &resolved, &type_out, &type_env, "test").expect("Compilation failed");

    // Use unique filenames per test to avoid race conditions.
    let id = TEST_COUNTER.fetch_add(1, Ordering::SeqCst);
    let dir = std::env::temp_dir().join("axion_test");
    std::fs::create_dir_all(&dir).unwrap();
    let obj_path = dir.join(format!("test_{}.o", id));
    let exe_path = dir.join(format!("test_exe_{}", id));

    std::fs::write(&obj_path, &obj_bytes).unwrap();

    // Link.
    let link_status = Command::new("cc")
        .arg(obj_path.to_str().unwrap())
        .arg("-o")
        .arg(exe_path.to_str().unwrap())
        .status()
        .expect("Failed to run linker");
    assert!(link_status.success(), "Linking failed");

    // Run.
    let output = Command::new(exe_path.to_str().unwrap())
        .output()
        .expect("Failed to run executable");

    // Clean up.
    let _ = std::fs::remove_file(&obj_path);
    let _ = std::fs::remove_file(&exe_path);

    let exit_code = output.status.code().unwrap_or(-1);
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();

    RunResult { exit_code, stdout }
}

#[allow(dead_code)]
fn compile_ir(src: &str) -> String {
    let (sf, _) = axion_parser::parse(src, "test.ax");
    let (resolved, _) = axion_resolve::resolve_single(&sf, "test.ax", src);
    let (type_out, _) = axion_types::type_check(&sf, &resolved, "test.ax", src);
    let mut unify = UnifyContext::new();
    let type_env = axion_types::env::TypeEnv::build(&sf, &resolved, &mut unify);
    compile_to_ir(&sf, &resolved, &type_out, &type_env, "test")
}

#[test]
fn compile_empty_main() {
    let result = compile_and_run("fn main()\n    0\n");
    assert_eq!(result.exit_code, 0);
}

#[test]
fn compile_int_return() {
    let result = compile_and_run("fn main() -> i64\n    42\n");
    assert_eq!(result.exit_code, 42);
}

#[test]
fn compile_arithmetic() {
    let result = compile_and_run("fn main() -> i64\n    2 + 3 * 4\n");
    assert_eq!(result.exit_code, 14);
}

#[test]
fn compile_let_binding() {
    let src = "\
fn main() -> i64
    let x = 10
    x + 5
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 15);
}

#[test]
fn compile_function_call() {
    let src = "\
fn add(a: i64, b: i64) -> i64
    a + b

fn main() -> i64
    add(20, 22)
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 42);
}

#[test]
fn compile_if_else() {
    let src = "\
fn main() -> i64
    if true
        1
    else
        2
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 1);
}

#[test]
fn compile_while_loop() {
    let src = "\
fn main() -> i64
    let mut sum: i64 = 0
    let mut i: i64 = 1
    while i <= 10
        sum = sum + i
        i = i + 1
    sum
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 55);
}

#[test]
fn compile_struct_field() {
    let src = "\
struct Point
    x: i64
    y: i64

fn main() -> i64
    let p = Point #{x: 7, y: 3}
    p.x + p.y
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 10);
}

#[test]
fn compile_println() {
    let src = "\
fn main()
    println(\"hello\")
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 0);
    assert_eq!(result.stdout.trim(), "hello");
}

#[test]
fn compile_comparison() {
    let src = "\
fn check(a: i64, b: i64) -> i64
    if a == b
        1
    else
        0

fn main() -> i64
    check(5, 5)
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 1);
}
