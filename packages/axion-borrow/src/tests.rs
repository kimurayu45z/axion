use axion_types::unify::UnifyContext;

use crate::borrow_check;

fn check(src: &str) -> Vec<axion_diagnostics::Diagnostic> {
    let (sf, parse_diags) = axion_parser::parse(src, "test.ax");
    let parse_errors: Vec<_> = parse_diags
        .iter()
        .filter(|d| d.severity == axion_diagnostics::Severity::Error)
        .collect();
    assert!(parse_errors.is_empty(), "Parse errors: {:?}", parse_errors);

    let (resolved, resolve_diags) = axion_resolve::resolve_single(&sf, "test.ax", src);
    let resolve_errors: Vec<_> = resolve_diags
        .iter()
        .filter(|d| d.severity == axion_diagnostics::Severity::Error)
        .collect();
    assert!(
        resolve_errors.is_empty(),
        "Resolve errors: {:?}",
        resolve_errors
    );

    let (type_out, type_diags) = axion_types::type_check(&sf, &resolved, "test.ax", src);
    let type_errors: Vec<_> = type_diags
        .iter()
        .filter(|d| d.severity == axion_diagnostics::Severity::Error)
        .collect();
    assert!(
        type_errors.is_empty(),
        "Type check errors: {:?}",
        type_errors
    );

    let mut unify = UnifyContext::new();
    let type_env = axion_types::env::TypeEnv::build(&sf, &resolved, &mut unify);

    borrow_check(&sf, &resolved, &type_out, &type_env, "test.ax", src)
}

fn check_no_errors(src: &str) {
    let diags = check(src);
    assert!(diags.is_empty(), "Expected no errors, got: {:?}", diags);
}

fn check_has_error(src: &str, code: &str) {
    let diags = check(src);
    assert!(
        diags.iter().any(|d| d.code == code),
        "Expected error {}, got: {:?}",
        code,
        diags
    );
}

// ===== Use after move =====

#[test]
fn use_after_move() {
    let src = "\
fn consume(move x: i64) -> i64
    x

fn main() -> i64
    let a: i64 = 10
    consume(move a)
    a
";
    check_has_error(src, "E0700");
}

// ===== Double move =====

#[test]
fn double_move() {
    let src = "\
fn consume(move x: i64) -> i64
    x

fn main()
    let a: i64 = 5
    consume(move a)
    consume(move a)
";
    check_has_error(src, "E0701");
}

// ===== Move and reassign OK =====

#[test]
fn move_and_reassign_ok() {
    let src = "\
fn consume(move x: i64) -> i64
    x

fn main() -> i64
    let mut a: i64 = 5
    consume(move a)
    a = 10
    a
";
    check_no_errors(src);
}

// ===== Borrow then use OK =====

#[test]
fn borrow_then_use_ok() {
    let src = "\
fn main() -> i64
    let x: i64 = 42
    let _y = &x
    x
";
    check_no_errors(src);
}

// ===== Move of borrowed value =====

#[test]
fn move_borrowed_value() {
    let src = "\
fn consume(move x: i64) -> i64
    x

fn main()
    let x: i64 = 10
    let _y = &x
    consume(move x)
";
    check_has_error(src, "E0704");
}

// ===== Assign to immutable =====

#[test]
fn assign_immutable() {
    let src = "\
fn main()
    let x: i64 = 10
    x = 20
";
    check_has_error(src, "E0705");
}

// ===== Assign to mutable OK =====

#[test]
fn assign_mutable_ok() {
    let src = "\
fn main() -> i64
    let mut x: i64 = 10
    x = 20
    x
";
    check_no_errors(src);
}


// ===== Borrow ends at scope =====

#[test]
fn borrow_ends_at_scope() {
    let src = "\
fn main() -> i64
    let mut x: i64 = 10
    if true
        let _y = &x
    x = 20
    x
";
    check_no_errors(src);
}

// ===== If/else both branches move =====

#[test]
fn if_else_move() {
    let src = "\
fn consume(move x: i64) -> i64
    x

fn main()
    let a: i64 = 5
    if true
        consume(move a)
    else
        consume(move a)
    a
";
    check_has_error(src, "E0700");
}

// ===== If one branch move =====

#[test]
fn if_one_branch_move() {
    let src = "\
fn consume(move x: i64) -> i64
    x

fn main()
    let a: i64 = 5
    if true
        consume(move a)
    a
";
    // Move in one branch means conditionally moved → still considered moved.
    check_has_error(src, "E0700");
}

// ===== Function param move =====

#[test]
fn function_param_move() {
    let src = "\
fn take(move x: i64) -> i64
    x

fn main() -> i64
    let a: i64 = 42
    take(move a)
";
    // This is fine — just passing by move, not using after.
    check_no_errors(src);
}

// ===== Multiple immutable borrows OK =====

#[test]
fn multiple_immutable_borrows_ok() {
    let src = "\
fn main() -> i64
    let x: i64 = 42
    let _a = &x
    let _b = &x
    x
";
    check_no_errors(src);
}

// ===== Use in closure after move =====

#[test]
fn closure_use_ok() {
    let src = "\
fn main() -> i64
    let x: i64 = 5
    let f = |a: i64| a + x
    f(10)
";
    check_no_errors(src);
}

// ===== Simple function, no issues =====

#[test]
fn simple_function_ok() {
    let src = "\
fn add(a: i64, b: i64) -> i64
    a + b

fn main() -> i64
    add(1, 2)
";
    check_no_errors(src);
}
