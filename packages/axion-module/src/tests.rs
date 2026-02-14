use axion_diagnostics::Severity;

use crate::{compile_sources, compile_sources_with_prelude};

fn errors(diags: &[axion_diagnostics::Diagnostic]) -> Vec<&axion_diagnostics::Diagnostic> {
    diags.iter().filter(|d| d.severity == Severity::Error).collect()
}

// -----------------------------------------------------------------------
// Basic cross-file import
// -----------------------------------------------------------------------

#[test]
fn basic_cross_file_import() {
    let output = compile_sources(&[
        (
            "math.ax",
            "pub fn add(a: i64, b: i64) -> i64\n    a + b\n",
        ),
        (
            "main.ax",
            "use pkg.math.add\n\nfn main()\n    add(1, 2)\n",
        ),
    ]);
    let errs = errors(&output.diagnostics);
    assert!(errs.is_empty(), "expected no errors, got: {errs:?}");
}

// -----------------------------------------------------------------------
// Import struct type
// -----------------------------------------------------------------------

#[test]
fn import_struct_type() {
    let output = compile_sources(&[
        (
            "shapes.ax",
            "pub struct Point\n    pub x: f64\n    pub y: f64\n",
        ),
        (
            "main.ax",
            "use pkg.shapes.Point\n\nfn make() -> Point\n    Point #{x: 1.0, y: 2.0}\n",
        ),
    ]);
    let errs = errors(&output.diagnostics);
    assert!(errs.is_empty(), "expected no errors, got: {errs:?}");
}

// -----------------------------------------------------------------------
// Import enum type
// -----------------------------------------------------------------------

#[test]
fn import_enum_type() {
    let output = compile_sources(&[
        (
            "color.ax",
            "pub enum Color\n    Red\n    Green\n    Blue\n",
        ),
        (
            "main.ax",
            "use pkg.color.Color\n\nfn main()\n    let c: Color = 0\n",
        ),
    ]);
    // This will produce a type error (i64 != Color), but no module/import errors.
    let module_errors: Vec<_> = errors(&output.diagnostics)
        .into_iter()
        .filter(|d| d.code.starts_with("E06"))
        .collect();
    assert!(module_errors.is_empty(), "expected no module errors, got: {module_errors:?}");
}

// -----------------------------------------------------------------------
// Grouped import
// -----------------------------------------------------------------------

#[test]
fn grouped_import() {
    let output = compile_sources(&[
        (
            "math.ax",
            "pub fn add(a: i64, b: i64) -> i64\n    a + b\n\npub fn sub(a: i64, b: i64) -> i64\n    a - b\n",
        ),
        (
            "main.ax",
            "use pkg.math.{add, sub}\n\nfn main()\n    add(1, 2)\n    sub(3, 1)\n",
        ),
    ]);
    let errs = errors(&output.diagnostics);
    assert!(errs.is_empty(), "expected no errors, got: {errs:?}");
}

// -----------------------------------------------------------------------
// Circular import detected
// -----------------------------------------------------------------------

#[test]
fn circular_import_detected() {
    let output = compile_sources(&[
        (
            "a.ax",
            "use pkg.b.bar\n\npub fn foo() -> i64\n    42\n",
        ),
        (
            "b.ax",
            "use pkg.a.foo\n\npub fn bar() -> i64\n    42\n",
        ),
    ]);
    let errs = errors(&output.diagnostics);
    assert!(!errs.is_empty(), "expected cycle error");
    assert!(
        errs.iter().any(|d| d.code == "E0601"),
        "expected E0601 circular_import, got: {errs:?}"
    );
}

// -----------------------------------------------------------------------
// Private not importable
// -----------------------------------------------------------------------

#[test]
fn private_not_importable() {
    let output = compile_sources(&[
        (
            "math.ax",
            "fn secret() -> i64\n    42\n",
        ),
        (
            "main.ax",
            "use pkg.math.secret\n\nfn main()\n    secret()\n",
        ),
    ]);
    let errs = errors(&output.diagnostics);
    assert!(
        errs.iter().any(|d| d.code == "E0602"),
        "expected E0602 private_import, got: {errs:?}"
    );
}

// -----------------------------------------------------------------------
// Unresolved module
// -----------------------------------------------------------------------

#[test]
fn unresolved_module() {
    let output = compile_sources(&[
        (
            "main.ax",
            "use pkg.nonexistent.foo\n\nfn main()\n    foo()\n",
        ),
    ]);
    let errs = errors(&output.diagnostics);
    assert!(
        errs.iter().any(|d| d.code == "E0600"),
        "expected E0600 unresolved_module, got: {errs:?}"
    );
}

// -----------------------------------------------------------------------
// Unresolved name in valid module
// -----------------------------------------------------------------------

#[test]
fn unresolved_name() {
    let output = compile_sources(&[
        (
            "math.ax",
            "pub fn add(a: i64, b: i64) -> i64\n    a + b\n",
        ),
        (
            "main.ax",
            "use pkg.math.multiply\n\nfn main()\n    multiply(1, 2)\n",
        ),
    ]);
    let errs = errors(&output.diagnostics);
    assert!(
        errs.iter().any(|d| d.code == "E0603"),
        "expected E0603 unresolved_import, got: {errs:?}"
    );
}

// -----------------------------------------------------------------------
// Cross-file type check
// -----------------------------------------------------------------------

#[test]
fn cross_file_type_check() {
    let output = compile_sources(&[
        (
            "math.ax",
            "pub fn add(a: i64, b: i64) -> i64\n    a + b\n",
        ),
        (
            "main.ax",
            "use pkg.math.add\n\nfn main()\n    let result: i64 = add(1, 2)\n    result\n",
        ),
    ]);
    let errs = errors(&output.diagnostics);
    assert!(errs.is_empty(), "expected no errors, got: {errs:?}");
}

// -----------------------------------------------------------------------
// Multi-level import (A → B → C chain)
// -----------------------------------------------------------------------

#[test]
fn multi_level_import() {
    let output = compile_sources(&[
        (
            "core.ax",
            "pub fn base() -> i64\n    1\n",
        ),
        (
            "mid.ax",
            "use pkg.core.base\n\npub fn middle() -> i64\n    base()\n",
        ),
        (
            "main.ax",
            "use pkg.mid.middle\n\nfn main()\n    middle()\n",
        ),
    ]);
    let errs = errors(&output.diagnostics);
    assert!(errs.is_empty(), "expected no errors, got: {errs:?}");
}

// -----------------------------------------------------------------------
// Cross-file with prelude: String type shared across modules
// -----------------------------------------------------------------------

#[test]
fn cross_file_with_prelude_string() {
    let output = compile_sources_with_prelude(&[
        ("util.ax", "pub fn greet() -> String\n    \"hello\"\n"),
        (
            "main.ax",
            "use pkg.util.greet\n\nfn main()\n    let s: String = greet()\n",
        ),
    ]);
    let errs = errors(&output.diagnostics);
    assert!(errs.is_empty(), "expected no errors, got: {errs:?}");
}
