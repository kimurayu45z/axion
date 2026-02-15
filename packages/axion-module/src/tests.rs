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
            "import pkg.math.add\n\nfn main()\n    add(1, 2)\n",
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
            "import pkg.shapes.Point\n\nfn make() -> Point\n    Point #{x: 1.0, y: 2.0}\n",
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
            "import pkg.color.Color\n\nfn main()\n    let c: Color = 0\n",
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
            "import pkg.math.{add, sub}\n\nfn main()\n    add(1, 2)\n    sub(3, 1)\n",
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
            "import pkg.b.bar\n\npub fn foo() -> i64\n    42\n",
        ),
        (
            "b.ax",
            "import pkg.a.foo\n\npub fn bar() -> i64\n    42\n",
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
            "import pkg.math.secret\n\nfn main()\n    secret()\n",
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
            "import pkg.nonexistent.foo\n\nfn main()\n    foo()\n",
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
            "import pkg.math.multiply\n\nfn main()\n    multiply(1, 2)\n",
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
            "import pkg.math.add\n\nfn main()\n    let result: i64 = add(1, 2)\n    result\n",
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
            "import pkg.core.base\n\npub fn middle() -> i64\n    base()\n",
        ),
        (
            "main.ax",
            "import pkg.mid.middle\n\nfn main()\n    middle()\n",
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
            "import pkg.util.greet\n\nfn main()\n    let s: String = greet()\n",
        ),
    ]);
    let errs = errors(&output.diagnostics);
    assert!(errs.is_empty(), "expected no errors, got: {errs:?}");
}

// -----------------------------------------------------------------------
// std import: use std.math.min
// -----------------------------------------------------------------------

#[test]
fn std_import_math_min() {
    let output = compile_sources_with_prelude(&[(
        "main.ax",
        "import std.math.min\n\nfn main() -> i64\n    min[i64](1, 2)\n",
    )]);
    let errs = errors(&output.diagnostics);
    assert!(errs.is_empty(), "expected no errors, got: {errs:?}");
}

// -----------------------------------------------------------------------
// std import: use std.option.Option
// -----------------------------------------------------------------------

#[test]
fn std_import_option() {
    let output = compile_sources_with_prelude(&[(
        "main.ax",
        "import std.option.Option\n\nfn main()\n    let x: Option[i64] = None\n",
    )]);
    let module_errors: Vec<_> = errors(&output.diagnostics)
        .into_iter()
        .filter(|d| d.code.starts_with("E06"))
        .collect();
    assert!(module_errors.is_empty(), "expected no module errors, got: {module_errors:?}");
}

// -----------------------------------------------------------------------
// std import: grouped use std.math.{min, max}
// -----------------------------------------------------------------------

#[test]
fn std_import_grouped() {
    let output = compile_sources_with_prelude(&[(
        "main.ax",
        "import std.math.{min, max}\n\nfn main() -> i64\n    min[i64](1, max[i64](2, 3))\n",
    )]);
    let errs = errors(&output.diagnostics);
    assert!(errs.is_empty(), "expected no errors, got: {errs:?}");
}

// -----------------------------------------------------------------------
// std import: nonexistent symbol → E0603
// -----------------------------------------------------------------------

#[test]
fn std_import_nonexistent_symbol() {
    let output = compile_sources_with_prelude(&[(
        "main.ax",
        "import std.math.nonexistent\n\nfn main()\n    nonexistent()\n",
    )]);
    let errs = errors(&output.diagnostics);
    assert!(
        errs.iter().any(|d| d.code == "E0603"),
        "expected E0603 unresolved_import, got: {errs:?}"
    );
}

// -----------------------------------------------------------------------
// std import: nonexistent std module → E0600
// -----------------------------------------------------------------------

#[test]
fn std_import_nonexistent_module() {
    let output = compile_sources_with_prelude(&[(
        "main.ax",
        "import std.nonexistent.foo\n\nfn main()\n    foo()\n",
    )]);
    let errs = errors(&output.diagnostics);
    assert!(
        errs.iter().any(|d| d.code == "E0600"),
        "expected E0600 unresolved_module, got: {errs:?}"
    );
}

// -----------------------------------------------------------------------
// std.collection imports
// -----------------------------------------------------------------------

#[test]
fn std_import_collection_hashmap() {
    let output = compile_sources_with_prelude(&[(
        "main.ax",
        "import std.collection.HashMap\n\nfn main()\n    let m = HashMap[i64, i64].new()\n",
    )]);
    let errs = errors(&output.diagnostics);
    assert!(errs.is_empty(), "expected no errors, got: {errs:?}");
}

#[test]
fn std_import_collection_grouped() {
    let output = compile_sources_with_prelude(&[(
        "main.ax",
        "import std.collection.{HashMap, HashSet}\n\nfn main()\n    let m = HashMap[i64, i64].new()\n    let s = HashSet[i64].new()\n",
    )]);
    let errs = errors(&output.diagnostics);
    assert!(errs.is_empty(), "expected no errors, got: {errs:?}");
}

// -----------------------------------------------------------------------
// Export re-export: A exports imported symbol, B imports from A
// -----------------------------------------------------------------------

#[test]
fn export_reexport_function() {
    let output = compile_sources(&[
        (
            "core.ax",
            "pub fn base() -> i64\n    42\n",
        ),
        (
            "facade.ax",
            "import pkg.core.base\nexport base\n",
        ),
        (
            "main.ax",
            "import pkg.facade.base\n\nfn main() -> i64\n    base()\n",
        ),
    ]);
    let errs = errors(&output.diagnostics);
    assert!(errs.is_empty(), "expected no errors, got: {errs:?}");
}

#[test]
fn export_reexport_grouped() {
    let output = compile_sources(&[
        (
            "math.ax",
            "pub fn add(a: i64, b: i64) -> i64\n    a + b\n\npub fn sub(a: i64, b: i64) -> i64\n    a - b\n",
        ),
        (
            "facade.ax",
            "import pkg.math.{add, sub}\nexport {add, sub}\n",
        ),
        (
            "main.ax",
            "import pkg.facade.{add, sub}\n\nfn main() -> i64\n    add(1, sub(3, 1))\n",
        ),
    ]);
    let errs = errors(&output.diagnostics);
    assert!(errs.is_empty(), "expected no errors, got: {errs:?}");
}

#[test]
fn export_without_import_error() {
    let output = compile_sources(&[
        (
            "facade.ax",
            "export nonexistent\n",
        ),
    ]);
    let errs = errors(&output.diagnostics);
    assert!(
        errs.iter().any(|d| d.code == "E0605"),
        "expected E0605 invalid_export, got: {errs:?}"
    );
}
