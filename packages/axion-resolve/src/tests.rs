use axion_diagnostics::Severity;
use axion_parser::parse;

use crate::builtins::primitive_type_names;
use crate::def_id::SymbolKind;
use crate::resolve_single;

/// Helper: parse + resolve, return diagnostics.
fn resolve_source(src: &str) -> (crate::ResolveOutput, Vec<axion_diagnostics::Diagnostic>) {
    let (ast, parse_diags) = parse(src, "test.ax");
    assert!(parse_diags.is_empty(), "parse errors: {parse_diags:?}");
    resolve_single(&ast, "test.ax", src)
}

/// Helper: collect only errors (not warnings).
fn errors(diags: &[axion_diagnostics::Diagnostic]) -> Vec<&axion_diagnostics::Diagnostic> {
    diags.iter().filter(|d| d.severity == Severity::Error).collect()
}

/// Helper: collect only warnings.
fn warnings(diags: &[axion_diagnostics::Diagnostic]) -> Vec<&axion_diagnostics::Diagnostic> {
    diags.iter().filter(|d| d.severity == Severity::Warning).collect()
}

// -----------------------------------------------------------------------
// Builtins
// -----------------------------------------------------------------------

#[test]
fn builtins_primitive_types_registered() {
    let (output, diags) = resolve_source("fn main()\n    42\n");
    assert!(errors(&diags).is_empty(), "errors: {diags:?}");
    // All primitive types should be resolvable (registered in type NS).
    for &prim in primitive_type_names() {
        let found = output.symbols.iter().any(|s| s.name == prim);
        assert!(found, "primitive type '{prim}' not found in symbols");
    }
}

#[test]
fn builtins_prelude_functions() {
    let src = "fn main()\n    println(42)\n";
    let (_, diags) = resolve_source(src);
    // `println` should be recognized without error.
    assert!(errors(&diags).is_empty(), "errors: {diags:?}");
}

// -----------------------------------------------------------------------
// Pass 1: Collector — duplicate detection
// -----------------------------------------------------------------------

#[test]
fn duplicate_function() {
    let src = "fn foo()\n    42\n\nfn foo()\n    43\n";
    let (_, diags) = resolve_source(src);
    let errs = errors(&diags);
    assert_eq!(errs.len(), 1);
    assert_eq!(errs[0].code, "E0100");
    assert!(errs[0].message.contains("foo"));
}

#[test]
fn duplicate_struct() {
    let src = "struct Foo\n    x: i64\n\nstruct Foo\n    y: i64\n";
    let (_, diags) = resolve_source(src);
    let errs = errors(&diags);
    assert_eq!(errs.len(), 1);
    assert_eq!(errs[0].code, "E0100");
}

#[test]
fn no_duplicate_different_ns() {
    // A function and a struct can share the same name (different namespaces).
    let src = "struct Foo\n    x: i64\n\nfn foo()\n    42\n";
    let (_, diags) = resolve_source(src);
    assert!(errors(&diags).is_empty(), "errors: {diags:?}");
}

#[test]
fn collector_enum_variants() {
    let src = "\
enum Shape
    Circle(radius: f64)
    Rect(w: f64, h: f64)
";
    let (output, diags) = resolve_source(src);
    assert!(errors(&diags).is_empty(), "errors: {diags:?}");
    let variants: Vec<_> = output.symbols.iter()
        .filter(|s| s.kind == SymbolKind::EnumVariant)
        .collect();
    assert_eq!(variants.len(), 2);
    assert!(variants.iter().any(|s| s.name == "Circle"));
    assert!(variants.iter().any(|s| s.name == "Rect"));
}

// -----------------------------------------------------------------------
// Pass 2: Resolver — expression resolution
// -----------------------------------------------------------------------

#[test]
fn resolve_ident_reference() {
    let src = "fn main()\n    let x = 1\n    x\n";
    let (output, diags) = resolve_source(src);
    assert!(errors(&diags).is_empty(), "errors: {diags:?}");
    // There should be a resolution for the `x` reference.
    assert!(!output.resolutions.is_empty());
}

#[test]
fn undefined_variable() {
    let src = "fn main()\n    y\n";
    let (_, diags) = resolve_source(src);
    let errs = errors(&diags);
    assert_eq!(errs.len(), 1);
    assert_eq!(errs[0].code, "E0102");
    assert!(errs[0].message.contains("'y'"));
}

#[test]
fn resolve_function_call() {
    let src = "\
fn add(a: i64, b: i64) -> i64
    a + b

fn main()
    add(1, 2)
";
    let (_, diags) = resolve_source(src);
    assert!(errors(&diags).is_empty(), "errors: {diags:?}");
}

#[test]
fn resolve_forward_reference() {
    // `main` calls `helper` which is defined later.
    let src = "\
fn main()
    helper()

fn helper()
    42
";
    let (_, diags) = resolve_source(src);
    assert!(errors(&diags).is_empty(), "errors: {diags:?}");
}

#[test]
fn resolve_closure() {
    let src = "\
fn main()
    let f = |x: i64| x + 1
    f(10)
";
    let (_, diags) = resolve_source(src);
    assert!(errors(&diags).is_empty(), "errors: {diags:?}");
}

#[test]
fn resolve_for_loop() {
    let src = "\
fn main()
    let items = 0..10
    for i in items
        i
";
    let (_, diags) = resolve_source(src);
    assert!(errors(&diags).is_empty(), "errors: {diags:?}");
}

#[test]
fn resolve_match_arms() {
    let src = "\
fn main()
    let x = 1
    match x
        0 =>
            0
        n =>
            n + 1
";
    let (_, diags) = resolve_source(src);
    assert!(errors(&diags).is_empty(), "errors: {diags:?}");
}

#[test]
fn resolve_if_else() {
    let src = "\
fn main()
    let x = true
    if x
        1
    else
        2
";
    let (_, diags) = resolve_source(src);
    assert!(errors(&diags).is_empty(), "errors: {diags:?}");
}

#[test]
fn resolve_while_loop() {
    let src = "\
fn main()
    let x = true
    while x
        42
";
    let (_, diags) = resolve_source(src);
    assert!(errors(&diags).is_empty(), "errors: {diags:?}");
}

// -----------------------------------------------------------------------
// Pass 2: Resolver — type resolution
// -----------------------------------------------------------------------

#[test]
fn resolve_named_type() {
    let src = "\
struct Point
    x: f64
    y: f64

fn origin() -> Point
    let p = 0.0
    p
";
    let (_, diags) = resolve_source(src);
    assert!(errors(&diags).is_empty(), "errors: {diags:?}");
}

#[test]
fn undefined_type() {
    let src = "fn main(x: Unknown)\n    x\n";
    let (_, diags) = resolve_source(src);
    let errs = errors(&diags);
    assert_eq!(errs.len(), 1);
    assert_eq!(errs[0].code, "E0103");
    assert!(errs[0].message.contains("'Unknown'"));
}

#[test]
fn resolve_generic_type_param() {
    let src = "\
fn identity[T](x: T) -> T
    x
";
    let (_, diags) = resolve_source(src);
    assert!(errors(&diags).is_empty(), "errors: {diags:?}");
}

#[test]
fn resolve_fn_type() {
    let src = "\
fn apply(f: Fn(i64) -> i64, x: i64) -> i64
    f(x)
";
    let (_, diags) = resolve_source(src);
    assert!(errors(&diags).is_empty(), "errors: {diags:?}");
}

#[test]
fn resolve_interface_bound() {
    let src = "\
interface Show
    fn show() -> str

fn display[T: Show](x: T) -> str
    42
";
    let (_, diags) = resolve_source(src);
    assert!(errors(&diags).is_empty(), "errors: {diags:?}");
}

#[test]
fn not_an_interface_error() {
    let src = "\
struct Foo
    x: i64

fn display[T: Foo](x: T) -> str
    42
";
    let (_, diags) = resolve_source(src);
    let errs = errors(&diags);
    assert_eq!(errs.len(), 1);
    assert_eq!(errs[0].code, "E0104");
    assert!(errs[0].message.contains("Foo"));
}

#[test]
fn resolve_ref_and_slice_types() {
    let src = "\
fn borrow(x: &str) -> &str
    x
";
    let (_, diags) = resolve_source(src);
    assert!(errors(&diags).is_empty(), "errors: {diags:?}");
}

// -----------------------------------------------------------------------
// Pass 2: Resolver — patterns
// -----------------------------------------------------------------------

#[test]
fn resolve_constructor_pattern() {
    let src = "\
enum Shape
    Circle(radius: f64)
    Point

fn main()
    let s = 0
    match s
        0 =>
            0
        _ =>
            1
";
    let (_, diags) = resolve_source(src);
    assert!(errors(&diags).is_empty(), "errors: {diags:?}");
}

#[test]
fn resolve_struct_pattern() {
    let src = "\
struct Point
    x: f64
    y: f64

fn main()
    let p = 0
    p
";
    let (_, diags) = resolve_source(src);
    assert!(errors(&diags).is_empty(), "errors: {diags:?}");
}

// -----------------------------------------------------------------------
// Special items: method self/Self, constructor Self, extern, test
// -----------------------------------------------------------------------

#[test]
fn resolve_method_self_and_upper_self() {
    let src = "\
struct Point
    x: f64
    y: f64

impl Point
    fn get_x(self) -> f64
        self.x
";
    let (_, diags) = resolve_source(src);
    assert!(errors(&diags).is_empty(), "errors: {diags:?}");
}

#[test]
fn resolve_constructor_self() {
    let src = "\
struct Point
    x: f64
    y: f64

fn Point.origin() -> Self
    Self #{x: 0.0, y: 0.0}
";
    let (_, diags) = resolve_source(src);
    assert!(errors(&diags).is_empty(), "errors: {diags:?}");
}

#[test]
fn resolve_extern_fn() {
    let src = "\
extern \"C\"
    fn puts(s: &str) -> i64

fn main()
    puts(&\"hello\")
";
    let (_, diags) = resolve_source(src);
    assert!(errors(&diags).is_empty(), "errors: {diags:?}");
}

#[test]
fn self_outside_method_error() {
    let src = "fn main()\n    self\n";
    let (_, diags) = resolve_source(src);
    let errs = errors(&diags);
    assert_eq!(errs.len(), 1);
    assert_eq!(errs[0].code, "E0106");
}

// -----------------------------------------------------------------------
// Post-pass: unused variable warning
// -----------------------------------------------------------------------

#[test]
fn unused_variable_warning() {
    let src = "\
fn main()
    let x = 42
    0
";
    let (_, diags) = resolve_source(src);
    assert!(errors(&diags).is_empty());
    let warns = warnings(&diags);
    assert_eq!(warns.len(), 1);
    assert_eq!(warns[0].code, "W0001");
    assert!(warns[0].message.contains("'x'"));
}

#[test]
fn underscore_variable_no_warning() {
    let src = "\
fn main()
    let _x = 42
    0
";
    let (_, diags) = resolve_source(src);
    let warns = warnings(&diags);
    assert!(warns.is_empty(), "got warnings: {warns:?}");
}

#[test]
fn used_variable_no_warning() {
    let src = "\
fn main()
    let x = 42
    x
";
    let (_, diags) = resolve_source(src);
    let warns = warnings(&diags);
    assert!(warns.is_empty(), "got warnings: {warns:?}");
}

// -----------------------------------------------------------------------
// Integration: the example from the spec
// -----------------------------------------------------------------------

#[test]
fn integration_full_example() {
    let src = "\
struct Point
    x: f64
    y: f64

fn Point.origin() -> Self
    Self #{x: 0.0, y: 0.0}

impl Point
    fn distance(self, other: Point) -> f64
        self.x

fn identity[T](x: T) -> T
    x

fn main()
    let p = Point.origin()
    let d = p.distance(Point.origin())
    let x = identity[i64](42)
    x
";
    let (output, diags) = resolve_source(src);
    // There should be no errors.
    let errs = errors(&diags);
    assert!(errs.is_empty(), "errors: {errs:?}");

    // `p` is used in `p.distance(...)`, `d` is unused, `x` is used at the end.
    let warns = warnings(&diags);
    let warn_names: Vec<_> = warns.iter().map(|w| &w.message).collect();
    assert!(warn_names.iter().any(|m| m.contains("'d'")), "expected unused warning for 'd', got: {warn_names:?}");
    assert!(!warn_names.iter().any(|m| m.contains("'p'")), "'p' should not be unused — it's used in p.distance()");
    assert!(!warn_names.iter().any(|m| m.contains("'x'")), "'x' should not be unused — it's the return value");

    // The struct `Point` should be registered.
    assert!(output.symbols.iter().any(|s| s.name == "Point" && s.kind == SymbolKind::Struct));

    // The constructor `Point.origin` should be registered.
    assert!(output.symbols.iter().any(|s| s.name == "Point.origin" && s.kind == SymbolKind::Constructor));

    // The method `Point.distance` should be registered.
    assert!(output.symbols.iter().any(|s| s.name == "Point.distance" && s.kind == SymbolKind::Method));

    // The generic function `identity` should be registered.
    assert!(output.symbols.iter().any(|s| s.name == "identity" && s.kind == SymbolKind::Function));
}

// -----------------------------------------------------------------------
// Resolution map
// -----------------------------------------------------------------------

#[test]
fn resolution_map_populated() {
    let src = "\
fn main()
    let x = 42
    x + 1
";
    let (output, diags) = resolve_source(src);
    assert!(errors(&diags).is_empty(), "errors: {diags:?}");
    // The reference to `x` on line 3 should produce a resolution entry.
    assert!(!output.resolutions.is_empty(), "expected resolution entries");
}
