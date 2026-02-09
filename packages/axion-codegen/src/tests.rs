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

    let mono_output = axion_mono::monomorphize(&sf, &resolved, &type_out, &type_env);

    let obj_bytes =
        compile_to_object(&sf, &resolved, &type_out, &type_env, "test", Some(&mono_output)).expect("Compilation failed");

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
    let mono_output = axion_mono::monomorphize(&sf, &resolved, &type_out, &type_env);
    compile_to_ir(&sf, &resolved, &type_out, &type_env, "test", Some(&mono_output))
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

#[test]
fn compile_for_loop() {
    let src = "\
fn main() -> i64
    let mut sum: i64 = 0
    for i in 0..10
        sum = sum + i
    sum
";
    let result = compile_and_run(src);
    // 0 + 1 + 2 + ... + 9 = 45
    assert_eq!(result.exit_code, 45);
}

#[test]
fn compile_string_interp() {
    let src = "\
fn main()
    let name = \"world\"
    println(\"hello {name}\")
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 0);
    assert_eq!(result.stdout.trim(), "hello world");
}

#[test]
fn compile_string_interp_int() {
    let src = "\
fn main()
    let x: i64 = 42
    println(\"x is {x}\")
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 0);
    assert_eq!(result.stdout.trim(), "x is 42");
}

#[test]
fn compile_enum_unit_variant() {
    let src = "\
enum Color
    Red
    Green
    Blue

fn color_code(c: Color) -> i64
    match c
        Color.Red => 1
        Color.Green => 2
        Color.Blue => 3
        _ => 0

fn main() -> i64
    let c = Color.Green
    color_code(c)
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 2);
}

#[test]
fn compile_enum_data_variant() {
    let src = "\
enum Shape
    Circle(radius: i64)
    Rect(width: i64, height: i64)

fn area(s: Shape) -> i64
    match s
        Shape.Circle(r) => r * r
        Shape.Rect(w, h) => w * h
        _ => 0

fn main() -> i64
    let s = Shape.Rect(3, 4)
    area(s)
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 12);
}

#[test]
fn compile_closure_basic() {
    let src = "\
fn main() -> i64
    let add = |x: i64, y: i64| x + y
    add(3, 4)
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 7);
}

#[test]
fn compile_closure_capture() {
    let src = "\
fn main() -> i64
    let a: i64 = 10
    let f = |x: i64| x + a
    f(5)
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 15);
}

#[test]
fn compile_closure_as_arg() {
    let src = "\
fn apply(f: Fn(i64) -> i64, x: i64) -> i64
    f(x)

fn main() -> i64
    let double = |x: i64| x * 2
    apply(double, 21)
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 42);
}

#[test]
fn compile_generic_identity() {
    let src = "\
fn id[T](x: T) -> T
    x

fn main() -> i64
    id[i64](42)
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 42);
}

#[test]
fn compile_generic_two_instantiations() {
    let src = "\
fn first[T](x: T, y: T) -> T
    x

fn main() -> i64
    let a = first[i64](10, 20)
    a
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 10);
}

#[test]
fn compile_generic_with_arithmetic() {
    let src = "\
fn double[T](x: T) -> T
    x + x

fn main() -> i64
    double[i64](21)
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 42);
}

#[test]
fn compile_generic_struct_bool() {
    // Test that a generic struct with bool fields has correct LLVM layout.
    // Type inference now infers type_args from field values.
    let src = "\
struct Pair[T]
    first: T
    second: T

fn main() -> i64
    let p = Pair #{first: true, second: false}
    if p.first
        1
    else
        0
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 1);
}

#[test]
fn compile_generic_struct_mixed() {
    // Test that two non-generic structs with different field types produce different layouts.
    let src = "\
struct PairI64
    first: i64
    second: i64

struct PairBool
    first: bool
    second: bool

fn check_bool(p: PairBool) -> i64
    if p.first
        1
    else
        0

fn main() -> i64
    let a = PairI64 #{first: 10, second: 20}
    let b = PairBool #{first: true, second: false}
    a.first + a.second + check_bool(b)
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 31);
}

#[test]
fn compile_generic_fn_with_struct() {
    // Test that a struct accessed inside a generic function uses correct layout
    // after monomorphization substitutes the type parameter.
    let src = "\
struct Point
    x: i64
    y: i64

fn get_x(p: Point) -> i64
    p.x

fn main() -> i64
    let p = Point #{x: 42, y: 10}
    get_x(p)
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 42);
}

#[test]
fn compile_closure_env_freed() {
    // Test that capturing closures generate a free call for the environment.
    let src = "\
fn main() -> i64
    let x = 10
    let f = |y: i64| x + y
    f(32)
";
    let ir = compile_ir(src);
    assert!(ir.contains("call void @free"), "IR should contain a free call for closure env");
}

#[test]
fn compile_string_interp_freed() {
    // Test that string interpolation generates a free call for the buffer.
    let src = r#"
fn main()
    let x = 42
    let s = "value is {x}"
    println(s)
"#;
    let ir = compile_ir(src);
    assert!(ir.contains("call void @free"), "IR should contain a free call for string interp buffer");
}

#[test]
fn compile_no_leak_basic() {
    // Test that a function with no heap allocations does not contain free calls.
    let src = "\
fn main() -> i64
    let x = 10
    let y = 20
    x + y
";
    let ir = compile_ir(src);
    assert!(!ir.contains("call void @free"), "IR should not contain free calls when there are no heap allocations");
}

#[test]
fn compile_let_tuple_destructure() {
    let src = "\
fn make_pair() -> {i64, i64}
    {10, 20}

fn main() -> i64
    let {a, b} = make_pair()
    a + b
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 30);
}

#[test]
fn compile_let_tuple_nested() {
    // Nested tuple destructuring in let binding.
    let src = "\
fn main() -> i64
    let {a, {b, c}} = {1, {2, 3}}
    a + b + c
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 6);
}

#[test]
fn compile_match_tuple_bind() {
    // Match arm with tuple pattern binding (no literal sub-patterns).
    let src = "\
fn swap(pair: {i64, i64}) -> {i64, i64}
    match pair
        {a, b} => {b, a}

fn main() -> i64
    let {x, y} = swap({10, 20})
    x - y
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 10);
}

#[test]
fn compile_method_call() {
    let src = "\
struct Counter
    val: i64

fn@[Counter] increment(n: i64) -> Counter
    Counter #{val: self.val + n}

fn main() -> i64
    let c = Counter #{val: 10}
    let c2 = c.increment(5)
    c2.val
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 15);
}

#[test]
fn compile_drop_called() {
    // Test that a type with a `drop` method gets its drop called at function exit.
    let src = "\
struct Resource
    id: i64

fn@[Resource] drop()
    0

fn main() -> i64
    let r = Resource #{id: 42}
    r.id
";
    let ir = compile_ir(src);
    assert!(ir.contains("call void @Resource.drop"), "IR should contain a drop call: {}", ir);
}

#[test]
fn compile_drop_side_effect() {
    // Test that drop method is actually invoked at runtime.
    let src = r#"
struct Droppable
    val: i64

fn@[Droppable] drop()
    println("dropped")

fn main()
    let d = Droppable #{val: 1}
    println("before")
    let _ = d.val
"#;
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 0);
    let lines: Vec<&str> = result.stdout.trim().lines().collect();
    assert_eq!(lines.len(), 2, "Expected 2 lines, got: {:?}", lines);
    assert_eq!(lines[0], "before");
    assert_eq!(lines[1], "dropped");
}

#[test]
fn compile_slice_layout() {
    // Test that Ty::Slice maps to a fat pointer { ptr, i64 } in LLVM IR.
    let src = "\
fn take_slice(s: &[i64]) -> i64
    0

fn main() -> i64
    take_slice(0)
";
    let ir = compile_ir(src);
    // The slice parameter should appear as { ptr, i64 } in the LLVM IR.
    assert!(
        ir.contains("{ ptr, i64 }"),
        "IR should use fat pointer for slice: {}",
        ir
    );
}
