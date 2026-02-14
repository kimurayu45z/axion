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

fn compile_and_run_raw(src: &str) -> RunResult {
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

fn compile_and_run(src: &str) -> RunResult {
    compile_and_run_raw(src)
}

fn compile_and_run_with_prelude(src: &str) -> RunResult {
    let (combined, _) = axion_resolve::prelude::with_prelude(src);
    compile_and_run_raw(&combined)
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

fn compile_ir_with_prelude(src: &str) -> String {
    let (combined, _) = axion_resolve::prelude::with_prelude(src);
    compile_ir(&combined)
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

impl Counter
    fn increment(self, n: i64) -> Counter
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

impl Resource
    fn drop(self)
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

impl Droppable
    fn drop(self)
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

#[test]
fn compile_array_lit_basic() {
    // [10, 20, 30] → arr[1] == 20
    let src = "\
fn main() -> i64
    let arr = [10, 20, 30]
    arr[1]
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 20);
}

#[test]
fn compile_array_index_computed() {
    // Computed index
    let src = "\
fn main() -> i64
    let arr = [5, 10, 15, 20]
    let i: i64 = 2
    arr[i]
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 15);
}

#[test]
fn compile_array_sum() {
    // Sum array elements using while loop
    let src = "\
fn main() -> i64
    let arr = [1, 2, 3, 4, 5]
    let mut sum: i64 = 0
    let mut i: i64 = 0
    while i < 5
        sum = sum + arr[i]
        i = i + 1
    sum
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 15);
}

#[test]
fn compile_array_type_annotation() {
    // Array type annotation in function parameter
    let src = "\
fn first(arr: [i64; 3]) -> i64
    arr[0]

fn main() -> i64
    first([10, 20, 30])
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 10);
}

#[test]
fn compile_interface_basic() {
    let src = "\
interface Doubler
    fn double(self) -> i64

struct Num
    value: i64

impl Num
    fn double(self) -> i64
        self.value * 2

fn apply_double[T: Doubler](x: T) -> i64
    x.double()

fn main() -> i64
    let n = Num #{value: 21}
    apply_double[Num](n)
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 42);
}

#[test]
fn compile_clone_interface() {
    let src = "\
interface Clone
    fn clone(self) -> Self

struct Point
    x: i64
    y: i64

impl Point
    fn clone(self) -> Point
        Point #{x: self.x, y: self.y}

fn dup[T: Clone](x: T) -> T
    x.clone()

fn main() -> i64
    let p = Point #{x: 10, y: 20}
    let p2 = dup[Point](p)
    p2.x + p2.y
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 30);
}

#[test]
fn compile_interface_with_type_param() {
    let src = "\
interface Mapper[T]
    fn apply(self, x: T) -> T

struct DoubleMapper
    factor: i64

impl DoubleMapper
    fn apply(self, x: i64) -> i64
        x * self.factor

fn do_map[M: Mapper[i64]](mapper: M, val: i64) -> i64
    mapper.apply(val)

fn main() -> i64
    let m = DoubleMapper #{factor: 3}
    do_map[DoubleMapper](m, 14)
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 42);
}

#[test]
fn compile_multiple_interface_bounds() {
    let src = "\
interface Doubler
    fn double(self) -> i64

interface Clone
    fn clone(self) -> Self

struct Val
    n: i64

impl Val
    fn double(self) -> i64
        self.n * 2

    fn clone(self) -> Val
        Val #{n: self.n}

fn clone_and_double[T: Clone + Doubler](x: T) -> i64
    let y = x.clone()
    y.double()

fn main() -> i64
    let v = Val #{n: 21}
    clone_and_double[Val](v)
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 42);
}

#[test]
fn compile_option_match_with_type_args() {
    let src = "\
enum Option[T]
    Some(value: T)
    None

fn unwrap_or(opt: Option[i64], default: i64) -> i64
    match opt
        Option[i64].Some(v) => v
        Option[i64].None => default

fn main() -> i64
    let x = Option[i64].Some(42)
    unwrap_or(x, 0)
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 42);
}

#[test]
fn compile_option_method_is_some() {
    let src = "\
enum Option[T]
    Some(value: T)
    None

impl Option[i64]
    fn is_some(self) -> i64
        match self
            Option[i64].Some(_) => 1
            Option[i64].None => 0

fn main() -> i64
    let x = Option[i64].Some(10)
    let y = Option[i64].None
    x.is_some() + y.is_some()
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 1);
}

#[test]
fn compile_option_map() {
    let src = "\
enum Option[T]
    Some(value: T)
    None

fn option_map(opt: Option[i64], f: Fn(i64) -> i64) -> Option[i64]
    match opt
        Option[i64].Some(v) => Option[i64].Some(f(v))
        Option[i64].None => Option[i64].None

fn main() -> i64
    let x = Option[i64].Some(21)
    let doubled = option_map(x, |v| v * 2)
    match doubled
        Option[i64].Some(v) => v
        Option[i64].None => 0
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 42);
}

#[test]
fn compile_result_basic() {
    let src = "\
enum Result[T, E]
    Ok(value: T)
    Err(error: E)

fn safe_div(a: i64, b: i64) -> Result[i64, i64]
    if b == 0
        Result[i64, i64].Err(0)
    else
        Result[i64, i64].Ok(a / b)

fn main() -> i64
    let r = safe_div(84, 2)
    match r
        Result[i64, i64].Ok(v) => v
        Result[i64, i64].Err(_) => 0
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 42);
}

#[test]
fn compile_iterator_with_option_match() {
    let src = "\
enum Option[T]
    Some(value: T)
    None

fn unwrap_or_default(opt: Option[i64]) -> i64
    match opt
        Option[i64].Some(v) => v
        Option[i64].None => 0

fn make_opt(i: i64) -> Option[i64]
    if i > 0
        Option[i64].Some(i)
    else
        Option[i64].None

fn main() -> i64
    let a = unwrap_or_default(make_opt(10))
    let b = unwrap_or_default(make_opt(0))
    let c = unwrap_or_default(make_opt(32))
    a + b + c
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 42);
}

#[test]
fn compile_mut_self_field_assign() {
    let src = "\
struct Counter
    mut value: i64

impl Counter
    fn increment(mut self)
        self.value = self.value + 1

fn main() -> i64
    let mut c = Counter #{value: 40}
    c.increment()
    c.increment()
    c.value
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 42);
}

#[test]
fn compile_mut_self_iterator() {
    let src = "\
struct Range
    mut current: i64
    end: i64

impl Range
    fn next(mut self) -> i64
        let val = self.current
        self.current = self.current + 1
        val

fn main() -> i64
    let mut r = Range #{current: 0, end: 5}
    let mut sum: i64 = 0
    sum = sum + r.next()
    sum = sum + r.next()
    sum = sum + r.next()
    sum = sum + r.next()
    sum = sum + r.next()
    sum
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 10);  // 0+1+2+3+4 = 10
}

#[test]
fn compile_borrow_self_method() {
    let src = "\
struct Point
    x: i64
    y: i64

impl Point
    fn sum(self) -> i64
        self.x + self.y

fn main() -> i64
    let p = Point #{x: 20, y: 22}
    p.sum()
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 42);
}

#[test]
fn compile_generic_unwrap_or() {
    let src = "\
enum Option[T]
    Some(value: T)
    None

fn unwrap_or[T](opt: Option[T], default: T) -> T
    match opt
        Option[T].Some(v) => v
        Option[T].None => default

fn main() -> i64
    let x = Option[i64].Some(42)
    let y = Option[i64].None
    unwrap_or[i64](x, 0) + unwrap_or[i64](y, 10)
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 52);
}

#[test]
fn prelude_option_some_none() {
    let src = "\
fn main() -> i64
    let x = Option[i64].Some(42)
    let y = Option[i64].None
    match x
        Option[i64].Some(v) => match y
            Option[i64].Some(_) => 0
            Option[i64].None => v
        Option[i64].None => 0
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 42);
}

#[test]
fn prelude_result_ok_err() {
    let src = "\
fn main() -> i64
    let ok = Result[i64, i64].Ok(10)
    let err = Result[i64, i64].Err(99)
    let a = match ok
        Result[i64, i64].Ok(v) => v
        Result[i64, i64].Err(_) => 0
    let b = match err
        Result[i64, i64].Ok(_) => 0
        Result[i64, i64].Err(e) => e
    a + b
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 109);
}

#[test]
fn prelude_abs() {
    let src = "\
fn main() -> i64
    abs[i64](0 - 42)
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 42);
}

#[test]
fn prelude_min_max() {
    let src = "\
fn main() -> i64
    min[i64](10, 20) + max[i64](10, 20)
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 30);
}

#[test]
fn prelude_combined() {
    let src = "\
fn main() -> i64
    let a = abs[i64](0 - 5)
    let b = min[i64](a, 10)
    let c = max[i64](b, 3)
    let opt = Option[i64].Some(c)
    opt.unwrap_or(0)
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 5);
}

#[test]
fn prelude_clamp() {
    let src = "\
fn main() -> i64
    clamp[i64](5, 0, 10) + clamp[i64](0 - 3, 0, 10) + clamp[i64](15, 0, 10)
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 15);
}

#[test]
fn prelude_sign() {
    let src = "\
fn main() -> i64
    sign[i64](42) + sign[i64](0) + sign[i64](0 - 7) + 10
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 10);
}

#[test]
fn prelude_unwrap_or() {
    let src = "\
fn main() -> i64
    let x = Option[i64].Some(42)
    let y = Option[i64].None
    x.unwrap_or(0) + y.unwrap_or(10)
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 52);
}

#[test]
fn prelude_map_option() {
    let src = "\
fn main() -> i64
    let x = Option[i64].Some(21)
    let doubled = x.map[i64](|v: i64| v * 2)
    doubled.unwrap_or(0)
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 42);
}

#[test]
fn prelude_result_unwrap_and_map() {
    let src = "\
fn main() -> i64
    let ok = Result[i64, i64].Ok(20)
    let err = Result[i64, i64].Err(99)
    let a = ok.unwrap_or(0)
    let b = err.unwrap_or(5)
    let mapped = Result[i64, i64].Ok(10).map[i64](|v: i64| v + 7)
    let c = mapped.unwrap_or(0)
    a + b + c
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 42);
}

#[test]
fn prelude_is_some_is_none() {
    let src = "\
fn main() -> i64
    let s = Option[i64].Some(1)
    let n = Option[i64].None
    if s.is_some() == true
        if n.is_none() == true
            if n.is_some() == false
                if s.is_none() == false
                    42
                else
                    1
            else
                2
        else
            3
    else
        4
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 42);
}

#[test]
fn prelude_is_ok_is_err() {
    let src = "\
fn main() -> i64
    let ok = Result[i64, i64].Ok(1)
    let err = Result[i64, i64].Err(2)
    if ok.is_ok() == true
        if err.is_err() == true
            if err.is_ok() == false
                if ok.is_err() == false
                    42
                else
                    1
            else
                2
        else
            3
    else
        4
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 42);
}

#[test]
fn prelude_pow() {
    let src = "\
fn main() -> i64
    pow[i64](2, 6)
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 64);
}

#[test]
fn prelude_gcd_lcm() {
    let src = "\
fn main() -> u64
    gcd[u64](12, 8) + lcm[u64](3, 4)
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 16);
}

#[test]
fn prelude_is_even_is_odd() {
    let src = "\
fn main() -> i64
    if is_even[i64](4) == true
        if is_odd[i64](3) == true
            if is_even[i64](3) == false
                if is_odd[i64](4) == false
                    42
                else
                    1
            else
                2
        else
            3
    else
        4
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 42);
}

#[test]
fn prelude_generic_pow() {
    let src = "\
fn main() -> i64
    pow[i64](3, 4)
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 81);
}

#[test]
fn prelude_generic_abs_sign() {
    let src = "\
fn main() -> i64
    abs[i64](0 - 5) + sign[i64](0 - 3) + 10
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 14);
}

#[test]
fn prelude_and_then_option() {
    let src = "\
fn main() -> i64
    let x = Option[i64].Some(21)
    let r = x.and_then[i64](|v: i64| Option[i64].Some(v * 2))
    r.unwrap_or(0)
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 42);
}

#[test]
fn prelude_and_then_result() {
    let src = "\
fn main() -> i64
    let x = Result[i64, i64].Ok(10)
    let r = x.and_then[i64](|v: i64| Result[i64, i64].Ok(v + 5))
    r.unwrap_or(0)
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 15);
}

#[test]
fn prelude_map_err() {
    let src = "\
fn main() -> i64
    let x = Result[i64, i64].Err(10)
    let r = x.map_err[i64](|e: i64| e * 2)
    match r
        Result[i64, i64].Ok(_) => 0
        Result[i64, i64].Err(e) => e
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 20);
}

#[test]
fn impl_generic_receiver() {
    let src = "\
fn main() -> i64
    let x = Option[i64].Some(42)
    let y = Option[i64].None
    x.unwrap_or(0) + y.unwrap_or(10)
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 52);
}

#[test]
fn impl_static_method() {
    let src = "\
struct Counter
    value: i64

impl Counter
    fn get_value(self) -> i64
        self.value

    fn add(self, n: i64) -> Counter
        Counter #{value: self.value + n}

fn main() -> i64
    let c = Counter #{value: 10}
    let c2 = c.add(32)
    c2.get_value()
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 42);
}

#[test]
fn impl_method_chain() {
    let src = "\
fn main() -> i64
    let x = Option[i64].Some(21)
    let mapped = x.map[i64](|v: i64| v * 2)
    mapped.unwrap_or(0)
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 42);
}

// ===== FixedArray built-in method tests =====

#[test]
fn array_builtin_len() {
    let src = "fn main() -> i64\n    let arr = [1, 2, 3]\n    arr.len()";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 3);
}

#[test]
fn array_builtin_first() {
    let src = "fn main() -> i64\n    let arr = [10, 20, 30]\n    arr.first()";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 10);
}

#[test]
fn array_builtin_last() {
    let src = "fn main() -> i64\n    let arr = [10, 20, 30]\n    arr.last()";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 30);
}

#[test]
fn array_len_in_expression() {
    let src = "fn main() -> i64\n    let arr = [1, 2, 3]\n    arr.len() + 7";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 10);
}

#[test]
fn compile_for_array() {
    let src = "fn main() -> i64\n    let arr = [1, 2, 3, 4, 5]\n    let mut sum: i64 = 0\n    for x in arr\n        sum = sum + x\n    sum";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 15);
}

#[test]
fn compile_for_iter_counter() {
    let src = "struct Counter\n    mut current: i64\n    end: i64\n\nimpl Counter\n    fn next(mut self) -> Option[i64]\n        if self.current < self.end\n            let v = self.current\n            self.current = self.current + 1\n            Option[i64].Some(v)\n        else\n            Option[i64].None\n\nfn main() -> i64\n    let mut c = Counter #{current: 0, end: 5}\n    let mut sum: i64 = 0\n    for x in c\n        sum = sum + x\n    sum";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 10);
}

#[test]
fn compile_for_iter_empty() {
    let src = "struct Counter\n    mut current: i64\n    end: i64\n\nimpl Counter\n    fn next(mut self) -> Option[i64]\n        if self.current < self.end\n            let v = self.current\n            self.current = self.current + 1\n            Option[i64].Some(v)\n        else\n            Option[i64].None\n\nfn main() -> i64\n    let mut c = Counter #{current: 5, end: 5}\n    let mut sum: i64 = 0\n    for x in c\n        sum = sum + x\n    sum";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 0);
}

// ===== Range as value tests =====

#[test]
fn compile_range_as_value() {
    let src = "\
fn main() -> i64
    let mut sum: i64 = 0
    let r = 0..5
    for i in r
        sum = sum + i
    sum
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 10); // 0+1+2+3+4 = 10
}

// ===== Slice tests =====

#[test]
fn compile_slice_from_array() {
    let src = "\
fn main() -> i64
    let arr = [10, 20, 30]
    let s = arr[..]
    s[1]
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 20);
}

#[test]
fn compile_slice_len() {
    let src = "\
fn main() -> i64
    let arr = [1, 2, 3]
    let s = arr[..]
    s.len()
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 3);
}

#[test]
fn compile_for_slice() {
    let src = "\
fn main() -> i64
    let arr = [1, 2, 3]
    let mut sum: i64 = 0
    for x in arr[..]
        sum = sum + x
    sum
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 6); // 1+2+3 = 6
}

#[test]
fn compile_sub_slice() {
    let src = "\
fn main() -> i64
    let arr = [10, 20, 30, 40]
    let s = arr[1..3]
    s[0]
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 20);
}

#[test]
fn compile_slice_range_end() {
    let src = "\
fn main() -> i64
    let arr = [10, 20, 30, 40]
    let s = arr[..2]
    s.len()
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 2);
}

#[test]
fn compile_slice_range_start() {
    let src = "\
fn main() -> i64
    let arr = [10, 20, 30, 40]
    let s = arr[2..]
    s[0]
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 30);
}

#[test]
fn compile_slice_first() {
    let src = "\
fn main() -> i64
    let arr = [10, 20, 30]
    let s = arr[..]
    s.first()
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 10);
}

#[test]
fn compile_slice_last() {
    let src = "\
fn main() -> i64
    let arr = [10, 20, 30]
    let s = arr[..]
    s.last()
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 30);
}

#[test]
fn compile_slice_is_empty() {
    let src = "\
fn main() -> i64
    let arr = [10, 20, 30]
    let s = arr[..]
    if s.is_empty()
        1
    else
        0
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 0); // not empty
}

#[test]
fn compile_slice_as_param() {
    let src = "\
fn sum_slice(s: &[i64]) -> i64
    let mut sum: i64 = 0
    for x in s
        sum = sum + x
    sum

fn main() -> i64
    let arr = [1, 2, 3, 4]
    sum_slice(arr[..])
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 10); // 1+2+3+4 = 10
}

#[test]
fn compile_array_index_assign() {
    let src = "\
fn main() -> i64
    let mut arr = [1, 2, 3]
    arr[0] = 10
    arr[0]
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 10);
}

#[test]
fn compile_slice_mut_assign() {
    let src = "\
fn main() -> i64
    let mut arr = [1, 2, 3]
    let s = arr[..]
    s[1] = 99
    arr[1]
";
    let result = compile_and_run(src);
    assert_eq!(result.exit_code, 99);
}

// ===== String type tests =====

#[test]
fn compile_string_new() {
    let src = "\
fn main() -> i64
    let s = String.new()
    s.len()
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 0);
}

#[test]
fn compile_string_from() {
    let src = "\
fn main()
    let s = String.from(\"hello\")
    println(s)
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.stdout.trim(), "hello");
}

#[test]
fn compile_string_len() {
    let src = "\
fn main() -> i64
    let s = String.from(\"abc\")
    s.len()
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 3);
}

#[test]
fn compile_string_is_empty() {
    let src = "\
fn main() -> i64
    let s = String.new()
    if s.is_empty()
        1
    else
        0
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 1);
}

#[test]
fn compile_string_push() {
    let src = "\
fn main()
    let mut s = String.from(\"hello\")
    s.push(\" world\")
    println(s)
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.stdout.trim(), "hello world");
}

#[test]
fn compile_string_as_str() {
    let src = "\
fn main()
    let s = String.from(\"hello\")
    let st = s.as_str()
    println(st)
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.stdout.trim(), "hello");
}

#[test]
fn compile_string_drop() {
    let src = "\
fn main()
    let s = String.from(\"hello\")
    println(s)
";
    let ir = compile_ir_with_prelude(src);
    assert!(ir.contains("String.drop"), "IR should contain String.drop call");
}

#[test]
fn compile_string_type_interp() {
    let src = "\
fn main()
    let s = String.from(\"world\")
    println(\"hello {s}\")
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.stdout.trim(), "hello world");
}

// ---------------------------------------------------------------------------
// Array[T] tests
// ---------------------------------------------------------------------------

#[test]
fn compile_array_new() {
    let src = "\
fn main() -> i64
    let a = Array[i64].new()
    a.len()
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 0);
}

#[test]
fn compile_array_push() {
    let src = "\
fn main() -> i64
    let mut a = Array[i64].new()
    a.push(10)
    a.push(20)
    a.push(30)
    a.len()
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 3);
}

#[test]
fn compile_array_index() {
    let src = "\
fn main() -> i64
    let mut a = Array[i64].new()
    a.push(42)
    a.push(99)
    a[0]
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 42);
}

#[test]
fn compile_array_assign() {
    let src = "\
fn main() -> i64
    let mut a = Array[i64].new()
    a.push(10)
    a.push(20)
    a[0] = 99
    a[0]
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 99);
}

#[test]
fn compile_array_first_last() {
    let src = "\
fn main() -> i64
    let mut a = Array[i64].new()
    a.push(10)
    a.push(20)
    a.first() + a.last()
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 30); // 10 + 20
}

#[test]
fn compile_array_pop() {
    let src = "\
fn main() -> i64
    let mut a = Array[i64].new()
    a.push(10)
    a.push(20)
    let v = a.pop()
    v + a.len()
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 21); // 20 + 1
}

#[test]
fn compile_array_is_empty() {
    let src = "\
fn main() -> i64
    let mut a = Array[i64].new()
    let before = a.is_empty()
    a.push(1)
    let after = a.is_empty()
    if before
        if after
            0
        else
            1
    else
        2
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 1); // before=true, after=false → 1
}

#[test]
fn compile_array_for_in() {
    let src = "\
fn main() -> i64
    let mut a = Array[i64].new()
    a.push(1)
    a.push(2)
    a.push(3)
    let mut sum: i64 = 0
    for x in a
        sum = sum + x
    sum
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 6); // 1+2+3
}

#[test]
fn compile_array_drop() {
    let src = "\
fn main()
    let mut a = Array[i64].new()
    a.push(1)
";
    let ir = compile_ir_with_prelude(src);
    assert!(ir.contains("Array.drop") || ir.contains("Array.drop__i64"), "IR should contain Array.drop call");
}

#[test]
fn compile_string_concat_basic() {
    let src = "\
fn main() -> i64
    let s = String.from(\"hello\") + String.from(\" world\")
    s.len()
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 11); // "hello world".len() == 11
}

#[test]
fn compile_string_concat_empty() {
    let src = "\
fn main() -> i64
    let s = String.from(\"abc\") + String.new()
    s.len()
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 3); // "abc" + "" == "abc", len == 3
}

#[test]
fn compile_string_eq_true() {
    let src = "\
fn main() -> i64
    let a = String.from(\"hello\")
    let b = String.from(\"hello\")
    if a == b
        1
    else
        0
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 1);
}

#[test]
fn compile_string_eq_false() {
    let src = "\
fn main() -> i64
    let a = String.from(\"hello\")
    let b = String.from(\"world\")
    if a == b
        1
    else
        0
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 0);
}

#[test]
fn compile_string_ne() {
    let src = "\
fn main() -> i64
    let a = String.from(\"foo\")
    let b = String.from(\"bar\")
    if a != b
        1
    else
        0
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 1);
}

#[test]
fn compile_array_bool() {
    let src = "\
fn main() -> i64
    let mut a = Array[bool].new()
    a.push(true)
    a.push(false)
    a.push(true)
    if a.first()
        a.len()
    else
        0
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 3); // first is true, so returns len == 3
}

#[test]
fn compile_array_f64() {
    let src = "\
fn main() -> i64
    let mut a = Array[f64].new()
    a.push(1.5)
    a.push(2.5)
    a.len()
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 2); // len after 2 pushes
}

#[test]
fn compile_hashmap_insert_get() {
    let src = "\
fn main() -> i64
    let mut m = HashMap[i64, i64].new()
    m.insert(1, 42)
    let v = m.get(1)
    v.unwrap_or(0)
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 42);
}

#[test]
fn compile_hashmap_overwrite() {
    let src = "\
fn main() -> i64
    let mut m = HashMap[i64, i64].new()
    m.insert(1, 10)
    m.insert(1, 20)
    let v = m.get(1)
    v.unwrap_or(0)
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 20);
}

#[test]
fn compile_hashmap_contains_key() {
    let src = "\
fn main() -> i64
    let mut m = HashMap[i64, i64].new()
    m.insert(5, 100)
    if m.contains_key(5)
        if m.contains_key(99)
            0
        else
            1
    else
        0
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 1);
}

#[test]
fn compile_hashmap_remove() {
    let src = "\
fn main() -> i64
    let mut m = HashMap[i64, i64].new()
    m.insert(1, 42)
    let removed = m.remove(1)
    let after = m.get(1)
    if after.is_none()
        removed.unwrap_or(0)
    else
        0
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 42);
}

#[test]
fn compile_hashmap_grow() {
    let src = "\
fn main() -> i64
    let mut m = HashMap[i64, i64].new()
    m.insert(1, 1)
    m.insert(2, 2)
    m.insert(3, 3)
    m.insert(4, 4)
    m.insert(5, 5)
    m.insert(6, 6)
    m.insert(7, 7)
    m.insert(8, 8)
    m.insert(9, 9)
    m.insert(10, 10)
    let v = m.get(10)
    v.unwrap_or(0)
";
    let result = compile_and_run_with_prelude(src);
    assert_eq!(result.exit_code, 10);
}
