use axion_parser::parse;

use crate::ty::{PrimTy, Ty};
use crate::unify::UnifyContext;

// ===== Helper =====

fn check(source: &str) -> (crate::TypeCheckOutput, Vec<axion_diagnostics::Diagnostic>) {
    let (ast, _parse_diags) = parse(source, "test.ax");
    let (resolved, _resolve_diags) = axion_resolve::resolve(&ast, "test.ax", source);
    crate::type_check(&ast, &resolved, "test.ax", source)
}

fn check_no_errors(source: &str) -> crate::TypeCheckOutput {
    let (output, diags) = check(source);
    if !diags.is_empty() {
        for d in &diags {
            eprintln!("  [{}] {}", d.code, d.message);
        }
        panic!("expected no type errors, got {}", diags.len());
    }
    output
}

fn check_errors(source: &str) -> Vec<axion_diagnostics::Diagnostic> {
    let (_, diags) = check(source);
    assert!(!diags.is_empty(), "expected type errors, got none");
    diags
}

// ===== Unification tests =====

#[test]
fn unify_same_prim() {
    let mut ctx = UnifyContext::new();
    let i64_ty = Ty::Prim(PrimTy::I64);
    assert!(ctx.unify(&i64_ty, &i64_ty).is_ok());
}

#[test]
fn unify_different_prim_fails() {
    let mut ctx = UnifyContext::new();
    let i64_ty = Ty::Prim(PrimTy::I64);
    let f64_ty = Ty::Prim(PrimTy::F64);
    assert!(ctx.unify(&i64_ty, &f64_ty).is_err());
}

#[test]
fn unify_infer_var_with_prim() {
    let mut ctx = UnifyContext::new();
    let var = ctx.fresh_var();
    let infer_ty = Ty::Infer(var);
    let i64_ty = Ty::Prim(PrimTy::I64);
    assert!(ctx.unify(&infer_ty, &i64_ty).is_ok());
    assert_eq!(ctx.resolve(&infer_ty), Ty::Prim(PrimTy::I64));
}

#[test]
fn unify_two_infer_vars() {
    let mut ctx = UnifyContext::new();
    let v1 = ctx.fresh_var();
    let v2 = ctx.fresh_var();
    let ty1 = Ty::Infer(v1);
    let ty2 = Ty::Infer(v2);
    assert!(ctx.unify(&ty1, &ty2).is_ok());
    // After unifying with a concrete type, both should resolve.
    assert!(ctx.unify(&ty1, &Ty::Prim(PrimTy::Bool)).is_ok());
    assert_eq!(ctx.resolve(&ty2), Ty::Prim(PrimTy::Bool));
}

#[test]
fn unify_error_poison() {
    let mut ctx = UnifyContext::new();
    assert!(ctx.unify(&Ty::Error, &Ty::Prim(PrimTy::I64)).is_ok());
    assert!(ctx.unify(&Ty::Prim(PrimTy::F64), &Ty::Error).is_ok());
}

#[test]
fn unify_unit() {
    let mut ctx = UnifyContext::new();
    assert!(ctx.unify(&Ty::Unit, &Ty::Unit).is_ok());
    assert!(ctx.unify(&Ty::Unit, &Ty::Prim(PrimTy::I64)).is_err());
}

#[test]
fn unify_tuple() {
    let mut ctx = UnifyContext::new();
    let t1 = Ty::Tuple(vec![Ty::Prim(PrimTy::I64), Ty::Prim(PrimTy::Bool)]);
    let t2 = Ty::Tuple(vec![Ty::Prim(PrimTy::I64), Ty::Prim(PrimTy::Bool)]);
    assert!(ctx.unify(&t1, &t2).is_ok());

    let t3 = Ty::Tuple(vec![Ty::Prim(PrimTy::I64)]);
    assert!(ctx.unify(&t1, &t3).is_err());
}

#[test]
fn unify_fn_type() {
    let mut ctx = UnifyContext::new();
    let fn1 = Ty::Fn {
        params: vec![Ty::Prim(PrimTy::I64)],
        ret: Box::new(Ty::Prim(PrimTy::Bool)),
    };
    let fn2 = Ty::Fn {
        params: vec![Ty::Prim(PrimTy::I64)],
        ret: Box::new(Ty::Prim(PrimTy::Bool)),
    };
    assert!(ctx.unify(&fn1, &fn2).is_ok());

    let fn3 = Ty::Fn {
        params: vec![Ty::Prim(PrimTy::F64)],
        ret: Box::new(Ty::Prim(PrimTy::Bool)),
    };
    assert!(ctx.unify(&fn1, &fn3).is_err());
}

// ===== Lower tests =====

#[test]
fn lower_named_prim() {
    let source = "fn foo(x: i64) -> bool\n    true\n";
    let (ast, _) = parse(source, "test.ax");
    let (resolved, _) = axion_resolve::resolve(&ast, "test.ax", source);
    let te = &ast.items[0].kind;
    if let axion_syntax::ItemKind::Function(f) = te {
        let param_ty = crate::lower::lower_type_expr(
            &f.params[0].ty,
            &resolved.symbols,
            &resolved.resolutions,
        );
        assert_eq!(param_ty, Ty::Prim(PrimTy::I64));

        let ret_ty = crate::lower::lower_type_expr(
            f.return_type.as_ref().unwrap(),
            &resolved.symbols,
            &resolved.resolutions,
        );
        assert_eq!(ret_ty, Ty::Prim(PrimTy::Bool));
    } else {
        panic!("expected function");
    }
}

#[test]
fn lower_tuple_type() {
    let source = "fn foo(x: {i64, bool})\n    x\n";
    let (ast, _) = parse(source, "test.ax");
    let (resolved, _) = axion_resolve::resolve(&ast, "test.ax", source);
    if let axion_syntax::ItemKind::Function(f) = &ast.items[0].kind {
        let ty = crate::lower::lower_type_expr(
            &f.params[0].ty,
            &resolved.symbols,
            &resolved.resolutions,
        );
        assert_eq!(
            ty,
            Ty::Tuple(vec![Ty::Prim(PrimTy::I64), Ty::Prim(PrimTy::Bool)])
        );
    }
}

#[test]
fn lower_fn_type() {
    let source = "fn apply(f: Fn(i64) -> bool)\n    f\n";
    let (ast, _) = parse(source, "test.ax");
    let (resolved, _) = axion_resolve::resolve(&ast, "test.ax", source);
    if let axion_syntax::ItemKind::Function(f) = &ast.items[0].kind {
        let ty = crate::lower::lower_type_expr(
            &f.params[0].ty,
            &resolved.symbols,
            &resolved.resolutions,
        );
        assert_eq!(
            ty,
            Ty::Fn {
                params: vec![Ty::Prim(PrimTy::I64)],
                ret: Box::new(Ty::Prim(PrimTy::Bool)),
            }
        );
    }
}

// ===== Literal type inference =====

#[test]
fn infer_int_literal() {
    let source = "fn main()\n    42\n";
    let output = check_no_errors(source);
    // Find the IntLit expression type.
    let has_i64 = output.expr_types.values().any(|ty| *ty == Ty::Prim(PrimTy::I64));
    assert!(has_i64, "expected i64 type for int literal");
}

#[test]
fn infer_int_literal_suffix() {
    let source = "fn main()\n    42_i32\n";
    let output = check_no_errors(source);
    let has_i32 = output.expr_types.values().any(|ty| *ty == Ty::Prim(PrimTy::I32));
    assert!(has_i32, "expected i32 type for suffixed int literal");
}

#[test]
fn infer_float_literal() {
    let source = "fn main()\n    3.14\n";
    let output = check_no_errors(source);
    let has_f64 = output.expr_types.values().any(|ty| *ty == Ty::Prim(PrimTy::F64));
    assert!(has_f64, "expected f64 type for float literal");
}

#[test]
fn infer_bool_literal() {
    let source = "fn main()\n    true\n";
    let output = check_no_errors(source);
    let has_bool = output.expr_types.values().any(|ty| *ty == Ty::Prim(PrimTy::Bool));
    assert!(has_bool, "expected bool type for bool literal");
}

#[test]
fn infer_char_literal() {
    let source = "fn main()\n    'a'\n";
    let output = check_no_errors(source);
    let has_char = output.expr_types.values().any(|ty| *ty == Ty::Prim(PrimTy::Char));
    assert!(has_char, "expected char type for char literal");
}

// ===== Binary operator tests =====

#[test]
fn infer_binop_add() {
    let source = "fn main()\n    1 + 2\n";
    let output = check_no_errors(source);
    let has_i64 = output.expr_types.values().any(|ty| *ty == Ty::Prim(PrimTy::I64));
    assert!(has_i64, "expected i64 type for add expression");
}

#[test]
fn infer_binop_comparison() {
    let source = "fn main()\n    1 < 2\n";
    let output = check_no_errors(source);
    let has_bool = output.expr_types.values().any(|ty| *ty == Ty::Prim(PrimTy::Bool));
    assert!(has_bool, "expected bool type for comparison");
}

#[test]
fn infer_binop_logical() {
    let source = "fn main()\n    true && false\n";
    let output = check_no_errors(source);
    let has_bool = output.expr_types.values().any(|ty| *ty == Ty::Prim(PrimTy::Bool));
    assert!(has_bool, "expected bool type for logical AND");
}

// ===== If expression =====

#[test]
fn infer_if_expr() {
    let source = "fn main()\n    if true\n        1\n    else\n        2\n";
    let output = check_no_errors(source);
    let has_i64 = output.expr_types.values().any(|ty| *ty == Ty::Prim(PrimTy::I64));
    assert!(has_i64, "expected i64 type for if expression");
}

// ===== Function call =====

#[test]
fn infer_fn_call() {
    let source = "fn add(a: i64, b: i64) -> i64\n    a + b\n\nfn main()\n    add(1, 2)\n";
    let output = check_no_errors(source);
    let has_i64 = output.expr_types.values().any(|ty| *ty == Ty::Prim(PrimTy::I64));
    assert!(has_i64, "expected i64 return type for fn call");
}

#[test]
fn infer_fn_call_wrong_arg_count() {
    let source = "fn add(a: i64, b: i64) -> i64\n    a + b\n\nfn main()\n    add(1)\n";
    let diags = check_errors(source);
    assert!(diags.iter().any(|d| d.code == "E0201"));
}

#[test]
fn infer_fn_call_type_mismatch() {
    let source =
        "fn add(a: i64, b: i64) -> i64\n    a + b\n\nfn main()\n    add(1, true)\n";
    let diags = check_errors(source);
    assert!(diags.iter().any(|d| d.code == "E0200"));
}

// ===== Struct tests =====

#[test]
fn infer_struct_field_access() {
    let source = "\
struct Point
    x: f64
    y: f64

fn@[Point] get_x() -> f64
    self.x
";
    let output = check_no_errors(source);
    // The field access self.x should resolve to f64.
    let has_f64 = output.expr_types.values().any(|ty| *ty == Ty::Prim(PrimTy::F64));
    assert!(has_f64, "expected f64 type for field access self.x");
    // Check that field_resolutions has an entry.
    assert!(!output.field_resolutions.is_empty(), "expected field resolution for self.x");
}

#[test]
fn infer_struct_lit() {
    let source = "\
struct Point
    x: f64
    y: f64

fn main()
    Point #{x: 1.0, y: 2.0}
";
    let output = check_no_errors(source);
    // The struct literal should produce a Struct type.
    let has_struct = output.expr_types.values().any(|ty| matches!(ty, Ty::Struct { .. }));
    assert!(has_struct, "expected Struct type for struct literal");
}

#[test]
fn infer_struct_lit_missing_field() {
    let source = "\
struct Point
    x: f64
    y: f64

fn main()
    Point #{x: 1.0}
";
    let diags = check_errors(source);
    assert!(diags.iter().any(|d| d.code == "E0205"));
}

#[test]
fn infer_struct_lit_extra_field() {
    let source = "\
struct Point
    x: f64
    y: f64

fn main()
    Point #{x: 1.0, y: 2.0, z: 3.0}
";
    let diags = check_errors(source);
    assert!(diags.iter().any(|d| d.code == "E0207"));
}

#[test]
fn infer_no_such_field() {
    let source = "\
struct Point
    x: f64
    y: f64

fn@[Point] get_z() -> f64
    self.z
";
    let diags = check_errors(source);
    assert!(diags.iter().any(|d| d.code == "E0202"));
}

// ===== Constructor =====

#[test]
fn infer_constructor_call() {
    let source = "\
struct Point
    x: f64
    y: f64

fn Point.origin() -> Self
    Self #{x: 0.0, y: 0.0}

fn main()
    Point.origin()
";
    let output = check_no_errors(source);
    let has_struct = output.expr_types.values().any(|ty| matches!(ty, Ty::Struct { .. }));
    assert!(has_struct, "expected Struct type for constructor call");
}

// ===== Method call =====

#[test]
fn infer_method_call() {
    let source = "\
struct Point
    x: f64
    y: f64

fn Point.origin() -> Self
    Self #{x: 0.0, y: 0.0}

fn@[Point] distance(other: Point) -> f64
    self.x

fn main()
    let p = Point.origin()
    p.distance(Point.origin())
";
    let output = check_no_errors(source);
    let has_f64 = output.expr_types.values().any(|ty| *ty == Ty::Prim(PrimTy::F64));
    assert!(has_f64, "expected f64 return type for method call");
}

// ===== Let binding =====

#[test]
fn infer_let_binding() {
    let source = "fn main()\n    let x = 42\n    x\n";
    let output = check_no_errors(source);
    let has_i64 = output.expr_types.values().any(|ty| *ty == Ty::Prim(PrimTy::I64));
    assert!(has_i64);
}

#[test]
fn infer_let_with_annotation() {
    let source = "fn main()\n    let x: i32 = 42_i32\n    x\n";
    let output = check_no_errors(source);
    let has_i32 = output.expr_types.values().any(|ty| *ty == Ty::Prim(PrimTy::I32));
    assert!(has_i32);
}

// ===== Return type checking =====

#[test]
fn return_type_mismatch() {
    let source = "fn foo() -> i64\n    true\n";
    let diags = check_errors(source);
    assert!(diags.iter().any(|d| d.code == "E0206"));
}

// ===== While loop =====

#[test]
fn infer_while_loop() {
    let source = "fn main()\n    while true\n        42\n";
    check_no_errors(source);
}

// ===== Tuple =====

#[test]
fn infer_tuple_lit() {
    let source = "fn main()\n    {1, true}\n";
    let output = check_no_errors(source);
    let has_tuple = output.expr_types.values().any(|ty| matches!(ty, Ty::Tuple(_)));
    assert!(has_tuple, "expected Tuple type");
}

// ===== Closure =====

#[test]
fn infer_closure() {
    let source = "fn main()\n    |x: i64| x + 1\n";
    let output = check_no_errors(source);
    let has_fn = output.expr_types.values().any(|ty| matches!(ty, Ty::Fn { .. }));
    assert!(has_fn, "expected Fn type for closure");
}

// ===== Integration test: full pipeline =====

#[test]
fn infer_generic_fn_call() {
    let source = "\
fn identity[T](x: T) -> T
    x

fn main()
    let x = identity[i64](42)
    x
";
    check_no_errors(source);
}

#[test]
fn integration_full_pipeline() {
    let source = "\
struct Point
    x: f64
    y: f64

fn Point.origin() -> Self
    Self #{x: 0.0, y: 0.0}

fn@[Point] distance(other: Point) -> f64
    self.x

fn identity[T](x: T) -> T
    x

fn main()
    let p = Point.origin()
    let d = p.distance(Point.origin())
    let x = identity[i64](42)
    x
";
    let output = check_no_errors(source);

    // p should be inferred as Point (Struct type).
    let has_struct = output.expr_types.values().any(|ty| matches!(ty, Ty::Struct { .. }));
    assert!(has_struct, "expected Point struct type");

    // d should be f64.
    let has_f64 = output.expr_types.values().any(|ty| *ty == Ty::Prim(PrimTy::F64));
    assert!(has_f64, "expected f64 type");

    // x should be i64.
    let has_i64 = output.expr_types.values().any(|ty| *ty == Ty::Prim(PrimTy::I64));
    assert!(has_i64, "expected i64 type");
}

#[test]
fn integration_enum_def() {
    let source = "\
enum Shape
    Circle
        radius: f64
    Rect
        width: f64
        height: f64

fn main()
    42
";
    check_no_errors(source);
}
