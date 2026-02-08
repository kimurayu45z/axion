use axion_types::ty::{PrimTy, Ty};
use axion_types::unify::UnifyContext;

use crate::monomorphize;

fn mono(src: &str) -> crate::output::MonoOutput {
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

    monomorphize(&sf, &resolved, &type_out, &type_env)
}

#[test]
fn mono_identity_fn() {
    let src = "\
fn id[T](x: T) -> T
    x

fn main() -> i64
    id[i64](42)
";
    let output = mono(src);
    assert_eq!(output.specialized_fns.len(), 1);
    assert!(output.specialized_fns[0].mangled_name.contains("id__"));
    assert!(output.specialized_fns[0].mangled_name.contains("i64"));
}

#[test]
fn mono_two_instantiations() {
    let src = "\
fn id[T](x: T) -> T
    x

fn main()
    id[i64](1)
    id[bool](true)
";
    let output = mono(src);
    assert_eq!(
        output.specialized_fns.len(),
        2,
        "Expected 2 specializations, got {:?}",
        output
            .specialized_fns
            .iter()
            .map(|s| &s.mangled_name)
            .collect::<Vec<_>>()
    );
}

#[test]
fn mono_no_generics() {
    let src = "\
fn add(a: i64, b: i64) -> i64
    a + b

fn main() -> i64
    add(1, 2)
";
    let output = mono(src);
    assert!(
        output.specialized_fns.is_empty(),
        "Non-generic code should produce no specializations"
    );
}

#[test]
fn mono_same_instantiation_dedup() {
    let src = "\
fn id[T](x: T) -> T
    x

fn main() -> i64
    let a = id[i64](1)
    let b = id[i64](2)
    a + b
";
    let output = mono(src);
    assert_eq!(
        output.specialized_fns.len(),
        1,
        "Same type args should be deduplicated"
    );
}

#[test]
fn mono_specialization_has_correct_type() {
    let src = "\
fn id[T](x: T) -> T
    x

fn main() -> i64
    id[i64](42)
";
    let output = mono(src);
    assert_eq!(output.specialized_fns.len(), 1);

    let spec = &output.specialized_fns[0];
    // The specialized type should be Fn(i64) -> i64 (no Ty::Param remaining).
    match &spec.fn_ty {
        Ty::Fn { params, ret } => {
            assert_eq!(params.len(), 1);
            assert_eq!(params[0], Ty::Prim(PrimTy::I64));
            assert_eq!(**ret, Ty::Prim(PrimTy::I64));
        }
        other => panic!("Expected Fn type, got {:?}", other),
    }
}

#[test]
fn mono_lookup_works() {
    let src = "\
fn id[T](x: T) -> T
    x

fn main() -> i64
    id[i64](42)
";
    let (sf, _) = axion_parser::parse(src, "test.ax");
    let (resolved, _) = axion_resolve::resolve_single(&sf, "test.ax", src);
    let (type_out, _) = axion_types::type_check(&sf, &resolved, "test.ax", src);
    let mut unify = UnifyContext::new();
    let type_env = axion_types::env::TypeEnv::build(&sf, &resolved, &mut unify);
    let output = monomorphize(&sf, &resolved, &type_out, &type_env);

    // Find the DefId of the `id` function.
    let id_def_id = resolved
        .symbols
        .iter()
        .find(|s| s.name == "id" && s.kind == axion_resolve::def_id::SymbolKind::Function)
        .map(|s| s.def_id)
        .expect("id function not found");

    let result = output.lookup(id_def_id, &[Ty::Prim(PrimTy::I64)]);
    assert!(result.is_some(), "Lookup should find the specialization");
    assert!(result.unwrap().contains("i64"));
}
