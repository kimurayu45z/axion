use axion_diagnostics::Diagnostic;
use axion_syntax::Span;

use crate::ty::Ty;

pub fn type_mismatch(expected: &Ty, found: &Ty, file: &str, span: Span, source: &str) -> Diagnostic {
    Diagnostic::error(
        "E0200",
        "type_mismatch",
        &format!("expected '{expected}', found '{found}'"),
        file,
        span,
        source,
    )
}

pub fn wrong_arg_count(expected: usize, found: usize, file: &str, span: Span, source: &str) -> Diagnostic {
    Diagnostic::error(
        "E0201",
        "wrong_arg_count",
        &format!("expected {expected} arguments, found {found}"),
        file,
        span,
        source,
    )
}

pub fn no_such_field(ty: &Ty, name: &str, file: &str, span: Span, source: &str) -> Diagnostic {
    Diagnostic::error(
        "E0202",
        "no_such_field",
        &format!("type '{ty}' has no field '{name}'"),
        file,
        span,
        source,
    )
}

pub fn not_callable(file: &str, span: Span, source: &str) -> Diagnostic {
    Diagnostic::error(
        "E0203",
        "not_callable",
        "expression is not callable",
        file,
        span,
        source,
    )
}

pub fn not_a_struct(name: &str, file: &str, span: Span, source: &str) -> Diagnostic {
    Diagnostic::error(
        "E0204",
        "not_a_struct",
        &format!("'{name}' is not a struct"),
        file,
        span,
        source,
    )
}

pub fn missing_field(name: &str, file: &str, span: Span, source: &str) -> Diagnostic {
    Diagnostic::error(
        "E0205",
        "missing_field",
        &format!("missing field '{name}' in struct literal"),
        file,
        span,
        source,
    )
}

pub fn return_type_mismatch(expected: &Ty, found: &Ty, file: &str, span: Span, source: &str) -> Diagnostic {
    Diagnostic::error(
        "E0206",
        "return_type_mismatch",
        &format!("return type mismatch: expected '{expected}', found '{found}'"),
        file,
        span,
        source,
    )
}

pub fn extra_field(name: &str, file: &str, span: Span, source: &str) -> Diagnostic {
    Diagnostic::error(
        "E0207",
        "extra_field",
        &format!("unknown field '{name}' in struct literal"),
        file,
        span,
        source,
    )
}

pub fn pattern_mismatch(ty: &Ty, file: &str, span: Span, source: &str) -> Diagnostic {
    Diagnostic::error(
        "E0208",
        "pattern_mismatch",
        &format!("pattern does not match type '{ty}'"),
        file,
        span,
        source,
    )
}

pub fn unsatisfied_bound(ty: &Ty, iface: &str, file: &str, span: Span, source: &str) -> Diagnostic {
    Diagnostic::error(
        "E0209",
        "unsatisfied_bound",
        &format!("type '{ty}' does not satisfy interface '{iface}'"),
        file,
        span,
        source,
    )
}

pub fn missing_method(ty: &Ty, method: &str, iface: &str, file: &str, span: Span, source: &str) -> Diagnostic {
    Diagnostic::error(
        "E0210",
        "missing_method",
        &format!("type '{ty}' is missing method '{method}' required by interface '{iface}'"),
        file,
        span,
        source,
    )
}

pub fn modifier_mismatch(expected: &str, found: &str, file: &str, span: Span, source: &str) -> Diagnostic {
    Diagnostic::error(
        "E0211",
        "modifier_mismatch",
        &format!("expected '{expected}' modifier, found '{found}'"),
        file,
        span,
        source,
    )
}

pub fn receiver_modifier_mismatch(expected: &str, found: &str, file: &str, span: Span, source: &str) -> Diagnostic {
    Diagnostic::error(
        "E0212",
        "receiver_modifier_mismatch",
        &format!("method requires '{expected}' receiver, but got '{found}'"),
        file,
        span,
        source,
    )
}

pub fn unhandled_effect(callee: &str, effect: &str, file: &str, span: Span, source: &str) -> Diagnostic {
    Diagnostic::error(
        "E0213",
        "unhandled_effect",
        &format!("function '{callee}' has effect '{effect}' which is not handled in this context"),
        file,
        span,
        source,
    )
}

pub fn effect_not_declared(effect: &str, file: &str, span: Span, source: &str) -> Diagnostic {
    Diagnostic::error(
        "E0214",
        "effect_not_declared",
        &format!("function has undeclared effect '{effect}'"),
        file,
        span,
        source,
    )
}
