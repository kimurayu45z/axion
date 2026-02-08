use axion_diagnostics::Diagnostic;
use axion_syntax::Span;

pub fn use_after_move(name: &str, file: &str, span: Span, source: &str) -> Diagnostic {
    Diagnostic::error(
        "E0700",
        "borrow-check",
        &format!("use of moved value '{name}'"),
        file,
        span,
        source,
    )
}

pub fn double_move(name: &str, file: &str, span: Span, source: &str) -> Diagnostic {
    Diagnostic::error(
        "E0701",
        "borrow-check",
        &format!("value '{name}' already moved"),
        file,
        span,
        source,
    )
}

pub fn mutable_borrow_conflict(name: &str, file: &str, span: Span, source: &str) -> Diagnostic {
    Diagnostic::error(
        "E0702",
        "borrow-check",
        &format!("cannot borrow '{name}' as mutable while immutably borrowed"),
        file,
        span,
        source,
    )
}

pub fn multiple_mut_borrows(name: &str, file: &str, span: Span, source: &str) -> Diagnostic {
    Diagnostic::error(
        "E0703",
        "borrow-check",
        &format!("cannot borrow '{name}' as mutable more than once"),
        file,
        span,
        source,
    )
}

pub fn move_of_borrowed(name: &str, file: &str, span: Span, source: &str) -> Diagnostic {
    Diagnostic::error(
        "E0704",
        "borrow-check",
        &format!("cannot move '{name}' while borrowed"),
        file,
        span,
        source,
    )
}

pub fn assign_to_immutable(name: &str, file: &str, span: Span, source: &str) -> Diagnostic {
    Diagnostic::error(
        "E0705",
        "borrow-check",
        &format!("cannot assign to immutable variable '{name}'"),
        file,
        span,
        source,
    )
}

pub fn mut_borrow_immutable(name: &str, file: &str, span: Span, source: &str) -> Diagnostic {
    Diagnostic::error(
        "E0706",
        "borrow-check",
        &format!("cannot mutably borrow immutable variable '{name}'"),
        file,
        span,
        source,
    )
}
