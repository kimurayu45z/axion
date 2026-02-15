use axion_diagnostics::Diagnostic;
use axion_syntax::Span;

// Error codes for module system (E0600–E0604).

pub const E0600: &str = "E0600";
pub const E0601: &str = "E0601";
pub const E0602: &str = "E0602";
pub const E0603: &str = "E0603";
pub const E0604: &str = "E0604";
pub const E0605: &str = "E0605";

pub fn unresolved_module(path: &str, file: &str, span: Span, source: &str) -> Diagnostic {
    Diagnostic::error(
        E0600,
        "unresolved_module",
        &format!("module '{path}' not found"),
        file,
        span,
        source,
    )
}

pub fn circular_import(cycle: &str, file: &str, span: Span, source: &str) -> Diagnostic {
    Diagnostic::error(
        E0601,
        "circular_import",
        &format!("circular dependency: {cycle}"),
        file,
        span,
        source,
    )
}

pub fn private_import(
    name: &str,
    module: &str,
    file: &str,
    span: Span,
    source: &str,
) -> Diagnostic {
    Diagnostic::error(
        E0602,
        "private_import",
        &format!("'{name}' is private in module '{module}'"),
        file,
        span,
        source,
    )
}

pub fn unresolved_name(
    name: &str,
    module: &str,
    file: &str,
    span: Span,
    source: &str,
) -> Diagnostic {
    Diagnostic::error(
        E0603,
        "unresolved_import",
        &format!("'{name}' not found in module '{module}'"),
        file,
        span,
        source,
    )
}

pub fn duplicate_import(name: &str, file: &str, span: Span, source: &str) -> Diagnostic {
    Diagnostic::error(
        E0604,
        "duplicate_import",
        &format!("'{name}' is imported multiple times"),
        file,
        span,
        source,
    )
}

pub fn invalid_export(name: &str, file: &str, span: Span, source: &str) -> Diagnostic {
    Diagnostic::error(
        E0605,
        "invalid_export",
        &format!("cannot export '{name}': only imported symbols can be exported"),
        file,
        span,
        source,
    )
}
