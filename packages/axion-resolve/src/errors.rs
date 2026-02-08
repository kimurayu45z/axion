use axion_diagnostics::Diagnostic;
use axion_syntax::Span;

// Error codes for name resolution (E0100–E0199).

pub const E0100: &str = "E0100";
pub const E0101: &str = "E0101";
pub const E0102: &str = "E0102";
pub const E0103: &str = "E0103";
pub const E0104: &str = "E0104";
pub const E0106: &str = "E0106";
pub const E0107: &str = "E0107";
pub const W0001: &str = "W0001";

pub fn duplicate_definition(name: &str, file: &str, span: Span, source: &str) -> Diagnostic {
    Diagnostic::error(
        E0100,
        "duplicate_definition",
        &format!("duplicate definition of '{name}'"),
        file,
        span,
        source,
    )
}

pub fn unresolved_import(path: &str, file: &str, span: Span, source: &str) -> Diagnostic {
    Diagnostic::error(
        E0101,
        "unresolved_import",
        &format!("unresolved import: cannot find '{path}'"),
        file,
        span,
        source,
    )
}

pub fn undefined_variable(name: &str, file: &str, span: Span, source: &str) -> Diagnostic {
    Diagnostic::error(
        E0102,
        "undefined_variable",
        &format!("undefined variable '{name}'"),
        file,
        span,
        source,
    )
}

pub fn undefined_type(name: &str, file: &str, span: Span, source: &str) -> Diagnostic {
    Diagnostic::error(
        E0103,
        "undefined_type",
        &format!("undefined type '{name}'"),
        file,
        span,
        source,
    )
}

pub fn not_an_interface(name: &str, file: &str, span: Span, source: &str) -> Diagnostic {
    Diagnostic::error(
        E0104,
        "not_an_interface",
        &format!("'{name}' is not an interface"),
        file,
        span,
        source,
    )
}

pub fn invalid_self(file: &str, span: Span, source: &str) -> Diagnostic {
    Diagnostic::error(
        E0106,
        "invalid_self",
        "'self' used outside of a method body",
        file,
        span,
        source,
    )
}

pub fn undefined_variant(
    enum_name: &str,
    variant_name: &str,
    file: &str,
    span: Span,
    source: &str,
) -> Diagnostic {
    Diagnostic::error(
        E0107,
        "undefined_variant",
        &format!("enum '{enum_name}' has no variant '{variant_name}'"),
        file,
        span,
        source,
    )
}

pub fn unused_variable(name: &str, file: &str, span: Span, source: &str) -> Diagnostic {
    Diagnostic::warning(
        W0001,
        "unused_variable",
        &format!("unused variable '{name}'"),
        file,
        span,
        source,
    )
}
