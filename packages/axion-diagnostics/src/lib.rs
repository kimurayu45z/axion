use axion_syntax::Span;
use serde::Serialize;

/// Severity level of a diagnostic.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Severity {
    Error,
    Warning,
}

/// A span location for JSON output (resolved line/col).
#[derive(Debug, Clone, Serialize)]
pub struct SpanLocation {
    pub file: String,
    pub line: u32,
    pub col: u32,
    pub end_line: u32,
    pub end_col: u32,
}

/// A label attached to a diagnostic pointing at a specific source location.
#[derive(Debug, Clone, Serialize)]
pub struct Label {
    pub span: SpanLocation,
    pub message: String,
}

/// A suggested fix for a diagnostic.
#[derive(Debug, Clone, Serialize)]
pub struct FixSuggestion {
    pub message: String,
    pub edits: Vec<FixEdit>,
}

/// A single text edit within a fix suggestion.
#[derive(Debug, Clone, Serialize)]
pub struct FixEdit {
    pub file: String,
    pub line: u32,
    pub old_text: String,
    pub new_text: String,
}

/// A related diagnostic location.
#[derive(Debug, Clone, Serialize)]
pub struct Related {
    pub message: String,
    pub span: SpanLocation,
}

/// A compiler diagnostic (error or warning).
///
/// Follows the JSON schema defined in spec section 12.2.
#[derive(Debug, Clone, Serialize)]
pub struct Diagnostic {
    pub severity: Severity,
    pub code: String,
    pub category: String,
    pub message: String,
    pub primary_span: SpanLocation,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub labels: Vec<Label>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub fix_suggestions: Vec<FixSuggestion>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub related: Vec<Related>,
}

/// Container for multiple diagnostics (for JSON output).
#[derive(Debug, Clone, Serialize)]
pub struct DiagnosticOutput {
    pub diagnostics: Vec<Diagnostic>,
}

impl Diagnostic {
    /// Create a simple error diagnostic.
    pub fn error(code: &str, category: &str, message: &str, file: &str, span: Span, source: &str) -> Self {
        let (line, col) = offset_to_line_col(source, span.start as usize);
        let (end_line, end_col) = offset_to_line_col(source, span.end as usize);
        Self {
            severity: Severity::Error,
            code: code.to_string(),
            category: category.to_string(),
            message: message.to_string(),
            primary_span: SpanLocation {
                file: file.to_string(),
                line,
                col,
                end_line,
                end_col,
            },
            labels: Vec::new(),
            fix_suggestions: Vec::new(),
            related: Vec::new(),
        }
    }

    /// Create a simple warning diagnostic.
    pub fn warning(code: &str, category: &str, message: &str, file: &str, span: Span, source: &str) -> Self {
        let mut diag = Self::error(code, category, message, file, span, source);
        diag.severity = Severity::Warning;
        diag
    }
}

impl DiagnosticOutput {
    pub fn new(diagnostics: Vec<Diagnostic>) -> Self {
        Self { diagnostics }
    }

    /// Serialize to JSON string.
    pub fn to_json(&self) -> String {
        serde_json::to_string_pretty(self).expect("diagnostic serialization should not fail")
    }
}

/// Convert a byte offset to 1-based line and column numbers.
fn offset_to_line_col(source: &str, offset: usize) -> (u32, u32) {
    let mut line = 1u32;
    let mut col = 1u32;
    for (i, ch) in source.char_indices() {
        if i >= offset {
            break;
        }
        if ch == '\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }
    (line, col)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_offset_to_line_col() {
        let src = "fn main()\n    let x = 1\n";
        assert_eq!(offset_to_line_col(src, 0), (1, 1));
        assert_eq!(offset_to_line_col(src, 3), (1, 4));
        assert_eq!(offset_to_line_col(src, 10), (2, 1)); // after \n
    }

    #[test]
    fn test_diagnostic_json() {
        let diag = Diagnostic::error(
            "E0001",
            "syntax_error",
            "unexpected token",
            "test.ax",
            Span::new(0, 2),
            "fn",
        );
        let output = DiagnosticOutput::new(vec![diag]);
        let json = output.to_json();
        assert!(json.contains("\"severity\": \"error\""));
        assert!(json.contains("\"code\": \"E0001\""));
    }
}
