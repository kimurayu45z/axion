use crate::Span;

/// A token produced by the lexer.
#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

/// All token kinds in the Axion language.
#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    // --- Keywords (spec 1.2, 35 reserved words) ---
    Fn,
    Let,
    Mut,
    Move,
    Type,
    Struct,
    Enum,
    Interface,
    Match,
    If,
    Else,
    For,
    While,
    In,
    Return,
    Break,
    Continue,
    Use,
    Mod,
    Pkg,
    Pub,
    SelfLower,  // `self`
    SelfUpper,  // `Self`
    True,
    False,
    With,
    Where,
    As,
    Const,
    Dim,
    Dyn,
    Extern,
    Handle,
    Assert,
    Test,

    // --- Identifiers ---
    /// Value/function/variable identifier: [a-z_][a-z0-9_]*
    Ident(String),
    /// Type/trait identifier: [A-Z][A-Za-z0-9]*
    TypeIdent(String),

    // --- Literals ---
    /// Integer literal, e.g. `42`, `0xff`, `1_000_i32`
    IntLit(String),
    /// Float literal, e.g. `3.14`, `1.0e10`, `2.5_f32`
    FloatLit(String),
    /// String literal (contents between quotes)
    StringLit(String),
    /// Character literal
    CharLit(char),

    // --- Operators ---
    Plus,       // +
    Minus,      // -
    Star,       // *
    Slash,      // /
    Percent,    // %
    Eq,         // =
    EqEq,       // ==
    BangEq,     // !=
    Lt,         // <
    LtEq,       // <=
    Gt,         // >
    GtEq,       // >=
    Amp,        // &
    AmpAmp,     // &&
    Pipe,       // |
    PipePipe,   // ||
    Bang,       // !
    Arrow,      // ->
    FatArrow,   // =>
    PipeGt,     // |>
    Question,   // ?
    DotDot,     // ..
    At,         // @

    // --- Delimiters ---
    LParen,     // (
    RParen,     // )
    LBracket,   // [
    RBracket,   // ]
    LBrace,     // {
    RBrace,     // }
    HashLBrace, // #{
    Comma,      // ,
    Colon,      // :
    Dot,        // .

    // --- Layout ---
    Newline,
    Indent,
    Dedent,

    // --- Comments ---
    /// Line comment: // ...
    LineComment(String),
    /// Doc comment: /// ...
    DocComment(String),

    // --- Special ---
    Eof,
}

impl TokenKind {
    /// Try to match an identifier string to a keyword.
    pub fn from_keyword(s: &str) -> Option<TokenKind> {
        match s {
            "fn" => Some(TokenKind::Fn),
            "let" => Some(TokenKind::Let),
            "mut" => Some(TokenKind::Mut),
            "move" => Some(TokenKind::Move),
            "type" => Some(TokenKind::Type),
            "struct" => Some(TokenKind::Struct),
            "enum" => Some(TokenKind::Enum),
            "interface" => Some(TokenKind::Interface),
            "match" => Some(TokenKind::Match),
            "if" => Some(TokenKind::If),
            "else" => Some(TokenKind::Else),
            "for" => Some(TokenKind::For),
            "while" => Some(TokenKind::While),
            "in" => Some(TokenKind::In),
            "return" => Some(TokenKind::Return),
            "break" => Some(TokenKind::Break),
            "continue" => Some(TokenKind::Continue),
            "use" => Some(TokenKind::Use),
            "mod" => Some(TokenKind::Mod),
            "pkg" => Some(TokenKind::Pkg),
            "pub" => Some(TokenKind::Pub),
            "self" => Some(TokenKind::SelfLower),
            "Self" => Some(TokenKind::SelfUpper),
            "true" => Some(TokenKind::True),
            "false" => Some(TokenKind::False),
            "with" => Some(TokenKind::With),
            "where" => Some(TokenKind::Where),
            "as" => Some(TokenKind::As),
            "const" => Some(TokenKind::Const),
            "dim" => Some(TokenKind::Dim),
            "dyn" => Some(TokenKind::Dyn),
            "extern" => Some(TokenKind::Extern),
            "handle" => Some(TokenKind::Handle),
            "assert" => Some(TokenKind::Assert),
            "test" => Some(TokenKind::Test),
            _ => None,
        }
    }

    /// Check if a lowercase identifier is a primitive type name.
    pub fn is_primitive_type(s: &str) -> bool {
        matches!(
            s,
            "i8" | "i16" | "i32" | "i64" | "i128"
                | "u8" | "u16" | "u32" | "u64" | "u128"
                | "usize"
                | "f16" | "f32" | "f64" | "bf16"
                | "bool" | "char" | "str"
                | "never"
        )
    }
}
