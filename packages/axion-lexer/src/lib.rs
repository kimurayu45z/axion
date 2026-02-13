use axion_diagnostics::Diagnostic;
use axion_syntax::{Span, Token, TokenKind};

/// The Axion lexer: transforms UTF-8 source into a token stream.
pub struct Lexer<'src> {
    source: &'src str,
    file: String,
    bytes: &'src [u8],
    pos: usize,
    diagnostics: Vec<Diagnostic>,
    /// Stack of indentation levels (in number of spaces).
    indent_stack: Vec<u32>,
    /// Whether we are at the beginning of a line (for indent handling).
    at_line_start: bool,
    /// Pending tokens to emit (for INDENT/DEDENT).
    pending: Vec<Token>,
}

impl<'src> Lexer<'src> {
    pub fn new(source: &'src str, file: &str) -> Self {
        Self {
            source,
            file: file.to_string(),
            bytes: source.as_bytes(),
            pos: 0,
            diagnostics: Vec::new(),
            indent_stack: vec![0],
            at_line_start: true,
            pending: Vec::new(),
        }
    }

    /// Tokenize the entire source, returning tokens and diagnostics.
    pub fn tokenize(mut self) -> (Vec<Token>, Vec<Diagnostic>) {
        let mut tokens = Vec::new();

        loop {
            if let Some(tok) = self.pending.pop() {
                tokens.push(tok);
                continue;
            }

            if self.is_eof() {
                // Emit remaining DEDENTs at EOF
                while self.indent_stack.len() > 1 {
                    self.indent_stack.pop();
                    tokens.push(Token {
                        kind: TokenKind::Dedent,
                        span: Span::new(self.pos as u32, self.pos as u32),
                    });
                }
                tokens.push(Token {
                    kind: TokenKind::Eof,
                    span: Span::new(self.pos as u32, self.pos as u32),
                });
                break;
            }

            if self.at_line_start {
                self.handle_indentation(&mut tokens);
                self.at_line_start = false;
                continue;
            }

            // Skip spaces (not at line start)
            if self.peek() == Some(b' ') {
                self.advance();
                continue;
            }

            // Newline — suppress if last token is a trailing operator (line continuation)
            if self.peek() == Some(b'\n') {
                let start = self.pos;
                self.advance();
                let suppress = tokens.last().map_or(false, |t| Self::is_continuation_op(&t.kind));
                if !suppress {
                    tokens.push(Token {
                        kind: TokenKind::Newline,
                        span: Span::new(start as u32, self.pos as u32),
                    });
                    self.at_line_start = true;
                } else {
                    // Skip leading whitespace on continuation line, but don't handle indentation
                    while self.peek() == Some(b' ') {
                        self.advance();
                    }
                }
                continue;
            }

            // Carriage return (skip, handle \r\n)
            if self.peek() == Some(b'\r') {
                self.advance();
                continue;
            }

            if let Some(tok) = self.next_token() {
                tokens.push(tok);
            }
        }

        (tokens, self.diagnostics)
    }

    fn handle_indentation(&mut self, tokens: &mut Vec<Token>) {
        let start = self.pos;
        let mut spaces = 0u32;

        while self.peek() == Some(b' ') {
            spaces += 1;
            self.advance();
        }

        // Skip blank lines and comment-only lines
        if self.peek() == Some(b'\n') || self.is_eof() {
            return;
        }
        // Skip carriage return
        if self.peek() == Some(b'\r') {
            return;
        }

        // Check for tabs (forbidden by spec 1.4)
        if self.peek() == Some(b'\t') {
            self.diagnostics.push(Diagnostic::error(
                "E0001",
                "syntax_error",
                "tabs are not allowed; use 4 spaces for indentation",
                &self.file,
                Span::new(self.pos as u32, (self.pos + 1) as u32),
                self.source,
            ));
            // Skip the tab and continue
            self.advance();
            return;
        }

        let current_indent = *self.indent_stack.last().unwrap();

        if spaces > current_indent {
            // Check that indent is exactly 4 more (spec 1.4)
            if spaces != current_indent + 4 {
                self.diagnostics.push(Diagnostic::error(
                    "E0002",
                    "syntax_error",
                    &format!(
                        "indentation must be exactly 4 spaces; found {} spaces (expected {})",
                        spaces,
                        current_indent + 4
                    ),
                    &self.file,
                    Span::new(start as u32, self.pos as u32),
                    self.source,
                ));
            }
            self.indent_stack.push(spaces);
            tokens.push(Token {
                kind: TokenKind::Indent,
                span: Span::new(start as u32, self.pos as u32),
            });
        } else if spaces < current_indent {
            // Emit DEDENT tokens for each closed indentation level
            while self.indent_stack.len() > 1 && *self.indent_stack.last().unwrap() > spaces {
                self.indent_stack.pop();
                tokens.push(Token {
                    kind: TokenKind::Dedent,
                    span: Span::new(start as u32, self.pos as u32),
                });
            }
            if *self.indent_stack.last().unwrap() != spaces {
                self.diagnostics.push(Diagnostic::error(
                    "E0003",
                    "syntax_error",
                    "dedent does not match any outer indentation level",
                    &self.file,
                    Span::new(start as u32, self.pos as u32),
                    self.source,
                ));
            }
        }
    }

    fn next_token(&mut self) -> Option<Token> {
        let start = self.pos;

        let b = self.peek()?;
        match b {
            // Comments
            b'/' if self.peek_at(1) != Some(b'/') => {
                self.advance();
                Some(Token { kind: TokenKind::Slash, span: Span::new(start as u32, self.pos as u32) })
            }
            b'/' if self.peek_at(1) == Some(b'/') => {
                self.advance(); // /
                self.advance(); // /
                let is_doc = self.peek() == Some(b'/');
                if is_doc {
                    self.advance(); // third /
                }
                let content_start = self.pos;
                while self.peek().is_some_and(|c| c != b'\n') {
                    self.advance();
                }
                let content = self.source[content_start..self.pos].trim().to_string();
                let kind = if is_doc {
                    TokenKind::DocComment(content)
                } else {
                    TokenKind::LineComment(content)
                };
                Some(Token {
                    kind,
                    span: Span::new(start as u32, self.pos as u32),
                })
            }

            // String literal
            b'"' => self.lex_string(start),

            // Character literal
            b'\'' => self.lex_char(start),

            // Number literal
            b'0'..=b'9' => self.lex_number(start),

            // Identifier or keyword
            b'a'..=b'z' | b'_' => self.lex_ident(start),

            // Type identifier or Self keyword
            b'A'..=b'Z' => self.lex_type_ident(start),

            // Operators and delimiters
            b'+' => { self.advance(); Some(Token { kind: TokenKind::Plus, span: Span::new(start as u32, self.pos as u32) }) }
            b'*' => { self.advance(); Some(Token { kind: TokenKind::Star, span: Span::new(start as u32, self.pos as u32) }) }
            b'%' => { self.advance(); Some(Token { kind: TokenKind::Percent, span: Span::new(start as u32, self.pos as u32) }) }
            b'?' => { self.advance(); Some(Token { kind: TokenKind::Question, span: Span::new(start as u32, self.pos as u32) }) }

            b'-' => {
                self.advance();
                if self.peek() == Some(b'>') {
                    self.advance();
                    Some(Token { kind: TokenKind::Arrow, span: Span::new(start as u32, self.pos as u32) })
                } else {
                    Some(Token { kind: TokenKind::Minus, span: Span::new(start as u32, self.pos as u32) })
                }
            }

            b'=' => {
                self.advance();
                if self.peek() == Some(b'=') {
                    self.advance();
                    Some(Token { kind: TokenKind::EqEq, span: Span::new(start as u32, self.pos as u32) })
                } else if self.peek() == Some(b'>') {
                    self.advance();
                    Some(Token { kind: TokenKind::FatArrow, span: Span::new(start as u32, self.pos as u32) })
                } else {
                    Some(Token { kind: TokenKind::Eq, span: Span::new(start as u32, self.pos as u32) })
                }
            }

            b'!' => {
                self.advance();
                if self.peek() == Some(b'=') {
                    self.advance();
                    Some(Token { kind: TokenKind::BangEq, span: Span::new(start as u32, self.pos as u32) })
                } else {
                    Some(Token { kind: TokenKind::Bang, span: Span::new(start as u32, self.pos as u32) })
                }
            }

            b'<' => {
                self.advance();
                if self.peek() == Some(b'=') {
                    self.advance();
                    Some(Token { kind: TokenKind::LtEq, span: Span::new(start as u32, self.pos as u32) })
                } else {
                    Some(Token { kind: TokenKind::Lt, span: Span::new(start as u32, self.pos as u32) })
                }
            }

            b'>' => {
                self.advance();
                if self.peek() == Some(b'=') {
                    self.advance();
                    Some(Token { kind: TokenKind::GtEq, span: Span::new(start as u32, self.pos as u32) })
                } else {
                    Some(Token { kind: TokenKind::Gt, span: Span::new(start as u32, self.pos as u32) })
                }
            }

            b'&' => {
                self.advance();
                if self.peek() == Some(b'&') {
                    self.advance();
                    Some(Token { kind: TokenKind::AmpAmp, span: Span::new(start as u32, self.pos as u32) })
                } else {
                    Some(Token { kind: TokenKind::Amp, span: Span::new(start as u32, self.pos as u32) })
                }
            }

            b'|' => {
                self.advance();
                if self.peek() == Some(b'|') {
                    self.advance();
                    Some(Token { kind: TokenKind::PipePipe, span: Span::new(start as u32, self.pos as u32) })
                } else {
                    Some(Token { kind: TokenKind::Pipe, span: Span::new(start as u32, self.pos as u32) })
                }
            }

            b'.' => {
                self.advance();
                if self.peek() == Some(b'.') {
                    self.advance();
                    Some(Token { kind: TokenKind::DotDot, span: Span::new(start as u32, self.pos as u32) })
                } else {
                    Some(Token { kind: TokenKind::Dot, span: Span::new(start as u32, self.pos as u32) })
                }
            }

            b'(' => { self.advance(); Some(Token { kind: TokenKind::LParen, span: Span::new(start as u32, self.pos as u32) }) }
            b')' => { self.advance(); Some(Token { kind: TokenKind::RParen, span: Span::new(start as u32, self.pos as u32) }) }
            b'[' => { self.advance(); Some(Token { kind: TokenKind::LBracket, span: Span::new(start as u32, self.pos as u32) }) }
            b']' => { self.advance(); Some(Token { kind: TokenKind::RBracket, span: Span::new(start as u32, self.pos as u32) }) }
            b'#' => {
                if self.peek_at(1) == Some(b'{') {
                    self.advance(); // #
                    self.advance(); // {
                    Some(Token { kind: TokenKind::HashLBrace, span: Span::new(start as u32, self.pos as u32) })
                } else {
                    self.advance();
                    self.diagnostics.push(Diagnostic::error(
                        "E0004",
                        "syntax_error",
                        "unexpected character: '#'",
                        &self.file,
                        Span::new(start as u32, self.pos as u32),
                        self.source,
                    ));
                    None
                }
            }
            b'{' => { self.advance(); Some(Token { kind: TokenKind::LBrace, span: Span::new(start as u32, self.pos as u32) }) }
            b'}' => { self.advance(); Some(Token { kind: TokenKind::RBrace, span: Span::new(start as u32, self.pos as u32) }) }
            b',' => { self.advance(); Some(Token { kind: TokenKind::Comma, span: Span::new(start as u32, self.pos as u32) }) }
            b':' => { self.advance(); Some(Token { kind: TokenKind::Colon, span: Span::new(start as u32, self.pos as u32) }) }
            b';' => { self.advance(); Some(Token { kind: TokenKind::Semi, span: Span::new(start as u32, self.pos as u32) }) }
            b'@' => { self.advance(); Some(Token { kind: TokenKind::At, span: Span::new(start as u32, self.pos as u32) }) }

            _ => {
                self.advance();
                self.diagnostics.push(Diagnostic::error(
                    "E0004",
                    "syntax_error",
                    &format!("unexpected character: {:?}", char::from(b)),
                    &self.file,
                    Span::new(start as u32, self.pos as u32),
                    self.source,
                ));
                None
            }
        }
    }

    fn lex_ident(&mut self, start: usize) -> Option<Token> {
        while self.peek().is_some_and(|b| b.is_ascii_alphanumeric() || b == b'_') {
            self.advance();
        }
        let text = &self.source[start..self.pos];
        let kind = TokenKind::from_keyword(text)
            .unwrap_or_else(|| TokenKind::Ident(text.to_string()));
        Some(Token {
            kind,
            span: Span::new(start as u32, self.pos as u32),
        })
    }

    fn lex_type_ident(&mut self, start: usize) -> Option<Token> {
        while self.peek().is_some_and(|b| b.is_ascii_alphanumeric() || b == b'_') {
            self.advance();
        }
        let text = &self.source[start..self.pos];
        // Check for `Self` keyword
        let kind = if text == "Self" {
            TokenKind::SelfUpper
        } else {
            TokenKind::TypeIdent(text.to_string())
        };
        Some(Token {
            kind,
            span: Span::new(start as u32, self.pos as u32),
        })
    }

    fn lex_number(&mut self, start: usize) -> Option<Token> {
        let mut is_float = false;

        // Handle hex/binary/octal prefixes
        if self.peek() == Some(b'0') && self.peek_at(1).is_some_and(|b| b == b'x' || b == b'b' || b == b'o') {
            self.advance(); // 0
            self.advance(); // x/b/o
            while self.peek().is_some_and(|b| b.is_ascii_hexdigit()) || (self.peek() == Some(b'_') && self.peek_at(1).is_some_and(|b| b.is_ascii_hexdigit())) {
                self.advance();
            }
        } else {
            // Decimal digits (don't consume _ if followed by alpha = type suffix)
            while self.peek().is_some_and(|b| b.is_ascii_digit()) || (self.peek() == Some(b'_') && self.peek_at(1).is_some_and(|b| b.is_ascii_digit())) {
                self.advance();
            }

            // Float: decimal point followed by digit
            if self.peek() == Some(b'.') && self.peek_at(1).is_some_and(|b| b.is_ascii_digit()) {
                is_float = true;
                self.advance(); // .
                while self.peek().is_some_and(|b| b.is_ascii_digit()) || (self.peek() == Some(b'_') && self.peek_at(1).is_some_and(|b| b.is_ascii_digit())) {
                    self.advance();
                }
            }

            // Exponent
            if self.peek().is_some_and(|b| b == b'e' || b == b'E') {
                is_float = true;
                self.advance(); // e/E
                if self.peek().is_some_and(|b| b == b'+' || b == b'-') {
                    self.advance();
                }
                while self.peek().is_some_and(|b| b.is_ascii_digit()) || (self.peek() == Some(b'_') && self.peek_at(1).is_some_and(|b| b.is_ascii_digit())) {
                    self.advance();
                }
            }
        }

        // Type suffix (e.g. _i32, _f64)
        if self.peek() == Some(b'_') && self.peek_at(1).is_some_and(|b| b.is_ascii_alphabetic()) {
            self.advance(); // _
            while self.peek().is_some_and(|b| b.is_ascii_alphanumeric()) {
                self.advance();
            }
        }

        let text = self.source[start..self.pos].to_string();
        let kind = if is_float {
            TokenKind::FloatLit(text)
        } else {
            TokenKind::IntLit(text)
        };

        Some(Token {
            kind,
            span: Span::new(start as u32, self.pos as u32),
        })
    }

    fn lex_string(&mut self, start: usize) -> Option<Token> {
        self.advance(); // opening "
        let mut content = String::new();

        loop {
            match self.peek() {
                None | Some(b'\n') => {
                    self.diagnostics.push(Diagnostic::error(
                        "E0005",
                        "syntax_error",
                        "unterminated string literal",
                        &self.file,
                        Span::new(start as u32, self.pos as u32),
                        self.source,
                    ));
                    break;
                }
                Some(b'\\') => {
                    self.advance();
                    match self.peek() {
                        Some(b'n') => { content.push('\n'); self.advance(); }
                        Some(b't') => { content.push('\t'); self.advance(); }
                        Some(b'r') => { content.push('\r'); self.advance(); }
                        Some(b'\\') => { content.push('\\'); self.advance(); }
                        Some(b'"') => { content.push('"'); self.advance(); }
                        Some(b'0') => { content.push('\0'); self.advance(); }
                        Some(b'{') => { content.push('{'); self.advance(); }
                        _ => {
                            self.diagnostics.push(Diagnostic::error(
                                "E0006",
                                "syntax_error",
                                "invalid escape sequence",
                                &self.file,
                                Span::new((self.pos - 1) as u32, (self.pos + 1) as u32),
                                self.source,
                            ));
                            self.advance();
                        }
                    }
                }
                Some(b'{') => {
                    // String interpolation: emit StringInterpStart, then lex the inner expression tokens,
                    // and continue with StringInterpPart / StringInterpEnd.
                    let start_tok = Token {
                        kind: TokenKind::StringInterpStart(content),
                        span: Span::new(start as u32, self.pos as u32),
                    };
                    self.advance(); // consume {

                    // Lex inner expression tokens until matching }
                    let mut inner_tokens = vec![start_tok];
                    let mut brace_depth = 1u32;
                    while !self.is_eof() && brace_depth > 0 {
                        // Skip spaces inside interpolation
                        if self.peek() == Some(b' ') {
                            self.advance();
                            continue;
                        }
                        if self.peek() == Some(b'}') {
                            brace_depth -= 1;
                            if brace_depth == 0 {
                                self.advance(); // consume closing }
                                break;
                            }
                        }
                        if self.peek() == Some(b'{') {
                            brace_depth += 1;
                        }
                        if let Some(tok) = self.next_token() {
                            inner_tokens.push(tok);
                        }
                    }

                    // Now continue reading the rest of the string
                    loop {
                        let mut part_content = String::new();
                        let part_start = self.pos;
                        loop {
                            match self.peek() {
                                None | Some(b'\n') => {
                                    self.diagnostics.push(Diagnostic::error(
                                        "E0005",
                                        "syntax_error",
                                        "unterminated string literal",
                                        &self.file,
                                        Span::new(part_start as u32, self.pos as u32),
                                        self.source,
                                    ));
                                    // Emit end token with whatever we have
                                    inner_tokens.push(Token {
                                        kind: TokenKind::StringInterpEnd(part_content),
                                        span: Span::new(part_start as u32, self.pos as u32),
                                    });
                                    // Push all tokens in reverse onto pending
                                    inner_tokens.reverse();
                                    for tok in inner_tokens {
                                        self.pending.push(tok);
                                    }
                                    return self.pending.pop();
                                }
                                Some(b'\\') => {
                                    self.advance();
                                    match self.peek() {
                                        Some(b'n') => { part_content.push('\n'); self.advance(); }
                                        Some(b't') => { part_content.push('\t'); self.advance(); }
                                        Some(b'r') => { part_content.push('\r'); self.advance(); }
                                        Some(b'\\') => { part_content.push('\\'); self.advance(); }
                                        Some(b'"') => { part_content.push('"'); self.advance(); }
                                        Some(b'0') => { part_content.push('\0'); self.advance(); }
                                        Some(b'{') => { part_content.push('{'); self.advance(); }
                                        _ => {
                                            self.diagnostics.push(Diagnostic::error(
                                                "E0006",
                                                "syntax_error",
                                                "invalid escape sequence",
                                                &self.file,
                                                Span::new((self.pos - 1) as u32, (self.pos + 1) as u32),
                                                self.source,
                                            ));
                                            self.advance();
                                        }
                                    }
                                }
                                Some(b'"') => {
                                    self.advance(); // closing "
                                    inner_tokens.push(Token {
                                        kind: TokenKind::StringInterpEnd(part_content),
                                        span: Span::new(part_start as u32, self.pos as u32),
                                    });
                                    // Push all tokens in reverse onto pending
                                    inner_tokens.reverse();
                                    for tok in inner_tokens {
                                        self.pending.push(tok);
                                    }
                                    return self.pending.pop();
                                }
                                Some(b'{') => {
                                    // Another interpolation
                                    inner_tokens.push(Token {
                                        kind: TokenKind::StringInterpPart(part_content),
                                        span: Span::new(part_start as u32, self.pos as u32),
                                    });
                                    self.advance(); // consume {
                                    // Lex inner expression tokens
                                    let mut depth = 1u32;
                                    while !self.is_eof() && depth > 0 {
                                        if self.peek() == Some(b' ') {
                                            self.advance();
                                            continue;
                                        }
                                        if self.peek() == Some(b'}') {
                                            depth -= 1;
                                            if depth == 0 {
                                                self.advance();
                                                break;
                                            }
                                        }
                                        if self.peek() == Some(b'{') {
                                            depth += 1;
                                        }
                                        if let Some(tok) = self.next_token() {
                                            inner_tokens.push(tok);
                                        }
                                    }
                                    break; // restart the outer loop for the next part
                                }
                                Some(_) => {
                                    let ch = self.next_char();
                                    if let Some(c) = ch {
                                        part_content.push(c);
                                    }
                                }
                            }
                        }
                    }
                }
                Some(b'"') => {
                    self.advance(); // closing "
                    break;
                }
                Some(_) => {
                    // Handle UTF-8 properly
                    let ch_start = self.pos;
                    let ch = self.next_char();
                    if let Some(c) = ch {
                        content.push(c);
                    } else {
                        self.diagnostics.push(Diagnostic::error(
                            "E0007",
                            "syntax_error",
                            "invalid UTF-8 in string",
                            &self.file,
                            Span::new(ch_start as u32, self.pos as u32),
                            self.source,
                        ));
                    }
                }
            }
        }

        // No interpolation — emit plain StringLit
        Some(Token {
            kind: TokenKind::StringLit(content),
            span: Span::new(start as u32, self.pos as u32),
        })
    }

    fn lex_char(&mut self, start: usize) -> Option<Token> {
        self.advance(); // opening '
        let ch = match self.peek() {
            Some(b'\\') => {
                self.advance();
                match self.peek() {
                    Some(b'n') => { self.advance(); '\n' }
                    Some(b't') => { self.advance(); '\t' }
                    Some(b'r') => { self.advance(); '\r' }
                    Some(b'\\') => { self.advance(); '\\' }
                    Some(b'\'') => { self.advance(); '\'' }
                    Some(b'0') => { self.advance(); '\0' }
                    _ => {
                        self.diagnostics.push(Diagnostic::error(
                            "E0006",
                            "syntax_error",
                            "invalid escape sequence in char literal",
                            &self.file,
                            Span::new((self.pos - 1) as u32, (self.pos + 1) as u32),
                            self.source,
                        ));
                        self.advance();
                        '\0'
                    }
                }
            }
            Some(_) => {
                let c = self.next_char().unwrap_or('\0');
                c
            }
            None => {
                self.diagnostics.push(Diagnostic::error(
                    "E0008",
                    "syntax_error",
                    "unterminated character literal",
                    &self.file,
                    Span::new(start as u32, self.pos as u32),
                    self.source,
                ));
                return None;
            }
        };

        if self.peek() == Some(b'\'') {
            self.advance();
        } else {
            self.diagnostics.push(Diagnostic::error(
                "E0008",
                "syntax_error",
                "unterminated character literal",
                &self.file,
                Span::new(start as u32, self.pos as u32),
                self.source,
            ));
        }

        Some(Token {
            kind: TokenKind::CharLit(ch),
            span: Span::new(start as u32, self.pos as u32),
        })
    }

    // --- Helper methods ---

    /// Returns true if the token kind is a trailing operator that triggers line continuation.
    fn is_continuation_op(kind: &TokenKind) -> bool {
        matches!(
            kind,
            TokenKind::Plus
                | TokenKind::Minus
                | TokenKind::Star
                | TokenKind::Slash
                | TokenKind::Percent
                | TokenKind::Eq
                | TokenKind::EqEq
                | TokenKind::BangEq
                | TokenKind::Lt
                | TokenKind::LtEq
                | TokenKind::Gt
                | TokenKind::GtEq
                | TokenKind::AmpAmp
                | TokenKind::PipePipe
                | TokenKind::Arrow
                | TokenKind::FatArrow
                | TokenKind::Dot
                | TokenKind::Comma
        )
    }

    fn is_eof(&self) -> bool {
        self.pos >= self.bytes.len()
    }

    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.pos).copied()
    }

    fn peek_at(&self, offset: usize) -> Option<u8> {
        self.bytes.get(self.pos + offset).copied()
    }

    fn advance(&mut self) {
        if self.pos < self.bytes.len() {
            self.pos += 1;
        }
    }

    /// Advance through a full UTF-8 character and return it.
    fn next_char(&mut self) -> Option<char> {
        let rest = &self.source[self.pos..];
        let ch = rest.chars().next()?;
        self.pos += ch.len_utf8();
        Some(ch)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lex(source: &str) -> Vec<Token> {
        let lexer = Lexer::new(source, "test.ax");
        let (tokens, _) = lexer.tokenize();
        tokens
    }

    fn token_kinds(source: &str) -> Vec<TokenKind> {
        lex(source).into_iter().map(|t| t.kind).collect()
    }

    #[test]
    fn test_keywords() {
        let kinds = token_kinds("fn let mut");
        assert_eq!(
            kinds,
            vec![TokenKind::Fn, TokenKind::Let, TokenKind::Mut, TokenKind::Eof]
        );
    }

    #[test]
    fn test_identifiers() {
        let kinds = token_kinds("foo bar_baz");
        assert_eq!(
            kinds,
            vec![
                TokenKind::Ident("foo".into()),
                TokenKind::Ident("bar_baz".into()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_type_identifiers() {
        let kinds = token_kinds("Vec Option");
        assert_eq!(
            kinds,
            vec![
                TokenKind::TypeIdent("Vec".into()),
                TokenKind::TypeIdent("Option".into()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_primitive_type_as_ident() {
        // Primitive types like i64, str are now lowercase identifiers
        let kinds = token_kinds("i64 str bool");
        assert_eq!(
            kinds,
            vec![
                TokenKind::Ident("i64".into()),
                TokenKind::Ident("str".into()),
                TokenKind::Ident("bool".into()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_number_literals() {
        let kinds = token_kinds("42 3.14 0xff 1_000_i32");
        assert_eq!(
            kinds,
            vec![
                TokenKind::IntLit("42".into()),
                TokenKind::FloatLit("3.14".into()),
                TokenKind::IntLit("0xff".into()),
                TokenKind::IntLit("1_000_i32".into()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_string_literal() {
        let kinds = token_kinds(r#""hello""#);
        assert_eq!(
            kinds,
            vec![TokenKind::StringLit("hello".into()), TokenKind::Eof]
        );
    }

    #[test]
    fn test_operators() {
        let kinds = token_kinds("+ - -> => == != ?");
        assert_eq!(
            kinds,
            vec![
                TokenKind::Plus,
                TokenKind::Minus,
                TokenKind::Arrow,
                TokenKind::FatArrow,
                TokenKind::EqEq,
                TokenKind::BangEq,
                TokenKind::Question,
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_indentation() {
        let source = "fn foo()\n    let x = 1\n";
        let kinds = token_kinds(source);
        assert!(kinds.contains(&TokenKind::Indent));
        assert!(kinds.contains(&TokenKind::Dedent));
    }

    #[test]
    fn test_comments() {
        let kinds = token_kinds("// this is a comment\n/// doc comment\n");
        assert!(matches!(kinds[0], TokenKind::LineComment(_)));
        assert!(matches!(kinds[2], TokenKind::DocComment(_)));
    }

    #[test]
    fn test_simple_function() {
        let source = "fn add(a: i64, b: i64) -> i64\n    a + b\n";
        let (tokens, diagnostics) = Lexer::new(source, "test.ax").tokenize();
        assert!(diagnostics.is_empty(), "unexpected errors: {:?}", diagnostics);
        let kinds: Vec<_> = tokens.iter().map(|t| &t.kind).collect();
        assert_eq!(kinds[0], &TokenKind::Fn);
        assert_eq!(kinds[1], &TokenKind::Ident("add".into()));
    }

    #[test]
    fn test_hash_lbrace() {
        let kinds = token_kinds("#{1, 2}");
        assert_eq!(
            kinds,
            vec![
                TokenKind::HashLBrace,
                TokenKind::IntLit("1".into()),
                TokenKind::Comma,
                TokenKind::IntLit("2".into()),
                TokenKind::RBrace,
                TokenKind::Eof,
            ]
        );
    }

    // --- String interpolation tests ---

    #[test]
    fn test_string_interp_simple() {
        let kinds = token_kinds("\"Hello, {name}\"");
        assert!(matches!(kinds[0], TokenKind::StringInterpStart(ref s) if s == "Hello, "));
        assert!(matches!(kinds[1], TokenKind::Ident(ref s) if s == "name"));
        assert!(matches!(kinds[2], TokenKind::StringInterpEnd(ref s) if s == ""));
        assert_eq!(kinds[3], TokenKind::Eof);
    }

    #[test]
    fn test_string_no_interp() {
        let kinds = token_kinds("\"no interp\"");
        assert_eq!(kinds, vec![TokenKind::StringLit("no interp".into()), TokenKind::Eof]);
    }

    #[test]
    fn test_string_interp_multi() {
        let kinds = token_kinds("\"a {x} b {y} c\"");
        assert!(matches!(kinds[0], TokenKind::StringInterpStart(ref s) if s == "a "));
        assert!(matches!(kinds[1], TokenKind::Ident(ref s) if s == "x"));
        assert!(matches!(kinds[2], TokenKind::StringInterpPart(ref s) if s == " b "));
        assert!(matches!(kinds[3], TokenKind::Ident(ref s) if s == "y"));
        assert!(matches!(kinds[4], TokenKind::StringInterpEnd(ref s) if s == " c"));
        assert_eq!(kinds[5], TokenKind::Eof);
    }

    #[test]
    fn test_string_interp_escaped() {
        let kinds = token_kinds("\"\\{escaped}\"");
        assert_eq!(kinds, vec![TokenKind::StringLit("{escaped}".into()), TokenKind::Eof]);
    }

    #[test]
    fn test_string_interp_expr() {
        let kinds = token_kinds("\"{a + b}\"");
        assert!(matches!(kinds[0], TokenKind::StringInterpStart(ref s) if s == ""));
        assert!(matches!(kinds[1], TokenKind::Ident(ref s) if s == "a"));
        assert_eq!(kinds[2], TokenKind::Plus);
        assert!(matches!(kinds[3], TokenKind::Ident(ref s) if s == "b"));
        assert!(matches!(kinds[4], TokenKind::StringInterpEnd(ref s) if s == ""));
        assert_eq!(kinds[5], TokenKind::Eof);
    }

    #[test]
    fn test_line_continuation_operator() {
        // Trailing `+` should suppress newline
        let kinds = token_kinds("a +\n    b");
        assert_eq!(kinds, vec![
            TokenKind::Ident("a".into()),
            TokenKind::Plus,
            TokenKind::Ident("b".into()),
            TokenKind::Eof,
        ]);
    }

    #[test]
    fn test_line_continuation_dot() {
        // Trailing `.` should suppress newline
        let kinds = token_kinds("foo.\n    bar");
        assert_eq!(kinds, vec![
            TokenKind::Ident("foo".into()),
            TokenKind::Dot,
            TokenKind::Ident("bar".into()),
            TokenKind::Eof,
        ]);
    }

    #[test]
    fn test_no_line_continuation() {
        // Non-operator trailing token should NOT suppress newline
        let kinds = token_kinds("foo\nbar");
        assert_eq!(kinds, vec![
            TokenKind::Ident("foo".into()),
            TokenKind::Newline,
            TokenKind::Ident("bar".into()),
            TokenKind::Eof,
        ]);
    }
}
