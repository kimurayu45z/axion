use axion_diagnostics::Diagnostic;
use axion_lexer::Lexer;
use axion_syntax::*;

/// Parse Axion source code into an AST.
pub fn parse(source: &str, file: &str) -> (SourceFile, Vec<Diagnostic>) {
    let lexer = Lexer::new(source, file);
    let (tokens, mut diagnostics) = lexer.tokenize();
    let mut parser = Parser::new(tokens, file, source);
    let source_file = parser.parse_source_file();
    diagnostics.extend(parser.diagnostics);
    (source_file, diagnostics)
}

/// The Axion parser: transforms a token stream into an AST.
struct Parser {
    tokens: Vec<Token>,
    pos: usize,
    file: String,
    source: String,
    diagnostics: Vec<Diagnostic>,
}

impl Parser {
    fn new(tokens: Vec<Token>, file: &str, source: &str) -> Self {
        Self {
            tokens,
            pos: 0,
            file: file.to_string(),
            source: source.to_string(),
            diagnostics: Vec::new(),
        }
    }

    fn parse_source_file(&mut self) -> SourceFile {
        let mut items = Vec::new();
        self.skip_newlines();

        while !self.is_at_end() {
            if let Some(item) = self.parse_item() {
                items.push(item);
            } else {
                // Skip to next potential item
                self.advance();
            }
            self.skip_newlines();
        }

        SourceFile { items }
    }

    fn parse_item(&mut self) -> Option<Item> {
        self.skip_newlines();

        let start_span = self.current_span();

        // Check for `pub` modifier
        let is_pub = self.check(&TokenKind::Pub);
        if is_pub {
            self.advance();
            self.skip_newlines();
        }

        match self.peek_kind() {
            Some(TokenKind::Fn) => {
                let fn_def = self.parse_fn_def(is_pub)?;
                Some(Item {
                    span: start_span.merge(self.prev_span()),
                    kind: ItemKind::Function(fn_def),
                })
            }
            Some(TokenKind::Struct) => {
                let struct_def = self.parse_struct_def(is_pub)?;
                Some(Item {
                    span: start_span.merge(self.prev_span()),
                    kind: ItemKind::Struct(struct_def),
                })
            }
            Some(TokenKind::Enum) => {
                let enum_def = self.parse_enum_def(is_pub)?;
                Some(Item {
                    span: start_span.merge(self.prev_span()),
                    kind: ItemKind::Enum(enum_def),
                })
            }
            Some(TokenKind::Test) => {
                let test_def = self.parse_test_def()?;
                Some(Item {
                    span: start_span.merge(self.prev_span()),
                    kind: ItemKind::Test(test_def),
                })
            }
            Some(TokenKind::Use) => {
                let use_decl = self.parse_use_decl()?;
                Some(Item {
                    span: start_span.merge(self.prev_span()),
                    kind: ItemKind::Use(use_decl),
                })
            }
            _ => {
                if is_pub {
                    self.error("expected `fn`, `struct`, `enum`, or `use` after `pub`");
                }
                None
            }
        }
    }

    fn parse_fn_def(&mut self, is_pub: bool) -> Option<FnDef> {
        self.expect(&TokenKind::Fn)?;

        let name = self.expect_ident()?;
        self.expect(&TokenKind::LParen)?;
        let params = self.parse_params()?;
        self.expect(&TokenKind::RParen)?;

        let return_type = if self.check(&TokenKind::Arrow) {
            self.advance();
            Some(self.parse_type_expr()?)
        } else {
            None
        };

        let effects = if self.check(&TokenKind::With) {
            self.advance();
            self.parse_effect_list()?
        } else {
            Vec::new()
        };

        self.skip_newlines();
        let body = self.parse_block()?;

        Some(FnDef {
            is_pub,
            name,
            params,
            return_type,
            effects,
            body,
        })
    }

    fn parse_params(&mut self) -> Option<Vec<Param>> {
        let mut params = Vec::new();

        if self.check(&TokenKind::RParen) {
            return Some(params);
        }

        loop {
            let param_span = self.current_span();
            let is_mut = self.check(&TokenKind::Mut);
            if is_mut {
                self.advance();
            }
            let name = self.expect_ident()?;
            self.expect(&TokenKind::Colon)?;
            let ty = self.parse_type_expr()?;

            params.push(Param {
                name,
                ty,
                is_mut,
                span: param_span.merge(self.prev_span()),
            });

            if !self.check(&TokenKind::Comma) {
                break;
            }
            self.advance(); // consume comma
        }

        Some(params)
    }

    fn parse_type_expr(&mut self) -> Option<TypeExpr> {
        let span = self.current_span();

        // Tuple type: {T1, T2, ...} or {} for unit
        if self.check(&TokenKind::LBrace) {
            self.advance();
            if self.check(&TokenKind::RBrace) {
                self.advance();
                return Some(TypeExpr::Tuple {
                    elements: Vec::new(),
                    span: span.merge(self.prev_span()),
                });
            }
            let mut elements = vec![self.parse_type_expr()?];
            while self.check(&TokenKind::Comma) {
                self.advance();
                elements.push(self.parse_type_expr()?);
            }
            self.expect(&TokenKind::RBrace)?;
            return Some(TypeExpr::Tuple {
                elements,
                span: span.merge(self.prev_span()),
            });
        }

        // Primitive type (lowercase ident): i64, str, bool, etc.
        if let Some(TokenKind::Ident(ref s)) = self.peek_kind() {
            if TokenKind::is_primitive_type(s) {
                let name = s.clone();
                self.advance();
                return Some(TypeExpr::Named {
                    name,
                    args: Vec::new(),
                    span: span.merge(self.prev_span()),
                });
            }
        }

        // Named type (PascalCase)
        let name = self.expect_type_ident()?;
        let mut args = Vec::new();

        // Type arguments: [T1, T2, ...]
        if self.check(&TokenKind::LBracket) {
            self.advance();
            args.push(self.parse_type_expr()?);
            while self.check(&TokenKind::Comma) {
                self.advance();
                args.push(self.parse_type_expr()?);
            }
            self.expect(&TokenKind::RBracket)?;
        }

        Some(TypeExpr::Named {
            name,
            args,
            span: span.merge(self.prev_span()),
        })
    }

    fn parse_effect_list(&mut self) -> Option<Vec<String>> {
        let mut effects = Vec::new();
        effects.push(self.expect_type_ident()?);
        while self.check(&TokenKind::Comma) {
            self.advance();
            effects.push(self.expect_type_ident()?);
        }
        Some(effects)
    }

    fn parse_block(&mut self) -> Option<Vec<Stmt>> {
        if !self.check(&TokenKind::Indent) {
            return Some(Vec::new());
        }
        self.advance(); // consume INDENT

        let mut stmts = Vec::new();
        loop {
            self.skip_newlines();
            if self.check(&TokenKind::Dedent) || self.is_at_end() {
                break;
            }
            if let Some(stmt) = self.parse_stmt() {
                stmts.push(stmt);
            } else {
                self.advance();
            }
        }

        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        Some(stmts)
    }

    fn parse_stmt(&mut self) -> Option<Stmt> {
        let span = self.current_span();

        match self.peek_kind() {
            Some(TokenKind::Let) => {
                self.advance();
                let is_mut = self.check(&TokenKind::Mut);
                if is_mut {
                    self.advance();
                }
                let name = self.expect_ident()?;

                let ty = if self.check(&TokenKind::Colon) {
                    self.advance();
                    Some(self.parse_type_expr()?)
                } else {
                    None
                };

                self.expect(&TokenKind::Eq)?;
                let value = self.parse_expr()?;

                Some(Stmt {
                    kind: StmtKind::Let {
                        is_mut,
                        name,
                        ty,
                        value,
                    },
                    span: span.merge(self.prev_span()),
                })
            }
            Some(TokenKind::Return) => {
                self.advance();
                let value = if self.check(&TokenKind::Newline) || self.check(&TokenKind::Dedent) || self.is_at_end() {
                    None
                } else {
                    Some(self.parse_expr()?)
                };
                Some(Stmt {
                    kind: StmtKind::Return(value),
                    span: span.merge(self.prev_span()),
                })
            }
            _ => {
                let expr = self.parse_expr()?;
                Some(Stmt {
                    kind: StmtKind::Expr(expr),
                    span: span.merge(self.prev_span()),
                })
            }
        }
    }

    fn parse_expr(&mut self) -> Option<Expr> {
        self.parse_or_expr()
    }

    fn parse_or_expr(&mut self) -> Option<Expr> {
        let mut left = self.parse_and_expr()?;

        while self.check(&TokenKind::PipePipe) {
            self.advance();
            let right = self.parse_and_expr()?;
            let span = left.span.merge(right.span);
            left = Expr {
                kind: ExprKind::BinOp {
                    op: BinOp::Or,
                    lhs: Box::new(left),
                    rhs: Box::new(right),
                },
                span,
            };
        }

        Some(left)
    }

    fn parse_and_expr(&mut self) -> Option<Expr> {
        let mut left = self.parse_comparison_expr()?;

        while self.check(&TokenKind::AmpAmp) {
            self.advance();
            let right = self.parse_comparison_expr()?;
            let span = left.span.merge(right.span);
            left = Expr {
                kind: ExprKind::BinOp {
                    op: BinOp::And,
                    lhs: Box::new(left),
                    rhs: Box::new(right),
                },
                span,
            };
        }

        Some(left)
    }

    fn parse_comparison_expr(&mut self) -> Option<Expr> {
        let mut left = self.parse_pipe_expr()?;

        loop {
            let op = match self.peek_kind() {
                Some(TokenKind::EqEq) => BinOp::Eq,
                Some(TokenKind::BangEq) => BinOp::NotEq,
                Some(TokenKind::Lt) => BinOp::Lt,
                Some(TokenKind::LtEq) => BinOp::LtEq,
                Some(TokenKind::Gt) => BinOp::Gt,
                Some(TokenKind::GtEq) => BinOp::GtEq,
                _ => break,
            };
            self.advance();
            let right = self.parse_pipe_expr()?;
            let span = left.span.merge(right.span);
            left = Expr {
                kind: ExprKind::BinOp {
                    op,
                    lhs: Box::new(left),
                    rhs: Box::new(right),
                },
                span,
            };
        }

        Some(left)
    }

    fn parse_pipe_expr(&mut self) -> Option<Expr> {
        let mut left = self.parse_additive_expr()?;

        while self.check(&TokenKind::PipeGt) {
            self.advance();
            let right = self.parse_additive_expr()?;
            let span = left.span.merge(right.span);
            left = Expr {
                kind: ExprKind::BinOp {
                    op: BinOp::Pipe,
                    lhs: Box::new(left),
                    rhs: Box::new(right),
                },
                span,
            };
        }

        Some(left)
    }

    fn parse_additive_expr(&mut self) -> Option<Expr> {
        let mut left = self.parse_multiplicative_expr()?;

        loop {
            let op = match self.peek_kind() {
                Some(TokenKind::Plus) => BinOp::Add,
                Some(TokenKind::Minus) => BinOp::Sub,
                _ => break,
            };
            self.advance();
            let right = self.parse_multiplicative_expr()?;
            let span = left.span.merge(right.span);
            left = Expr {
                kind: ExprKind::BinOp {
                    op,
                    lhs: Box::new(left),
                    rhs: Box::new(right),
                },
                span,
            };
        }

        Some(left)
    }

    fn parse_multiplicative_expr(&mut self) -> Option<Expr> {
        let mut left = self.parse_unary_expr()?;

        loop {
            let op = match self.peek_kind() {
                Some(TokenKind::Star) => BinOp::Mul,
                Some(TokenKind::Slash) => BinOp::Div,
                Some(TokenKind::Percent) => BinOp::Mod,
                _ => break,
            };
            self.advance();
            let right = self.parse_unary_expr()?;
            let span = left.span.merge(right.span);
            left = Expr {
                kind: ExprKind::BinOp {
                    op,
                    lhs: Box::new(left),
                    rhs: Box::new(right),
                },
                span,
            };
        }

        Some(left)
    }

    fn parse_unary_expr(&mut self) -> Option<Expr> {
        let span = self.current_span();
        match self.peek_kind() {
            Some(TokenKind::Minus) => {
                self.advance();
                let operand = self.parse_postfix_expr()?;
                Some(Expr {
                    span: span.merge(operand.span),
                    kind: ExprKind::UnaryOp {
                        op: UnaryOp::Neg,
                        operand: Box::new(operand),
                    },
                })
            }
            Some(TokenKind::Bang) => {
                self.advance();
                let operand = self.parse_postfix_expr()?;
                Some(Expr {
                    span: span.merge(operand.span),
                    kind: ExprKind::UnaryOp {
                        op: UnaryOp::Not,
                        operand: Box::new(operand),
                    },
                })
            }
            _ => self.parse_postfix_expr(),
        }
    }

    fn parse_postfix_expr(&mut self) -> Option<Expr> {
        let mut expr = self.parse_primary_expr()?;

        loop {
            if self.check(&TokenKind::Dot) {
                self.advance();
                let name = self.expect_ident()?;
                let span = expr.span.merge(self.prev_span());
                expr = Expr {
                    kind: ExprKind::Field {
                        expr: Box::new(expr),
                        name,
                    },
                    span,
                };
            } else if self.check(&TokenKind::LParen) {
                self.advance();
                let mut args = Vec::new();
                if !self.check(&TokenKind::RParen) {
                    args.push(self.parse_expr()?);
                    while self.check(&TokenKind::Comma) {
                        self.advance();
                        args.push(self.parse_expr()?);
                    }
                }
                self.expect(&TokenKind::RParen)?;
                let span = expr.span.merge(self.prev_span());
                expr = Expr {
                    kind: ExprKind::Call {
                        func: Box::new(expr),
                        args,
                    },
                    span,
                };
            } else {
                break;
            }
        }

        Some(expr)
    }

    fn parse_primary_expr(&mut self) -> Option<Expr> {
        let span = self.current_span();

        match self.peek_kind() {
            Some(TokenKind::IntLit(_)) => {
                if let TokenKind::IntLit(s) = self.advance_and_get() {
                    // Strip underscores and type suffix for parsing
                    let clean: String = s.chars().take_while(|c| *c != '_' || s.contains("0x") || s.contains("0b")).collect();
                    let num_str: String = clean.replace('_', "");
                    let value = if num_str.starts_with("0x") {
                        i128::from_str_radix(&num_str[2..], 16).unwrap_or(0)
                    } else if num_str.starts_with("0b") {
                        i128::from_str_radix(&num_str[2..], 2).unwrap_or(0)
                    } else if num_str.starts_with("0o") {
                        i128::from_str_radix(&num_str[2..], 8).unwrap_or(0)
                    } else {
                        num_str.parse().unwrap_or(0)
                    };
                    Some(Expr {
                        kind: ExprKind::IntLit(value),
                        span,
                    })
                } else {
                    None
                }
            }
            Some(TokenKind::FloatLit(_)) => {
                if let TokenKind::FloatLit(s) = self.advance_and_get() {
                    let clean: String = s.replace('_', "");
                    let value: f64 = clean.parse().unwrap_or(0.0);
                    Some(Expr {
                        kind: ExprKind::FloatLit(value),
                        span,
                    })
                } else {
                    None
                }
            }
            Some(TokenKind::StringLit(_)) => {
                if let TokenKind::StringLit(s) = self.advance_and_get() {
                    Some(Expr {
                        kind: ExprKind::StringLit(s),
                        span,
                    })
                } else {
                    None
                }
            }
            Some(TokenKind::CharLit(_)) => {
                if let TokenKind::CharLit(c) = self.advance_and_get() {
                    Some(Expr {
                        kind: ExprKind::IntLit(c as i128),
                        span,
                    })
                } else {
                    None
                }
            }
            Some(TokenKind::True) => {
                self.advance();
                Some(Expr {
                    kind: ExprKind::BoolLit(true),
                    span,
                })
            }
            Some(TokenKind::False) => {
                self.advance();
                Some(Expr {
                    kind: ExprKind::BoolLit(false),
                    span,
                })
            }
            Some(TokenKind::Ident(_)) => {
                if let TokenKind::Ident(name) = self.advance_and_get() {
                    Some(Expr {
                        kind: ExprKind::Ident(name),
                        span,
                    })
                } else {
                    None
                }
            }
            Some(TokenKind::TypeIdent(_)) => {
                if let TokenKind::TypeIdent(name) = self.advance_and_get() {
                    // Check if followed by #{ for struct literal: TypeName #{field: value}
                    if self.check(&TokenKind::HashLBrace) {
                        self.advance(); // consume #{
                        let mut fields = Vec::new();
                        if !self.check(&TokenKind::RBrace) {
                            loop {
                                let f_span = self.current_span();
                                let f_name = self.expect_ident()?;
                                self.expect(&TokenKind::Colon)?;
                                let f_value = self.parse_expr()?;
                                fields.push(FieldInit {
                                    name: f_name,
                                    value: f_value,
                                    span: f_span.merge(self.prev_span()),
                                });
                                if !self.check(&TokenKind::Comma) {
                                    break;
                                }
                                self.advance();
                            }
                        }
                        self.expect(&TokenKind::RBrace)?;
                        Some(Expr {
                            kind: ExprKind::StructLit { name, fields },
                            span: span.merge(self.prev_span()),
                        })
                    } else {
                        Some(Expr {
                            kind: ExprKind::Ident(name),
                            span,
                        })
                    }
                } else {
                    None
                }
            }
            Some(TokenKind::If) => self.parse_if_expr(),
            Some(TokenKind::LParen) => {
                self.advance();
                let expr = self.parse_expr()?;
                self.expect(&TokenKind::RParen)?;
                Some(expr)
            }
            // Tuple literal: {} or {expr, expr, ...}
            Some(TokenKind::LBrace) => {
                self.advance();
                if self.check(&TokenKind::RBrace) {
                    self.advance();
                    return Some(Expr {
                        kind: ExprKind::TupleLit(Vec::new()),
                        span: span.merge(self.prev_span()),
                    });
                }
                let mut elements = vec![self.parse_expr()?];
                while self.check(&TokenKind::Comma) {
                    self.advance();
                    elements.push(self.parse_expr()?);
                }
                self.expect(&TokenKind::RBrace)?;
                Some(Expr {
                    kind: ExprKind::TupleLit(elements),
                    span: span.merge(self.prev_span()),
                })
            }
            // #{...}: struct literal, map literal, or set literal
            Some(TokenKind::HashLBrace) => self.parse_hash_brace_expr(),
            _ => {
                self.error("expected expression");
                None
            }
        }
    }

    fn parse_if_expr(&mut self) -> Option<Expr> {
        let span = self.current_span();
        self.expect(&TokenKind::If)?;

        let cond = self.parse_expr()?;
        self.skip_newlines();
        let then_branch = self.parse_block()?;

        let else_branch = if self.check(&TokenKind::Else) {
            self.advance();
            self.skip_newlines();
            if self.check(&TokenKind::If) {
                // else if => wrap in a block with single if-expr stmt
                let if_expr = self.parse_if_expr()?;
                Some(vec![Stmt {
                    span: if_expr.span,
                    kind: StmtKind::Expr(if_expr),
                }])
            } else {
                Some(self.parse_block()?)
            }
        } else {
            None
        };

        Some(Expr {
            span: span.merge(self.prev_span()),
            kind: ExprKind::If {
                cond: Box::new(cond),
                then_branch,
                else_branch,
            },
        })
    }

    /// Parse `#{...}` — disambiguate between map and set literal.
    /// Map: `#{key => value, ...}`
    /// Set: `#{expr, ...}`
    fn parse_hash_brace_expr(&mut self) -> Option<Expr> {
        let span = self.current_span();
        self.advance(); // consume #{

        // Empty: #{}  → empty map
        if self.check(&TokenKind::RBrace) {
            self.advance();
            return Some(Expr {
                kind: ExprKind::MapLit(Vec::new()),
                span: span.merge(self.prev_span()),
            });
        }

        // Parse first element, then look for => to disambiguate
        let first = self.parse_expr()?;

        if self.check(&TokenKind::FatArrow) {
            // Map literal: #{key => value, ...}
            self.advance(); // consume =>
            let value = self.parse_expr()?;
            let mut entries = vec![MapEntry {
                span: first.span.merge(value.span),
                key: first,
                value,
            }];
            while self.check(&TokenKind::Comma) {
                self.advance();
                if self.check(&TokenKind::RBrace) {
                    break; // trailing comma
                }
                let key = self.parse_expr()?;
                self.expect(&TokenKind::FatArrow)?;
                let val = self.parse_expr()?;
                entries.push(MapEntry {
                    span: key.span.merge(val.span),
                    key,
                    value: val,
                });
            }
            self.expect(&TokenKind::RBrace)?;
            Some(Expr {
                kind: ExprKind::MapLit(entries),
                span: span.merge(self.prev_span()),
            })
        } else {
            // Set literal: #{expr, ...}
            let mut elements = vec![first];
            while self.check(&TokenKind::Comma) {
                self.advance();
                if self.check(&TokenKind::RBrace) {
                    break; // trailing comma
                }
                elements.push(self.parse_expr()?);
            }
            self.expect(&TokenKind::RBrace)?;
            Some(Expr {
                kind: ExprKind::SetLit(elements),
                span: span.merge(self.prev_span()),
            })
        }
    }

    fn parse_struct_def(&mut self, is_pub: bool) -> Option<StructDef> {
        self.expect(&TokenKind::Struct)?;
        let name = self.expect_type_ident()?;
        self.skip_newlines();

        let mut fields = Vec::new();
        if self.check(&TokenKind::Indent) {
            self.advance();
            loop {
                self.skip_newlines();
                if self.check(&TokenKind::Dedent) || self.is_at_end() {
                    break;
                }
                let field_span = self.current_span();
                let field_pub = self.check(&TokenKind::Pub);
                if field_pub {
                    self.advance();
                }
                let field_mut = self.check(&TokenKind::Mut);
                if field_mut {
                    self.advance();
                }
                let field_name = self.expect_ident()?;
                self.expect(&TokenKind::Colon)?;
                let field_ty = self.parse_type_expr()?;
                fields.push(FieldDef {
                    is_pub: field_pub,
                    is_mut: field_mut,
                    name: field_name,
                    ty: field_ty,
                    span: field_span.merge(self.prev_span()),
                });
            }
            if self.check(&TokenKind::Dedent) {
                self.advance();
            }
        }

        Some(StructDef {
            is_pub,
            name,
            fields,
        })
    }

    fn parse_enum_def(&mut self, is_pub: bool) -> Option<EnumDef> {
        self.expect(&TokenKind::Enum)?;
        let name = self.expect_type_ident()?;
        self.skip_newlines();

        let mut variants = Vec::new();
        if self.check(&TokenKind::Indent) {
            self.advance();
            loop {
                self.skip_newlines();
                if self.check(&TokenKind::Dedent) || self.is_at_end() {
                    break;
                }
                let variant_span = self.current_span();
                let variant_name = self.expect_type_ident()?;

                let mut fields = Vec::new();
                if self.check(&TokenKind::LParen) {
                    self.advance();
                    if !self.check(&TokenKind::RParen) {
                        loop {
                            let f_span = self.current_span();
                            let f_name = self.expect_ident()?;
                            self.expect(&TokenKind::Colon)?;
                            let f_ty = self.parse_type_expr()?;
                            fields.push(FieldDef {
                                is_pub: false,
                                is_mut: false,
                                name: f_name,
                                ty: f_ty,
                                span: f_span.merge(self.prev_span()),
                            });
                            if !self.check(&TokenKind::Comma) {
                                break;
                            }
                            self.advance();
                        }
                    }
                    self.expect(&TokenKind::RParen)?;
                }

                variants.push(VariantDef {
                    name: variant_name,
                    fields,
                    span: variant_span.merge(self.prev_span()),
                });
            }
            if self.check(&TokenKind::Dedent) {
                self.advance();
            }
        }

        Some(EnumDef {
            is_pub,
            name,
            variants,
        })
    }

    fn parse_test_def(&mut self) -> Option<TestDef> {
        self.expect(&TokenKind::Test)?;

        let name = match self.peek_kind() {
            Some(TokenKind::StringLit(_)) => {
                if let TokenKind::StringLit(s) = self.advance_and_get() {
                    s
                } else {
                    return None;
                }
            }
            _ => {
                self.error("expected string literal after `test`");
                return None;
            }
        };

        self.skip_newlines();
        let body = self.parse_block()?;

        Some(TestDef { name, body })
    }

    fn parse_use_decl(&mut self) -> Option<UseDecl> {
        let span = self.current_span();
        self.expect(&TokenKind::Use)?;

        let mut path = Vec::new();
        // First segment can be an ident or type ident
        match self.peek_kind() {
            Some(TokenKind::Ident(_)) => {
                if let TokenKind::Ident(s) = self.advance_and_get() {
                    path.push(s);
                }
            }
            Some(TokenKind::TypeIdent(_)) => {
                if let TokenKind::TypeIdent(s) = self.advance_and_get() {
                    path.push(s);
                }
            }
            _ => {
                self.error("expected module path after `use`");
                return None;
            }
        }

        while self.check(&TokenKind::Dot) {
            self.advance();
            match self.peek_kind() {
                Some(TokenKind::Ident(_)) => {
                    if let TokenKind::Ident(s) = self.advance_and_get() {
                        path.push(s);
                    }
                }
                Some(TokenKind::TypeIdent(_)) => {
                    if let TokenKind::TypeIdent(s) = self.advance_and_get() {
                        path.push(s);
                    }
                }
                _ => {
                    self.error("expected identifier in use path");
                    break;
                }
            }
        }

        Some(UseDecl {
            path,
            span: span.merge(self.prev_span()),
        })
    }

    // --- Token helpers ---

    fn peek_kind(&self) -> Option<TokenKind> {
        self.tokens.get(self.pos).map(|t| t.kind.clone())
    }

    fn check(&self, kind: &TokenKind) -> bool {
        self.peek_kind().as_ref() == Some(kind)
    }

    fn check_matches(&self, kind: &TokenKind) -> bool {
        match (self.peek_kind().as_ref(), kind) {
            (Some(TokenKind::Ident(_)), TokenKind::Ident(_)) => true,
            (Some(TokenKind::TypeIdent(_)), TokenKind::TypeIdent(_)) => true,
            (Some(TokenKind::IntLit(_)), TokenKind::IntLit(_)) => true,
            (Some(TokenKind::FloatLit(_)), TokenKind::FloatLit(_)) => true,
            (Some(TokenKind::StringLit(_)), TokenKind::StringLit(_)) => true,
            (a, b) => a == Some(b),
        }
    }

    fn advance(&mut self) {
        if self.pos < self.tokens.len() {
            self.pos += 1;
        }
    }

    fn advance_and_get(&mut self) -> TokenKind {
        let kind = self.tokens[self.pos].kind.clone();
        self.advance();
        kind
    }

    fn current_span(&self) -> Span {
        self.tokens
            .get(self.pos)
            .map(|t| t.span)
            .unwrap_or(Span::dummy())
    }

    fn prev_span(&self) -> Span {
        if self.pos > 0 {
            self.tokens[self.pos - 1].span
        } else {
            Span::dummy()
        }
    }

    fn is_at_end(&self) -> bool {
        self.pos >= self.tokens.len()
            || matches!(self.tokens.get(self.pos), Some(Token { kind: TokenKind::Eof, .. }))
    }

    fn skip_newlines(&mut self) {
        while self.peek_kind() == Some(TokenKind::Newline) {
            self.advance();
        }
        // Also skip line comments and doc comments between items
        while matches!(
            self.peek_kind(),
            Some(TokenKind::LineComment(_)) | Some(TokenKind::DocComment(_))
        ) {
            self.advance();
            while self.peek_kind() == Some(TokenKind::Newline) {
                self.advance();
            }
        }
    }

    fn expect(&mut self, kind: &TokenKind) -> Option<()> {
        if self.check_matches(kind) {
            self.advance();
            Some(())
        } else {
            self.error(&format!("expected {:?}", kind));
            None
        }
    }

    fn expect_ident(&mut self) -> Option<String> {
        match self.peek_kind() {
            Some(TokenKind::Ident(s)) => {
                self.advance();
                Some(s)
            }
            _ => {
                self.error("expected identifier");
                None
            }
        }
    }

    fn expect_type_ident(&mut self) -> Option<String> {
        match self.peek_kind() {
            Some(TokenKind::TypeIdent(s)) => {
                self.advance();
                Some(s)
            }
            _ => {
                self.error("expected type identifier");
                None
            }
        }
    }

    fn error(&mut self, msg: &str) {
        let span = self.current_span();
        self.diagnostics.push(Diagnostic::error(
            "E0010",
            "parse_error",
            msg,
            &self.file,
            span,
            &self.source,
        ));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_fn_def() {
        let source = "fn add(a: i64, b: i64) -> i64\n    a + b\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        assert_eq!(file.items.len(), 1);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                assert_eq!(f.name, "add");
                assert_eq!(f.params.len(), 2);
                assert!(f.return_type.is_some());
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_let_binding() {
        let source = "fn main()\n    let x = 42\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        assert_eq!(file.items.len(), 1);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                assert_eq!(f.body.len(), 1);
                match &f.body[0].kind {
                    StmtKind::Let { name, value, .. } => {
                        assert_eq!(name, "x");
                        assert!(matches!(value.kind, ExprKind::IntLit(42)));
                    }
                    _ => panic!("expected let"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_struct() {
        let source = "struct User\n    name: str\n    age: u32\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        assert_eq!(file.items.len(), 1);
        match &file.items[0].kind {
            ItemKind::Struct(s) => {
                assert_eq!(s.name, "User");
                assert_eq!(s.fields.len(), 2);
            }
            _ => panic!("expected struct"),
        }
    }

    #[test]
    fn test_parse_enum() {
        let source = "enum Shape\n    Circle(radius: f64)\n    Point\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        assert_eq!(file.items.len(), 1);
        match &file.items[0].kind {
            ItemKind::Enum(e) => {
                assert_eq!(e.name, "Shape");
                assert_eq!(e.variants.len(), 2);
                assert_eq!(e.variants[0].name, "Circle");
                assert_eq!(e.variants[0].fields.len(), 1);
                assert_eq!(e.variants[1].name, "Point");
                assert_eq!(e.variants[1].fields.len(), 0);
            }
            _ => panic!("expected enum"),
        }
    }

    #[test]
    fn test_parse_with_effects() {
        let source = "fn read_file(path: str) -> str with IO\n    path\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                assert_eq!(f.effects, vec!["IO"]);
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_tuple_type() {
        let source = "fn pair() -> {i64, str}\n    {42, \"hello\"}\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.return_type {
                    Some(TypeExpr::Tuple { elements, .. }) => {
                        assert_eq!(elements.len(), 2);
                    }
                    other => panic!("expected tuple type, got {:?}", other),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_unit_type() {
        // {} is the unit type (empty tuple)
        let source = "fn noop() -> {}\n    {}\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.return_type {
                    Some(TypeExpr::Tuple { elements, .. }) => {
                        assert_eq!(elements.len(), 0);
                    }
                    other => panic!("expected empty tuple type, got {:?}", other),
                }
                // Body should contain a TupleLit with 0 elements
                match &f.body[0].kind {
                    StmtKind::Expr(expr) => {
                        assert!(matches!(expr.kind, ExprKind::TupleLit(ref elems) if elems.is_empty()));
                    }
                    _ => panic!("expected expr stmt"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_struct_literal() {
        let source = "fn main()\n    let u = User #{name: \"Alice\", age: 30}\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Let { value, .. } => {
                        match &value.kind {
                            ExprKind::StructLit { name, fields } => {
                                assert_eq!(name, "User");
                                assert_eq!(fields.len(), 2);
                                assert_eq!(fields[0].name, "name");
                                assert_eq!(fields[1].name, "age");
                            }
                            other => panic!("expected struct lit, got {:?}", other),
                        }
                    }
                    _ => panic!("expected let"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_map_literal() {
        let source = "fn main()\n    let m = #{\"a\" => 1, \"b\" => 2}\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Let { value, .. } => {
                        match &value.kind {
                            ExprKind::MapLit(entries) => {
                                assert_eq!(entries.len(), 2);
                            }
                            other => panic!("expected map lit, got {:?}", other),
                        }
                    }
                    _ => panic!("expected let"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_set_literal() {
        let source = "fn main()\n    let s = #{1, 2, 3}\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Let { value, .. } => {
                        match &value.kind {
                            ExprKind::SetLit(elements) => {
                                assert_eq!(elements.len(), 3);
                            }
                            other => panic!("expected set lit, got {:?}", other),
                        }
                    }
                    _ => panic!("expected let"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_binary_expr() {
        let source = "fn main()\n    let x = 1 + 2 * 3\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Let { value, .. } => {
                        // Should be Add(1, Mul(2, 3)) due to precedence
                        match &value.kind {
                            ExprKind::BinOp { op: BinOp::Add, rhs, .. } => {
                                assert!(matches!(rhs.kind, ExprKind::BinOp { op: BinOp::Mul, .. }));
                            }
                            _ => panic!("expected binop, got {:?}", value.kind),
                        }
                    }
                    _ => panic!("expected let"),
                }
            }
            _ => panic!("expected function"),
        }
    }
}
