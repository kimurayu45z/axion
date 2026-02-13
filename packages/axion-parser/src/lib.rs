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
            if let Some(impl_items) = self.try_parse_impl_block() {
                items.extend(impl_items);
            } else if let Some(item) = self.parse_item() {
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

        // Check for `pub` or `pub(pkg)` modifier
        let vis = self.parse_visibility();

        match self.peek_kind() {
            Some(TokenKind::Fn) => {
                // Disambiguate: fn Type.name (constructor), fn name (function)
                if self.is_constructor_def() {
                    let ctor_def = self.parse_constructor_def(vis)?;
                    Some(Item {
                        span: start_span.merge(self.prev_span()),
                        kind: ItemKind::Constructor(ctor_def),
                    })
                } else {
                    let fn_def = self.parse_fn_def(vis)?;
                    Some(Item {
                        span: start_span.merge(self.prev_span()),
                        kind: ItemKind::Function(fn_def),
                    })
                }
            }
            Some(TokenKind::Struct) => {
                let struct_def = self.parse_struct_def(vis)?;
                Some(Item {
                    span: start_span.merge(self.prev_span()),
                    kind: ItemKind::Struct(struct_def),
                })
            }
            Some(TokenKind::Enum) => {
                let enum_def = self.parse_enum_def(vis)?;
                Some(Item {
                    span: start_span.merge(self.prev_span()),
                    kind: ItemKind::Enum(enum_def),
                })
            }
            Some(TokenKind::Interface) => {
                let iface_def = self.parse_interface_def(vis)?;
                Some(Item {
                    span: start_span.merge(self.prev_span()),
                    kind: ItemKind::Interface(iface_def),
                })
            }
            Some(TokenKind::Type) => {
                let type_alias = self.parse_type_alias(vis)?;
                Some(Item {
                    span: start_span.merge(self.prev_span()),
                    kind: ItemKind::TypeAlias(type_alias),
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
            Some(TokenKind::Extern) => {
                let extern_block = self.parse_extern_block()?;
                Some(Item {
                    span: start_span.merge(self.prev_span()),
                    kind: ItemKind::Extern(extern_block),
                })
            }
            _ => {
                if vis != Visibility::Private {
                    self.error("expected `fn`, `struct`, `enum`, `interface`, `type`, or `use` after visibility modifier");
                }
                None
            }
        }
    }

    // --- Visibility ---

    fn parse_visibility(&mut self) -> Visibility {
        if self.check(&TokenKind::Pub) {
            self.advance();
            // Check for `pub(pkg)`
            if self.check(&TokenKind::LParen) {
                if self.peek_at_kind(1) == Some(TokenKind::Pkg) {
                    self.advance(); // (
                    self.advance(); // pkg
                    if self.check(&TokenKind::RParen) {
                        self.advance(); // )
                    } else {
                        self.error("expected `)` after `pub(pkg`");
                    }
                    self.skip_newlines();
                    return Visibility::PubPkg;
                }
            }
            self.skip_newlines();
            Visibility::Pub
        } else {
            Visibility::Private
        }
    }

    // --- Helper: check if next tokens form a constructor def (fn TypeIdent.ident) ---

    fn is_constructor_def(&self) -> bool {
        // fn TypeIdent . ident (
        if self.peek_at_kind(1).map_or(false, |k| matches!(k, TokenKind::TypeIdent(_))) {
            if self.peek_at_kind(2) == Some(TokenKind::Dot) {
                return true;
            }
        }
        false
    }

    // --- Function definition ---

    fn parse_fn_def(&mut self, vis: Visibility) -> Option<FnDef> {
        self.expect(&TokenKind::Fn)?;

        let name = self.expect_ident()?;

        let type_params = if self.check(&TokenKind::LBracket) {
            self.parse_type_params()?
        } else {
            Vec::new()
        };

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
            vis,
            name,
            type_params,
            params,
            return_type,
            effects,
            body,
        })
    }

    // --- impl block: impl[T] Type[T] { methods... } ---

    /// Try to parse an impl block at the current position.
    /// Returns Some(Vec<Item>) if the current token is `impl` (or `pub impl`),
    /// otherwise returns None without consuming any tokens.
    fn try_parse_impl_block(&mut self) -> Option<Vec<Item>> {
        let saved_pos = self.pos;

        // Check for optional `pub` before `impl`
        let vis = if self.check(&TokenKind::Pub) {
            if self.peek_at_kind(1) == Some(TokenKind::Impl) {
                self.advance(); // consume pub
                Visibility::Pub
            } else {
                return None;
            }
        } else {
            Visibility::Private
        };

        if !self.check(&TokenKind::Impl) {
            self.pos = saved_pos;
            return None;
        }

        match self.parse_impl_block(vis) {
            Some(items) => Some(items),
            None => {
                // Parsing failed — restore position.
                self.pos = saved_pos;
                None
            }
        }
    }

    /// Parse an impl block and desugar to Method/Constructor items.
    ///
    /// Syntax:
    ///   impl[T] Option[T]
    ///       fn unwrap_or(self, default: T) -> T
    ///           ...
    ///       fn new(value: T) -> Option[T]
    ///           ...
    fn parse_impl_block(&mut self, vis: Visibility) -> Option<Vec<Item>> {
        let block_start = self.current_span();
        self.expect(&TokenKind::Impl)?;

        // Parse optional type params: [T], [T, E], etc.
        let impl_type_params = if self.check(&TokenKind::LBracket) {
            self.parse_type_params()?
        } else {
            Vec::new()
        };

        // Parse the first type: could be receiver type or interface name.
        let first_type = self.parse_type_expr()?;

        // NEW: impl Interface for Type
        if self.check(&TokenKind::For) {
            self.advance();
            let target_type = self.parse_type_expr()?;
            let item_span = block_start.merge(self.prev_span());
            return Some(vec![Item {
                span: item_span,
                kind: ItemKind::ImplFor(ImplForDef {
                    interface: first_type,
                    type_params: impl_type_params,
                    target_type,
                }),
            }]);
        }

        let receiver_type = first_type;

        self.skip_newlines();

        let mut items = Vec::new();

        // Parse indented method block
        if self.check(&TokenKind::Indent) {
            self.advance();
            loop {
                self.skip_newlines();
                if self.check(&TokenKind::Dedent) || self.is_at_end() {
                    break;
                }
                if let Some(item) = self.parse_impl_method(vis.clone(), &impl_type_params, &receiver_type) {
                    items.push(item);
                } else {
                    self.advance();
                }
            }
            if self.check(&TokenKind::Dedent) {
                self.advance();
            }
        }

        let _ = block_start; // Used for span tracking if needed
        Some(items)
    }

    /// Parse a single method inside an impl block.
    /// Desugars to ItemKind::Method or ItemKind::Constructor.
    fn parse_impl_method(
        &mut self,
        vis: Visibility,
        impl_type_params: &[TypeParam],
        receiver_type: &TypeExpr,
    ) -> Option<Item> {
        let start_span = self.current_span();
        self.expect(&TokenKind::Fn)?;

        let name = self.expect_ident()?;

        // Parse method-specific type params: fn map[U](...)
        let method_type_params = if self.check(&TokenKind::LBracket) {
            self.parse_type_params()?
        } else {
            Vec::new()
        };

        self.expect(&TokenKind::LParen)?;

        // Check for self/mut self/move self at the beginning of the param list
        let (receiver_modifier, params) = self.parse_impl_method_params()?;

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

        let item_span = start_span.merge(self.prev_span());

        // Merge impl type_params + method type_params
        let mut merged_type_params = impl_type_params.to_vec();
        merged_type_params.extend(method_type_params);

        if let Some(recv_mod) = receiver_modifier {
            // Instance method (has self parameter)
            Some(Item {
                span: item_span,
                kind: ItemKind::Method(MethodDef {
                    vis,
                    receiver_modifier: recv_mod,
                    receiver_type: receiver_type.clone(),
                    name,
                    type_params: merged_type_params,
                    params,
                    return_type,
                    effects,
                    body,
                }),
            })
        } else {
            // Static method (no self parameter) → desugar to Constructor
            let type_name = match receiver_type {
                TypeExpr::Named { name, .. } => name.clone(),
                _ => "Unknown".to_string(),
            };
            Some(Item {
                span: item_span,
                kind: ItemKind::Constructor(ConstructorDef {
                    vis,
                    type_name,
                    name,
                    type_params: merged_type_params,
                    params,
                    return_type,
                    body,
                }),
            })
        }
    }

    /// Parse parameters for an impl method, handling self/mut self/move self.
    /// Returns (Option<ReceiverModifier>, Vec<Param>).
    /// - Some(modifier) if self was present
    /// - None if no self (static method)
    fn parse_impl_method_params(&mut self) -> Option<(Option<ReceiverModifier>, Vec<Param>)> {
        // Check for empty params
        if self.check(&TokenKind::RParen) {
            return Some((None, Vec::new()));
        }

        // Check for self/mut self/move self
        let receiver_modifier = if self.check(&TokenKind::SelfLower) {
            self.advance();
            // Consume trailing comma if present
            if self.check(&TokenKind::Comma) {
                self.advance();
            }
            Some(ReceiverModifier::Borrow)
        } else if self.check(&TokenKind::Mut)
            && self.peek_at_kind(1) == Some(TokenKind::SelfLower)
        {
            self.advance(); // mut
            self.advance(); // self
            if self.check(&TokenKind::Comma) {
                self.advance();
            }
            Some(ReceiverModifier::Mut)
        } else if self.check(&TokenKind::Move)
            && self.peek_at_kind(1) == Some(TokenKind::SelfLower)
        {
            self.advance(); // move
            self.advance(); // self
            if self.check(&TokenKind::Comma) {
                self.advance();
            }
            Some(ReceiverModifier::Move)
        } else {
            None
        };

        // Parse remaining params (after self, if any)
        let params = if self.check(&TokenKind::RParen) {
            Vec::new()
        } else {
            self.parse_params()?
        };

        Some((receiver_modifier, params))
    }

    // --- Constructor definition: fn Type.name() ---

    fn parse_constructor_def(&mut self, vis: Visibility) -> Option<ConstructorDef> {
        self.expect(&TokenKind::Fn)?;

        let type_name = self.expect_type_ident()?;
        self.expect(&TokenKind::Dot)?;
        let name = self.expect_ident()?;

        let type_params = if self.check(&TokenKind::LBracket) {
            self.parse_type_params()?
        } else {
            Vec::new()
        };

        self.expect(&TokenKind::LParen)?;
        let params = self.parse_params()?;
        self.expect(&TokenKind::RParen)?;

        let return_type = if self.check(&TokenKind::Arrow) {
            self.advance();
            Some(self.parse_type_expr()?)
        } else {
            None
        };

        self.skip_newlines();
        let body = self.parse_block()?;

        Some(ConstructorDef {
            vis,
            type_name,
            name,
            type_params,
            params,
            return_type,
            body,
        })
    }

    // --- Type parameters ---

    fn parse_type_params(&mut self) -> Option<Vec<TypeParam>> {
        self.expect(&TokenKind::LBracket)?;
        let mut params = Vec::new();

        if self.check(&TokenKind::RBracket) {
            self.advance();
            return Some(params);
        }

        loop {
            let span = self.current_span();

            if self.check(&TokenKind::Const) {
                // const N: type
                self.advance();
                let name = self.expect_ident()?;
                self.expect(&TokenKind::Colon)?;
                let ty = self.parse_type_expr()?;
                params.push(TypeParam::Const {
                    name,
                    ty,
                    span: span.merge(self.prev_span()),
                });
            } else if self.check(&TokenKind::Dim) {
                // dim M
                self.advance();
                let name = self.expect_any_ident()?;
                params.push(TypeParam::Dim {
                    name,
                    span: span.merge(self.prev_span()),
                });
            } else {
                // Type param: T or T: Bound1 + Bound2
                let name = self.expect_type_ident()?;
                let mut bounds = Vec::new();
                if self.check(&TokenKind::Colon) {
                    self.advance();
                    bounds.push(self.parse_interface_bound()?);
                    while self.check(&TokenKind::Plus) {
                        self.advance();
                        bounds.push(self.parse_interface_bound()?);
                    }
                }
                params.push(TypeParam::Type {
                    name,
                    bounds,
                    span: span.merge(self.prev_span()),
                });
            }

            if !self.check(&TokenKind::Comma) {
                break;
            }
            self.advance();
        }

        self.expect(&TokenKind::RBracket)?;
        Some(params)
    }

    fn parse_interface_bound(&mut self) -> Option<InterfaceBound> {
        let span = self.current_span();
        let name = self.expect_type_ident()?;
        let mut args = Vec::new();
        if self.check(&TokenKind::LBracket) {
            self.advance();
            args.push(self.parse_type_expr()?);
            while self.check(&TokenKind::Comma) {
                self.advance();
                args.push(self.parse_type_expr()?);
            }
            self.expect(&TokenKind::RBracket)?;
        }
        Some(InterfaceBound {
            name,
            args,
            span: span.merge(self.prev_span()),
        })
    }

    // --- Parameters ---

    fn parse_params(&mut self) -> Option<Vec<Param>> {
        let mut params = Vec::new();

        if self.check(&TokenKind::RParen) {
            return Some(params);
        }

        loop {
            let param_span = self.current_span();

            let modifier = if self.check(&TokenKind::Move) {
                self.advance();
                if self.check(&TokenKind::Mut) {
                    self.advance();
                    ParamModifier::MoveMut
                } else {
                    ParamModifier::Move
                }
            } else if self.check(&TokenKind::Mut) {
                self.advance();
                ParamModifier::Mut
            } else {
                ParamModifier::None
            };

            let name = self.expect_ident()?;
            self.expect(&TokenKind::Colon)?;
            let ty = self.parse_type_expr()?;

            params.push(Param {
                name,
                ty,
                modifier,
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

        // Reference type: &Type or Slice type: &[T]
        if self.check(&TokenKind::Amp) {
            self.advance();
            // Check for slice: &[T]
            if self.check(&TokenKind::LBracket) {
                self.advance();
                let inner = self.parse_type_expr()?;
                self.expect(&TokenKind::RBracket)?;
                return Some(TypeExpr::Slice {
                    span: span.merge(self.prev_span()),
                    inner: Box::new(inner),
                });
            }
            let inner = self.parse_type_expr()?;
            return Some(TypeExpr::Ref {
                span: span.merge(self.prev_span()),
                inner: Box::new(inner),
            });
        }

        // Dyn type: dyn Type
        if self.check(&TokenKind::Dyn) {
            self.advance();
            let inner = self.parse_type_expr()?;
            return Some(TypeExpr::Dyn {
                span: span.merge(self.prev_span()),
                inner: Box::new(inner),
            });
        }

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

        // Array type: [T; N]
        if self.check(&TokenKind::LBracket) {
            self.advance();
            let inner = self.parse_type_expr()?;
            self.expect(&TokenKind::Semi)?;
            // Parse the size as an integer literal
            if let Some(TokenKind::IntLit(s)) = self.peek_kind() {
                let s = s.clone();
                self.advance();
                let size: u64 = s.replace('_', "").parse().unwrap_or(0);
                self.expect(&TokenKind::RBracket)?;
                return Some(TypeExpr::Array {
                    inner: Box::new(inner),
                    size,
                    span: span.merge(self.prev_span()),
                });
            } else {
                self.error("expected integer literal for array size");
                return None;
            }
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

        // SelfUpper as type
        if self.check(&TokenKind::SelfUpper) {
            self.advance();
            return Some(TypeExpr::Named {
                name: "Self".to_string(),
                args: Vec::new(),
                span: span.merge(self.prev_span()),
            });
        }

        // Function type: Fn(T1, T2) -> RetType
        if let Some(TokenKind::TypeIdent(ref s)) = self.peek_kind() {
            if s == "Fn" && self.peek_at_kind(1) == Some(TokenKind::LParen) {
                self.advance(); // consume Fn
                self.advance(); // consume (
                let mut params = Vec::new();
                if !self.check(&TokenKind::RParen) {
                    params.push(self.parse_type_expr()?);
                    while self.check(&TokenKind::Comma) {
                        self.advance();
                        params.push(self.parse_type_expr()?);
                    }
                }
                self.expect(&TokenKind::RParen)?;
                self.expect(&TokenKind::Arrow)?;
                let ret = self.parse_type_expr()?;
                return Some(TypeExpr::Fn {
                    params,
                    ret: Box::new(ret),
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

        let mut ty = TypeExpr::Named {
            name,
            args,
            span: span.merge(self.prev_span()),
        };

        // DimApply: Type[T][dim1, dim2]
        // After the first [args], check for additional [dims]
        if self.check(&TokenKind::LBracket) {
            self.advance();
            let mut dims = vec![self.parse_dim_expr()?];
            while self.check(&TokenKind::Comma) {
                self.advance();
                dims.push(self.parse_dim_expr()?);
            }
            self.expect(&TokenKind::RBracket)?;
            ty = TypeExpr::DimApply {
                base: Box::new(ty),
                dims,
                span: span.merge(self.prev_span()),
            };
        }

        // Active fields: T@{f1, f2}
        if self.check(&TokenKind::At) {
            self.advance();
            self.expect(&TokenKind::LBrace)?;
            let mut fields = Vec::new();
            if !self.check(&TokenKind::RBrace) {
                fields.push(self.expect_ident()?);
                while self.check(&TokenKind::Comma) {
                    self.advance();
                    fields.push(self.expect_ident()?);
                }
            }
            self.expect(&TokenKind::RBrace)?;
            ty = TypeExpr::Active {
                base: Box::new(ty),
                fields,
                span: span.merge(self.prev_span()),
            };
        }

        Some(ty)
    }

    // --- Dim expressions ---

    fn parse_dim_expr(&mut self) -> Option<DimExpr> {
        let left = self.parse_dim_atom()?;
        self.parse_dim_binop(left)
    }

    fn parse_dim_atom(&mut self) -> Option<DimExpr> {
        match self.peek_kind() {
            Some(TokenKind::IntLit(ref s)) => {
                let val: i128 = s.replace('_', "").parse().unwrap_or(0);
                self.advance();
                Some(DimExpr::Lit(val))
            }
            Some(TokenKind::Ident(ref s)) if s == "_" => {
                self.advance();
                Some(DimExpr::Wildcard)
            }
            Some(TokenKind::Question) => {
                self.advance();
                Some(DimExpr::Wildcard)
            }
            Some(TokenKind::Ident(ref s)) => {
                let name = s.clone();
                self.advance();
                Some(DimExpr::Var(name))
            }
            Some(TokenKind::TypeIdent(ref s)) => {
                let name = s.clone();
                self.advance();
                Some(DimExpr::Var(name))
            }
            _ => {
                self.error("expected dimension expression");
                None
            }
        }
    }

    fn parse_dim_binop(&mut self, left: DimExpr) -> Option<DimExpr> {
        let op = match self.peek_kind() {
            Some(TokenKind::Plus) => DimBinOp::Add,
            Some(TokenKind::Minus) => DimBinOp::Sub,
            Some(TokenKind::Star) => DimBinOp::Mul,
            Some(TokenKind::Slash) => DimBinOp::Div,
            _ => return Some(left),
        };
        self.advance();
        let right = self.parse_dim_atom()?;
        Some(DimExpr::BinOp {
            op,
            lhs: Box::new(left),
            rhs: Box::new(right),
        })
    }

    fn parse_effect_list(&mut self) -> Option<Vec<Effect>> {
        let mut effects = Vec::new();
        loop {
            let span = self.current_span();
            let name = self.expect_type_ident()?;
            let args = if self.check(&TokenKind::LBracket) {
                self.advance();
                let mut a = Vec::new();
                if !self.check(&TokenKind::RBracket) {
                    a.push(self.parse_type_expr()?);
                    while self.check(&TokenKind::Comma) {
                        self.advance();
                        a.push(self.parse_type_expr()?);
                    }
                }
                self.expect(&TokenKind::RBracket)?;
                a
            } else {
                Vec::new()
            };
            effects.push(Effect {
                name,
                args,
                span: span.merge(self.prev_span()),
            });
            if !self.check(&TokenKind::Comma) {
                break;
            }
            self.advance();
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

                // Check for pattern destructuring: `let {x, y} = ...` or `let [first, ..rest] = ...`
                if self.check(&TokenKind::LBrace) || self.check(&TokenKind::LBracket) {
                    let pattern = self.parse_pattern_atom()?;
                    let ty = if self.check(&TokenKind::Colon) {
                        self.advance();
                        Some(self.parse_type_expr()?)
                    } else {
                        None
                    };
                    self.expect(&TokenKind::Eq)?;
                    let value = self.parse_expr()?;
                    return Some(Stmt {
                        kind: StmtKind::LetPattern {
                            is_mut,
                            pattern,
                            ty,
                            value,
                        },
                        span: span.merge(self.prev_span()),
                    });
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
            Some(TokenKind::Break) => {
                self.advance();
                let value = if self.check(&TokenKind::Newline) || self.check(&TokenKind::Dedent) || self.is_at_end() {
                    None
                } else {
                    Some(self.parse_expr()?)
                };
                Some(Stmt {
                    kind: StmtKind::Break(value),
                    span: span.merge(self.prev_span()),
                })
            }
            Some(TokenKind::Continue) => {
                self.advance();
                Some(Stmt {
                    kind: StmtKind::Continue,
                    span,
                })
            }
            Some(TokenKind::Assert) => {
                self.advance();
                let cond = self.parse_expr()?;
                let message = if self.check(&TokenKind::Comma) {
                    self.advance();
                    Some(self.parse_expr()?)
                } else {
                    None
                };
                Some(Stmt {
                    kind: StmtKind::Assert { cond, message },
                    span: span.merge(self.prev_span()),
                })
            }
            _ => {
                let expr = self.parse_expr()?;
                // Check for assignment: `expr = value`
                if self.check(&TokenKind::Eq) {
                    self.advance();
                    let value = self.parse_expr()?;
                    return Some(Stmt {
                        kind: StmtKind::Assign {
                            target: expr,
                            value,
                        },
                        span: span.merge(self.prev_span()),
                    });
                }
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
        let mut left = self.parse_range_expr()?;

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
            let right = self.parse_range_expr()?;
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
            Some(TokenKind::Amp) => {
                self.advance();
                let operand = self.parse_postfix_expr()?;
                Some(Expr {
                    span: span.merge(operand.span),
                    kind: ExprKind::Ref(Box::new(operand)),
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
                // Check for `.await` postfix
                if let Some(TokenKind::Ident(ref s)) = self.peek_kind() {
                    if s == "await" {
                        self.advance();
                        let span = expr.span.merge(self.prev_span());
                        expr = Expr {
                            kind: ExprKind::Await(Box::new(expr)),
                            span,
                        };
                        continue;
                    }
                }
                let name = self.expect_any_ident()?;
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
                    args.push(self.parse_call_arg()?);
                    while self.check(&TokenKind::Comma) {
                        self.advance();
                        args.push(self.parse_call_arg()?);
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
            } else if self.check(&TokenKind::LBracket) {
                // Determine: TypeApp vs Index
                // TypeApp if: left side is TypeIdent/primitive, or content starts with a type token
                let is_type_app = match &expr.kind {
                    ExprKind::Ident(name) => {
                        name.chars().next().map_or(false, |c| c.is_uppercase())
                            || TokenKind::is_primitive_type(name)
                    }
                    ExprKind::TypeApp { .. } => true,
                    _ => false,
                };
                // If not decided by left-side, peek inside brackets:
                // If content is a type (TypeIdent or primitive), treat as TypeApp
                let is_type_app = is_type_app || {
                    match self.peek_at_kind(1) {
                        Some(TokenKind::TypeIdent(_)) => true,
                        Some(TokenKind::Ident(ref s)) => TokenKind::is_primitive_type(s),
                        Some(TokenKind::Amp) => true, // &Type
                        Some(TokenKind::LBracket) => true, // [T; N] array type
                        _ => false,
                    }
                };
                if is_type_app {
                    // Turbofish type application: `f[T](args)`, `HashMap[K, V].new()`
                    self.advance();
                    let mut type_args = Vec::new();
                    if !self.check(&TokenKind::RBracket) {
                        type_args.push(self.parse_type_expr()?);
                        while self.check(&TokenKind::Comma) {
                            self.advance();
                            type_args.push(self.parse_type_expr()?);
                        }
                    }
                    self.expect(&TokenKind::RBracket)?;
                    let span = expr.span.merge(self.prev_span());
                    expr = Expr {
                        kind: ExprKind::TypeApp {
                            expr: Box::new(expr),
                            type_args,
                        },
                        span,
                    };
                } else {
                    // Index access: `arr[i]`
                    self.advance(); // consume [
                    let index = self.parse_expr()?;
                    self.expect(&TokenKind::RBracket)?;
                    let span = expr.span.merge(self.prev_span());
                    expr = Expr {
                        kind: ExprKind::Index {
                            expr: Box::new(expr),
                            index: Box::new(index),
                        },
                        span,
                    };
                }
            } else if self.check(&TokenKind::Question) {
                self.advance();
                let span = expr.span.merge(self.prev_span());
                expr = Expr {
                    kind: ExprKind::Try(Box::new(expr)),
                    span,
                };
            } else {
                break;
            }
        }

        Some(expr)
    }

    fn parse_call_arg(&mut self) -> Option<CallArg> {
        let modifier = if self.check(&TokenKind::Move) {
            // Peek ahead to see if this is `move expr` or `move mut expr`
            self.advance();
            if self.check(&TokenKind::Mut) {
                self.advance();
                ParamModifier::MoveMut
            } else {
                ParamModifier::Move
            }
        } else if self.check(&TokenKind::Mut) {
            self.advance();
            ParamModifier::Mut
        } else {
            ParamModifier::None
        };
        let expr = self.parse_expr()?;
        Some(CallArg { modifier, expr })
    }

    fn parse_primary_expr(&mut self) -> Option<Expr> {
        let span = self.current_span();

        match self.peek_kind() {
            Some(TokenKind::IntLit(_)) => {
                if let TokenKind::IntLit(s) = self.advance_and_get() {
                    // Extract optional type suffix (e.g. "42_i32" -> suffix "i32")
                    let suffix_pos = s.rfind('_').filter(|&i| {
                        i + 1 < s.len() && s.as_bytes()[i + 1].is_ascii_alphabetic()
                    });
                    let (num_part, suffix) = if let Some(i) = suffix_pos {
                        (&s[..i], Some(s[i + 1..].to_string()))
                    } else {
                        (s.as_str(), None)
                    };
                    let num_str: String = num_part.replace('_', "");
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
                        kind: ExprKind::IntLit(value, suffix),
                        span,
                    })
                } else {
                    None
                }
            }
            Some(TokenKind::FloatLit(_)) => {
                if let TokenKind::FloatLit(s) = self.advance_and_get() {
                    // Extract optional type suffix (e.g. "3.14_f64" -> suffix "f64")
                    let suffix_pos = s.rfind('_').filter(|&i| {
                        i + 1 < s.len() && s.as_bytes()[i + 1].is_ascii_alphabetic()
                    });
                    let (num_part, suffix) = if let Some(i) = suffix_pos {
                        (&s[..i], Some(s[i + 1..].to_string()))
                    } else {
                        (s.as_str(), None)
                    };
                    let clean: String = num_part.replace('_', "");
                    let value: f64 = clean.parse().unwrap_or(0.0);
                    Some(Expr {
                        kind: ExprKind::FloatLit(value, suffix),
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
            Some(TokenKind::StringInterpStart(_)) => {
                self.parse_string_interp_expr()
            }
            Some(TokenKind::CharLit(_)) => {
                if let TokenKind::CharLit(c) = self.advance_and_get() {
                    Some(Expr {
                        kind: ExprKind::CharLit(c),
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
            Some(TokenKind::SelfLower) => {
                self.advance();
                Some(Expr {
                    kind: ExprKind::Ident("self".to_string()),
                    span,
                })
            }
            Some(TokenKind::SelfUpper) => {
                self.advance();
                // Check if followed by #{ for struct literal: Self #{field: value}
                if self.check(&TokenKind::HashLBrace) {
                    self.advance(); // consume #{
                    let mut fields = Vec::new();
                    if !self.check(&TokenKind::RBrace) {
                        loop {
                            let f_span = self.current_span();
                            let f_name = self.expect_ident()?;
                            let f_value = if self.check(&TokenKind::Colon) {
                                self.advance();
                                self.parse_expr()?
                            } else {
                                Expr {
                                    kind: ExprKind::Ident(f_name.clone()),
                                    span: f_span,
                                }
                            };
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
                        kind: ExprKind::StructLit {
                            name: "Self".to_string(),
                            fields,
                        },
                        span: span.merge(self.prev_span()),
                    })
                } else {
                    Some(Expr {
                        kind: ExprKind::Ident("Self".to_string()),
                        span,
                    })
                }
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
                                // Support shorthand: `#{name, age}` (no colon)
                                let f_value = if self.check(&TokenKind::Colon) {
                                    self.advance();
                                    self.parse_expr()?
                                } else {
                                    Expr {
                                        kind: ExprKind::Ident(f_name.clone()),
                                        span: f_span,
                                    }
                                };
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
            Some(TokenKind::While) => self.parse_while_expr(),
            Some(TokenKind::Match) => self.parse_match_expr(),
            Some(TokenKind::For) => self.parse_for_expr(),
            Some(TokenKind::Handle) => self.parse_handle_expr(),
            Some(TokenKind::Assert) => {
                self.advance();
                let cond = self.parse_expr()?;
                let message = if self.check(&TokenKind::Comma) {
                    self.advance();
                    Some(Box::new(self.parse_expr()?))
                } else {
                    None
                };
                Some(Expr {
                    kind: ExprKind::Assert { cond: Box::new(cond), message },
                    span: span.merge(self.prev_span()),
                })
            }
            Some(TokenKind::Pipe) => self.parse_closure_expr(),
            Some(TokenKind::PipePipe) => {
                // `||` is lexed as a single token; treat as empty-param closure `|| body`
                self.advance(); // consume ||
                let body = if self.check(&TokenKind::Newline) || self.check(&TokenKind::Indent) {
                    self.skip_newlines();
                    self.parse_block()?
                } else {
                    let expr = self.parse_expr()?;
                    vec![Stmt {
                        span: expr.span,
                        kind: StmtKind::Expr(expr),
                    }]
                };
                Some(Expr {
                    span: span.merge(self.prev_span()),
                    kind: ExprKind::Closure {
                        params: Vec::new(),
                        body,
                    },
                })
            }
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
            // Array literal: [expr, expr, ...]
            Some(TokenKind::LBracket) => {
                self.advance(); // consume [
                if self.check(&TokenKind::RBracket) {
                    self.advance();
                    return Some(Expr {
                        kind: ExprKind::ArrayLit(Vec::new()),
                        span: span.merge(self.prev_span()),
                    });
                }
                let mut elements = vec![self.parse_expr()?];
                while self.check(&TokenKind::Comma) {
                    self.advance();
                    elements.push(self.parse_expr()?);
                }
                self.expect(&TokenKind::RBracket)?;
                Some(Expr {
                    kind: ExprKind::ArrayLit(elements),
                    span: span.merge(self.prev_span()),
                })
            }
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

    fn parse_while_expr(&mut self) -> Option<Expr> {
        let span = self.current_span();
        self.expect(&TokenKind::While)?;

        let cond = self.parse_expr()?;
        self.skip_newlines();
        let body = self.parse_block()?;

        Some(Expr {
            span: span.merge(self.prev_span()),
            kind: ExprKind::While {
                cond: Box::new(cond),
                body,
            },
        })
    }

    fn parse_handle_expr(&mut self) -> Option<Expr> {
        let span = self.current_span();
        self.expect(&TokenKind::Handle)?;

        let expr = self.parse_expr()?;
        self.skip_newlines();

        let mut arms = Vec::new();
        if self.check(&TokenKind::Indent) {
            self.advance();
            loop {
                self.skip_newlines();
                if self.check(&TokenKind::Dedent) || self.is_at_end() {
                    break;
                }
                let arm_span = self.current_span();
                let effect = self.expect_type_ident()?;
                let mut params = Vec::new();
                if self.check(&TokenKind::LParen) {
                    self.advance();
                    if !self.check(&TokenKind::RParen) {
                        params.push(self.expect_ident()?);
                        while self.check(&TokenKind::Comma) {
                            self.advance();
                            params.push(self.expect_ident()?);
                        }
                    }
                    self.expect(&TokenKind::RParen)?;
                }
                self.expect(&TokenKind::FatArrow)?;

                let body = if self.check(&TokenKind::Newline) || self.check(&TokenKind::Indent) {
                    self.skip_newlines();
                    self.parse_block()?
                } else {
                    let e = self.parse_expr()?;
                    vec![Stmt {
                        span: e.span,
                        kind: StmtKind::Expr(e),
                    }]
                };

                arms.push(HandleArm {
                    effect,
                    params,
                    body,
                    span: arm_span.merge(self.prev_span()),
                });
            }
            if self.check(&TokenKind::Dedent) {
                self.advance();
            }
        }

        Some(Expr {
            span: span.merge(self.prev_span()),
            kind: ExprKind::Handle {
                expr: Box::new(expr),
                arms,
            },
        })
    }

    /// Parse `#{...}` — disambiguate between map and set literal.
    fn parse_hash_brace_expr(&mut self) -> Option<Expr> {
        let span = self.current_span();
        self.advance(); // consume #{

        // Empty: #{}  -> empty map
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

    // --- Pattern matching ---

    fn parse_pattern(&mut self) -> Option<Pattern> {
        let first = self.parse_pattern_atom()?;

        // Check for OR pattern: `A | B | C`
        if self.check(&TokenKind::Pipe) {
            let mut alternatives = vec![first.clone()];
            while self.check(&TokenKind::Pipe) {
                self.advance();
                alternatives.push(self.parse_pattern_atom()?);
            }
            let span = alternatives.first().unwrap().span.merge(alternatives.last().unwrap().span);
            return Some(Pattern {
                kind: PatternKind::Or(alternatives),
                span,
            });
        }

        Some(first)
    }

    fn parse_pattern_atom(&mut self) -> Option<Pattern> {
        let span = self.current_span();

        match self.peek_kind() {
            // Wildcard: `_`
            Some(TokenKind::Ident(ref s)) if s == "_" => {
                self.advance();
                Some(Pattern {
                    kind: PatternKind::Wildcard,
                    span,
                })
            }
            // Rest pattern: `..` or `..rest`
            Some(TokenKind::DotDot) => {
                self.advance();
                let name = if let Some(TokenKind::Ident(ref s)) = self.peek_kind() {
                    if s != "_" {
                        let n = s.clone();
                        self.advance();
                        Some(n)
                    } else {
                        None
                    }
                } else {
                    None
                };
                Some(Pattern {
                    kind: PatternKind::Rest(name),
                    span: span.merge(self.prev_span()),
                })
            }
            // Tuple pattern: `{a, b}`
            Some(TokenKind::LBrace) => self.parse_tuple_pattern(),
            // List pattern: `[first, ..rest]`
            Some(TokenKind::LBracket) => self.parse_list_pattern(),
            // Constructor pattern: `Type.Variant(...)` or `Type #{...}` (struct pattern)
            Some(TokenKind::TypeIdent(_)) => self.parse_constructor_pattern(),
            // Literal patterns: int, float, string, bool
            Some(TokenKind::IntLit(_)) | Some(TokenKind::FloatLit(_))
            | Some(TokenKind::StringLit(_)) | Some(TokenKind::True) | Some(TokenKind::False) => {
                let expr = self.parse_primary_expr()?;
                Some(Pattern {
                    span: expr.span,
                    kind: PatternKind::Literal(Box::new(expr)),
                })
            }
            // Negative literal pattern: `-1`
            Some(TokenKind::Minus) => {
                let expr = self.parse_unary_expr()?;
                Some(Pattern {
                    span: expr.span,
                    kind: PatternKind::Literal(Box::new(expr)),
                })
            }
            // Ident binding
            Some(TokenKind::Ident(_)) => {
                if let TokenKind::Ident(name) = self.advance_and_get() {
                    Some(Pattern {
                        kind: PatternKind::Ident(name),
                        span,
                    })
                } else {
                    None
                }
            }
            _ => {
                self.error("expected pattern");
                None
            }
        }
    }

    fn parse_list_pattern(&mut self) -> Option<Pattern> {
        let span = self.current_span();
        self.expect(&TokenKind::LBracket)?;

        let mut elements = Vec::new();
        if !self.check(&TokenKind::RBracket) {
            elements.push(self.parse_pattern()?);
            while self.check(&TokenKind::Comma) {
                self.advance();
                if self.check(&TokenKind::RBracket) {
                    break;
                }
                elements.push(self.parse_pattern()?);
            }
        }
        self.expect(&TokenKind::RBracket)?;

        Some(Pattern {
            kind: PatternKind::List(elements),
            span: span.merge(self.prev_span()),
        })
    }

    fn parse_tuple_pattern(&mut self) -> Option<Pattern> {
        let span = self.current_span();
        self.expect(&TokenKind::LBrace)?;

        let mut elements = Vec::new();
        if !self.check(&TokenKind::RBrace) {
            elements.push(self.parse_pattern()?);
            while self.check(&TokenKind::Comma) {
                self.advance();
                if self.check(&TokenKind::RBrace) {
                    break;
                }
                elements.push(self.parse_pattern()?);
            }
        }
        self.expect(&TokenKind::RBrace)?;

        Some(Pattern {
            kind: PatternKind::TuplePattern(elements),
            span: span.merge(self.prev_span()),
        })
    }

    fn parse_constructor_pattern(&mut self) -> Option<Pattern> {
        let span = self.current_span();
        let mut path = Vec::new();

        // First segment: TypeIdent
        if let TokenKind::TypeIdent(name) = self.advance_and_get() {
            path.push(name);
        } else {
            return None;
        }

        // Optional type arguments: `[T1, T2, ...]`
        let mut type_args = Vec::new();
        if self.check(&TokenKind::LBracket) {
            self.advance();
            type_args.push(self.parse_type_expr()?);
            while self.check(&TokenKind::Comma) {
                self.advance();
                type_args.push(self.parse_type_expr()?);
            }
            self.expect(&TokenKind::RBracket)?;
        }

        // Additional path segments: `.Variant`
        while self.check(&TokenKind::Dot) {
            self.advance();
            match self.peek_kind() {
                Some(TokenKind::TypeIdent(_)) => {
                    if let TokenKind::TypeIdent(name) = self.advance_and_get() {
                        path.push(name);
                    }
                }
                Some(TokenKind::Ident(_)) => {
                    if let TokenKind::Ident(name) = self.advance_and_get() {
                        path.push(name);
                    }
                }
                _ => {
                    self.error("expected identifier after `.` in pattern");
                    break;
                }
            }
        }

        // Check for struct pattern: `Type #{name, age, ..}`
        if self.check(&TokenKind::HashLBrace) {
            self.advance(); // consume #{
            let type_name = path.join(".");
            let mut fields = Vec::new();
            let mut has_rest = false;
            if !self.check(&TokenKind::RBrace) {
                loop {
                    if self.check(&TokenKind::DotDot) {
                        self.advance();
                        has_rest = true;
                        break;
                    }
                    let f_span = self.current_span();
                    let f_name = self.expect_ident()?;
                    let f_pattern = if self.check(&TokenKind::Colon) {
                        self.advance();
                        Some(self.parse_pattern()?)
                    } else {
                        None
                    };
                    fields.push(FieldPattern {
                        name: f_name,
                        pattern: f_pattern,
                        span: f_span.merge(self.prev_span()),
                    });
                    if !self.check(&TokenKind::Comma) {
                        break;
                    }
                    self.advance();
                    if self.check(&TokenKind::RBrace) {
                        break;
                    }
                }
            }
            self.expect(&TokenKind::RBrace)?;
            return Some(Pattern {
                kind: PatternKind::Struct {
                    name: type_name,
                    fields,
                    has_rest,
                },
                span: span.merge(self.prev_span()),
            });
        }

        // Optional fields: `(pattern, ...)`
        let mut fields = Vec::new();
        if self.check(&TokenKind::LParen) {
            self.advance();
            if !self.check(&TokenKind::RParen) {
                fields.push(self.parse_pattern()?);
                while self.check(&TokenKind::Comma) {
                    self.advance();
                    if self.check(&TokenKind::RParen) {
                        break;
                    }
                    fields.push(self.parse_pattern()?);
                }
            }
            self.expect(&TokenKind::RParen)?;
        }

        Some(Pattern {
            kind: PatternKind::Constructor { path, type_args, fields },
            span: span.merge(self.prev_span()),
        })
    }

    fn parse_match_arm(&mut self) -> Option<MatchArm> {
        let span = self.current_span();
        let pattern = self.parse_pattern()?;

        // Optional guard: `if expr`
        let guard = if self.check(&TokenKind::If) {
            self.advance();
            Some(self.parse_expr()?)
        } else {
            None
        };

        self.expect(&TokenKind::FatArrow)?;

        // Body: either single expression on same line, or indented block
        let body = if self.check(&TokenKind::Newline) || self.check(&TokenKind::Indent) {
            self.skip_newlines();
            self.parse_block()?
        } else {
            let expr = self.parse_expr()?;
            vec![Stmt {
                span: expr.span,
                kind: StmtKind::Expr(expr),
            }]
        };

        Some(MatchArm {
            pattern,
            guard,
            body,
            span: span.merge(self.prev_span()),
        })
    }

    fn parse_match_expr(&mut self) -> Option<Expr> {
        let span = self.current_span();
        self.expect(&TokenKind::Match)?;

        let expr = self.parse_expr()?;
        self.skip_newlines();

        // Parse indented block of arms
        let mut arms = Vec::new();
        if self.check(&TokenKind::Indent) {
            self.advance();
            loop {
                self.skip_newlines();
                if self.check(&TokenKind::Dedent) || self.is_at_end() {
                    break;
                }
                if let Some(arm) = self.parse_match_arm() {
                    arms.push(arm);
                } else {
                    self.advance();
                }
            }
            if self.check(&TokenKind::Dedent) {
                self.advance();
            }
        }

        Some(Expr {
            span: span.merge(self.prev_span()),
            kind: ExprKind::Match {
                expr: Box::new(expr),
                arms,
            },
        })
    }

    // --- For loop ---

    fn parse_for_expr(&mut self) -> Option<Expr> {
        let span = self.current_span();
        self.expect(&TokenKind::For)?;

        let pattern = self.parse_pattern()?;
        self.expect(&TokenKind::In)?;
        let iter = self.parse_expr()?;
        self.skip_newlines();
        let body = self.parse_block()?;

        Some(Expr {
            span: span.merge(self.prev_span()),
            kind: ExprKind::For {
                pattern,
                iter: Box::new(iter),
                body,
            },
        })
    }

    // --- Range expression ---

    fn parse_range_expr(&mut self) -> Option<Expr> {
        // Bare `..` or `..end` (no start)
        if self.check(&TokenKind::DotDot) {
            let start_span = self.current_span();
            self.advance();
            let end = if self.can_start_expr() {
                Some(Box::new(self.parse_additive_expr()?))
            } else {
                None
            };
            let end_span = end.as_ref().map(|e| e.span).unwrap_or(self.prev_span());
            return Some(Expr {
                kind: ExprKind::Range { start: None, end },
                span: start_span.merge(end_span),
            });
        }

        let mut left = self.parse_additive_expr()?;
        if self.check(&TokenKind::DotDot) {
            self.advance();
            let end = if self.can_start_expr() {
                Some(Box::new(self.parse_additive_expr()?))
            } else {
                None
            };
            let span = left.span.merge(end.as_ref().map(|e| e.span).unwrap_or(self.prev_span()));
            left = Expr {
                kind: ExprKind::Range {
                    start: Some(Box::new(left)),
                    end,
                },
                span,
            };
        }
        Some(left)
    }

    fn can_start_expr(&self) -> bool {
        !matches!(self.peek_kind(), Some(
            TokenKind::RBracket | TokenKind::RParen | TokenKind::Comma
            | TokenKind::Newline | TokenKind::Dedent | TokenKind::Eof
        ) | None)
    }

    // --- Closure ---

    fn parse_closure_expr(&mut self) -> Option<Expr> {
        let span = self.current_span();
        self.expect(&TokenKind::Pipe)?;

        // Parse parameters
        let mut params = Vec::new();
        if !self.check(&TokenKind::Pipe) {
            loop {
                let param_span = self.current_span();
                let name = self.expect_ident()?;

                let ty = if self.check(&TokenKind::Colon) {
                    self.advance();
                    Some(self.parse_type_expr()?)
                } else {
                    None
                };

                params.push(ClosureParam {
                    name,
                    ty,
                    span: param_span.merge(self.prev_span()),
                });

                if !self.check(&TokenKind::Comma) {
                    break;
                }
                self.advance();
            }
        }
        self.expect(&TokenKind::Pipe)?;

        // Body: indented block or single expression
        let body = if self.check(&TokenKind::Newline) || self.check(&TokenKind::Indent) {
            self.skip_newlines();
            self.parse_block()?
        } else {
            let expr = self.parse_expr()?;
            vec![Stmt {
                span: expr.span,
                kind: StmtKind::Expr(expr),
            }]
        };

        Some(Expr {
            span: span.merge(self.prev_span()),
            kind: ExprKind::Closure { params, body },
        })
    }

    fn parse_string_interp_expr(&mut self) -> Option<Expr> {
        let span = self.current_span();
        let mut parts = Vec::new();

        // Consume StringInterpStart
        if let TokenKind::StringInterpStart(s) = self.advance_and_get() {
            if !s.is_empty() {
                parts.push(StringInterpPart::Literal(s));
            }
        } else {
            return None;
        }

        loop {
            // Parse expression(s) until we see StringInterpPart or StringInterpEnd
            let mut expr_parts = Vec::new();
            loop {
                match self.peek_kind() {
                    Some(TokenKind::StringInterpPart(_)) | Some(TokenKind::StringInterpEnd(_)) | None => break,
                    _ => {
                        if let Some(expr) = self.parse_expr() {
                            expr_parts.push(expr);
                        } else {
                            break;
                        }
                    }
                }
            }
            // If we got exactly one expression, use it; otherwise, use the first one
            if let Some(expr) = expr_parts.into_iter().next() {
                parts.push(StringInterpPart::Expr(expr));
            }

            match self.peek_kind() {
                Some(TokenKind::StringInterpPart(_)) => {
                    if let TokenKind::StringInterpPart(s) = self.advance_and_get() {
                        if !s.is_empty() {
                            parts.push(StringInterpPart::Literal(s));
                        }
                    }
                    // Continue loop for next expression
                }
                Some(TokenKind::StringInterpEnd(_)) => {
                    if let TokenKind::StringInterpEnd(s) = self.advance_and_get() {
                        if !s.is_empty() {
                            parts.push(StringInterpPart::Literal(s));
                        }
                    }
                    break;
                }
                _ => {
                    self.error("expected string interpolation continuation");
                    break;
                }
            }
        }

        Some(Expr {
            kind: ExprKind::StringInterp { parts },
            span: span.merge(self.prev_span()),
        })
    }

    fn parse_struct_def(&mut self, vis: Visibility) -> Option<StructDef> {
        self.expect(&TokenKind::Struct)?;
        let name = self.expect_type_ident()?;

        let type_params = if self.check(&TokenKind::LBracket) {
            self.parse_type_params()?
        } else {
            Vec::new()
        };

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
            vis,
            name,
            type_params,
            fields,
        })
    }

    fn parse_enum_def(&mut self, vis: Visibility) -> Option<EnumDef> {
        self.expect(&TokenKind::Enum)?;
        let name = self.expect_type_ident()?;

        let type_params = if self.check(&TokenKind::LBracket) {
            self.parse_type_params()?
        } else {
            Vec::new()
        };

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
            vis,
            name,
            type_params,
            variants,
        })
    }

    fn parse_interface_def(&mut self, vis: Visibility) -> Option<InterfaceDef> {
        self.expect(&TokenKind::Interface)?;
        let name = self.expect_type_ident()?;

        let type_params = if self.check(&TokenKind::LBracket) {
            self.parse_type_params()?
        } else {
            Vec::new()
        };

        self.skip_newlines();

        let mut methods = Vec::new();
        if self.check(&TokenKind::Indent) {
            self.advance();
            loop {
                self.skip_newlines();
                if self.check(&TokenKind::Dedent) || self.is_at_end() {
                    break;
                }
                if let Some(method) = self.parse_interface_method() {
                    methods.push(method);
                } else {
                    self.advance();
                }
            }
            if self.check(&TokenKind::Dedent) {
                self.advance();
            }
        }

        Some(InterfaceDef {
            vis,
            name,
            type_params,
            methods,
        })
    }

    fn parse_interface_method(&mut self) -> Option<InterfaceMethod> {
        let span = self.current_span();
        self.expect(&TokenKind::Fn)?;

        let name = self.expect_ident()?;
        self.expect(&TokenKind::LParen)?;

        // Parse params with possible self/mut self/move self
        let (receiver_modifier, params) = self.parse_impl_method_params()?;

        self.expect(&TokenKind::RParen)?;

        let return_type = if self.check(&TokenKind::Arrow) {
            self.advance();
            Some(self.parse_type_expr()?)
        } else {
            None
        };

        Some(InterfaceMethod {
            name,
            receiver_modifier,
            params,
            return_type,
            span: span.merge(self.prev_span()),
        })
    }

    fn parse_type_alias(&mut self, vis: Visibility) -> Option<TypeAlias> {
        self.expect(&TokenKind::Type)?;
        let name = self.expect_type_ident()?;
        self.expect(&TokenKind::Eq)?;

        // Check for `newtype` keyword (parsed as ident since it's not a keyword)
        let is_newtype = if let Some(TokenKind::Ident(ref s)) = self.peek_kind() {
            if s == "newtype" {
                self.advance();
                true
            } else {
                false
            }
        } else {
            false
        };

        let ty = self.parse_type_expr()?;

        Some(TypeAlias {
            vis,
            name,
            is_newtype,
            ty,
        })
    }

    fn parse_extern_block(&mut self) -> Option<ExternBlock> {
        let span = self.current_span();
        self.expect(&TokenKind::Extern)?;

        // Optional ABI string: extern "C"
        let abi = if let Some(TokenKind::StringLit(_)) = self.peek_kind() {
            if let TokenKind::StringLit(s) = self.advance_and_get() {
                Some(s)
            } else {
                None
            }
        } else {
            None
        };

        self.skip_newlines();

        let mut decls = Vec::new();
        if self.check(&TokenKind::Indent) {
            self.advance();
            loop {
                self.skip_newlines();
                if self.check(&TokenKind::Dedent) || self.is_at_end() {
                    break;
                }
                if let Some(decl) = self.parse_extern_fn_decl() {
                    decls.push(decl);
                } else {
                    self.advance();
                }
            }
            if self.check(&TokenKind::Dedent) {
                self.advance();
            }
        }

        Some(ExternBlock {
            abi,
            decls,
            span: span.merge(self.prev_span()),
        })
    }

    fn parse_extern_fn_decl(&mut self) -> Option<ExternFnDecl> {
        let span = self.current_span();
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

        Some(ExternFnDecl {
            name,
            params,
            return_type,
            span: span.merge(self.prev_span()),
        })
    }

    fn parse_test_def(&mut self) -> Option<TestDef> {
        self.expect(&TokenKind::Test)?;

        // Check for modifier: fuzz, property, snapshot, bench (parsed as idents)
        let modifier = if let Some(TokenKind::Ident(ref s)) = self.peek_kind() {
            match s.as_str() {
                "fuzz" => {
                    self.advance();
                    Some(TestModifier::Fuzz)
                }
                "property" => {
                    self.advance();
                    Some(TestModifier::Property)
                }
                "snapshot" => {
                    self.advance();
                    Some(TestModifier::Snapshot)
                }
                "bench" => {
                    self.advance();
                    Some(TestModifier::Bench)
                }
                _ => None,
            }
        } else {
            None
        };

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

        // Parse optional `for` clause: `for (param1: Type1, param2: Type2)` or `for param1, param2`
        let mut for_params = Vec::new();
        if self.check(&TokenKind::For) {
            self.advance();
            if self.check(&TokenKind::LParen) {
                // Parenthesized typed parameters: `for (xs: Array[i64], ys: Array[i64])`
                self.advance();
                if !self.check(&TokenKind::RParen) {
                    loop {
                        let p_span = self.current_span();
                        let p_name = self.expect_ident()?;
                        let p_ty = if self.check(&TokenKind::Colon) {
                            self.advance();
                            Some(self.parse_type_expr()?)
                        } else {
                            None
                        };
                        for_params.push(TestParam {
                            name: p_name,
                            ty: p_ty,
                            span: p_span.merge(self.prev_span()),
                        });
                        if !self.check(&TokenKind::Comma) {
                            break;
                        }
                        self.advance();
                    }
                }
                self.expect(&TokenKind::RParen)?;
            } else {
                // Unparenthesized: `for param1, param2`
                let p_span = self.current_span();
                let p_name = self.expect_ident()?;
                for_params.push(TestParam {
                    name: p_name,
                    ty: None,
                    span: p_span.merge(self.prev_span()),
                });
                while self.check(&TokenKind::Comma) {
                    self.advance();
                    let p_span = self.current_span();
                    let p_name = self.expect_ident()?;
                    for_params.push(TestParam {
                        name: p_name,
                        ty: None,
                        span: p_span.merge(self.prev_span()),
                    });
                }
            }
        }

        self.skip_newlines();
        let body = self.parse_block()?;

        Some(TestDef {
            name,
            modifier,
            for_params,
            body,
        })
    }

    fn parse_use_decl(&mut self) -> Option<UseDecl> {
        let span = self.current_span();
        self.expect(&TokenKind::Use)?;

        let mut path = Vec::new();
        // First segment can be an ident, type ident, or `pkg` keyword
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
            Some(TokenKind::Pkg) => {
                self.advance();
                path.push("pkg".to_string());
            }
            _ => {
                self.error("expected module path after `use`");
                return None;
            }
        }

        while self.check(&TokenKind::Dot) {
            self.advance();
            match self.peek_kind() {
                Some(TokenKind::LBrace) => {
                    // Grouped use: use foo.bar.{A, B, C}
                    break;
                }
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

        // Check for grouped import: {A, B, C}
        let members = if self.check(&TokenKind::LBrace) {
            self.advance();
            let mut names = Vec::new();
            if !self.check(&TokenKind::RBrace) {
                names.push(self.expect_any_ident()?);
                while self.check(&TokenKind::Comma) {
                    self.advance();
                    if self.check(&TokenKind::RBrace) {
                        break;
                    }
                    names.push(self.expect_any_ident()?);
                }
            }
            self.expect(&TokenKind::RBrace)?;
            Some(names)
        } else {
            None
        };

        Some(UseDecl {
            path,
            members,
            span: span.merge(self.prev_span()),
        })
    }

    // --- Token helpers ---

    fn peek_kind(&self) -> Option<TokenKind> {
        self.tokens.get(self.pos).map(|t| t.kind.clone())
    }

    fn peek_at_kind(&self, offset: usize) -> Option<TokenKind> {
        self.tokens.get(self.pos + offset).map(|t| t.kind.clone())
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
            Some(TokenKind::SelfUpper) => {
                self.advance();
                Some("Self".to_string())
            }
            _ => {
                self.error("expected type identifier");
                None
            }
        }
    }

    /// Accept either a lowercase ident or a type ident (PascalCase).
    fn expect_any_ident(&mut self) -> Option<String> {
        match self.peek_kind() {
            Some(TokenKind::Ident(s)) => {
                self.advance();
                Some(s)
            }
            Some(TokenKind::TypeIdent(s)) => {
                self.advance();
                Some(s)
            }
            _ => {
                self.error("expected identifier");
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
                        assert!(matches!(value.kind, ExprKind::IntLit(42, None)));
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
                assert_eq!(f.effects.len(), 1);
                assert_eq!(f.effects[0].name, "IO");
                assert!(f.effects[0].args.is_empty());
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

    // --- Match expression tests ---

    #[test]
    fn test_parse_match_basic() {
        let source = "fn main()\n    match x\n        1 => \"one\"\n        2 => \"two\"\n        _ => \"other\"\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Expr(expr) => match &expr.kind {
                        ExprKind::Match { arms, .. } => {
                            assert_eq!(arms.len(), 3);
                            assert!(matches!(arms[0].pattern.kind, PatternKind::Literal(_)));
                            assert!(matches!(arms[2].pattern.kind, PatternKind::Wildcard));
                        }
                        other => panic!("expected match, got {:?}", other),
                    },
                    _ => panic!("expected expr stmt"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_match_with_guard() {
        let source = "fn main()\n    match x\n        n if n > 0 => \"positive\"\n        _ => \"non-positive\"\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Expr(expr) => match &expr.kind {
                        ExprKind::Match { arms, .. } => {
                            assert_eq!(arms.len(), 2);
                            assert!(matches!(arms[0].pattern.kind, PatternKind::Ident(_)));
                            assert!(arms[0].guard.is_some());
                            assert!(arms[1].guard.is_none());
                        }
                        other => panic!("expected match, got {:?}", other),
                    },
                    _ => panic!("expected expr stmt"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_match_tuple_pattern() {
        let source = "fn main()\n    match point\n        {0, 0} => \"origin\"\n        {x, y} => \"other\"\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Expr(expr) => match &expr.kind {
                        ExprKind::Match { arms, .. } => {
                            assert_eq!(arms.len(), 2);
                            match &arms[0].pattern.kind {
                                PatternKind::TuplePattern(elems) => assert_eq!(elems.len(), 2),
                                other => panic!("expected tuple pattern, got {:?}", other),
                            }
                            match &arms[1].pattern.kind {
                                PatternKind::TuplePattern(elems) => {
                                    assert_eq!(elems.len(), 2);
                                    assert!(matches!(elems[0].kind, PatternKind::Ident(_)));
                                }
                                other => panic!("expected tuple pattern, got {:?}", other),
                            }
                        }
                        other => panic!("expected match, got {:?}", other),
                    },
                    _ => panic!("expected expr stmt"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_match_constructor_pattern() {
        let source = "fn main()\n    match shape\n        Shape.Circle(r) => r\n        Shape.Point => 0\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Expr(expr) => match &expr.kind {
                        ExprKind::Match { arms, .. } => {
                            assert_eq!(arms.len(), 2);
                            match &arms[0].pattern.kind {
                                PatternKind::Constructor { path, type_args, fields } => {
                                    assert_eq!(path, &["Shape", "Circle"]);
                                    assert!(type_args.is_empty());
                                    assert_eq!(fields.len(), 1);
                                }
                                other => panic!("expected constructor pattern, got {:?}", other),
                            }
                            match &arms[1].pattern.kind {
                                PatternKind::Constructor { path, type_args, fields } => {
                                    assert_eq!(path, &["Shape", "Point"]);
                                    assert!(type_args.is_empty());
                                    assert_eq!(fields.len(), 0);
                                }
                                other => panic!("expected constructor pattern, got {:?}", other),
                            }
                        }
                        other => panic!("expected match, got {:?}", other),
                    },
                    _ => panic!("expected expr stmt"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    // --- For loop tests ---

    #[test]
    fn test_parse_for_basic() {
        let source = "fn main()\n    for x in items\n        print(x)\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Expr(expr) => match &expr.kind {
                        ExprKind::For { pattern, body, .. } => {
                            assert!(matches!(pattern.kind, PatternKind::Ident(ref s) if s == "x"));
                            assert_eq!(body.len(), 1);
                        }
                        other => panic!("expected for, got {:?}", other),
                    },
                    _ => panic!("expected expr stmt"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_for_tuple_destructure() {
        let source = "fn main()\n    for {k, v} in entries\n        print(k)\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Expr(expr) => match &expr.kind {
                        ExprKind::For { pattern, .. } => {
                            match &pattern.kind {
                                PatternKind::TuplePattern(elems) => assert_eq!(elems.len(), 2),
                                other => panic!("expected tuple pattern, got {:?}", other),
                            }
                        }
                        other => panic!("expected for, got {:?}", other),
                    },
                    _ => panic!("expected expr stmt"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_for_range() {
        let source = "fn main()\n    for i in 0..10\n        print(i)\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Expr(expr) => match &expr.kind {
                        ExprKind::For { iter, .. } => {
                            assert!(matches!(iter.kind, ExprKind::Range { .. }));
                        }
                        other => panic!("expected for, got {:?}", other),
                    },
                    _ => panic!("expected expr stmt"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_break_with_value() {
        let source = "fn main()\n    for x in items\n        break 42\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Expr(expr) => match &expr.kind {
                        ExprKind::For { body, .. } => {
                            match &body[0].kind {
                                StmtKind::Break(Some(val)) => {
                                    assert!(matches!(val.kind, ExprKind::IntLit(42, None)));
                                }
                                other => panic!("expected break with value, got {:?}", other),
                            }
                        }
                        other => panic!("expected for, got {:?}", other),
                    },
                    _ => panic!("expected expr stmt"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_continue() {
        let source = "fn main()\n    for x in items\n        continue\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Expr(expr) => match &expr.kind {
                        ExprKind::For { body, .. } => {
                            assert!(matches!(body[0].kind, StmtKind::Continue));
                        }
                        other => panic!("expected for, got {:?}", other),
                    },
                    _ => panic!("expected expr stmt"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    // --- Closure tests ---

    #[test]
    fn test_parse_closure_typed() {
        let source = "fn main()\n    let f = |x: i64, y: i64| x + y\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Let { value, .. } => match &value.kind {
                        ExprKind::Closure { params, body } => {
                            assert_eq!(params.len(), 2);
                            assert_eq!(params[0].name, "x");
                            assert!(params[0].ty.is_some());
                            assert_eq!(params[1].name, "y");
                            assert!(params[1].ty.is_some());
                            assert_eq!(body.len(), 1);
                        }
                        other => panic!("expected closure, got {:?}", other),
                    },
                    _ => panic!("expected let"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_closure_untyped() {
        let source = "fn main()\n    let f = |x, y| x + y\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Let { value, .. } => match &value.kind {
                        ExprKind::Closure { params, .. } => {
                            assert_eq!(params.len(), 2);
                            assert!(params[0].ty.is_none());
                            assert!(params[1].ty.is_none());
                        }
                        other => panic!("expected closure, got {:?}", other),
                    },
                    _ => panic!("expected let"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_closure_multiline() {
        let source = "fn main()\n    let f = |x|\n        let y = x + 1\n        y\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Let { value, .. } => match &value.kind {
                        ExprKind::Closure { params, body } => {
                            assert_eq!(params.len(), 1);
                            assert_eq!(body.len(), 2);
                        }
                        other => panic!("expected closure, got {:?}", other),
                    },
                    _ => panic!("expected let"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_closure_no_params() {
        let source = "fn main()\n    let f = || 42\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Let { value, .. } => match &value.kind {
                        ExprKind::Closure { params, body } => {
                            assert_eq!(params.len(), 0);
                            assert_eq!(body.len(), 1);
                        }
                        other => panic!("expected closure, got {:?}", other),
                    },
                    _ => panic!("expected let"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    // --- New feature tests (Steps 5-13) ---

    #[test]
    fn test_parse_while_loop() {
        let source = "fn main()\n    while x > 0\n        x\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Expr(expr) => match &expr.kind {
                        ExprKind::While { body, .. } => {
                            assert_eq!(body.len(), 1);
                        }
                        other => panic!("expected while, got {:?}", other),
                    },
                    _ => panic!("expected expr stmt"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_assert_stmt() {
        let source = "fn main()\n    assert x > 0\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Assert { message, .. } => {
                        assert!(message.is_none());
                    }
                    other => panic!("expected assert, got {:?}", other),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_assert_with_message() {
        let source = "fn main()\n    assert x > 0, \"must be positive\"\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Assert { message, .. } => {
                        assert!(message.is_some());
                    }
                    other => panic!("expected assert, got {:?}", other),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_move_param() {
        let source = "fn take(move x: Vec[i32]) -> Vec[i32]\n    x\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                assert_eq!(f.params[0].modifier, ParamModifier::Move);
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_move_mut_param() {
        let source = "fn take(move mut x: Vec[i32]) -> Vec[i32]\n    x\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                assert_eq!(f.params[0].modifier, ParamModifier::MoveMut);
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_type_params() {
        let source = "fn identity[T](x: T) -> T\n    x\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                assert_eq!(f.type_params.len(), 1);
                match &f.type_params[0] {
                    TypeParam::Type { name, bounds, .. } => {
                        assert_eq!(name, "T");
                        assert!(bounds.is_empty());
                    }
                    _ => panic!("expected type param"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_type_params_with_bounds() {
        let source = "fn show[T: Display](x: T) -> str\n    x\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                assert_eq!(f.type_params.len(), 1);
                match &f.type_params[0] {
                    TypeParam::Type { name, bounds, .. } => {
                        assert_eq!(name, "T");
                        assert_eq!(bounds.len(), 1);
                        assert_eq!(bounds[0].name, "Display");
                    }
                    _ => panic!("expected type param"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_dim_type_params() {
        let source = "fn matmul[dim M, dim K, dim N](a: Tensor[f32][M, K], b: Tensor[f32][K, N]) -> Tensor[f32][M, N]\n    a\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                assert_eq!(f.type_params.len(), 3);
                for tp in &f.type_params {
                    assert!(matches!(tp, TypeParam::Dim { .. }));
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_ref_type() {
        let source = "fn name() -> &str\n    \"hello\"\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                assert!(matches!(f.return_type, Some(TypeExpr::Ref { .. })));
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_method_def() {
        let source = "impl User\n    fn display_name(self) -> &str\n        self.name\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Method(m) => {
                assert!(matches!(&m.receiver_type, TypeExpr::Named { name, args, .. } if name == "User" && args.is_empty()));
                assert_eq!(m.name, "display_name");
                assert_eq!(m.receiver_modifier, ReceiverModifier::Borrow);
            }
            other => panic!("expected method, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_method_mut_receiver() {
        let source = "impl User\n    fn set_name(mut self, name: str)\n        self.name\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Method(m) => {
                assert_eq!(m.receiver_modifier, ReceiverModifier::Mut);
            }
            other => panic!("expected method, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_constructor_def() {
        let source = "fn User.new(name: str, age: u32) -> Self\n    Self #{name: name, age: age}\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Constructor(c) => {
                assert_eq!(c.type_name, "User");
                assert_eq!(c.name, "new");
                assert_eq!(c.params.len(), 2);
            }
            other => panic!("expected constructor, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_interface() {
        let source = "interface Hashable\n    fn hash() -> u64\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Interface(i) => {
                assert_eq!(i.name, "Hashable");
                assert_eq!(i.methods.len(), 1);
                assert_eq!(i.methods[0].name, "hash");
            }
            other => panic!("expected interface, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_use_grouped() {
        let source = "use std.collections.{HashMap, HashSet}\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Use(u) => {
                assert_eq!(u.path, vec!["std", "collections"]);
                assert_eq!(u.members, Some(vec!["HashMap".to_string(), "HashSet".to_string()]));
            }
            other => panic!("expected use, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_self_expr() {
        let source = "impl User\n    fn name(self) -> &str\n        self.name\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Method(m) => {
                match &m.body[0].kind {
                    StmtKind::Expr(expr) => match &expr.kind {
                        ExprKind::Field { expr: inner, name } => {
                            assert!(matches!(inner.kind, ExprKind::Ident(ref s) if s == "self"));
                            assert_eq!(name, "name");
                        }
                        other => panic!("expected field access, got {:?}", other),
                    },
                    _ => panic!("expected expr stmt"),
                }
            }
            _ => panic!("expected method"),
        }
    }

    #[test]
    fn test_parse_call_with_move() {
        let source = "fn main()\n    consume(move x)\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Expr(expr) => match &expr.kind {
                        ExprKind::Call { args, .. } => {
                            assert_eq!(args.len(), 1);
                            assert_eq!(args[0].modifier, ParamModifier::Move);
                        }
                        other => panic!("expected call, got {:?}", other),
                    },
                    _ => panic!("expected expr stmt"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_pub_pkg() {
        let source = "pub(pkg) fn internal() -> i32\n    42\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                assert_eq!(f.vis, Visibility::PubPkg);
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_extern_block() {
        let source = "extern\n    fn c_puts(s: str) -> i32\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Extern(e) => {
                assert_eq!(e.decls.len(), 1);
                assert_eq!(e.decls[0].name, "c_puts");
            }
            other => panic!("expected extern, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_type_alias() {
        let source = "type UserId = u64\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::TypeAlias(t) => {
                assert_eq!(t.name, "UserId");
                assert!(!t.is_newtype);
            }
            other => panic!("expected type alias, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_newtype() {
        let source = "type Email = newtype str\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::TypeAlias(t) => {
                assert_eq!(t.name, "Email");
                assert!(t.is_newtype);
            }
            other => panic!("expected type alias, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_struct_with_type_params() {
        let source = "struct Pair[T, U]\n    first: T\n    second: U\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Struct(s) => {
                assert_eq!(s.type_params.len(), 2);
            }
            _ => panic!("expected struct"),
        }
    }

    #[test]
    fn test_parse_full_example() {
        // Test the full example from the plan
        let source = concat!(
            "impl User\n",
            "    fn display_name(self) -> &str\n",
            "        self.name\n",
            "\n",
            "fn User.new(name: str, age: u32) -> Self\n",
            "    Self #{name: name, age: age}\n",
            "\n",
            "interface Hashable\n",
            "    fn hash() -> u64\n",
            "\n",
            "fn matmul[dim M, dim K, dim N](a: Tensor[f32][M, K], b: Tensor[f32][K, N]) -> Tensor[f32][M, N]\n",
            "    a\n",
        );
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        assert_eq!(file.items.len(), 4);
        assert!(matches!(file.items[0].kind, ItemKind::Method(_)));
        assert!(matches!(file.items[1].kind, ItemKind::Constructor(_)));
        assert!(matches!(file.items[2].kind, ItemKind::Interface(_)));
        assert!(matches!(file.items[3].kind, ItemKind::Function(_)));
    }

    // =======================================================================
    // Phase 2 tests — Batches 1–7
    // =======================================================================

    // --- Batch 1: Assignment + Try (?) ---

    #[test]
    fn test_parse_assign_simple() {
        let source = "fn main()\n    x = 42\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Assign { target, value } => {
                        assert!(matches!(target.kind, ExprKind::Ident(ref s) if s == "x"));
                        assert!(matches!(value.kind, ExprKind::IntLit(42, None)));
                    }
                    other => panic!("expected assign, got {:?}", other),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_assign_field() {
        let source = "impl User\n    fn rename(mut self, new_name: str)\n        self.name = new_name\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Method(m) => {
                match &m.body[0].kind {
                    StmtKind::Assign { target, .. } => {
                        match &target.kind {
                            ExprKind::Field { expr, name } => {
                                assert!(matches!(expr.kind, ExprKind::Ident(ref s) if s == "self"));
                                assert_eq!(name, "name");
                            }
                            other => panic!("expected field access, got {:?}", other),
                        }
                    }
                    other => panic!("expected assign, got {:?}", other),
                }
            }
            _ => panic!("expected method"),
        }
    }

    #[test]
    fn test_parse_assign_chain() {
        let source = "fn main()\n    a.b.c = 1\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                assert!(matches!(f.body[0].kind, StmtKind::Assign { .. }));
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_try_postfix() {
        let source = "fn main()\n    let x = foo()?\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Let { value, .. } => {
                        assert!(matches!(value.kind, ExprKind::Try(_)));
                    }
                    other => panic!("expected let, got {:?}", other),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_try_chained() {
        let source = "fn main()\n    let x = foo()?.bar()?\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Let { value, .. } => {
                        // outer should be Try
                        match &value.kind {
                            ExprKind::Try(inner) => {
                                // inner should be Call
                                assert!(matches!(inner.kind, ExprKind::Call { .. }));
                            }
                            other => panic!("expected try, got {:?}", other),
                        }
                    }
                    other => panic!("expected let, got {:?}", other),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_try_then_field() {
        let source = "fn main()\n    let x = a.b()?.c\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Let { value, .. } => {
                        // Should be Field access on a Try
                        match &value.kind {
                            ExprKind::Field { expr, name } => {
                                assert_eq!(name, "c");
                                assert!(matches!(expr.kind, ExprKind::Try(_)));
                            }
                            other => panic!("expected field, got {:?}", other),
                        }
                    }
                    other => panic!("expected let, got {:?}", other),
                }
            }
            _ => panic!("expected function"),
        }
    }

    // --- Batch 2: OR pattern + Rest pattern ---

    #[test]
    fn test_parse_or_pattern_simple() {
        let source = "fn main()\n    match x\n        1 | 2 => \"small\"\n        _ => \"other\"\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Expr(expr) => match &expr.kind {
                        ExprKind::Match { arms, .. } => {
                            match &arms[0].pattern.kind {
                                PatternKind::Or(alts) => assert_eq!(alts.len(), 2),
                                other => panic!("expected or pattern, got {:?}", other),
                            }
                        }
                        other => panic!("expected match, got {:?}", other),
                    },
                    _ => panic!("expected expr stmt"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_or_pattern_triple() {
        let source = "fn main()\n    match x\n        1 | 2 | 3 => \"small\"\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Expr(expr) => match &expr.kind {
                        ExprKind::Match { arms, .. } => {
                            match &arms[0].pattern.kind {
                                PatternKind::Or(alts) => assert_eq!(alts.len(), 3),
                                other => panic!("expected or pattern, got {:?}", other),
                            }
                        }
                        _ => panic!("expected match"),
                    },
                    _ => panic!("expected expr stmt"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_or_pattern_constructor() {
        let source = "fn main()\n    match s\n        Shape.Circle(r) | Shape.Point => \"ok\"\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Expr(expr) => match &expr.kind {
                        ExprKind::Match { arms, .. } => {
                            match &arms[0].pattern.kind {
                                PatternKind::Or(alts) => {
                                    assert_eq!(alts.len(), 2);
                                    assert!(matches!(alts[0].kind, PatternKind::Constructor { .. }));
                                    assert!(matches!(alts[1].kind, PatternKind::Constructor { .. }));
                                }
                                other => panic!("expected or pattern, got {:?}", other),
                            }
                        }
                        _ => panic!("expected match"),
                    },
                    _ => panic!("expected expr stmt"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_rest_pattern() {
        let source = "fn main()\n    match t\n        {a, ..} => a\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Expr(expr) => match &expr.kind {
                        ExprKind::Match { arms, .. } => {
                            match &arms[0].pattern.kind {
                                PatternKind::TuplePattern(elems) => {
                                    assert_eq!(elems.len(), 2);
                                    assert!(matches!(elems[0].kind, PatternKind::Ident(ref s) if s == "a"));
                                    assert!(matches!(elems[1].kind, PatternKind::Rest(None)));
                                }
                                other => panic!("expected tuple pattern, got {:?}", other),
                            }
                        }
                        _ => panic!("expected match"),
                    },
                    _ => panic!("expected expr stmt"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_rest_pattern_named() {
        let source = "fn main()\n    match t\n        {first, ..rest} => first\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Expr(expr) => match &expr.kind {
                        ExprKind::Match { arms, .. } => {
                            match &arms[0].pattern.kind {
                                PatternKind::TuplePattern(elems) => {
                                    assert_eq!(elems.len(), 2);
                                    assert!(matches!(elems[1].kind, PatternKind::Rest(Some(ref s)) if s == "rest"));
                                }
                                other => panic!("expected tuple pattern, got {:?}", other),
                            }
                        }
                        _ => panic!("expected match"),
                    },
                    _ => panic!("expected expr stmt"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    // --- Batch 3: List pattern + Struct pattern ---

    #[test]
    fn test_parse_list_pattern_empty() {
        let source = "fn main()\n    match lst\n        [] => \"empty\"\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Expr(expr) => match &expr.kind {
                        ExprKind::Match { arms, .. } => {
                            match &arms[0].pattern.kind {
                                PatternKind::List(elems) => assert_eq!(elems.len(), 0),
                                other => panic!("expected list pattern, got {:?}", other),
                            }
                        }
                        _ => panic!("expected match"),
                    },
                    _ => panic!("expected expr stmt"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_list_pattern_single() {
        let source = "fn main()\n    match lst\n        [x] => \"one\"\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Expr(expr) => match &expr.kind {
                        ExprKind::Match { arms, .. } => {
                            match &arms[0].pattern.kind {
                                PatternKind::List(elems) => {
                                    assert_eq!(elems.len(), 1);
                                    assert!(matches!(elems[0].kind, PatternKind::Ident(ref s) if s == "x"));
                                }
                                other => panic!("expected list pattern, got {:?}", other),
                            }
                        }
                        _ => panic!("expected match"),
                    },
                    _ => panic!("expected expr stmt"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_list_pattern_rest() {
        let source = "fn main()\n    match lst\n        [first, ..rest] => first\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Expr(expr) => match &expr.kind {
                        ExprKind::Match { arms, .. } => {
                            match &arms[0].pattern.kind {
                                PatternKind::List(elems) => {
                                    assert_eq!(elems.len(), 2);
                                    assert!(matches!(elems[0].kind, PatternKind::Ident(ref s) if s == "first"));
                                    assert!(matches!(elems[1].kind, PatternKind::Rest(Some(ref s)) if s == "rest"));
                                }
                                other => panic!("expected list pattern, got {:?}", other),
                            }
                        }
                        _ => panic!("expected match"),
                    },
                    _ => panic!("expected expr stmt"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_struct_pattern() {
        let source = "fn main()\n    match u\n        User #{name, age} => name\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Expr(expr) => match &expr.kind {
                        ExprKind::Match { arms, .. } => {
                            match &arms[0].pattern.kind {
                                PatternKind::Struct { name, fields, has_rest } => {
                                    assert_eq!(name, "User");
                                    assert_eq!(fields.len(), 2);
                                    assert_eq!(fields[0].name, "name");
                                    assert!(fields[0].pattern.is_none());
                                    assert_eq!(fields[1].name, "age");
                                    assert!(!has_rest);
                                }
                                other => panic!("expected struct pattern, got {:?}", other),
                            }
                        }
                        _ => panic!("expected match"),
                    },
                    _ => panic!("expected expr stmt"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_struct_pattern_with_rest() {
        let source = "fn main()\n    match u\n        User #{name, ..} => name\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Expr(expr) => match &expr.kind {
                        ExprKind::Match { arms, .. } => {
                            match &arms[0].pattern.kind {
                                PatternKind::Struct { name, fields, has_rest } => {
                                    assert_eq!(name, "User");
                                    assert_eq!(fields.len(), 1);
                                    assert!(*has_rest);
                                }
                                other => panic!("expected struct pattern, got {:?}", other),
                            }
                        }
                        _ => panic!("expected match"),
                    },
                    _ => panic!("expected expr stmt"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_struct_pattern_renamed() {
        let source = "fn main()\n    match u\n        User #{name: n, age} => n\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Expr(expr) => match &expr.kind {
                        ExprKind::Match { arms, .. } => {
                            match &arms[0].pattern.kind {
                                PatternKind::Struct { fields, .. } => {
                                    assert_eq!(fields[0].name, "name");
                                    match &fields[0].pattern {
                                        Some(p) => assert!(matches!(p.kind, PatternKind::Ident(ref s) if s == "n")),
                                        None => panic!("expected rename pattern"),
                                    }
                                }
                                other => panic!("expected struct pattern, got {:?}", other),
                            }
                        }
                        _ => panic!("expected match"),
                    },
                    _ => panic!("expected expr stmt"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    // --- Batch 4: Let pattern + Slice type ---

    #[test]
    fn test_parse_let_tuple_destructure() {
        let source = "fn main()\n    let {x, y} = point\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::LetPattern { pattern, .. } => {
                        assert!(matches!(pattern.kind, PatternKind::TuplePattern(_)));
                    }
                    other => panic!("expected let pattern, got {:?}", other),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_let_tuple_rest() {
        let source = "fn main()\n    let {data, ..} = view\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::LetPattern { pattern, .. } => {
                        match &pattern.kind {
                            PatternKind::TuplePattern(elems) => {
                                assert_eq!(elems.len(), 2);
                                assert!(matches!(elems[1].kind, PatternKind::Rest(None)));
                            }
                            other => panic!("expected tuple pattern, got {:?}", other),
                        }
                    }
                    other => panic!("expected let pattern, got {:?}", other),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_let_list_destructure() {
        let source = "fn main()\n    let [first, ..rest] = items\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::LetPattern { pattern, .. } => {
                        match &pattern.kind {
                            PatternKind::List(elems) => {
                                assert_eq!(elems.len(), 2);
                                assert!(matches!(elems[0].kind, PatternKind::Ident(ref s) if s == "first"));
                                assert!(matches!(elems[1].kind, PatternKind::Rest(Some(ref s)) if s == "rest"));
                            }
                            other => panic!("expected list pattern, got {:?}", other),
                        }
                    }
                    other => panic!("expected let pattern, got {:?}", other),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_slice_type() {
        let source = "fn sum(items: &[i64]) -> i64\n    0\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.params[0].ty {
                    TypeExpr::Slice { inner, .. } => {
                        assert!(matches!(**inner, TypeExpr::Named { ref name, .. } if name == "i64"));
                    }
                    other => panic!("expected slice type, got {:?}", other),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_slice_return_type() {
        let source = "fn get() -> &[i64]\n    items\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                assert!(matches!(f.return_type, Some(TypeExpr::Slice { .. })));
            }
            _ => panic!("expected function"),
        }
    }

    // --- Batch 5: String interpolation ---

    #[test]
    fn test_parse_string_interp_simple() {
        let source = "fn main()\n    let x = \"Hello, {name}\"\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Let { value, .. } => {
                        match &value.kind {
                            ExprKind::StringInterp { parts } => {
                                assert_eq!(parts.len(), 2);
                                assert!(matches!(&parts[0], StringInterpPart::Literal(s) if s == "Hello, "));
                                assert!(matches!(&parts[1], StringInterpPart::Expr(e) if matches!(e.kind, ExprKind::Ident(ref s) if s == "name")));
                            }
                            other => panic!("expected string interp, got {:?}", other),
                        }
                    }
                    _ => panic!("expected let"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_string_no_interp() {
        let source = "fn main()\n    let x = \"no interp\"\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Let { value, .. } => {
                        assert!(matches!(value.kind, ExprKind::StringLit(ref s) if s == "no interp"));
                    }
                    _ => panic!("expected let"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_string_interp_multi() {
        let source = "fn main()\n    let x = \"a {x} b {y} c\"\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Let { value, .. } => {
                        match &value.kind {
                            ExprKind::StringInterp { parts } => {
                                // "a " + x + " b " + y + " c"
                                assert_eq!(parts.len(), 5);
                                assert!(matches!(&parts[0], StringInterpPart::Literal(s) if s == "a "));
                                assert!(matches!(&parts[1], StringInterpPart::Expr(_)));
                                assert!(matches!(&parts[2], StringInterpPart::Literal(s) if s == " b "));
                                assert!(matches!(&parts[3], StringInterpPart::Expr(_)));
                                assert!(matches!(&parts[4], StringInterpPart::Literal(s) if s == " c"));
                            }
                            other => panic!("expected string interp, got {:?}", other),
                        }
                    }
                    _ => panic!("expected let"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_string_interp_escaped() {
        let source = "fn main()\n    let x = \"\\{escaped}\"\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Let { value, .. } => {
                        // \{ should produce literal {, so no interpolation
                        assert!(matches!(value.kind, ExprKind::StringLit(ref s) if s == "{escaped}"));
                    }
                    _ => panic!("expected let"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_string_interp_expr() {
        let source = "fn main()\n    let x = \"{a + b}\"\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Let { value, .. } => {
                        match &value.kind {
                            ExprKind::StringInterp { parts } => {
                                assert_eq!(parts.len(), 1);
                                match &parts[0] {
                                    StringInterpPart::Expr(e) => {
                                        assert!(matches!(e.kind, ExprKind::BinOp { op: BinOp::Add, .. }));
                                    }
                                    other => panic!("expected expr part, got {:?}", other),
                                }
                            }
                            other => panic!("expected string interp, got {:?}", other),
                        }
                    }
                    _ => panic!("expected let"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    // --- Batch 6: Interface method modifier + Extern ABI ---

    #[test]
    fn test_parse_interface_method_mut() {
        let source = "interface MutableCollection\n    fn clear(mut self)\n    fn len() -> usize\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Interface(i) => {
                assert_eq!(i.name, "MutableCollection");
                assert_eq!(i.methods.len(), 2);
                assert_eq!(i.methods[0].name, "clear");
                assert_eq!(i.methods[0].receiver_modifier, Some(ReceiverModifier::Mut));
                assert_eq!(i.methods[1].name, "len");
                assert_eq!(i.methods[1].receiver_modifier, None);
            }
            other => panic!("expected interface, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_interface_method_move() {
        let source = "interface Consumable\n    fn consume(move self) -> Data\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Interface(i) => {
                assert_eq!(i.methods[0].name, "consume");
                assert_eq!(i.methods[0].receiver_modifier, Some(ReceiverModifier::Move));
            }
            other => panic!("expected interface, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_extern_abi() {
        let source = "extern \"C\"\n    fn malloc(size: usize) -> Ptr[{}]\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Extern(e) => {
                assert_eq!(e.abi, Some("C".to_string()));
                assert_eq!(e.decls.len(), 1);
                assert_eq!(e.decls[0].name, "malloc");
            }
            other => panic!("expected extern, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_extern_no_abi() {
        let source = "extern\n    fn custom_fn(x: i64)\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Extern(e) => {
                assert_eq!(e.abi, None);
                assert_eq!(e.decls.len(), 1);
            }
            other => panic!("expected extern, got {:?}", other),
        }
    }

    // --- Batch 7: Test modifiers + Dim ? ---

    #[test]
    fn test_parse_test_property() {
        let source = "test property \"sort idempotent\" for (xs: Array[i64])\n    assert xs.sort() == xs.sort().sort()\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Test(t) => {
                assert_eq!(t.name, "sort idempotent");
                assert_eq!(t.modifier, Some(TestModifier::Property));
                assert_eq!(t.for_params.len(), 1);
                assert_eq!(t.for_params[0].name, "xs");
                assert!(t.for_params[0].ty.is_some());
                match &t.for_params[0].ty {
                    Some(TypeExpr::Named { name, args, .. }) => {
                        assert_eq!(name, "Array");
                        assert_eq!(args.len(), 1);
                    }
                    other => panic!("expected Array[i64], got {:?}", other),
                }
            }
            other => panic!("expected test, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_test_snapshot() {
        let source = "test snapshot \"renders correctly\"\n    assert true\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Test(t) => {
                assert_eq!(t.modifier, Some(TestModifier::Snapshot));
            }
            other => panic!("expected test, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_test_bench() {
        let source = "test bench \"fast sort\"\n    sort(data)\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Test(t) => {
                assert_eq!(t.modifier, Some(TestModifier::Bench));
            }
            other => panic!("expected test, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_dim_question_wildcard() {
        let source = "fn process(t: Tensor[f32][?, 784]) -> Tensor[f32][?, 10]\n    t\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.params[0].ty {
                    TypeExpr::DimApply { dims, .. } => {
                        assert_eq!(dims.len(), 2);
                        assert!(matches!(dims[0], DimExpr::Wildcard));
                        assert!(matches!(dims[1], DimExpr::Lit(784)));
                    }
                    other => panic!("expected dim apply, got {:?}", other),
                }
            }
            _ => panic!("expected function"),
        }
    }

    // --- P1 gap fixes: Fn type, .await, &expr ---

    #[test]
    fn test_parse_fn_type_simple() {
        let source = "fn apply(f: Fn(i64) -> i64, x: i64) -> i64\n    f(x)\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.params[0].ty {
                    TypeExpr::Fn { params, ret, .. } => {
                        assert_eq!(params.len(), 1);
                        assert!(matches!(params[0], TypeExpr::Named { ref name, .. } if name == "i64"));
                        assert!(matches!(**ret, TypeExpr::Named { ref name, .. } if name == "i64"));
                    }
                    other => panic!("expected Fn type, got {:?}", other),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_fn_type_no_params() {
        let source = "fn run(f: Fn() -> {}) -> {}\n    f()\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.params[0].ty {
                    TypeExpr::Fn { params, .. } => {
                        assert_eq!(params.len(), 0);
                    }
                    other => panic!("expected Fn type, got {:?}", other),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_fn_type_multi_params() {
        let source = "fn apply2(f: Fn(i64, str) -> bool) -> bool\n    f(1, \"a\")\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.params[0].ty {
                    TypeExpr::Fn { params, ret, .. } => {
                        assert_eq!(params.len(), 2);
                        assert!(matches!(**ret, TypeExpr::Named { ref name, .. } if name == "bool"));
                    }
                    other => panic!("expected Fn type, got {:?}", other),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_fn_type_return() {
        let source = "fn make_filter(move prefix: String) -> Fn(&str) -> bool\n    |s| s.starts_with(prefix)\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.return_type {
                    Some(TypeExpr::Fn { params, ret, .. }) => {
                        assert_eq!(params.len(), 1);
                        assert!(matches!(params[0], TypeExpr::Ref { .. }));
                        assert!(matches!(**ret, TypeExpr::Named { ref name, .. } if name == "bool"));
                    }
                    other => panic!("expected Fn return type, got {:?}", other),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_await_expr() {
        let source = "fn fetch(url: &str) -> Result[Data, Error] with IO, Async\n    let data = http.get(url).await\n    data\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Let { value, .. } => {
                        assert!(matches!(value.kind, ExprKind::Await(_)));
                    }
                    other => panic!("expected let, got {:?}", other),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_await_chained() {
        let source = "fn main()\n    let x = fetch().await.parse()\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Let { value, .. } => {
                        // Should be Call(Field(Await(Call(...)), "parse"))
                        match &value.kind {
                            ExprKind::Call { func, .. } => {
                                match &func.kind {
                                    ExprKind::Field { expr, name } => {
                                        assert_eq!(name, "parse");
                                        assert!(matches!(expr.kind, ExprKind::Await(_)));
                                    }
                                    other => panic!("expected field, got {:?}", other),
                                }
                            }
                            other => panic!("expected call, got {:?}", other),
                        }
                    }
                    _ => panic!("expected let"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_ref_expr() {
        let source = "fn main()\n    let x = &\"hello\"\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Let { value, .. } => {
                        match &value.kind {
                            ExprKind::Ref(inner) => {
                                assert!(matches!(inner.kind, ExprKind::StringLit(ref s) if s == "hello"));
                            }
                            other => panic!("expected ref, got {:?}", other),
                        }
                    }
                    _ => panic!("expected let"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_ref_in_call() {
        let source = "fn main()\n    contains(&\"@\")\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                match &f.body[0].kind {
                    StmtKind::Expr(expr) => match &expr.kind {
                        ExprKind::Call { args, .. } => {
                            assert_eq!(args.len(), 1);
                            assert!(matches!(args[0].expr.kind, ExprKind::Ref(_)));
                        }
                        other => panic!("expected call, got {:?}", other),
                    },
                    _ => panic!("expected expr stmt"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    // --- P2/P3: CharLit, numeric suffixes, turbofish, parameterized effects, generic receiver, line continuation ---

    #[test]
    fn test_parse_char_lit() {
        let source = "fn main()\n    let c = 'A'\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => match &f.body[0].kind {
                StmtKind::Let { value, .. } => {
                    assert!(matches!(value.kind, ExprKind::CharLit('A')));
                }
                _ => panic!("expected let"),
            },
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_int_suffix() {
        let source = "fn main()\n    let x = 42_i32\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => match &f.body[0].kind {
                StmtKind::Let { value, .. } => match &value.kind {
                    ExprKind::IntLit(42, Some(suffix)) => {
                        assert_eq!(suffix, "i32");
                    }
                    other => panic!("expected IntLit(42, Some(\"i32\")), got {:?}", other),
                },
                _ => panic!("expected let"),
            },
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_int_no_suffix() {
        let source = "fn main()\n    let x = 1_000\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => match &f.body[0].kind {
                StmtKind::Let { value, .. } => match &value.kind {
                    ExprKind::IntLit(1000, None) => {}
                    other => panic!("expected IntLit(1000, None), got {:?}", other),
                },
                _ => panic!("expected let"),
            },
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_float_suffix() {
        let source = "fn main()\n    let x = 3.14_f32\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => match &f.body[0].kind {
                StmtKind::Let { value, .. } => match &value.kind {
                    ExprKind::FloatLit(_, Some(suffix)) => {
                        assert_eq!(suffix, "f32");
                    }
                    other => panic!("expected FloatLit with suffix f32, got {:?}", other),
                },
                _ => panic!("expected let"),
            },
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_turbofish_call() {
        let source = "fn main()\n    parse[Config](\"config.toml\")\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => match &f.body[0].kind {
                StmtKind::Expr(expr) => match &expr.kind {
                    ExprKind::Call { func, args } => {
                        match &func.kind {
                            ExprKind::TypeApp { expr: inner, type_args } => {
                                assert!(matches!(&inner.kind, ExprKind::Ident(s) if s == "parse"));
                                assert_eq!(type_args.len(), 1);
                            }
                            other => panic!("expected TypeApp, got {:?}", other),
                        }
                        assert_eq!(args.len(), 1);
                    }
                    other => panic!("expected Call, got {:?}", other),
                },
                _ => panic!("expected expr stmt"),
            },
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_turbofish_method() {
        let source = "fn main()\n    HashMap[String, i64].new()\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => match &f.body[0].kind {
                StmtKind::Expr(expr) => match &expr.kind {
                    ExprKind::Call { func, .. } => {
                        // func should be Field { expr: TypeApp { HashMap, [String, i64] }, name: "new" }
                        match &func.kind {
                            ExprKind::Field { expr: base, name } => {
                                assert_eq!(name, "new");
                                assert!(matches!(&base.kind, ExprKind::TypeApp { type_args, .. } if type_args.len() == 2));
                            }
                            other => panic!("expected Field, got {:?}", other),
                        }
                    }
                    other => panic!("expected Call, got {:?}", other),
                },
                _ => panic!("expected expr stmt"),
            },
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_parameterized_effects() {
        let source = "fn run(config: Config) -> Result[Data, Error] with IO, State[Config]\n    config\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                assert_eq!(f.effects.len(), 2);
                assert_eq!(f.effects[0].name, "IO");
                assert!(f.effects[0].args.is_empty());
                assert_eq!(f.effects[1].name, "State");
                assert_eq!(f.effects[1].args.len(), 1);
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_generic_receiver_type() {
        let source = "impl[T] Vec[T]\n    fn len(self) -> usize\n        0\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Method(m) => {
                match &m.receiver_type {
                    TypeExpr::Named { name, args, .. } => {
                        assert_eq!(name, "Vec");
                        assert_eq!(args.len(), 1);
                    }
                    other => panic!("expected Named type, got {:?}", other),
                }
                assert_eq!(m.name, "len");
            }
            _ => panic!("expected method"),
        }
    }

    #[test]
    fn test_parse_line_continuation() {
        // Line ending with `+` should suppress newline
        let source = "fn main()\n    let x = 1 +\n        2\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => match &f.body[0].kind {
                StmtKind::Let { value, .. } => match &value.kind {
                    ExprKind::BinOp { op, .. } => {
                        assert_eq!(*op, BinOp::Add);
                    }
                    other => panic!("expected BinOp(Add), got {:?}", other),
                },
                _ => panic!("expected let"),
            },
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_line_continuation_dot() {
        // Line ending with `.` should suppress newline
        let source = "fn main()\n    foo.\n        bar().\n        baz()\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => {
                assert_eq!(f.body.len(), 1);
                // Should be a single chained call: foo.bar().baz()
                match &f.body[0].kind {
                    StmtKind::Expr(expr) => match &expr.kind {
                        ExprKind::Call { func, .. } => {
                            match &func.kind {
                                ExprKind::Field { name, .. } => assert_eq!(name, "baz"),
                                other => panic!("expected Field(baz), got {:?}", other),
                            }
                        }
                        other => panic!("expected Call, got {:?}", other),
                    },
                    _ => panic!("expected expr stmt"),
                }
            }
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_line_continuation_comma() {
        // Line ending with `,` should suppress newline (multi-line args)
        let source = "fn main()\n    foo(1,\n        2,\n        3)\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => match &f.body[0].kind {
                StmtKind::Expr(expr) => match &expr.kind {
                    ExprKind::Call { args, .. } => {
                        assert_eq!(args.len(), 3);
                    }
                    other => panic!("expected Call with 3 args, got {:?}", other),
                },
                _ => panic!("expected expr stmt"),
            },
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_hex_int_suffix() {
        let source = "fn main()\n    let x = 0xff_u8\n";
        let (file, diagnostics) = parse(source, "test.ax");
        assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics);
        match &file.items[0].kind {
            ItemKind::Function(f) => match &f.body[0].kind {
                StmtKind::Let { value, .. } => match &value.kind {
                    ExprKind::IntLit(255, Some(suffix)) => {
                        assert_eq!(suffix, "u8");
                    }
                    other => panic!("expected IntLit(255, Some(\"u8\")), got {:?}", other),
                },
                _ => panic!("expected let"),
            },
            _ => panic!("expected function"),
        }
    }

    #[test]
    fn test_parse_full_spec_example() {
        let source = concat!(
            "fn parse_config(path: &str) -> Result[Config, AppError] with IO\n",
            "    let content = fs.read_to_str(path)?\n",
            "    let parsed = toml.parse(content)?\n",
            "    Ok(Config.from(parsed))\n",
            "\n",
            "fn describe(value: Value) -> String\n",
            "    match value\n",
            "        Value.Int(n) if n > 0 => \"positive: {n}\"\n",
            "        Value.Int(0) => \"zero\"\n",
            "        Value.Str(s) | Value.Label(s) => \"text: {s}\"\n",
            "        Value.List([first, ..rest]) => \"list\"\n",
            "        _ => \"other\"\n",
            "\n",
            "impl User\n",
            "    fn rename(mut self, new_name: String)\n",
            "        self.name = new_name\n",
            "\n",
            "let {data, ..} = view\n",
            "\n",
            "interface MutableCollection\n",
            "    fn clear(mut self)\n",
            "    fn len() -> usize\n",
            "\n",
            "extern \"C\"\n",
            "    fn malloc(size: usize) -> Ptr[{}]\n",
            "\n",
            "test property \"sort idempotent\" for (xs: Array[i64])\n",
            "    assert xs.sort() == xs.sort().sort()\n",
        );
        let (file, diagnostics) = parse(source, "test.ax");
        // Some items like bare `let` at top level won't parse as items,
        // but we check that most parse successfully
        assert!(
            diagnostics.len() <= 2,
            "too many errors: {:?}",
            diagnostics
        );
        // We should have at least 5 successfully parsed items
        assert!(file.items.len() >= 5, "expected >= 5 items, got {}: {:?}", file.items.len(), file.items.iter().map(|i| &i.kind).collect::<Vec<_>>());
    }
}
