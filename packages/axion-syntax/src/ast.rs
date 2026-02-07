use crate::Span;

/// A complete Axion source file.
#[derive(Debug, Clone, PartialEq)]
pub struct SourceFile {
    pub items: Vec<Item>,
}

/// A top-level item.
#[derive(Debug, Clone, PartialEq)]
pub struct Item {
    pub kind: ItemKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ItemKind {
    Function(FnDef),
    Struct(StructDef),
    Enum(EnumDef),
    Trait(TraitDef),
    Impl(ImplBlock),
    TypeAlias(TypeAlias),
    Use(UseDecl),
    Test(TestDef),
}

/// Function definition.
#[derive(Debug, Clone, PartialEq)]
pub struct FnDef {
    pub is_pub: bool,
    pub name: String,
    pub params: Vec<Param>,
    pub return_type: Option<TypeExpr>,
    pub effects: Vec<String>,
    pub body: Vec<Stmt>,
}

/// Function parameter.
#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub name: String,
    pub ty: TypeExpr,
    pub is_mut: bool,
    pub span: Span,
}

/// A type expression.
#[derive(Debug, Clone, PartialEq)]
pub enum TypeExpr {
    /// A named type, e.g. `i64`, `str`, `Vec[T]`
    Named {
        name: String,
        args: Vec<TypeExpr>,
        span: Span,
    },
    /// Tuple type, e.g. `{i64, str}` (empty `{}` is the unit type)
    Tuple {
        elements: Vec<TypeExpr>,
        span: Span,
    },
    /// Function type, e.g. `Fn(i64) -> bool`
    Fn {
        params: Vec<TypeExpr>,
        ret: Box<TypeExpr>,
        span: Span,
    },
}

/// Struct definition.
#[derive(Debug, Clone, PartialEq)]
pub struct StructDef {
    pub is_pub: bool,
    pub name: String,
    pub fields: Vec<FieldDef>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FieldDef {
    pub is_pub: bool,
    pub is_mut: bool,
    pub name: String,
    pub ty: TypeExpr,
    pub span: Span,
}

/// Enum definition.
#[derive(Debug, Clone, PartialEq)]
pub struct EnumDef {
    pub is_pub: bool,
    pub name: String,
    pub variants: Vec<VariantDef>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct VariantDef {
    pub name: String,
    pub fields: Vec<FieldDef>,
    pub span: Span,
}

/// Trait definition.
#[derive(Debug, Clone, PartialEq)]
pub struct TraitDef {
    pub is_pub: bool,
    pub name: String,
    pub methods: Vec<FnDef>,
}

/// Impl block.
#[derive(Debug, Clone, PartialEq)]
pub struct ImplBlock {
    pub trait_name: Option<String>,
    pub target: String,
    pub methods: Vec<FnDef>,
}

/// Type alias.
#[derive(Debug, Clone, PartialEq)]
pub struct TypeAlias {
    pub is_pub: bool,
    pub name: String,
    pub ty: TypeExpr,
}

/// Use declaration.
#[derive(Debug, Clone, PartialEq)]
pub struct UseDecl {
    pub path: Vec<String>,
    pub span: Span,
}

/// Test definition.
#[derive(Debug, Clone, PartialEq)]
pub struct TestDef {
    pub name: String,
    pub body: Vec<Stmt>,
}

/// A statement.
#[derive(Debug, Clone, PartialEq)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum StmtKind {
    /// `let [mut] name [: type] = expr`
    Let {
        is_mut: bool,
        name: String,
        ty: Option<TypeExpr>,
        value: Expr,
    },
    /// Expression statement
    Expr(Expr),
    /// `return [expr]`
    Return(Option<Expr>),
}

/// An expression.
#[derive(Debug, Clone, PartialEq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExprKind {
    /// Integer literal
    IntLit(i128),
    /// Float literal
    FloatLit(f64),
    /// String literal
    StringLit(String),
    /// Bool literal
    BoolLit(bool),
    /// Variable reference
    Ident(String),
    /// Binary operation: `a + b`
    BinOp {
        op: BinOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    /// Unary operation: `-x`, `!x`
    UnaryOp {
        op: UnaryOp,
        operand: Box<Expr>,
    },
    /// Function call: `f(args...)`
    Call {
        func: Box<Expr>,
        args: Vec<Expr>,
    },
    /// Field access: `x.field`
    Field {
        expr: Box<Expr>,
        name: String,
    },
    /// If expression
    If {
        cond: Box<Expr>,
        then_branch: Vec<Stmt>,
        else_branch: Option<Vec<Stmt>>,
    },
    /// Match expression
    Match {
        expr: Box<Expr>,
        arms: Vec<MatchArm>,
    },
    /// Tuple literal, e.g. `{1, 2}` (empty `{}` is the unit value)
    TupleLit(Vec<Expr>),
    /// Struct literal, e.g. `User #{name: "Alice", age: 30}`
    StructLit {
        name: String,
        fields: Vec<FieldInit>,
    },
    /// Map literal, e.g. `#{"key" => value}`
    MapLit(Vec<MapEntry>),
    /// Set literal, e.g. `#{1, 2, 3}`
    SetLit(Vec<Expr>),
    /// Block expression (sequence of statements, last is the value)
    Block(Vec<Stmt>),
}

/// A field initializer in a struct literal.
#[derive(Debug, Clone, PartialEq)]
pub struct FieldInit {
    pub name: String,
    pub value: Expr,
    pub span: Span,
}

/// A key-value entry in a map literal.
#[derive(Debug, Clone, PartialEq)]
pub struct MapEntry {
    pub key: Expr,
    pub value: Expr,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Eq,
    NotEq,
    Lt,
    LtEq,
    Gt,
    GtEq,
    And,
    Or,
    Pipe, // |>
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
    Not,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub guard: Option<Expr>,
    pub body: Vec<Stmt>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Pattern {
    pub kind: PatternKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum PatternKind {
    /// Wildcard `_`
    Wildcard,
    /// Binding: `x`
    Ident(String),
    /// Literal pattern: `42`, `"hello"`, `true`
    Literal(Expr),
    /// Constructor: `Shape.Circle(r)`
    Constructor {
        path: Vec<String>,
        fields: Vec<Pattern>,
    },
}
