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
    Method(MethodDef),
    Constructor(ConstructorDef),
    Struct(StructDef),
    Enum(EnumDef),
    Interface(InterfaceDef),
    TypeAlias(TypeAlias),
    Use(UseDecl),
    Extern(ExternBlock),
    Test(TestDef),
}

// --- Visibility ---

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Visibility {
    Private,
    Pub,
    PubPkg,
}

// --- Parameter modifier ---

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParamModifier {
    None,
    Mut,
    Move,
    MoveMut,
}

// --- Type parameters ---

#[derive(Debug, Clone, PartialEq)]
pub enum TypeParam {
    /// `T` or `T: Bound1 + Bound2`
    Type {
        name: String,
        bounds: Vec<InterfaceBound>,
        span: Span,
    },
    /// `const N: usize`
    Const {
        name: String,
        ty: TypeExpr,
        span: Span,
    },
    /// `dim M`
    Dim {
        name: String,
        span: Span,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct InterfaceBound {
    pub name: String,
    pub args: Vec<TypeExpr>,
    pub span: Span,
}

// --- Function definition ---

#[derive(Debug, Clone, PartialEq)]
pub struct FnDef {
    pub vis: Visibility,
    pub name: String,
    pub type_params: Vec<TypeParam>,
    pub params: Vec<Param>,
    pub return_type: Option<TypeExpr>,
    pub effects: Vec<Effect>,
    pub body: Vec<Stmt>,
}

/// An effect in a `with` clause, e.g. `IO`, `State[Config]`
#[derive(Debug, Clone, PartialEq)]
pub struct Effect {
    pub name: String,
    pub args: Vec<TypeExpr>,
    pub span: Span,
}

/// Function parameter.
#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub name: String,
    pub ty: TypeExpr,
    pub modifier: ParamModifier,
    pub span: Span,
}

// --- Method definition: fn@[Type] ---

#[derive(Debug, Clone, PartialEq)]
pub struct MethodDef {
    pub vis: Visibility,
    pub receiver_modifier: ReceiverModifier,
    pub receiver_type: TypeExpr,
    pub name: String,
    pub type_params: Vec<TypeParam>,
    pub params: Vec<Param>,
    pub return_type: Option<TypeExpr>,
    pub effects: Vec<Effect>,
    pub body: Vec<Stmt>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReceiverModifier {
    Borrow,
    Mut,
    Move,
}

// --- Constructor definition: fn Type.name() ---

#[derive(Debug, Clone, PartialEq)]
pub struct ConstructorDef {
    pub vis: Visibility,
    pub type_name: String,
    pub name: String,
    pub type_params: Vec<TypeParam>,
    pub params: Vec<Param>,
    pub return_type: Option<TypeExpr>,
    pub body: Vec<Stmt>,
}

// --- Type expression ---

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
    /// Reference type: `&str`, `&[T]`
    Ref {
        inner: Box<TypeExpr>,
        span: Span,
    },
    /// Slice type: `&[T]`
    Slice {
        inner: Box<TypeExpr>,
        span: Span,
    },
    /// Dynamic dispatch type: `dyn Type`
    Dyn {
        inner: Box<TypeExpr>,
        span: Span,
    },
    /// Active fields type: `T@{f1, f2}`
    Active {
        base: Box<TypeExpr>,
        fields: Vec<String>,
        span: Span,
    },
    /// Array type: `[i64; 3]`
    Array {
        inner: Box<TypeExpr>,
        size: u64,
        span: Span,
    },
    /// Dimension-applied type: `Tensor[f32][M, K]`
    DimApply {
        base: Box<TypeExpr>,
        dims: Vec<DimExpr>,
        span: Span,
    },
}

// --- Dim expressions ---

#[derive(Debug, Clone, PartialEq)]
pub enum DimExpr {
    /// Integer literal dimension: `3`
    Lit(i128),
    /// Named dimension variable: `M`
    Var(String),
    /// Wildcard: `_`
    Wildcard,
    /// Binary operation: `M + 1`, `M * K`
    BinOp {
        op: DimBinOp,
        lhs: Box<DimExpr>,
        rhs: Box<DimExpr>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DimBinOp {
    Add,
    Sub,
    Mul,
    Div,
}

// --- Struct definition ---

#[derive(Debug, Clone, PartialEq)]
pub struct StructDef {
    pub vis: Visibility,
    pub name: String,
    pub type_params: Vec<TypeParam>,
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

// --- Enum definition ---

#[derive(Debug, Clone, PartialEq)]
pub struct EnumDef {
    pub vis: Visibility,
    pub name: String,
    pub type_params: Vec<TypeParam>,
    pub variants: Vec<VariantDef>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct VariantDef {
    pub name: String,
    pub fields: Vec<FieldDef>,
    pub span: Span,
}

// --- Interface definition ---

#[derive(Debug, Clone, PartialEq)]
pub struct InterfaceDef {
    pub vis: Visibility,
    pub name: String,
    pub type_params: Vec<TypeParam>,
    pub methods: Vec<InterfaceMethod>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct InterfaceMethod {
    pub name: String,
    pub receiver_modifier: Option<ReceiverModifier>,
    pub params: Vec<Param>,
    pub return_type: Option<TypeExpr>,
    pub span: Span,
}

// --- Type alias ---

#[derive(Debug, Clone, PartialEq)]
pub struct TypeAlias {
    pub vis: Visibility,
    pub name: String,
    pub is_newtype: bool,
    pub ty: TypeExpr,
}

// --- Use declaration ---

#[derive(Debug, Clone, PartialEq)]
pub struct UseDecl {
    pub path: Vec<String>,
    pub members: Option<Vec<String>>,
    pub span: Span,
}

// --- Extern block ---

#[derive(Debug, Clone, PartialEq)]
pub struct ExternBlock {
    pub abi: Option<String>,
    pub decls: Vec<ExternFnDecl>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ExternFnDecl {
    pub name: String,
    pub params: Vec<Param>,
    pub return_type: Option<TypeExpr>,
    pub span: Span,
}

// --- Test definition ---

#[derive(Debug, Clone, PartialEq)]
pub struct TestDef {
    pub name: String,
    pub modifier: Option<TestModifier>,
    pub for_params: Vec<TestParam>,
    pub body: Vec<Stmt>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TestParam {
    pub name: String,
    pub ty: Option<TypeExpr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TestModifier {
    Fuzz,
    Property,
    Snapshot,
    Bench,
}

// --- Statement ---

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
    /// `let {x, y} = expr` or `let [first, ..rest] = items`
    LetPattern {
        is_mut: bool,
        pattern: Pattern,
        ty: Option<TypeExpr>,
        value: Expr,
    },
    /// Assignment: `x = value`, `self.name = new_name`, `a.b.c = 1`
    Assign {
        target: Expr,
        value: Expr,
    },
    /// Expression statement
    Expr(Expr),
    /// `return [expr]`
    Return(Option<Expr>),
    /// `break [expr]`
    Break(Option<Expr>),
    /// `continue`
    Continue,
    /// `assert expr [, message]`
    Assert {
        cond: Expr,
        message: Option<Expr>,
    },
}

// --- Expression ---

#[derive(Debug, Clone, PartialEq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

/// Call argument with optional modifier.
#[derive(Debug, Clone, PartialEq)]
pub struct CallArg {
    pub modifier: ParamModifier,
    pub expr: Expr,
}

/// Handle arm for `handle` expressions.
#[derive(Debug, Clone, PartialEq)]
pub struct HandleArm {
    pub effect: String,
    pub params: Vec<String>,
    pub body: Vec<Stmt>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExprKind {
    /// Integer literal with optional type suffix (e.g. `42_i32`)
    IntLit(i128, Option<String>),
    /// Float literal with optional type suffix (e.g. `3.14_f64`)
    FloatLit(f64, Option<String>),
    /// String literal
    StringLit(String),
    /// Character literal
    CharLit(char),
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
        args: Vec<CallArg>,
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
    /// While loop
    While {
        cond: Box<Expr>,
        body: Vec<Stmt>,
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
    /// For loop: `for pattern in iter`
    For {
        pattern: Pattern,
        iter: Box<Expr>,
        body: Vec<Stmt>,
    },
    /// Range expression: `a..b`
    Range {
        start: Box<Expr>,
        end: Box<Expr>,
    },
    /// Closure: `|params| body`
    Closure {
        params: Vec<ClosureParam>,
        body: Vec<Stmt>,
    },
    /// Block expression (sequence of statements, last is the value)
    Block(Vec<Stmt>),
    /// Assert expression: `assert cond [, message]`
    Assert {
        cond: Box<Expr>,
        message: Option<Box<Expr>>,
    },
    /// Handle expression
    Handle {
        expr: Box<Expr>,
        arms: Vec<HandleArm>,
    },
    /// Postfix `?` — error propagation
    Try(Box<Expr>),
    /// Postfix `.await` — async await
    Await(Box<Expr>),
    /// Reference expression: `&expr` (e.g. `&"hello"`)
    Ref(Box<Expr>),
    /// String interpolation: `"Hello, {name}!"`
    StringInterp {
        parts: Vec<StringInterpPart>,
    },
    /// Type application (turbofish): `f[T]`, `parse[Config](...)`
    TypeApp {
        expr: Box<Expr>,
        type_args: Vec<TypeExpr>,
    },
    /// Array literal: `[1, 2, 3]`
    ArrayLit(Vec<Expr>),
    /// Index access: `arr[i]`
    Index {
        expr: Box<Expr>,
        index: Box<Expr>,
    },
}

/// Part of an interpolated string.
#[derive(Debug, Clone, PartialEq)]
pub enum StringInterpPart {
    /// Literal text
    Literal(String),
    /// Interpolated expression
    Expr(Expr),
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

/// A parameter in a closure expression.
#[derive(Debug, Clone, PartialEq)]
pub struct ClosureParam {
    pub name: String,
    pub ty: Option<TypeExpr>,
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
    Literal(Box<Expr>),
    /// Tuple pattern: `{a, b}`
    TuplePattern(Vec<Pattern>),
    /// Constructor: `Shape.Circle(r)`
    Constructor {
        path: Vec<String>,
        fields: Vec<Pattern>,
    },
    /// OR pattern: `A | B`
    Or(Vec<Pattern>),
    /// Rest pattern: `..` or `..rest`
    Rest(Option<String>),
    /// List pattern: `[first, ..rest]`
    List(Vec<Pattern>),
    /// Struct pattern: `User #{name, age}` or `User #{name: n, ..}`
    Struct {
        name: String,
        fields: Vec<FieldPattern>,
        has_rest: bool,
    },
}

/// A field in a struct pattern.
#[derive(Debug, Clone, PartialEq)]
pub struct FieldPattern {
    pub name: String,
    pub pattern: Option<Pattern>,
    pub span: Span,
}
