/// A unique identifier for every definition in a compilation unit.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DefId(pub u32);

/// The kind of entity a definition represents.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymbolKind {
    Function,
    Method,
    Constructor,
    Struct,
    Enum,
    EnumVariant,
    Interface,
    TypeAlias,
    TypeParam,
    ConstParam,
    DimParam,
    LocalVar,
    Param,
    ClosureParam,
    ExternFn,
}
