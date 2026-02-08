use axion_syntax::{Span, Visibility};

use crate::def_id::{DefId, SymbolKind};

/// A single definition entry in the symbol table.
#[derive(Debug, Clone)]
pub struct Symbol {
    pub def_id: DefId,
    pub name: String,
    pub kind: SymbolKind,
    pub vis: Visibility,
    pub span: Span,
    /// Parent definition (e.g. enum variant → enum, method → receiver type).
    pub parent: Option<DefId>,
    /// Whether this symbol has been referenced (for unused-variable detection).
    pub used: bool,
}
