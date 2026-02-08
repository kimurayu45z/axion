pub mod def_id;
pub mod symbol;
pub mod scope;
pub mod collector;
pub mod resolver;
pub mod builtins;
pub mod errors;

use std::collections::HashMap;

use axion_diagnostics::Diagnostic;
use axion_syntax::{SourceFile, Span, Visibility};

use crate::def_id::{DefId, SymbolKind};
use crate::scope::{ScopeKind, ScopeTree};
use crate::symbol::Symbol;

/// The output of name resolution.
#[derive(Debug)]
pub struct ResolveOutput {
    /// All symbols defined in the compilation unit.
    pub symbols: Vec<Symbol>,
    /// The scope hierarchy.
    pub scope_tree: ScopeTree,
    /// Resolution map: `Span.start` → `DefId` for each resolved reference.
    pub resolutions: HashMap<u32, DefId>,
}

/// Internal mutable context threaded through the resolution passes.
pub(crate) struct ResolveContext {
    pub symbols: Vec<Symbol>,
    pub scope_tree: ScopeTree,
    pub resolutions: HashMap<u32, DefId>,
    pub diagnostics: Vec<Diagnostic>,
    pub file_name: String,
    pub source: String,
    next_def_id: u32,
}

impl ResolveContext {
    fn new(file_name: &str, source: &str) -> Self {
        Self {
            symbols: Vec::new(),
            scope_tree: ScopeTree::new(),
            resolutions: HashMap::new(),
            diagnostics: Vec::new(),
            file_name: file_name.to_string(),
            source: source.to_string(),
            next_def_id: 0,
        }
    }

    pub fn alloc_symbol(
        &mut self,
        name: String,
        kind: SymbolKind,
        vis: Visibility,
        span: Span,
        parent: Option<DefId>,
    ) -> DefId {
        let id = DefId(self.next_def_id);
        self.next_def_id += 1;
        self.symbols.push(Symbol {
            def_id: id,
            name,
            kind,
            vis,
            span,
            parent,
            used: false,
        });
        id
    }

    pub fn record_resolution(&mut self, span_start: u32, def_id: DefId) {
        self.resolutions.insert(span_start, def_id);
    }

    pub fn mark_used(&mut self, def_id: DefId) {
        if let Some(sym) = self.symbols.get_mut(def_id.0 as usize) {
            sym.used = true;
        }
    }
}

/// Run name resolution on a parsed source file.
///
/// Returns the resolution output and any diagnostics produced.
pub fn resolve(
    source_file: &SourceFile,
    file_name: &str,
    source: &str,
) -> (ResolveOutput, Vec<Diagnostic>) {
    let mut ctx = ResolveContext::new(file_name, source);

    // Create the root (module) scope.
    let root = ctx.scope_tree.push_scope(ScopeKind::Module, None);

    // Register built-in types and prelude.
    builtins::register_builtins(&mut ctx, root);

    // Pass 1: Collect all top-level definitions.
    collector::collect_top_level(&mut ctx, source_file, root);

    // Pass 2: Resolve all references.
    resolver::resolve_all(&mut ctx, source_file, root);

    let diagnostics = ctx.diagnostics;
    let output = ResolveOutput {
        symbols: ctx.symbols,
        scope_tree: ctx.scope_tree,
        resolutions: ctx.resolutions,
    };
    (output, diagnostics)
}

#[cfg(test)]
mod tests;
