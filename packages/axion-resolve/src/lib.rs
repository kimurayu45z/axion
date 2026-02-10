pub mod def_id;
pub mod symbol;
pub mod scope;
pub mod collector;
pub mod resolver;
pub mod builtins;
pub mod errors;
pub mod prelude;

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
    /// The starting DefId for this file (used for indexing into `symbols`).
    pub start_def_id: u32,
}

impl ResolveContext {
    fn new(file_name: &str, source: &str, start_def_id: u32) -> Self {
        Self {
            symbols: Vec::new(),
            scope_tree: ScopeTree::new(),
            resolutions: HashMap::new(),
            diagnostics: Vec::new(),
            file_name: file_name.to_string(),
            source: source.to_string(),
            next_def_id: start_def_id,
            start_def_id,
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
        let index = def_id.0.checked_sub(self.start_def_id);
        if let Some(idx) = index {
            if let Some(sym) = self.symbols.get_mut(idx as usize) {
                sym.used = true;
            }
        }
        // Imported DefIds (outside our range) are silently ignored.
    }

    /// Look up a symbol by DefId, handling the offset from start_def_id.
    pub fn lookup_symbol(&self, def_id: DefId) -> Option<&Symbol> {
        let index = def_id.0.checked_sub(self.start_def_id)?;
        self.symbols.get(index as usize)
    }
}

/// Run name resolution on a parsed source file.
///
/// - `start_def_id`: the first DefId for this file (ensures global uniqueness across files).
/// - `imports`: pre-resolved names to inject into the root scope before resolution.
///
/// Returns the resolution output and any diagnostics produced.
pub fn resolve(
    source_file: &SourceFile,
    file_name: &str,
    source: &str,
    start_def_id: u32,
    imports: &[(String, DefId, SymbolKind)],
) -> (ResolveOutput, Vec<Diagnostic>) {
    let mut ctx = ResolveContext::new(file_name, source, start_def_id);

    // Create the root (module) scope.
    let root = ctx.scope_tree.push_scope(ScopeKind::Module, None);

    // Register built-in types and prelude.
    builtins::register_builtins(&mut ctx, root);

    // Inject imported symbols into the root scope.
    for (name, def_id, kind) in imports {
        match kind {
            SymbolKind::Struct
            | SymbolKind::Enum
            | SymbolKind::Interface
            | SymbolKind::TypeAlias
            | SymbolKind::TypeParam => {
                ctx.scope_tree.insert_type(root, name.clone(), *def_id);
            }
            _ => {
                ctx.scope_tree.insert_value(root, name.clone(), *def_id);
            }
        }
    }

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

/// Convenience wrapper for single-file resolution (backward-compatible).
pub fn resolve_single(
    source_file: &SourceFile,
    file_name: &str,
    source: &str,
) -> (ResolveOutput, Vec<Diagnostic>) {
    resolve(source_file, file_name, source, 0, &[])
}

#[cfg(test)]
mod tests;
