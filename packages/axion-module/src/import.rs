use std::collections::HashMap;

use axion_diagnostics::Diagnostic;
use axion_resolve::def_id::{DefId, SymbolKind};
use axion_resolve::ResolveOutput;
use axion_syntax::{ItemKind, Visibility};

use crate::errors;
use crate::graph::ModuleGraph;
use crate::Module;

/// An exported symbol from a module (includes all top-level symbols, not just public).
#[derive(Debug, Clone)]
pub struct Export {
    pub name: String,
    pub def_id: DefId,
    pub kind: SymbolKind,
    pub vis: Visibility,
}

/// Resolve imports and name resolution across modules in topological order.
///
/// For each module, builds the import list from dependency exports, then calls
/// `axion_resolve::resolve()` with the correct `start_def_id` and imports.
///
/// `prelude_imports`: symbols to inject into every module (from the prelude module).
/// `start_def_id_offset`: the starting DefId offset (accounts for prelude symbols).
/// `std_exports`: per-std-module exports for validating `use std.*` declarations.
pub fn resolve_in_order(
    modules: &mut [Module],
    graph: &ModuleGraph,
    order: &[usize],
    prelude_imports: &[(String, DefId, SymbolKind)],
    start_def_id_offset: u32,
    std_exports: &HashMap<String, Vec<Export>>,
) -> (Vec<Vec<Export>>, Vec<Diagnostic>) {
    let mut diagnostics = Vec::new();
    let mut exports: Vec<Vec<Export>> = vec![Vec::new(); modules.len()];
    let mut next_def_id: u32 = start_def_id_offset;

    for &idx in order {
        // Build imports list from dependencies.
        let mut imports: Vec<(String, DefId, SymbolKind)> = Vec::new();

        // Inject prelude imports first.
        imports.extend_from_slice(prelude_imports);
        let mut imported_names: HashMap<String, usize> = HashMap::new(); // name → dep_idx

        // Validate `use std.*` declarations against std_exports.
        // Also inject symbols from non-auto-import std modules (like io, log)
        // that the user explicitly imports via `use std.*`.
        if !std_exports.is_empty() {
            let std_extra = validate_std_imports(&modules[idx], std_exports, &mut diagnostics);
            imports.extend(std_extra);
        }

        for &dep_idx in &graph.dependencies[idx] {
            let dep_exports = &exports[dep_idx];

            // Find which names this module imports from the dependency.
            let requested = collect_imports_from(&modules[idx], &modules[dep_idx]);

            for req_name in &requested {
                // Find the symbol in the dependency's exports.
                if let Some(export) = dep_exports.iter().find(|e| e.name == *req_name) {
                    // Check visibility: private symbols can't be imported.
                    if export.vis == Visibility::Private {
                        diagnostics.push(errors::private_import(
                            req_name,
                            &modules[dep_idx].module_path.display(),
                            &modules[idx].file_path,
                            find_use_span(&modules[idx], req_name),
                            &modules[idx].source,
                        ));
                        continue;
                    }

                    // Check for duplicate imports.
                    if let Some(&prev_dep) = imported_names.get(req_name) {
                        if prev_dep != dep_idx {
                            diagnostics.push(errors::duplicate_import(
                                req_name,
                                &modules[idx].file_path,
                                find_use_span(&modules[idx], req_name),
                                &modules[idx].source,
                            ));
                            continue;
                        }
                    }

                    imported_names.insert(req_name.clone(), dep_idx);
                    imports.push((req_name.clone(), export.def_id, export.kind));
                } else {
                    diagnostics.push(errors::unresolved_name(
                        req_name,
                        &modules[dep_idx].module_path.display(),
                        &modules[idx].file_path,
                        find_use_span(&modules[idx], req_name),
                        &modules[idx].source,
                    ));
                }
            }
        }

        // Resolve this module.
        let (resolved, resolve_diags) = axion_resolve::resolve(
            &modules[idx].ast,
            &modules[idx].file_path,
            &modules[idx].source,
            next_def_id,
            &imports,
        );
        diagnostics.extend(resolve_diags);

        // Extract exports from this module.
        let module_exports = extract_exports(&resolved);
        exports[idx] = module_exports;

        next_def_id += resolved.symbols.len() as u32;
        modules[idx].resolved = Some(resolved);
    }

    (exports, diagnostics)
}

/// Extract all top-level symbols from a resolved module (for import checking).
///
/// Includes both public and private symbols so we can distinguish
/// "private" (E0602) from "not found" (E0603) errors.
fn extract_exports(resolved: &ResolveOutput) -> Vec<Export> {
    resolved
        .symbols
        .iter()
        .filter(|s| {
            matches!(
                s.kind,
                SymbolKind::Function
                    | SymbolKind::Struct
                    | SymbolKind::Enum
                    | SymbolKind::Interface
                    | SymbolKind::TypeAlias
                    | SymbolKind::Constructor
                    | SymbolKind::Method
                    | SymbolKind::ExternFn
            )
            // Exclude builtins (they have Span::dummy()) from exports.
            && s.span != axion_syntax::Span::dummy()
        })
        .map(|s| Export {
            name: s.name.clone(),
            def_id: s.def_id,
            kind: s.kind,
            vis: s.vis.clone(),
        })
        .collect()
}

/// Collect the names that module `source` imports from module `target`.
fn collect_imports_from(source: &Module, target: &Module) -> Vec<String> {
    let mut names = Vec::new();
    let target_path = &target.module_path.0;

    for item in &source.ast.items {
        if let ItemKind::Use(use_decl) = &item.kind {
            let segments = if !use_decl.path.is_empty()
                && (use_decl.path[0] == "pkg" || use_decl.path[0] == "std")
            {
                &use_decl.path[1..]
            } else {
                &use_decl.path[..]
            };

            // Check if this use targets the given module.
            // Case 1: `use pkg.math.add` → segments = ["math", "add"], target = ["math"]
            if segments.len() >= 2 && &segments[..segments.len() - 1] == target_path.as_slice() {
                let item_name = &segments[segments.len() - 1];
                // If there are grouped members, use those instead.
                if let Some(ref members) = use_decl.members {
                    for member in members {
                        names.push(member.clone());
                    }
                } else {
                    names.push(item_name.clone());
                }
            }
            // Case 2: `use pkg.math.{add, sub}` where segments == target_path
            else if segments == target_path.as_slice() {
                if let Some(ref members) = use_decl.members {
                    for member in members {
                        names.push(member.clone());
                    }
                }
            }
        }
    }

    names
}

/// Validate `use std.*` declarations in a module against the std exports map.
///
/// Returns extra imports for symbols from non-auto-import std modules (e.g. io, log)
/// that the user explicitly imports. Auto-import module symbols are already in the
/// prelude, so only non-auto-import symbols need to be returned here.
fn validate_std_imports(
    module: &Module,
    std_exports: &HashMap<String, Vec<Export>>,
    diagnostics: &mut Vec<Diagnostic>,
) -> Vec<(String, DefId, SymbolKind)> {
    let mut extra_imports = Vec::new();
    for item in &module.ast.items {
        if let ItemKind::Use(use_decl) = &item.kind {
            if use_decl.path.first().map(|s| s.as_str()) != Some("std") {
                continue;
            }
            // Expect at least `std.<module>.<name>` (3 segments),
            // or `std.<module>.{names}` (2 segments with members).
            let has_members = use_decl.members.is_some();
            if use_decl.path.len() < 3 && !(use_decl.path.len() == 2 && has_members) {
                let path_str = use_decl.path.join(".");
                diagnostics.push(errors::unresolved_module(
                    &path_str,
                    &module.file_path,
                    use_decl.span,
                    &module.source,
                ));
                continue;
            }

            let std_mod_name = &use_decl.path[1];
            let mod_exports = match std_exports.get(std_mod_name.as_str()) {
                Some(exports) => exports,
                None => {
                    let path_str = use_decl.path.join(".");
                    diagnostics.push(errors::unresolved_module(
                        &path_str,
                        &module.file_path,
                        use_decl.span,
                        &module.source,
                    ));
                    continue;
                }
            };

            // Collect requested names: either grouped `{a, b}` or the last path segment.
            let names: Vec<&str> = if let Some(ref members) = use_decl.members {
                members.iter().map(|s| s.as_str()).collect()
            } else {
                vec![use_decl.path.last().unwrap().as_str()]
            };

            for name in &names {
                if let Some(export) = mod_exports.iter().find(|e| e.name == *name) {
                    // Symbol found — collect as extra import (needed for
                    // non-auto-import modules whose symbols aren't in the prelude).
                    extra_imports.push((export.name.clone(), export.def_id, export.kind));

                    // For struct/enum types, also import associated methods and constructors.
                    if matches!(export.kind, SymbolKind::Struct | SymbolKind::Enum) {
                        let prefix = format!("{}.", name);
                        for assoc in mod_exports.iter() {
                            if assoc.name.starts_with(&prefix) {
                                extra_imports.push((assoc.name.clone(), assoc.def_id, assoc.kind));
                            }
                        }
                    }
                } else {
                    diagnostics.push(errors::unresolved_name(
                        name,
                        &format!("std.{}", std_mod_name),
                        &module.file_path,
                        use_decl.span,
                        &module.source,
                    ));
                }
            }
        }
    }

    extra_imports
}

/// Find the span of a use declaration that imports a given name.
fn find_use_span(module: &Module, name: &str) -> axion_syntax::Span {
    for item in &module.ast.items {
        if let ItemKind::Use(use_decl) = &item.kind {
            if let Some(ref members) = use_decl.members {
                if members.iter().any(|m| m == name) {
                    return use_decl.span;
                }
            } else if use_decl.path.last().is_some_and(|last| last == name) {
                return use_decl.span;
            }
        }
    }
    axion_syntax::Span::dummy()
}
