pub mod discovery;
pub mod errors;
pub mod graph;
pub mod import;

use std::collections::HashMap;
use std::path::Path;

use axion_diagnostics::Diagnostic;
use axion_resolve::def_id::{DefId, SymbolKind};
use axion_resolve::prelude::{self, aux_std_modules};
use axion_resolve::ResolveOutput;
use axion_syntax::SourceFile;
use axion_types::ExternalTypeInfo;
use axion_types::TypeCheckOutput;

use import::Export;

/// A dot-separated module path, e.g. `["net", "http"]`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ModulePath(pub Vec<String>);

/// A single module in the compilation.
pub struct Module {
    pub file_id: u16,
    pub module_path: ModulePath,
    pub file_path: String,
    pub source: String,
    pub ast: SourceFile,
    pub resolved: Option<ResolveOutput>,
    pub type_output: Option<TypeCheckOutput>,
}

/// The output of compiling a multi-file project.
pub struct CompilationOutput {
    pub modules: Vec<Module>,
    pub diagnostics: Vec<Diagnostic>,
}

/// Compile a project from a root directory.
///
/// Discovers all `.ax` files, builds the dependency graph, resolves names
/// and type-checks in topological order.
pub fn compile_project(root: &Path) -> CompilationOutput {
    let modules = discovery::discover_modules(root);
    compile_modules(modules)
}

/// Compile a set of modules from in-memory sources (for testing).
pub fn compile_sources(sources: &[(&str, &str)]) -> CompilationOutput {
    let modules = discovery::modules_from_sources(sources);
    compile_modules(modules)
}

/// Compile a project from a root directory with prelude support.
///
/// The prelude is parsed and resolved once, and its exports are injected
/// into every user module as implicit imports.
pub fn compile_project_with_prelude(root: &Path) -> CompilationOutput {
    let modules = discovery::discover_modules(root);
    compile_modules_with_prelude(modules)
}

/// Compile sources with prelude support (for testing).
pub fn compile_sources_with_prelude(sources: &[(&str, &str)]) -> CompilationOutput {
    let modules = discovery::modules_from_sources(sources);
    compile_modules_with_prelude(modules)
}

fn compile_modules_with_prelude(user_modules: Vec<Module>) -> CompilationOutput {
    // 1. Build core modules from embedded sources.
    let mut core_modules = build_core_modules();

    // 2. Build dependency graph and resolve core modules in topological order.
    let (core_graph, core_graph_diags) = graph::ModuleGraph::build(&core_modules);
    // (Ignore graph diags for core modules — they are known-good.)
    let _ = core_graph_diags;
    let core_order = core_graph.topological_sort();
    let (core_exports, _core_resolve_diags) = import::resolve_in_order(
        &mut core_modules,
        &core_graph,
        &core_order,
        &[],
        0,
        &HashMap::new(),
    );

    // 3. The prelude module's exports are the prelude_imports for user modules.
    let prelude_idx = core_modules
        .iter()
        .position(|m| m.module_path.0 == vec!["prelude"])
        .expect("prelude module not found in core modules");
    let prelude_imports: Vec<(String, DefId, SymbolKind)> = core_exports[prelude_idx]
        .iter()
        .map(|e| (e.name.clone(), e.def_id, e.kind))
        .collect();

    // 4. Calculate total DefId offset from all core modules.
    let total_core_symbols: u32 = core_modules
        .iter()
        .filter_map(|m| m.resolved.as_ref())
        .map(|r| r.symbols.len() as u32)
        .sum();

    // 5. Build std_exports from core module exports (for `import std.xxx.*` validation).
    let mut std_exports: HashMap<String, Vec<Export>> = HashMap::new();
    for (idx, module) in core_modules.iter().enumerate() {
        if idx != prelude_idx {
            let mod_name = module.module_path.display();
            std_exports
                .entry(mod_name)
                .or_default()
                .extend(core_exports[idx].iter().cloned());
        }
    }

    // 6–8. Build prelude TypeEnv from all core modules, then compile
    //       collection and aux modules (collecting their type info too).
    let mut prelude_ext = ExternalTypeInfo::default();
    for module in &core_modules {
        if let Some(ref resolved) = module.resolved {
            let mut unify = axion_types::unify::UnifyContext::new();
            let env =
                axion_types::env::TypeEnv::build(&module.ast, resolved, &mut unify);
            for (id, info) in &env.defs {
                prelude_ext.defs.insert(*id, info.clone());
            }
            for (id, fields) in &env.struct_fields {
                prelude_ext.struct_fields.insert(*id, fields.clone());
            }
            for (id, variants) in &env.enum_variants {
                prelude_ext.enum_variants.insert(*id, variants.clone());
            }
        }
    }

    // 6. Compile collection modules with prelude_imports injected.
    let mut next_def_offset = total_core_symbols;
    let collection_sources: &[(&str, &str)] = &[
        ("collection", prelude::STD_COLLECTION_HASHMAP),
        ("collection", prelude::STD_COLLECTION_HASHSET),
        ("collection", prelude::STD_COLLECTION_BTREEMAP),
        ("collection", prelude::STD_COLLECTION_BTREESET),
    ];
    for (group, src) in collection_sources {
        let file_name = format!("<std.{}>", group);
        let (ast, _) = axion_parser::parse(src, &file_name);
        let (resolved, _) = axion_resolve::resolve(
            &ast,
            &file_name,
            src,
            next_def_offset,
            &prelude_imports,
        );
        let exports = extract_exports_for_std(&resolved);
        std_exports
            .entry(group.to_string())
            .or_default()
            .extend(exports);
        // Also build type info for collection modules.
        let mut unify = axion_types::unify::UnifyContext::new();
        let env = axion_types::env::TypeEnv::build(&ast, &resolved, &mut unify);
        for (id, info) in &env.defs {
            prelude_ext.defs.insert(*id, info.clone());
        }
        for (id, fields) in &env.struct_fields {
            prelude_ext.struct_fields.insert(*id, fields.clone());
        }
        for (id, variants) in &env.enum_variants {
            prelude_ext.enum_variants.insert(*id, variants.clone());
        }
        next_def_offset += resolved.symbols.len() as u32;
    }

    // 7. Compile auxiliary std modules (io, log) with prelude_imports.
    for aux in aux_std_modules() {
        let file_name = format!("<std.{}>", aux.name);
        let (ast, _) = axion_parser::parse(aux.source, &file_name);
        let (resolved, _) = axion_resolve::resolve(
            &ast,
            &file_name,
            aux.source,
            next_def_offset,
            &prelude_imports,
        );
        let exports = extract_exports_for_std(&resolved);
        std_exports
            .entry(aux.name.clone())
            .or_default()
            .extend(exports);
        // Also build type info for aux modules.
        let mut unify = axion_types::unify::UnifyContext::new();
        let env = axion_types::env::TypeEnv::build(&ast, &resolved, &mut unify);
        for (id, info) in &env.defs {
            prelude_ext.defs.insert(*id, info.clone());
        }
        for (id, fields) in &env.struct_fields {
            prelude_ext.struct_fields.insert(*id, fields.clone());
        }
        for (id, variants) in &env.enum_variants {
            prelude_ext.enum_variants.insert(*id, variants.clone());
        }
        next_def_offset += resolved.symbols.len() as u32;
    }

    // 9. Compile user modules with prelude context.
    compile_modules_inner(
        user_modules,
        &prelude_imports,
        next_def_offset,
        &prelude_ext,
        &std_exports,
    )
}

/// Build core Module objects from embedded stdlib sources.
fn build_core_modules() -> Vec<Module> {
    let mut modules = Vec::new();

    for (idx, (name, src)) in prelude::core_module_sources().iter().enumerate() {
        let file_name = format!("<core.{}>", name);
        let (ast, _) = axion_parser::parse(src, &file_name);
        modules.push(Module {
            file_id: idx as u16,
            module_path: ModulePath(vec![name.to_string()]),
            file_path: file_name,
            source: src.to_string(),
            ast,
            resolved: None,
            type_output: None,
        });
    }

    // Add prelude.ax module.
    let prelude_src = prelude::PRELUDE_AX;
    let (prelude_ast, _) = axion_parser::parse(prelude_src, "<prelude>");
    modules.push(Module {
        file_id: modules.len() as u16,
        module_path: ModulePath(vec!["prelude".to_string()]),
        file_path: "<prelude>".to_string(),
        source: prelude_src.to_string(),
        ast: prelude_ast,
        resolved: None,
        type_output: None,
    });

    modules
}

/// Extract exports from a resolved std module (collection, io, log).
fn extract_exports_for_std(resolved: &ResolveOutput) -> Vec<Export> {
    resolved
        .symbols
        .iter()
        .filter(|s| {
            matches!(
                s.kind,
                SymbolKind::Function
                    | SymbolKind::Struct
                    | SymbolKind::Enum
                    | SymbolKind::ExternFn
                    | SymbolKind::Constructor
                    | SymbolKind::Method
                    | SymbolKind::Interface
                    | SymbolKind::TypeAlias
            ) && s.span != axion_syntax::Span::dummy()
        })
        .map(|s| Export {
            name: s.name.clone(),
            def_id: s.def_id,
            kind: s.kind,
            vis: s.vis.clone(),
        })
        .collect()
}

/// Backward-compatible: compile without prelude.
fn compile_modules(modules: Vec<Module>) -> CompilationOutput {
    compile_modules_inner(modules, &[], 0, &ExternalTypeInfo::default(), &HashMap::new())
}

fn compile_modules_inner(
    mut modules: Vec<Module>,
    prelude_imports: &[(String, DefId, SymbolKind)],
    start_def_id_offset: u32,
    prelude_ext: &ExternalTypeInfo,
    std_exports: &HashMap<String, Vec<Export>>,
) -> CompilationOutput {
    let mut all_diagnostics = Vec::new();

    if modules.is_empty() {
        return CompilationOutput {
            modules,
            diagnostics: all_diagnostics,
        };
    }

    // Phase 2: Build dependency graph.
    let (graph, graph_diags) = graph::ModuleGraph::build(&modules);
    all_diagnostics.extend(graph_diags);

    // Phase 3: Detect cycles.
    let cycle_diags = graph.detect_cycles(&modules);
    if !cycle_diags.is_empty() {
        all_diagnostics.extend(cycle_diags);
        return CompilationOutput {
            modules,
            diagnostics: all_diagnostics,
        };
    }

    // Phase 4: Topological sort and resolve.
    let order = graph.topological_sort();
    let (_exports, resolve_diags) =
        import::resolve_in_order(&mut modules, &graph, &order, prelude_imports, start_def_id_offset, std_exports);
    all_diagnostics.extend(resolve_diags);

    // Phase 5: Type check each module in topological order.
    // Build external type info from dependency modules' type environments.
    // We'll build the TypeEnv for each dependency and collect exported type info.
    let mut type_envs: Vec<Option<ExternalTypeInfo>> =
        (0..modules.len()).map(|_| None).collect();

    for &idx in &order {
        if let Some(ref resolved) = modules[idx].resolved {
            // Merge type info from dependencies.
            let mut external = ExternalTypeInfo::default();

            // Inject prelude type info into every module.
            external.defs.extend(
                prelude_ext.defs.iter().map(|(k, v)| (*k, v.clone())),
            );
            external.struct_fields.extend(
                prelude_ext
                    .struct_fields
                    .iter()
                    .map(|(k, v)| (*k, v.clone())),
            );
            external.enum_variants.extend(
                prelude_ext
                    .enum_variants
                    .iter()
                    .map(|(k, v)| (*k, v.clone())),
            );

            for &dep_idx in &graph.dependencies[idx] {
                if let Some(ref dep_ext) = type_envs[dep_idx] {
                    external
                        .defs
                        .extend(dep_ext.defs.iter().map(|(k, v)| (*k, v.clone())));
                    external
                        .struct_fields
                        .extend(dep_ext.struct_fields.iter().map(|(k, v)| (*k, v.clone())));
                    external
                        .enum_variants
                        .extend(dep_ext.enum_variants.iter().map(|(k, v)| (*k, v.clone())));
                }
            }

            let ext = if external.defs.is_empty()
                && external.struct_fields.is_empty()
                && external.enum_variants.is_empty()
            {
                None
            } else {
                Some(external)
            };

            let (type_output, type_diags) = axion_types::type_check_with_imports(
                &modules[idx].ast,
                resolved,
                &modules[idx].file_path,
                &modules[idx].source,
                ext.as_ref(),
            );
            all_diagnostics.extend(type_diags);

            // Build external type info for this module (for downstream dependents).
            // Re-build the TypeEnv to capture what this module exports.
            let mut module_ext = ExternalTypeInfo::default();

            // Build a fresh env to extract type info for exported symbols.
            let mut unify = axion_types::unify::UnifyContext::new();
            let env = axion_types::env::TypeEnv::build(&modules[idx].ast, resolved, &mut unify);

            // Also include any external defs we injected.
            if let Some(ref ext) = ext {
                module_ext
                    .defs
                    .extend(ext.defs.iter().map(|(k, v)| (*k, v.clone())));
                module_ext
                    .struct_fields
                    .extend(ext.struct_fields.iter().map(|(k, v)| (*k, v.clone())));
                module_ext
                    .enum_variants
                    .extend(ext.enum_variants.iter().map(|(k, v)| (*k, v.clone())));
            }

            // Add this module's own type info.
            for (id, info) in &env.defs {
                module_ext.defs.insert(*id, info.clone());
            }
            for (id, fields) in &env.struct_fields {
                module_ext.struct_fields.insert(*id, fields.clone());
            }
            for (id, variants) in &env.enum_variants {
                module_ext.enum_variants.insert(*id, variants.clone());
            }

            type_envs[idx] = Some(module_ext);
            modules[idx].type_output = Some(type_output);
        }
    }

    CompilationOutput {
        modules,
        diagnostics: all_diagnostics,
    }
}

#[cfg(test)]
mod tests;
