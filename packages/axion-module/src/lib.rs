pub mod discovery;
pub mod errors;
pub mod graph;
pub mod import;

use std::path::Path;

use axion_diagnostics::Diagnostic;
use axion_resolve::def_id::{DefId, SymbolKind};
use axion_resolve::prelude::prelude_source;
use axion_resolve::ResolveOutput;
use axion_syntax::SourceFile;
use axion_types::ExternalTypeInfo;
use axion_types::TypeCheckOutput;

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

fn compile_modules_with_prelude(modules: Vec<Module>) -> CompilationOutput {
    // 1. Parse & resolve prelude as a single unit.
    let src = prelude_source();
    let (prelude_ast, _) = axion_parser::parse(&src, "<prelude>");
    let (prelude_resolved, _) = axion_resolve::resolve_single(&prelude_ast, "<prelude>", &src);

    // 2. Extract prelude exports: all top-level symbols that user modules may need.
    let prelude_imports: Vec<(String, DefId, SymbolKind)> = prelude_resolved
        .symbols
        .iter()
        .filter(|s| {
            matches!(
                s.kind,
                SymbolKind::Struct
                    | SymbolKind::Enum
                    | SymbolKind::Function
                    | SymbolKind::Interface
                    | SymbolKind::TypeAlias
                    | SymbolKind::Constructor
                    | SymbolKind::Method
                    | SymbolKind::ExternFn
            )
        })
        .map(|s| (s.name.clone(), s.def_id, s.kind))
        .collect();

    let prelude_def_id_offset = prelude_resolved.symbols.len() as u32;

    // 3. Build prelude TypeEnv for ExternalTypeInfo.
    let mut prelude_unify = axion_types::unify::UnifyContext::new();
    let prelude_type_env =
        axion_types::env::TypeEnv::build(&prelude_ast, &prelude_resolved, &mut prelude_unify);
    let prelude_ext = build_prelude_external_type_info(&prelude_type_env);

    // 4. Compile modules with prelude context.
    compile_modules_inner(modules, &prelude_imports, prelude_def_id_offset, &prelude_ext)
}

/// Build ExternalTypeInfo from a prelude TypeEnv.
fn build_prelude_external_type_info(env: &axion_types::env::TypeEnv) -> ExternalTypeInfo {
    let mut ext = ExternalTypeInfo::default();
    for (id, info) in &env.defs {
        ext.defs.insert(*id, info.clone());
    }
    for (id, fields) in &env.struct_fields {
        ext.struct_fields.insert(*id, fields.clone());
    }
    for (id, variants) in &env.enum_variants {
        ext.enum_variants.insert(*id, variants.clone());
    }
    ext
}

/// Backward-compatible: compile without prelude.
fn compile_modules(modules: Vec<Module>) -> CompilationOutput {
    compile_modules_inner(modules, &[], 0, &ExternalTypeInfo::default())
}

fn compile_modules_inner(
    mut modules: Vec<Module>,
    prelude_imports: &[(String, DefId, SymbolKind)],
    start_def_id_offset: u32,
    prelude_ext: &ExternalTypeInfo,
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
        import::resolve_in_order(&mut modules, &graph, &order, prelude_imports, start_def_id_offset);
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
