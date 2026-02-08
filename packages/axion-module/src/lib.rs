pub mod discovery;
pub mod errors;
pub mod graph;
pub mod import;

use std::collections::HashMap;
use std::path::Path;

use axion_diagnostics::Diagnostic;
use axion_resolve::ResolveOutput;
use axion_syntax::SourceFile;
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

fn compile_modules(mut modules: Vec<Module>) -> CompilationOutput {
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
    let (_exports, resolve_diags) = import::resolve_in_order(&mut modules, &graph, &order);
    all_diagnostics.extend(resolve_diags);

    // Phase 5: Type check each module in topological order.
    // Build external type info from dependency modules' type environments.
    // We'll build the TypeEnv for each dependency and collect exported type info.
    let mut type_envs: Vec<Option<axion_types::ExternalTypeInfo>> = (0..modules.len()).map(|_| None).collect();

    for &idx in &order {
        if let Some(ref resolved) = modules[idx].resolved {
            // Merge type info from dependencies.
            let mut external = axion_types::ExternalTypeInfo {
                defs: HashMap::new(),
                struct_fields: HashMap::new(),
                enum_variants: HashMap::new(),
            };

            for &dep_idx in &graph.dependencies[idx] {
                if let Some(ref dep_ext) = type_envs[dep_idx] {
                    external.defs.extend(dep_ext.defs.iter().map(|(k, v)| (*k, v.clone())));
                    external.struct_fields.extend(dep_ext.struct_fields.iter().map(|(k, v)| (*k, v.clone())));
                    external.enum_variants.extend(dep_ext.enum_variants.iter().map(|(k, v)| (*k, v.clone())));
                }
            }

            let ext = if external.defs.is_empty() && external.struct_fields.is_empty() && external.enum_variants.is_empty() {
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
            let mut module_ext = axion_types::ExternalTypeInfo {
                defs: HashMap::new(),
                struct_fields: HashMap::new(),
                enum_variants: HashMap::new(),
            };

            // Build a fresh env to extract type info for exported symbols.
            let mut unify = axion_types::unify::UnifyContext::new();
            let env = axion_types::env::TypeEnv::build(&modules[idx].ast, resolved, &mut unify);

            // Also include any external defs we injected.
            if let Some(ref ext) = ext {
                module_ext.defs.extend(ext.defs.iter().map(|(k, v)| (*k, v.clone())));
                module_ext.struct_fields.extend(ext.struct_fields.iter().map(|(k, v)| (*k, v.clone())));
                module_ext.enum_variants.extend(ext.enum_variants.iter().map(|(k, v)| (*k, v.clone())));
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
