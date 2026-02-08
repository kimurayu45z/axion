use std::collections::HashMap;

use axion_diagnostics::Diagnostic;
use axion_syntax::ItemKind;

use crate::errors;
use crate::{Module, ModulePath};

/// The module dependency graph.
pub struct ModuleGraph {
    /// Map from module path to index in the modules vec.
    pub path_to_idx: HashMap<Vec<String>, usize>,
    /// Adjacency list: `dependencies[i]` = list of module indices that module `i` depends on.
    pub dependencies: Vec<Vec<usize>>,
}

impl ModuleGraph {
    /// Build the dependency graph from a set of modules.
    ///
    /// Scans each module's `use` declarations to determine edges.
    pub fn build(modules: &[Module]) -> (Self, Vec<Diagnostic>) {
        let mut diagnostics = Vec::new();
        let mut path_to_idx = HashMap::new();
        for (i, module) in modules.iter().enumerate() {
            path_to_idx.insert(module.module_path.0.clone(), i);
        }

        let mut dependencies = vec![Vec::new(); modules.len()];

        for (i, module) in modules.iter().enumerate() {
            for item in &module.ast.items {
                if let ItemKind::Use(use_decl) = &item.kind {
                    if let Some(target_idx) =
                        resolve_use_target(&use_decl.path, &path_to_idx, modules)
                    {
                        if !dependencies[i].contains(&target_idx) {
                            dependencies[i].push(target_idx);
                        }
                    } else {
                        // Build the module path string for the error.
                        let path_str = use_decl.path.join(".");
                        diagnostics.push(errors::unresolved_module(
                            &path_str,
                            &module.file_path,
                            use_decl.span,
                            &module.source,
                        ));
                    }
                }
            }
        }

        (
            ModuleGraph {
                path_to_idx,
                dependencies,
            },
            diagnostics,
        )
    }

    /// Detect cycles in the dependency graph using DFS with white/gray/black coloring.
    ///
    /// Returns a list of cycle diagnostics.
    pub fn detect_cycles(&self, modules: &[Module]) -> Vec<Diagnostic> {
        let n = modules.len();
        // 0 = white (unvisited), 1 = gray (in progress), 2 = black (done)
        let mut color = vec![0u8; n];
        let mut parent = vec![usize::MAX; n];
        let mut diagnostics = Vec::new();

        for start in 0..n {
            if color[start] == 0 {
                self.dfs_cycle(
                    start, &mut color, &mut parent, modules, &mut diagnostics,
                );
            }
        }

        diagnostics
    }

    fn dfs_cycle(
        &self,
        u: usize,
        color: &mut [u8],
        parent: &mut [usize],
        modules: &[Module],
        diagnostics: &mut Vec<Diagnostic>,
    ) {
        color[u] = 1; // gray

        for &v in &self.dependencies[u] {
            if color[v] == 1 {
                // Back edge found — cycle from u → v.
                let cycle_str = format!(
                    "{} -> {}",
                    modules[u].module_path.display(),
                    modules[v].module_path.display(),
                );
                // Find the use decl that caused this edge.
                let span = find_use_span_for_dep(&modules[u], &modules[v]);
                diagnostics.push(errors::circular_import(
                    &cycle_str,
                    &modules[u].file_path,
                    span,
                    &modules[u].source,
                ));
            } else if color[v] == 0 {
                parent[v] = u;
                self.dfs_cycle(v, color, parent, modules, diagnostics);
            }
        }

        color[u] = 2; // black
    }

    /// Return a topological ordering of the modules.
    ///
    /// Modules without dependencies come first (dependencies before dependents).
    pub fn topological_sort(&self) -> Vec<usize> {
        let n = self.dependencies.len();
        let mut visited = vec![false; n];
        let mut order = Vec::with_capacity(n);

        for i in 0..n {
            if !visited[i] {
                self.topo_dfs(i, &mut visited, &mut order);
            }
        }

        // Post-order DFS on "A depends on B" edges naturally gives
        // dependencies before dependents — no reversal needed.
        order
    }

    fn topo_dfs(&self, u: usize, visited: &mut [bool], order: &mut Vec<usize>) {
        visited[u] = true;
        for &v in &self.dependencies[u] {
            if !visited[v] {
                self.topo_dfs(v, visited, order);
            }
        }
        order.push(u);
    }
}

/// Resolve a `use` path to a target module index.
///
/// Path format: `pkg.module_segment.name` or `pkg.module_segment.{name1, name2}`
/// The first segment is `pkg` (current package). The remaining segments minus the last
/// determine the target module path.
fn resolve_use_target(
    path: &[String],
    path_to_idx: &HashMap<Vec<String>, usize>,
    _modules: &[Module],
) -> Option<usize> {
    if path.is_empty() {
        return None;
    }

    // For now, treat the first segment as the package root marker.
    // The remaining path segments (minus the last one, which is the imported name)
    // form the target module path.
    let segments = if path[0] == "pkg" || path[0] == "std" {
        &path[1..]
    } else {
        &path[..]
    };

    if segments.is_empty() {
        return None;
    }

    // The target module path is all segments except the last (which is the item name).
    // But if the entire path matches a module, use that.
    // Try full match first.
    let full: Vec<String> = segments.to_vec();
    if let Some(&idx) = path_to_idx.get(&full) {
        return Some(idx);
    }

    // Try without the last segment (it's the imported item name).
    if segments.len() >= 2 {
        let module_path: Vec<String> = segments[..segments.len() - 1].to_vec();
        if let Some(&idx) = path_to_idx.get(&module_path) {
            return Some(idx);
        }
    }

    // Single segment: try as module name directly.
    if segments.len() == 1 {
        let single = vec![segments[0].clone()];
        if let Some(&idx) = path_to_idx.get(&single) {
            return Some(idx);
        }
    }

    None
}

/// Find the span of a `use` declaration in `source_module` that targets `target_module`.
fn find_use_span_for_dep(
    source_module: &Module,
    target_module: &Module,
) -> axion_syntax::Span {
    for item in &source_module.ast.items {
        if let ItemKind::Use(use_decl) = &item.kind {
            // Check if this use points to the target module.
            let segments = if !use_decl.path.is_empty()
                && (use_decl.path[0] == "pkg" || use_decl.path[0] == "std")
            {
                &use_decl.path[1..]
            } else {
                &use_decl.path[..]
            };

            // Match against target module path.
            let target = &target_module.module_path.0;
            if segments == target.as_slice() {
                return use_decl.span;
            }
            // Also try: segments without last == target module path.
            if segments.len() >= 2 && &segments[..segments.len() - 1] == target.as_slice() {
                return use_decl.span;
            }
        }
    }
    axion_syntax::Span::dummy()
}

impl ModulePath {
    pub fn display(&self) -> String {
        self.0.join(".")
    }
}
