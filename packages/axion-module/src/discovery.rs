use std::path::{Path, PathBuf};

use axion_parser::parse;

use crate::{Module, ModulePath};

/// Walk the project directory for `*.ax` files and parse each one.
///
/// Returns the list of discovered modules (with parsed ASTs).
pub fn discover_modules(root: &Path) -> Vec<Module> {
    let src_dir = root.join("src");
    let search_dir = if src_dir.is_dir() { &src_dir } else { root };
    let mut modules = Vec::new();

    walk_dir(search_dir, search_dir, &mut modules);
    modules
}

fn walk_dir(dir: &Path, base: &Path, modules: &mut Vec<Module>) {
    let entries = match std::fs::read_dir(dir) {
        Ok(e) => e,
        Err(_) => return,
    };

    let mut entries_vec: Vec<PathBuf> = entries.filter_map(|e| e.ok().map(|e| e.path())).collect();
    entries_vec.sort();

    for entry in entries_vec {
        if entry.is_dir() {
            walk_dir(&entry, base, modules);
        } else if entry.extension().is_some_and(|ext| ext == "ax") {
            if let Some(module) = parse_file(&entry, base, modules.len() as u16) {
                modules.push(module);
            }
        }
    }
}

fn parse_file(path: &Path, base: &Path, file_id: u16) -> Option<Module> {
    let source = std::fs::read_to_string(path).ok()?;
    let file_path = path.to_string_lossy().to_string();
    let (ast, _parse_diags) = parse(&source, &file_path);

    let module_path = derive_module_path(path, base);

    Some(Module {
        file_id,
        module_path,
        file_path,
        source,
        ast,
        resolved: None,
        type_output: None,
    })
}

/// Derive a `ModulePath` from a file path relative to the base directory.
///
/// Example: `src/net/http.ax` with base `src/` → `["net", "http"]`
pub fn derive_module_path(file_path: &Path, base: &Path) -> ModulePath {
    let relative = file_path.strip_prefix(base).unwrap_or(file_path);
    let segments: Vec<String> = relative
        .with_extension("")
        .components()
        .filter_map(|c| {
            if let std::path::Component::Normal(s) = c {
                Some(s.to_string_lossy().to_string())
            } else {
                None
            }
        })
        .collect();
    ModulePath(segments)
}

/// Build modules from source strings (for testing).
pub fn modules_from_sources(sources: &[(&str, &str)]) -> Vec<Module> {
    sources
        .iter()
        .enumerate()
        .map(|(i, (path, source))| {
            let file_path = path.to_string();
            let (ast, _) = parse(source, &file_path);

            // Derive module path from the file name.
            // E.g. "math.ax" → ["math"], "net/http.ax" → ["net", "http"]
            let module_path = derive_module_path_from_string(path);

            Module {
                file_id: i as u16,
                module_path,
                file_path,
                source: source.to_string(),
                ast,
                resolved: None,
                type_output: None,
            }
        })
        .collect()
}

fn derive_module_path_from_string(path: &str) -> ModulePath {
    let p = Path::new(path);
    let segments: Vec<String> = p
        .with_extension("")
        .components()
        .filter_map(|c| {
            if let std::path::Component::Normal(s) = c {
                Some(s.to_string_lossy().to_string())
            } else {
                None
            }
        })
        .collect();
    ModulePath(segments)
}
