pub mod collect;
pub mod output;
pub mod specialize;

#[cfg(test)]
mod tests;

use axion_resolve::ResolveOutput;
use axion_syntax::SourceFile;
use axion_types::env::TypeEnv;
use axion_types::TypeCheckOutput;

use crate::collect::collect_instantiations;
use crate::output::MonoOutput;
use crate::specialize::specialize;

/// Run monomorphization on a source file.
///
/// This should be called after type checking, before codegen.
/// It collects all generic function instantiations, creates specialized copies,
/// and returns a MonoOutput with mangled names and specialized function definitions.
pub fn monomorphize(
    source_file: &SourceFile,
    resolved: &ResolveOutput,
    type_check: &TypeCheckOutput,
    type_env: &TypeEnv,
) -> MonoOutput {
    let instantiations = collect_instantiations(source_file, resolved, type_check);

    if instantiations.is_empty() {
        return MonoOutput::new();
    }

    specialize(source_file, resolved, type_env, &instantiations)
}
