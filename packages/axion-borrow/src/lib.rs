pub mod state;
pub mod check;
pub mod errors;

#[cfg(test)]
mod tests;

use axion_diagnostics::Diagnostic;
use axion_resolve::def_id::SymbolKind;
use axion_resolve::ResolveOutput;
use axion_syntax::*;
use axion_types::env::TypeEnv;
use axion_types::TypeCheckOutput;

use crate::check::BorrowCtx;

/// Run borrow checking on a source file.
///
/// This should be called after type checking, before codegen.
/// Returns a list of diagnostics (errors/warnings).
pub fn borrow_check(
    source_file: &SourceFile,
    resolved: &ResolveOutput,
    type_check: &TypeCheckOutput,
    type_env: &TypeEnv,
    file_name: &str,
    source: &str,
) -> Vec<Diagnostic> {
    let mut all_diagnostics = Vec::new();

    for item in &source_file.items {
        match &item.kind {
            ItemKind::Function(f) => {
                let mut ctx =
                    BorrowCtx::new(resolved, type_check, type_env, file_name, source);
                ctx.check_fn(&f.params, &f.body);
                all_diagnostics.extend(ctx.diagnostics);
            }
            ItemKind::Method(m) => {
                let mut ctx =
                    BorrowCtx::new(resolved, type_check, type_env, file_name, source);
                // Register `self` param.
                let self_sym = resolved.symbols.iter().find(|s| {
                    s.name == "self" && s.kind == SymbolKind::Param && s.parent == Some(
                        resolved.symbols.iter().find(|s2| s2.span == item.span).map(|s2| s2.def_id).unwrap_or(axion_resolve::def_id::DefId(u32::MAX))
                    )
                });
                if let Some(sym) = self_sym {
                    let is_mut = matches!(m.receiver_modifier, ReceiverModifier::Mut);
                    ctx.state.declare(sym.def_id, is_mut);
                }
                ctx.check_fn(&m.params, &m.body);
                all_diagnostics.extend(ctx.diagnostics);
            }
            ItemKind::Constructor(c) => {
                let mut ctx =
                    BorrowCtx::new(resolved, type_check, type_env, file_name, source);
                ctx.check_fn(&c.params, &c.body);
                all_diagnostics.extend(ctx.diagnostics);
            }
            _ => {}
        }
    }

    all_diagnostics
}
