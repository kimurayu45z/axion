pub mod ty;
pub mod errors;
pub(crate) mod lower;
pub mod unify;
pub mod env;
pub(crate) mod infer;

use std::collections::HashMap;

use axion_diagnostics::Diagnostic;
use axion_resolve::def_id::SymbolKind;
use axion_resolve::ResolveOutput;
use axion_syntax::*;

use crate::env::TypeEnv;
use crate::infer::InferCtx;
use crate::lower::lower_type_expr;
use crate::ty::Ty;
use crate::unify::UnifyContext;

/// Output of the type checking phase.
#[derive(Debug)]
pub struct TypeCheckOutput {
    /// Expression types: span.start → inferred Ty.
    pub expr_types: HashMap<u32, Ty>,
    /// Field access resolutions: span.start → field index.
    pub field_resolutions: HashMap<u32, usize>,
}

/// External type information to inject before type checking (for cross-module imports).
pub struct ExternalTypeInfo {
    pub defs: HashMap<axion_resolve::def_id::DefId, env::TypeInfo>,
    pub struct_fields: HashMap<axion_resolve::def_id::DefId, Vec<(String, ty::Ty)>>,
    pub enum_variants: HashMap<axion_resolve::def_id::DefId, Vec<(String, axion_resolve::def_id::DefId, Vec<(String, ty::Ty)>)>>,
}

/// Run type checking on a parsed and resolved source file.
pub fn type_check(
    source_file: &SourceFile,
    resolved: &ResolveOutput,
    file_name: &str,
    source: &str,
) -> (TypeCheckOutput, Vec<Diagnostic>) {
    type_check_with_imports(source_file, resolved, file_name, source, None)
}

/// Run type checking with optional external type imports.
pub fn type_check_with_imports(
    source_file: &SourceFile,
    resolved: &ResolveOutput,
    file_name: &str,
    source: &str,
    external: Option<&ExternalTypeInfo>,
) -> (TypeCheckOutput, Vec<Diagnostic>) {
    let mut diagnostics = Vec::new();
    let mut unify = UnifyContext::new();
    let mut expr_types = HashMap::new();
    let mut field_resolutions = HashMap::new();

    // Phase 1: Build type environment from all top-level definitions.
    let mut env = TypeEnv::build(source_file, resolved, &mut unify);

    // Inject external type info if available.
    if let Some(ext) = external {
        env.inject_external(&ext.defs, &ext.struct_fields, &ext.enum_variants);
    }

    // Phase 2: Type-check each function/method/constructor body.
    for item in &source_file.items {
        match &item.kind {
            ItemKind::Function(f) => {
                let ret_ty = match &f.return_type {
                    Some(te) => {
                        lower_type_expr(te, &resolved.symbols, &resolved.resolutions)
                    }
                    None => Ty::Unit,
                };

                // Register self params for function bodies.
                register_fn_params(&mut env, &f.params, resolved, &mut unify);

                // Look up effects for this function.
                let fn_def_id = resolved
                    .symbols
                    .iter()
                    .find(|s| s.span == item.span)
                    .map(|s| s.def_id);
                let current_effects = fn_def_id
                    .and_then(|id| env.fn_effects.get(&id))
                    .cloned()
                    .unwrap_or_default();

                let mut ctx = InferCtx {
                    env: &mut env,
                    unify: &mut unify,
                    resolved,
                    diagnostics: &mut diagnostics,
                    file_name,
                    source,
                    expr_types: &mut expr_types,
                    field_resolutions: &mut field_resolutions,
                    current_return_ty: ret_ty,
                    self_ty: None,
                    current_effects,
                    handled_effects: Vec::new(),
                };
                let body_ty = ctx.infer_block_ty(&f.body);

                // Check body type against return type only if explicit.
                if f.return_type.is_some() {
                    let expected_ret = ctx.current_return_ty.clone();
                    if ctx.unify.unify(&expected_ret, &body_ty).is_err() {
                        diagnostics.push(errors::return_type_mismatch(
                            &unify.resolve(&expected_ret),
                            &unify.resolve(&body_ty),
                            file_name,
                            item.span,
                            source,
                        ));
                    }
                }
            }
            ItemKind::Method(m) => {
                let ret_ty = match &m.return_type {
                    Some(te) => {
                        lower_type_expr(te, &resolved.symbols, &resolved.resolutions)
                    }
                    None => Ty::Unit,
                };

                // Register `Self` type and `self` parameter.
                let receiver_name = match &m.receiver_type {
                    TypeExpr::Named { name, .. } => name.clone(),
                    _ => String::new(),
                };
                if !receiver_name.is_empty() {
                    register_self_type(&mut env, &receiver_name, resolved);
                }
                let receiver_ty =
                    lower_type_expr(&m.receiver_type, &resolved.symbols, &resolved.resolutions);
                register_self_param(&mut env, item, resolved, &receiver_ty);
                register_fn_params(&mut env, &m.params, resolved, &mut unify);

                // Look up effects for this method.
                let method_def_id = resolved
                    .symbols
                    .iter()
                    .find(|s| s.span == item.span)
                    .map(|s| s.def_id);
                let current_effects = method_def_id
                    .and_then(|id| env.fn_effects.get(&id))
                    .cloned()
                    .unwrap_or_default();

                let self_ty_for_method = receiver_ty.clone();
                let mut ctx = InferCtx {
                    env: &mut env,
                    unify: &mut unify,
                    resolved,
                    diagnostics: &mut diagnostics,
                    file_name,
                    source,
                    expr_types: &mut expr_types,
                    field_resolutions: &mut field_resolutions,
                    current_return_ty: ret_ty,
                    self_ty: Some(self_ty_for_method),
                    current_effects,
                    handled_effects: Vec::new(),
                };
                let body_ty = ctx.infer_block_ty(&m.body);

                if m.return_type.is_some() {
                    let expected_ret = ctx.current_return_ty.clone();
                    if ctx.unify.unify(&expected_ret, &body_ty).is_err() {
                        diagnostics.push(errors::return_type_mismatch(
                            &unify.resolve(&expected_ret),
                            &unify.resolve(&body_ty),
                            file_name,
                            item.span,
                            source,
                        ));
                    }
                }
            }
            ItemKind::Constructor(c) => {
                // Return type: explicit or Self (the struct type).
                let ret_ty = if let Some(te) = &c.return_type {
                    lower_type_expr(te, &resolved.symbols, &resolved.resolutions)
                } else {
                    let struct_def = resolved
                        .symbols
                        .iter()
                        .find(|s| s.name == c.type_name && s.kind == SymbolKind::Struct);
                    if let Some(s) = struct_def {
                        Ty::Struct {
                            def_id: s.def_id,
                            type_args: vec![],
                        }
                    } else {
                        Ty::Error
                    }
                };

                register_fn_params(&mut env, &c.params, resolved, &mut unify);

                // Register `Self` type in env for this constructor's scope.
                register_self_type(&mut env, &c.type_name, resolved);

                let mut ctx = InferCtx {
                    env: &mut env,
                    unify: &mut unify,
                    resolved,
                    diagnostics: &mut diagnostics,
                    file_name,
                    source,
                    expr_types: &mut expr_types,
                    field_resolutions: &mut field_resolutions,
                    current_return_ty: ret_ty,
                    self_ty: None,
                    current_effects: Vec::new(),
                    handled_effects: Vec::new(),
                };
                let body_ty = ctx.infer_block_ty(&c.body);

                let expected_ret = ctx.current_return_ty.clone();
                if ctx.unify.unify(&expected_ret, &body_ty).is_err() {
                    diagnostics.push(errors::return_type_mismatch(
                        &unify.resolve(&expected_ret),
                        &unify.resolve(&body_ty),
                        file_name,
                        item.span,
                        source,
                    ));
                }
            }
            ItemKind::Test(t) => {
                // Type-check test bodies.
                let mut ctx = InferCtx {
                    env: &mut env,
                    unify: &mut unify,
                    resolved,
                    diagnostics: &mut diagnostics,
                    file_name,
                    source,
                    expr_types: &mut expr_types,
                    field_resolutions: &mut field_resolutions,
                    current_return_ty: Ty::Unit,
                    self_ty: None,
                    current_effects: Vec::new(),
                    handled_effects: Vec::new(),
                };
                ctx.infer_stmts(&t.body);
            }
            _ => {}
        }
    }

    // Resolve all inference variables in expr_types.
    let resolved_expr_types: HashMap<u32, Ty> = expr_types
        .into_iter()
        .map(|(k, v)| (k, unify.resolve(&v)))
        .collect();

    let output = TypeCheckOutput {
        expr_types: resolved_expr_types,
        field_resolutions,
    };
    (output, diagnostics)
}

/// Register function parameters in the type environment.
fn register_fn_params(
    env: &mut TypeEnv,
    params: &[Param],
    resolved: &ResolveOutput,
    _unify: &mut UnifyContext,
) {
    for param in params {
        // Find the Param symbol for this parameter.
        let param_sym = resolved.symbols.iter().find(|s| {
            s.kind == SymbolKind::Param && s.span == param.span
        });
        if let Some(sym) = param_sym {
            if !env.defs.contains_key(&sym.def_id) {
                let ty = lower_type_expr(
                    &param.ty,
                    &resolved.symbols,
                    &resolved.resolutions,
                );
                env.defs.insert(sym.def_id, crate::env::TypeInfo { ty });
            }
        }
    }
}

/// Register `self` for method bodies.
fn register_self_param(
    env: &mut TypeEnv,
    _item: &Item,
    resolved: &ResolveOutput,
    receiver_ty: &Ty,
) {
    // The resolver registers `self` as a Param with Span::dummy().
    // We need to register ALL `self` params. Since there can be multiple methods,
    // we register all of them — each method gets its own `self` DefId.
    for sym in &resolved.symbols {
        if sym.name == "self" && sym.kind == SymbolKind::Param {
            if !env.defs.contains_key(&sym.def_id) {
                env.defs.insert(
                    sym.def_id,
                    crate::env::TypeInfo {
                        ty: receiver_ty.clone(),
                    },
                );
            }
        }
    }
}

/// Register `Self` type for constructors and methods.
/// The resolver creates a `Self` TypeParam symbol with parent pointing to the struct.
fn register_self_type(
    env: &mut TypeEnv,
    type_name: &str,
    resolved: &ResolveOutput,
) {
    // Find the struct DefId.
    let struct_def = resolved
        .symbols
        .iter()
        .find(|s| s.name == type_name && s.kind == SymbolKind::Struct);

    if let Some(struct_sym) = struct_def {
        let self_ty = Ty::Struct {
            def_id: struct_sym.def_id,
            type_args: vec![],
        };

        // Find `Self` TypeParam symbols registered by the resolver
        // (they have parent = Some(struct_def_id)).
        for sym in &resolved.symbols {
            if sym.name == "Self"
                && sym.kind == SymbolKind::TypeParam
                && sym.parent == Some(struct_sym.def_id)
            {
                env.defs.insert(
                    sym.def_id,
                    crate::env::TypeInfo {
                        ty: self_ty.clone(),
                    },
                );
            }
        }
    }
}

#[cfg(test)]
mod tests;
