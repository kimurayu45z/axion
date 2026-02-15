use axion_syntax::*;

use crate::def_id::SymbolKind;
use crate::errors;
use crate::scope::ScopeId;
use crate::ResolveContext;

/// Pass 1: Collect all top-level definitions from the source file into the
/// module scope. This makes forward references work — functions can call
/// other functions defined later in the file.
pub(crate) fn collect_top_level(ctx: &mut ResolveContext, source_file: &SourceFile, root: ScopeId) {
    for item in &source_file.items {
        collect_item(ctx, item, root);
    }
}

fn collect_item(ctx: &mut ResolveContext, item: &Item, root: ScopeId) {
    match &item.kind {
        ItemKind::Function(f) => {
            let def_id = ctx.alloc_symbol(
                f.name.clone(),
                SymbolKind::Function,
                f.vis.clone(),
                item.span,
                None,
            );
            if ctx.scope_tree.insert_value(root, f.name.clone(), def_id).is_some() {
                ctx.diagnostics.push(errors::duplicate_definition(
                    &f.name,
                    &ctx.file_name,
                    item.span,
                    &ctx.source,
                ));
            }
        }

        ItemKind::Struct(s) => {
            let def_id = ctx.alloc_symbol(
                s.name.clone(),
                SymbolKind::Struct,
                s.vis.clone(),
                item.span,
                None,
            );
            if ctx.scope_tree.insert_type(root, s.name.clone(), def_id).is_some() {
                ctx.diagnostics.push(errors::duplicate_definition(
                    &s.name,
                    &ctx.file_name,
                    item.span,
                    &ctx.source,
                ));
            }
        }

        ItemKind::Enum(e) => {
            let enum_def_id = ctx.alloc_symbol(
                e.name.clone(),
                SymbolKind::Enum,
                e.vis.clone(),
                item.span,
                None,
            );
            if ctx.scope_tree.insert_type(root, e.name.clone(), enum_def_id).is_some() {
                ctx.diagnostics.push(errors::duplicate_definition(
                    &e.name,
                    &ctx.file_name,
                    item.span,
                    &ctx.source,
                ));
            }
            // Register each variant as a child of the enum.
            for variant in &e.variants {
                let _variant_def_id = ctx.alloc_symbol(
                    variant.name.clone(),
                    SymbolKind::EnumVariant,
                    e.vis.clone(),
                    variant.span,
                    Some(enum_def_id),
                );
                // Variants are accessed via `EnumName.VariantName`, not directly
                // in the value namespace. They are looked up through the enum.
            }
        }

        ItemKind::Interface(iface) => {
            let def_id = ctx.alloc_symbol(
                iface.name.clone(),
                SymbolKind::Interface,
                iface.vis.clone(),
                item.span,
                None,
            );
            if ctx.scope_tree.insert_type(root, iface.name.clone(), def_id).is_some() {
                ctx.diagnostics.push(errors::duplicate_definition(
                    &iface.name,
                    &ctx.file_name,
                    item.span,
                    &ctx.source,
                ));
            }
        }

        ItemKind::TypeAlias(ta) => {
            let def_id = ctx.alloc_symbol(
                ta.name.clone(),
                SymbolKind::TypeAlias,
                ta.vis.clone(),
                item.span,
                None,
            );
            if ctx.scope_tree.insert_type(root, ta.name.clone(), def_id).is_some() {
                ctx.diagnostics.push(errors::duplicate_definition(
                    &ta.name,
                    &ctx.file_name,
                    item.span,
                    &ctx.source,
                ));
            }
        }

        ItemKind::Constructor(c) => {
            // Constructors are registered as `TypeName.name` in the value NS.
            let key = format!("{}.{}", c.type_name, c.name);
            let def_id = ctx.alloc_symbol(
                key.clone(),
                SymbolKind::Constructor,
                c.vis.clone(),
                item.span,
                None,
            );
            if ctx.scope_tree.insert_value(root, key.clone(), def_id).is_some() {
                ctx.diagnostics.push(errors::duplicate_definition(
                    &key,
                    &ctx.file_name,
                    item.span,
                    &ctx.source,
                ));
            }
        }

        ItemKind::Method(m) => {
            // Methods are registered as `ReceiverType.name` in the value NS.
            // For specialized impls (no impl type_params, concrete receiver type args),
            // use qualified key like "Range[i64].next" to avoid collisions.
            let receiver_key = method_receiver_key(m);
            let key = format!("{receiver_key}.{}", m.name);
            let def_id = ctx.alloc_symbol(
                key.clone(),
                SymbolKind::Method,
                m.vis.clone(),
                item.span,
                None,
            );
            if ctx.scope_tree.insert_value(root, key.clone(), def_id).is_some() {
                ctx.diagnostics.push(errors::duplicate_definition(
                    &key,
                    &ctx.file_name,
                    item.span,
                    &ctx.source,
                ));
            }
        }

        ItemKind::Extern(ext) => {
            for decl in &ext.decls {
                let def_id = ctx.alloc_symbol(
                    decl.name.clone(),
                    SymbolKind::ExternFn,
                    Visibility::Pub,
                    decl.span,
                    None,
                );
                if ctx.scope_tree.insert_value(root, decl.name.clone(), def_id).is_some() {
                    ctx.diagnostics.push(errors::duplicate_definition(
                        &decl.name,
                        &ctx.file_name,
                        decl.span,
                        &ctx.source,
                    ));
                }
            }
        }

        ItemKind::Import(_) => {
            // Import declarations require cross-module resolution — deferred.
        }
        ItemKind::Export(_) => {
            // Export declarations require cross-module resolution — deferred.
        }

        ItemKind::Test(_) => {
            // Tests are not visible as named entities.
        }

        ItemKind::ImplFor(_) => {
            // Compile-time assertion only — no symbols to register.
        }
    }
}

/// Extract the simple name from a type expression (for method receiver keys).
fn type_expr_name(ty: &TypeExpr) -> String {
    match ty {
        TypeExpr::Named { name, .. } => name.clone(),
        _ => "<unknown>".to_string(),
    }
}

/// Build the receiver key for a method.
/// For specialized impls (no type_params but receiver has concrete type args),
/// returns a qualified key like "Range[i64]".
/// For generic impls (has type_params), returns just the base name like "Array".
fn method_receiver_key(m: &MethodDef) -> String {
    let base_name = type_expr_name(&m.receiver_type);
    if m.type_params.is_empty() {
        if let TypeExpr::Named { args, .. } = &m.receiver_type {
            if !args.is_empty() {
                let arg_strs: Vec<String> = args.iter().map(type_expr_to_string).collect();
                return format!("{}[{}]", base_name, arg_strs.join(", "));
            }
        }
    }
    base_name
}

/// Convert a TypeExpr to its string representation for use in method keys.
fn type_expr_to_string(ty: &TypeExpr) -> String {
    match ty {
        TypeExpr::Named { name, args, .. } if !args.is_empty() => {
            let arg_strs: Vec<String> = args.iter().map(type_expr_to_string).collect();
            format!("{}[{}]", name, arg_strs.join(", "))
        }
        TypeExpr::Named { name, .. } => name.clone(),
        _ => "<unknown>".to_string(),
    }
}
