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
            let receiver_name = type_expr_name(&m.receiver_type);
            let key = format!("{receiver_name}.{}", m.name);
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

        ItemKind::Use(_) => {
            // Use declarations require cross-module resolution — deferred.
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
