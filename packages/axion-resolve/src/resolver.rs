use axion_syntax::*;

use crate::def_id::SymbolKind;
use crate::errors;
use crate::scope::{ScopeId, ScopeKind};
use crate::ResolveContext;

/// Pass 2: Walk all items and resolve references inside bodies.
pub(crate) fn resolve_all(ctx: &mut ResolveContext, source_file: &SourceFile, root: ScopeId) {
    for item in &source_file.items {
        resolve_item(ctx, item, root);
    }
    check_unused(ctx);
}

// ---------------------------------------------------------------------------
// Items
// ---------------------------------------------------------------------------

fn resolve_item(ctx: &mut ResolveContext, item: &Item, root: ScopeId) {
    match &item.kind {
        ItemKind::Function(f) => resolve_fn_def(ctx, f, root),
        ItemKind::Method(m) => resolve_method_def(ctx, m, root),
        ItemKind::Constructor(c) => resolve_constructor_def(ctx, c, root),
        ItemKind::Struct(s) => resolve_struct_def(ctx, s, root),
        ItemKind::Enum(e) => resolve_enum_def(ctx, e, root),
        ItemKind::Interface(iface) => resolve_interface_def(ctx, iface, root),
        ItemKind::TypeAlias(ta) => resolve_type_alias(ctx, ta, root),
        ItemKind::Extern(ext) => resolve_extern_block(ctx, ext, root),
        ItemKind::Test(t) => resolve_test_def(ctx, t, root),
        ItemKind::Use(_) => { /* deferred to cross-module resolution */ }
        ItemKind::ImplFor(_) => { /* checked during type checking */ }
    }
}

fn resolve_fn_def(ctx: &mut ResolveContext, f: &FnDef, parent: ScopeId) {
    let scope = ctx.scope_tree.push_scope(ScopeKind::Function, Some(parent));

    // Register type params.
    register_type_params(ctx, &f.type_params, scope);

    // Register parameters.
    for p in &f.params {
        let def_id = ctx.alloc_symbol(
            p.name.clone(),
            SymbolKind::Param,
            Visibility::Private,
            p.span,
            None,
        );
        ctx.scope_tree.insert_value(scope, p.name.clone(), def_id);
        resolve_type_expr(ctx, &p.ty, scope);
    }

    // Return type.
    if let Some(ref ret) = f.return_type {
        resolve_type_expr(ctx, ret, scope);
    }

    // Effects.
    for eff in &f.effects {
        resolve_effect(ctx, eff, scope);
    }

    // Body.
    resolve_stmts(ctx, &f.body, scope);
}

fn resolve_method_def(ctx: &mut ResolveContext, m: &MethodDef, parent: ScopeId) {
    let scope = ctx.scope_tree.push_scope(ScopeKind::Function, Some(parent));

    // Register type params.
    register_type_params(ctx, &m.type_params, scope);

    // Register `Self` in type namespace (points to the receiver type).
    let receiver_name = type_expr_name(&m.receiver_type);
    if let Some(type_def) = ctx.scope_tree.lookup_type(parent, &receiver_name) {
        let self_def = ctx.alloc_symbol(
            "Self".to_string(),
            SymbolKind::TypeParam,
            Visibility::Private,
            Span::dummy(),
            Some(type_def),
        );
        ctx.scope_tree.insert_type(scope, "Self".to_string(), self_def);
    }

    // Register `self` in value namespace.
    let self_val = ctx.alloc_symbol(
        "self".to_string(),
        SymbolKind::Param,
        Visibility::Private,
        Span::dummy(),
        None,
    );
    ctx.scope_tree.insert_value(scope, "self".to_string(), self_val);

    // Resolve receiver type.
    resolve_type_expr(ctx, &m.receiver_type, scope);

    // Register parameters.
    for p in &m.params {
        let def_id = ctx.alloc_symbol(
            p.name.clone(),
            SymbolKind::Param,
            Visibility::Private,
            p.span,
            None,
        );
        ctx.scope_tree.insert_value(scope, p.name.clone(), def_id);
        resolve_type_expr(ctx, &p.ty, scope);
    }

    // Return type.
    if let Some(ref ret) = m.return_type {
        resolve_type_expr(ctx, ret, scope);
    }

    // Effects.
    for eff in &m.effects {
        resolve_effect(ctx, eff, scope);
    }

    // Body.
    resolve_stmts(ctx, &m.body, scope);
}

fn resolve_constructor_def(ctx: &mut ResolveContext, c: &ConstructorDef, parent: ScopeId) {
    let scope = ctx.scope_tree.push_scope(ScopeKind::Function, Some(parent));

    // Register type params.
    register_type_params(ctx, &c.type_params, scope);

    // Register `Self` in type namespace.
    if let Some(type_def) = ctx.scope_tree.lookup_type(parent, &c.type_name) {
        let self_def = ctx.alloc_symbol(
            "Self".to_string(),
            SymbolKind::TypeParam,
            Visibility::Private,
            Span::dummy(),
            Some(type_def),
        );
        ctx.scope_tree.insert_type(scope, "Self".to_string(), self_def);
    }

    // Parameters.
    for p in &c.params {
        let def_id = ctx.alloc_symbol(
            p.name.clone(),
            SymbolKind::Param,
            Visibility::Private,
            p.span,
            None,
        );
        ctx.scope_tree.insert_value(scope, p.name.clone(), def_id);
        resolve_type_expr(ctx, &p.ty, scope);
    }

    // Return type.
    if let Some(ref ret) = c.return_type {
        resolve_type_expr(ctx, ret, scope);
    }

    // Body.
    resolve_stmts(ctx, &c.body, scope);
}

fn resolve_struct_def(ctx: &mut ResolveContext, s: &StructDef, parent: ScopeId) {
    // Resolve types in fields. We don't need a new scope for the struct itself
    // unless it has type params.
    let scope = if s.type_params.is_empty() {
        parent
    } else {
        let sc = ctx.scope_tree.push_scope(ScopeKind::Block, Some(parent));
        register_type_params(ctx, &s.type_params, sc);
        sc
    };
    for field in &s.fields {
        resolve_type_expr(ctx, &field.ty, scope);
    }
}

fn resolve_enum_def(ctx: &mut ResolveContext, e: &EnumDef, parent: ScopeId) {
    let scope = if e.type_params.is_empty() {
        parent
    } else {
        let sc = ctx.scope_tree.push_scope(ScopeKind::Block, Some(parent));
        register_type_params(ctx, &e.type_params, sc);
        sc
    };
    for variant in &e.variants {
        for field in &variant.fields {
            resolve_type_expr(ctx, &field.ty, scope);
        }
    }
}

fn resolve_interface_def(ctx: &mut ResolveContext, iface: &InterfaceDef, parent: ScopeId) {
    // Always push a scope for Self and optional type params.
    let scope = ctx.scope_tree.push_scope(ScopeKind::Block, Some(parent));
    if !iface.type_params.is_empty() {
        register_type_params(ctx, &iface.type_params, scope);
    }

    // Register `Self` as an implicit type parameter for the interface.
    // Use a span inside the interface def so env.rs can locate it.
    let iface_def_id = ctx.scope_tree.lookup_type(parent, &iface.name);
    let iface_span = iface_def_id
        .and_then(|did| ctx.lookup_symbol(did))
        .map(|s| s.span)
        .unwrap_or(Span::dummy());
    let self_def = ctx.alloc_symbol(
        "Self".to_string(),
        SymbolKind::TypeParam,
        Visibility::Private,
        iface_span,
        iface_def_id,
    );
    ctx.scope_tree.insert_type(scope, "Self".to_string(), self_def);

    for method in &iface.methods {
        for p in &method.params {
            resolve_type_expr(ctx, &p.ty, scope);
        }
        if let Some(ref ret) = method.return_type {
            resolve_type_expr(ctx, ret, scope);
        }
    }
}

fn resolve_type_alias(ctx: &mut ResolveContext, ta: &TypeAlias, parent: ScopeId) {
    resolve_type_expr(ctx, &ta.ty, parent);
}

fn resolve_extern_block(ctx: &mut ResolveContext, ext: &ExternBlock, parent: ScopeId) {
    for decl in &ext.decls {
        for p in &decl.params {
            resolve_type_expr(ctx, &p.ty, parent);
        }
        if let Some(ref ret) = decl.return_type {
            resolve_type_expr(ctx, ret, parent);
        }
    }
}

fn resolve_test_def(ctx: &mut ResolveContext, t: &TestDef, parent: ScopeId) {
    let scope = ctx.scope_tree.push_scope(ScopeKind::Function, Some(parent));
    for p in &t.for_params {
        let def_id = ctx.alloc_symbol(
            p.name.clone(),
            SymbolKind::Param,
            Visibility::Private,
            p.span,
            None,
        );
        ctx.scope_tree.insert_value(scope, p.name.clone(), def_id);
        if let Some(ref ty) = p.ty {
            resolve_type_expr(ctx, ty, scope);
        }
    }
    resolve_stmts(ctx, &t.body, scope);
}

// ---------------------------------------------------------------------------
// Type params helper
// ---------------------------------------------------------------------------

fn register_type_params(ctx: &mut ResolveContext, params: &[TypeParam], scope: ScopeId) {
    for tp in params {
        match tp {
            TypeParam::Type { name, bounds, span } => {
                let def_id = ctx.alloc_symbol(
                    name.clone(),
                    SymbolKind::TypeParam,
                    Visibility::Private,
                    *span,
                    None,
                );
                ctx.scope_tree.insert_type(scope, name.clone(), def_id);
                for bound in bounds {
                    resolve_interface_bound(ctx, bound, scope);
                }
            }
            TypeParam::Const { name, ty, span } => {
                let def_id = ctx.alloc_symbol(
                    name.clone(),
                    SymbolKind::ConstParam,
                    Visibility::Private,
                    *span,
                    None,
                );
                ctx.scope_tree.insert_value(scope, name.clone(), def_id);
                resolve_type_expr(ctx, ty, scope);
            }
            TypeParam::Dim { name, span } => {
                let def_id = ctx.alloc_symbol(
                    name.clone(),
                    SymbolKind::DimParam,
                    Visibility::Private,
                    *span,
                    None,
                );
                ctx.scope_tree.insert_type(scope, name.clone(), def_id);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Statements
// ---------------------------------------------------------------------------

fn resolve_stmts(ctx: &mut ResolveContext, stmts: &[Stmt], scope: ScopeId) {
    for stmt in stmts {
        resolve_stmt(ctx, stmt, scope);
    }
}

fn resolve_stmt(ctx: &mut ResolveContext, stmt: &Stmt, scope: ScopeId) {
    match &stmt.kind {
        StmtKind::Let { name, ty, value, .. } => {
            // Resolve the value first (before binding the name, to prevent self-reference).
            resolve_expr(ctx, value, scope);
            if let Some(ty) = ty {
                resolve_type_expr(ctx, ty, scope);
            }
            let def_id = ctx.alloc_symbol(
                name.clone(),
                SymbolKind::LocalVar,
                Visibility::Private,
                stmt.span,
                None,
            );
            ctx.scope_tree.insert_value(scope, name.clone(), def_id);
        }

        StmtKind::LetPattern { pattern, ty, value, .. } => {
            resolve_expr(ctx, value, scope);
            if let Some(ty) = ty {
                resolve_type_expr(ctx, ty, scope);
            }
            bind_pattern(ctx, pattern, scope);
        }

        StmtKind::Assign { target, value } => {
            resolve_expr(ctx, target, scope);
            resolve_expr(ctx, value, scope);
        }

        StmtKind::Expr(expr) => {
            resolve_expr(ctx, expr, scope);
        }

        StmtKind::Return(opt_expr) => {
            if let Some(expr) = opt_expr {
                resolve_expr(ctx, expr, scope);
            }
        }

        StmtKind::Break(opt_expr) => {
            if let Some(expr) = opt_expr {
                resolve_expr(ctx, expr, scope);
            }
        }

        StmtKind::Continue => {}

        StmtKind::Assert { cond, message } => {
            resolve_expr(ctx, cond, scope);
            if let Some(msg) = message {
                resolve_expr(ctx, msg, scope);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------

fn resolve_expr(ctx: &mut ResolveContext, expr: &Expr, scope: ScopeId) {
    match &expr.kind {
        ExprKind::IntLit(_, _)
        | ExprKind::FloatLit(_, _)
        | ExprKind::StringLit(_)
        | ExprKind::CharLit(_)
        | ExprKind::BoolLit(_) => {}

        ExprKind::Ident(name) => {
            if name == "self" {
                // `self` is valid only inside a method — check value NS.
                if let Some(def_id) = ctx.scope_tree.lookup_value(scope, "self") {
                    ctx.record_resolution(expr.span.start, def_id);
                    ctx.mark_used(def_id);
                } else {
                    ctx.diagnostics.push(errors::invalid_self(
                        &ctx.file_name,
                        expr.span,
                        &ctx.source,
                    ));
                }
            } else if let Some(def_id) = ctx.scope_tree.lookup_value(scope, name) {
                ctx.record_resolution(expr.span.start, def_id);
                ctx.mark_used(def_id);
            } else if let Some(def_id) = ctx.scope_tree.lookup_type(scope, name) {
                // Type names can appear in expression context for constructor/method
                // calls like `Point.origin()` or struct literals like `Self #{...}`.
                ctx.record_resolution(expr.span.start, def_id);
                ctx.mark_used(def_id);
            } else {
                ctx.diagnostics.push(errors::undefined_variable(
                    name,
                    &ctx.file_name,
                    expr.span,
                    &ctx.source,
                ));
            }
        }

        ExprKind::BinOp { lhs, rhs, .. } => {
            resolve_expr(ctx, lhs, scope);
            resolve_expr(ctx, rhs, scope);
        }

        ExprKind::UnaryOp { operand, .. } => {
            resolve_expr(ctx, operand, scope);
        }

        ExprKind::Call { func, args } => {
            resolve_expr(ctx, func, scope);
            for arg in args {
                resolve_expr(ctx, &arg.expr, scope);
            }
        }

        ExprKind::Field { expr: inner, .. } => {
            // Resolve the base expression; field resolution requires type info (deferred).
            resolve_expr(ctx, inner, scope);
        }

        ExprKind::If { cond, then_branch, else_branch } => {
            resolve_expr(ctx, cond, scope);
            let then_scope = ctx.scope_tree.push_scope(ScopeKind::Block, Some(scope));
            resolve_stmts(ctx, then_branch, then_scope);
            if let Some(else_stmts) = else_branch {
                let else_scope = ctx.scope_tree.push_scope(ScopeKind::Block, Some(scope));
                resolve_stmts(ctx, else_stmts, else_scope);
            }
        }

        ExprKind::While { cond, body } => {
            resolve_expr(ctx, cond, scope);
            let body_scope = ctx.scope_tree.push_scope(ScopeKind::Block, Some(scope));
            resolve_stmts(ctx, body, body_scope);
        }

        ExprKind::Match { expr: scrutinee, arms } => {
            resolve_expr(ctx, scrutinee, scope);
            for arm in arms {
                let arm_scope = ctx.scope_tree.push_scope(ScopeKind::MatchArm, Some(scope));
                bind_pattern(ctx, &arm.pattern, arm_scope);
                if let Some(ref guard) = arm.guard {
                    resolve_expr(ctx, guard, arm_scope);
                }
                resolve_stmts(ctx, &arm.body, arm_scope);
            }
        }

        ExprKind::TupleLit(elems) => {
            for e in elems {
                resolve_expr(ctx, e, scope);
            }
        }

        ExprKind::StructLit { name, fields } => {
            // Resolve the struct name in the type namespace.
            if let Some(def_id) = ctx.scope_tree.lookup_type(scope, name) {
                ctx.record_resolution(expr.span.start, def_id);
                ctx.mark_used(def_id);
            } else {
                ctx.diagnostics.push(errors::undefined_type(
                    name,
                    &ctx.file_name,
                    expr.span,
                    &ctx.source,
                ));
            }
            for field in fields {
                resolve_expr(ctx, &field.value, scope);
            }
        }

        ExprKind::MapLit(entries) => {
            for entry in entries {
                resolve_expr(ctx, &entry.key, scope);
                resolve_expr(ctx, &entry.value, scope);
            }
        }

        ExprKind::SetLit(elems) => {
            for e in elems {
                resolve_expr(ctx, e, scope);
            }
        }

        ExprKind::For { pattern, iter, body } => {
            resolve_expr(ctx, iter, scope);
            let for_scope = ctx.scope_tree.push_scope(ScopeKind::ForLoop, Some(scope));
            bind_pattern(ctx, pattern, for_scope);
            resolve_stmts(ctx, body, for_scope);
        }

        ExprKind::Range { start, end } => {
            resolve_expr(ctx, start, scope);
            resolve_expr(ctx, end, scope);
        }

        ExprKind::Closure { params, body } => {
            let closure_scope = ctx.scope_tree.push_scope(ScopeKind::Closure, Some(scope));
            for p in params {
                let def_id = ctx.alloc_symbol(
                    p.name.clone(),
                    SymbolKind::ClosureParam,
                    Visibility::Private,
                    p.span,
                    None,
                );
                ctx.scope_tree.insert_value(closure_scope, p.name.clone(), def_id);
                if let Some(ref ty) = p.ty {
                    resolve_type_expr(ctx, ty, closure_scope);
                }
            }
            resolve_stmts(ctx, body, closure_scope);
        }

        ExprKind::Block(stmts) => {
            let block_scope = ctx.scope_tree.push_scope(ScopeKind::Block, Some(scope));
            resolve_stmts(ctx, stmts, block_scope);
        }

        ExprKind::Assert { cond, message } => {
            resolve_expr(ctx, cond, scope);
            if let Some(msg) = message {
                resolve_expr(ctx, msg, scope);
            }
        }

        ExprKind::Handle { expr: inner, arms } => {
            resolve_expr(ctx, inner, scope);
            for arm in arms {
                let arm_scope = ctx.scope_tree.push_scope(ScopeKind::HandleArm, Some(scope));
                // Bind handle arm params as local variables.
                for param_name in &arm.params {
                    let def_id = ctx.alloc_symbol(
                        param_name.clone(),
                        SymbolKind::Param,
                        Visibility::Private,
                        arm.span,
                        None,
                    );
                    ctx.scope_tree.insert_value(arm_scope, param_name.clone(), def_id);
                }
                resolve_stmts(ctx, &arm.body, arm_scope);
            }
        }

        ExprKind::Try(inner) => {
            resolve_expr(ctx, inner, scope);
        }

        ExprKind::Await(inner) => {
            resolve_expr(ctx, inner, scope);
        }

        ExprKind::Ref(inner) => {
            resolve_expr(ctx, inner, scope);
        }

        ExprKind::StringInterp { parts } => {
            for part in parts {
                if let StringInterpPart::Expr(e) = part {
                    resolve_expr(ctx, e, scope);
                }
            }
        }

        ExprKind::TypeApp { expr: inner, type_args } => {
            resolve_expr(ctx, inner, scope);
            for ty in type_args {
                resolve_type_expr(ctx, ty, scope);
            }
        }

        ExprKind::ArrayLit(elems) => {
            for e in elems {
                resolve_expr(ctx, e, scope);
            }
        }

        ExprKind::Index { expr: inner, index } => {
            resolve_expr(ctx, inner, scope);
            resolve_expr(ctx, index, scope);
        }
    }
}

// ---------------------------------------------------------------------------
// Type expressions
// ---------------------------------------------------------------------------

fn resolve_type_expr(ctx: &mut ResolveContext, ty: &TypeExpr, scope: ScopeId) {
    match ty {
        TypeExpr::Named { name, args, span } => {
            if let Some(def_id) = ctx.scope_tree.lookup_type(scope, name) {
                ctx.record_resolution(span.start, def_id);
                ctx.mark_used(def_id);
            } else {
                ctx.diagnostics.push(errors::undefined_type(
                    name,
                    &ctx.file_name,
                    *span,
                    &ctx.source,
                ));
            }
            for arg in args {
                resolve_type_expr(ctx, arg, scope);
            }
        }

        TypeExpr::Tuple { elements, .. } => {
            for e in elements {
                resolve_type_expr(ctx, e, scope);
            }
        }

        TypeExpr::Fn { params, ret, .. } => {
            for p in params {
                resolve_type_expr(ctx, p, scope);
            }
            resolve_type_expr(ctx, ret, scope);
        }

        TypeExpr::Ref { inner, .. } => {
            resolve_type_expr(ctx, inner, scope);
        }

        TypeExpr::Slice { inner, .. } => {
            resolve_type_expr(ctx, inner, scope);
        }

        TypeExpr::Array { inner, .. } => {
            resolve_type_expr(ctx, inner, scope);
        }

        TypeExpr::Dyn { inner, .. } => {
            resolve_type_expr(ctx, inner, scope);
        }

        TypeExpr::Active { base, .. } => {
            resolve_type_expr(ctx, base, scope);
        }

        TypeExpr::DimApply { base, dims, .. } => {
            resolve_type_expr(ctx, base, scope);
            for dim in dims {
                resolve_dim_expr(ctx, dim, scope);
            }
        }
    }
}

fn resolve_dim_expr(ctx: &mut ResolveContext, dim: &DimExpr, scope: ScopeId) {
    match dim {
        DimExpr::Lit(_) | DimExpr::Wildcard => {}
        DimExpr::Var(name) => {
            // Dim vars live in the type namespace (as DimParam).
            if ctx.scope_tree.lookup_type(scope, name).is_none() {
                ctx.diagnostics.push(errors::undefined_type(
                    name,
                    &ctx.file_name,
                    Span::dummy(),
                    &ctx.source,
                ));
            }
        }
        DimExpr::BinOp { lhs, rhs, .. } => {
            resolve_dim_expr(ctx, lhs, scope);
            resolve_dim_expr(ctx, rhs, scope);
        }
    }
}

fn resolve_interface_bound(ctx: &mut ResolveContext, bound: &InterfaceBound, scope: ScopeId) {
    if let Some(def_id) = ctx.scope_tree.lookup_type(scope, &bound.name) {
        // Verify it is actually an interface.
        let kind = ctx.lookup_symbol(def_id).map(|s| s.kind);
        if kind != Some(SymbolKind::Interface) && kind.is_some() {
            ctx.diagnostics.push(errors::not_an_interface(
                &bound.name,
                &ctx.file_name,
                bound.span,
                &ctx.source,
            ));
        }
        ctx.record_resolution(bound.span.start, def_id);
        ctx.mark_used(def_id);
    } else {
        ctx.diagnostics.push(errors::undefined_type(
            &bound.name,
            &ctx.file_name,
            bound.span,
            &ctx.source,
        ));
    }
    for arg in &bound.args {
        resolve_type_expr(ctx, arg, scope);
    }
}

fn resolve_effect(ctx: &mut ResolveContext, eff: &Effect, scope: ScopeId) {
    if let Some(def_id) = ctx.scope_tree.lookup_type(scope, &eff.name) {
        ctx.record_resolution(eff.span.start, def_id);
        ctx.mark_used(def_id);
    }
    // Effects are not required to be defined at this stage (they may be
    // language-level effects). We silently ignore unresolved effects for now.
    for arg in &eff.args {
        resolve_type_expr(ctx, arg, scope);
    }
}

// ---------------------------------------------------------------------------
// Patterns
// ---------------------------------------------------------------------------

/// Bind names introduced by a pattern into the given scope.
fn bind_pattern(ctx: &mut ResolveContext, pat: &Pattern, scope: ScopeId) {
    match &pat.kind {
        PatternKind::Wildcard => {}

        PatternKind::Ident(name) => {
            let def_id = ctx.alloc_symbol(
                name.clone(),
                SymbolKind::LocalVar,
                Visibility::Private,
                pat.span,
                None,
            );
            ctx.scope_tree.insert_value(scope, name.clone(), def_id);
        }

        PatternKind::Literal(expr) => {
            // Literal patterns don't bind anything, but may contain idents
            // (e.g. a named constant — for now we just resolve the expr).
            resolve_expr(ctx, expr, scope);
        }

        PatternKind::TuplePattern(pats) => {
            for p in pats {
                bind_pattern(ctx, p, scope);
            }
        }

        PatternKind::Constructor { path, type_args: _, fields } => {
            // path[0] is the enum name, path[1] is the variant name.
            if path.len() >= 2 {
                let enum_name = &path[0];
                let variant_name = &path[1];
                if let Some(enum_def) = ctx.scope_tree.lookup_type(scope, enum_name) {
                    ctx.record_resolution(pat.span.start, enum_def);
                    ctx.mark_used(enum_def);
                    // Check that the variant exists.
                    let found = ctx.symbols.iter().any(|s| {
                        s.kind == SymbolKind::EnumVariant
                            && s.parent == Some(enum_def)
                            && s.name == *variant_name
                    });
                    if !found {
                        ctx.diagnostics.push(errors::undefined_variant(
                            enum_name,
                            variant_name,
                            &ctx.file_name,
                            pat.span,
                            &ctx.source,
                        ));
                    }
                } else {
                    ctx.diagnostics.push(errors::undefined_type(
                        enum_name,
                        &ctx.file_name,
                        pat.span,
                        &ctx.source,
                    ));
                }
            }
            for p in fields {
                bind_pattern(ctx, p, scope);
            }
        }

        PatternKind::Or(pats) => {
            // Each alternative should bind the same names; for now, just process them all.
            for p in pats {
                bind_pattern(ctx, p, scope);
            }
        }

        PatternKind::Rest(opt_name) => {
            if let Some(name) = opt_name {
                let def_id = ctx.alloc_symbol(
                    name.clone(),
                    SymbolKind::LocalVar,
                    Visibility::Private,
                    pat.span,
                    None,
                );
                ctx.scope_tree.insert_value(scope, name.clone(), def_id);
            }
        }

        PatternKind::List(pats) => {
            for p in pats {
                bind_pattern(ctx, p, scope);
            }
        }

        PatternKind::Struct { name, fields, .. } => {
            // Resolve the struct name in the type namespace.
            if let Some(def_id) = ctx.scope_tree.lookup_type(scope, name) {
                ctx.record_resolution(pat.span.start, def_id);
                ctx.mark_used(def_id);
            } else {
                ctx.diagnostics.push(errors::undefined_type(
                    name,
                    &ctx.file_name,
                    pat.span,
                    &ctx.source,
                ));
            }
            for fp in fields {
                if let Some(ref inner_pat) = fp.pattern {
                    bind_pattern(ctx, inner_pat, scope);
                } else {
                    // Shorthand: `#{name}` binds `name` as a local variable.
                    let def_id = ctx.alloc_symbol(
                        fp.name.clone(),
                        SymbolKind::LocalVar,
                        Visibility::Private,
                        fp.span,
                        None,
                    );
                    ctx.scope_tree.insert_value(scope, fp.name.clone(), def_id);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Post-pass: unused variable check
// ---------------------------------------------------------------------------

fn check_unused(ctx: &mut ResolveContext) {
    for sym in &ctx.symbols {
        if sym.kind == SymbolKind::LocalVar && !sym.used && !sym.name.starts_with('_') {
            ctx.diagnostics.push(errors::unused_variable(
                &sym.name,
                &ctx.file_name,
                sym.span,
                &ctx.source,
            ));
        }
    }
}

/// Extract the simple name from a type expression.
fn type_expr_name(ty: &TypeExpr) -> String {
    match ty {
        TypeExpr::Named { name, .. } => name.clone(),
        _ => "<unknown>".to_string(),
    }
}
