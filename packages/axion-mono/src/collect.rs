use std::collections::HashSet;

use axion_resolve::def_id::{DefId, SymbolKind};
use axion_resolve::ResolveOutput;
use axion_syntax::*;
use axion_types::ty::Ty;
use axion_types::TypeCheckOutput;

use crate::output::SpecKey;

/// Collected instantiation: a generic function called with specific type args.
#[derive(Debug, Clone)]
pub struct Instantiation {
    pub fn_def_id: DefId,
    pub type_args: Vec<Ty>,
}

/// Scan the AST for all generic function instantiations.
pub fn collect_instantiations(
    source_file: &SourceFile,
    resolved: &ResolveOutput,
    type_check: &TypeCheckOutput,
) -> Vec<Instantiation> {
    let mut result = Vec::new();
    let mut seen = std::collections::HashSet::new();

    for item in &source_file.items {
        match &item.kind {
            ItemKind::Function(f) => {
                collect_from_stmts(&f.body, resolved, type_check, &mut result, &mut seen);
            }
            ItemKind::Method(m) => {
                collect_from_stmts(&m.body, resolved, type_check, &mut result, &mut seen);
            }
            ItemKind::Constructor(c) => {
                collect_from_stmts(&c.body, resolved, type_check, &mut result, &mut seen);
            }
            ItemKind::Test(t) => {
                collect_from_stmts(&t.body, resolved, type_check, &mut result, &mut seen);
            }
            _ => {}
        }
    }

    // Auto-collect transitive method calls: when a method on a generic type
    // calls other methods on `self`, those also need to be specialized with
    // the same type_args.
    collect_transitive_self_calls(&mut result, &mut seen, source_file, resolved);

    // Auto-collect `drop` method specializations for any generic type whose
    // methods were instantiated, since `drop` is called implicitly at cleanup.
    collect_implicit_drop(&mut result, &mut seen, resolved);

    result
}

/// Iteratively discover transitive method calls on `self` within method bodies.
///
/// When `HashMap.insert with [i64, i64]` is collected, and `insert`'s body
/// calls `self._grow()`, this function ensures `HashMap._grow with [i64, i64]`
/// is also collected. Iterates to a fixed point.
fn collect_transitive_self_calls(
    result: &mut Vec<Instantiation>,
    seen: &mut HashSet<SpecKey>,
    source_file: &SourceFile,
    resolved: &ResolveOutput,
) {
    let mut i = 0;
    while i < result.len() {
        let inst = result[i].clone();
        i += 1;

        // Find the symbol for this instantiation.
        let sym = match resolved.symbols.iter().find(|s| s.def_id == inst.fn_def_id) {
            Some(s) if matches!(s.kind, SymbolKind::Method | SymbolKind::Constructor) => s,
            _ => continue,
        };

        // Extract the type name from "TypeName.method_name".
        let type_name = match sym.name.find('.') {
            Some(pos) => &sym.name[..pos],
            None => continue,
        };

        // Find the method's AST node by matching on receiver type name and method name.
        let method_name = &sym.name[sym.name.find('.').unwrap() + 1..];
        let method_body = source_file.items.iter().find_map(|item| {
            if let ItemKind::Method(m) = &item.kind {
                let recv_name = type_expr_name_simple(&m.receiver_type);
                if recv_name == type_name && m.name == method_name {
                    return Some(&m.body);
                }
            }
            None
        });

        let body = match method_body {
            Some(b) => b,
            None => continue,
        };

        // Find all method calls on `self` in this method's body.
        let self_calls = find_self_method_calls(body);
        for call_name in &self_calls {
            let method_key = format!("{}.{}", type_name, call_name);
            let method_sym = resolved.symbols.iter().find(|s| {
                s.name == method_key
                    && matches!(s.kind, SymbolKind::Method | SymbolKind::Constructor)
            });
            if let Some(method_sym) = method_sym {
                let key = SpecKey {
                    fn_def_id: method_sym.def_id,
                    type_args: inst.type_args.clone(),
                };
                if !seen.contains(&key) {
                    seen.insert(key);
                    result.push(Instantiation {
                        fn_def_id: method_sym.def_id,
                        type_args: inst.type_args.clone(),
                    });
                }
            }
        }
    }
}

/// Extract a simple name from a TypeExpr (for matching receiver types).
fn type_expr_name_simple(te: &TypeExpr) -> &str {
    match te {
        TypeExpr::Named { name, .. } => name.as_str(),
        _ => "",
    }
}

/// Find all method names called on `self` in a list of statements.
fn find_self_method_calls(stmts: &[Stmt]) -> Vec<String> {
    let mut names = Vec::new();
    for stmt in stmts {
        find_self_calls_in_stmt(stmt, &mut names);
    }
    names
}

fn find_self_calls_in_stmt(stmt: &Stmt, names: &mut Vec<String>) {
    match &stmt.kind {
        StmtKind::Let { value, .. } => find_self_calls_in_expr(value, names),
        StmtKind::LetPattern { value, .. } => find_self_calls_in_expr(value, names),
        StmtKind::Assign { target, value } => {
            find_self_calls_in_expr(target, names);
            find_self_calls_in_expr(value, names);
        }
        StmtKind::Expr(e) => find_self_calls_in_expr(e, names),
        StmtKind::Return(opt) => {
            if let Some(e) = opt {
                find_self_calls_in_expr(e, names);
            }
        }
        StmtKind::Break(opt) => {
            if let Some(e) = opt {
                find_self_calls_in_expr(e, names);
            }
        }
        StmtKind::Continue => {}
        StmtKind::Assert { cond, message } => {
            find_self_calls_in_expr(cond, names);
            if let Some(m) = message {
                find_self_calls_in_expr(m, names);
            }
        }
    }
}

fn find_self_calls_in_expr(expr: &Expr, names: &mut Vec<String>) {
    match &expr.kind {
        ExprKind::Call { func, args } => {
            // Check if this is a self.method_name() call.
            if let ExprKind::Field { expr: inner, name } = &func.kind {
                if is_self_expr(inner) {
                    names.push(name.clone());
                }
            }
            find_self_calls_in_expr(func, names);
            for arg in args {
                find_self_calls_in_expr(&arg.expr, names);
            }
        }
        ExprKind::BinOp { lhs, rhs, .. } => {
            find_self_calls_in_expr(lhs, names);
            find_self_calls_in_expr(rhs, names);
        }
        ExprKind::UnaryOp { operand, .. } => {
            find_self_calls_in_expr(operand, names);
        }
        ExprKind::If { cond, then_branch, else_branch } => {
            find_self_calls_in_expr(cond, names);
            for s in then_branch {
                find_self_calls_in_stmt(s, names);
            }
            if let Some(els) = else_branch {
                for s in els {
                    find_self_calls_in_stmt(s, names);
                }
            }
        }
        ExprKind::While { cond, body } => {
            find_self_calls_in_expr(cond, names);
            for s in body {
                find_self_calls_in_stmt(s, names);
            }
        }
        ExprKind::Block(stmts) => {
            for s in stmts {
                find_self_calls_in_stmt(s, names);
            }
        }
        ExprKind::Match { expr: scrutinee, arms } => {
            find_self_calls_in_expr(scrutinee, names);
            for arm in arms {
                for s in &arm.body {
                    find_self_calls_in_stmt(s, names);
                }
            }
        }
        ExprKind::For { iter, body, .. } => {
            find_self_calls_in_expr(iter, names);
            for s in body {
                find_self_calls_in_stmt(s, names);
            }
        }
        ExprKind::Closure { body, .. } => {
            for s in body {
                find_self_calls_in_stmt(s, names);
            }
        }
        ExprKind::Field { expr: inner, .. }
        | ExprKind::Ref(inner)
        | ExprKind::Try(inner)
        | ExprKind::Await(inner) => {
            find_self_calls_in_expr(inner, names);
        }
        ExprKind::StructLit { fields, .. } => {
            for f in fields {
                find_self_calls_in_expr(&f.value, names);
            }
        }
        ExprKind::TupleLit(elems) | ExprKind::SetLit(elems) => {
            for e in elems {
                find_self_calls_in_expr(e, names);
            }
        }
        ExprKind::Range { start, end } => {
            if let Some(s) = start { find_self_calls_in_expr(s, names); }
            if let Some(e) = end { find_self_calls_in_expr(e, names); }
        }
        ExprKind::StringInterp { parts } => {
            for part in parts {
                if let StringInterpPart::Expr(e) = part {
                    find_self_calls_in_expr(e, names);
                }
            }
        }
        ExprKind::MapLit(entries) => {
            for entry in entries {
                find_self_calls_in_expr(&entry.key, names);
                find_self_calls_in_expr(&entry.value, names);
            }
        }
        ExprKind::Handle { expr: inner, arms } => {
            find_self_calls_in_expr(inner, names);
            for arm in arms {
                for s in &arm.body {
                    find_self_calls_in_stmt(s, names);
                }
            }
        }
        ExprKind::Assert { cond, message } => {
            find_self_calls_in_expr(cond, names);
            if let Some(m) = message {
                find_self_calls_in_expr(m, names);
            }
        }
        ExprKind::Cast { expr: inner, .. } => {
            find_self_calls_in_expr(inner, names);
        }
        _ => {}
    }
}

/// Check if an expression is `self`.
fn is_self_expr(expr: &Expr) -> bool {
    matches!(&expr.kind, ExprKind::Ident(name) if name == "self")
}

/// For every method instantiation on a generic type, ensure the type's `drop`
/// method (if any) is also collected with the same type_args.
fn collect_implicit_drop(
    result: &mut Vec<Instantiation>,
    seen: &mut HashSet<SpecKey>,
    resolved: &ResolveOutput,
) {
    // Gather (type_name, type_args) pairs from existing instantiations.
    let mut type_instances: Vec<(String, Vec<Ty>)> = Vec::new();
    for inst in result.iter() {
        let sym = resolved.symbols.iter().find(|s| s.def_id == inst.fn_def_id);
        if let Some(sym) = sym {
            if matches!(sym.kind, SymbolKind::Method | SymbolKind::Constructor) {
                // Method name is "TypeName.method_name" — extract the type name.
                if let Some(dot_pos) = sym.name.find('.') {
                    let type_name = &sym.name[..dot_pos];
                    type_instances.push((type_name.to_string(), inst.type_args.clone()));
                }
            }
        }
    }

    // For each type instance, check if a drop method exists and collect it.
    for (type_name, type_args) in &type_instances {
        let drop_key = format!("{}.drop", type_name);
        let drop_sym = resolved.symbols.iter().find(|s| {
            s.name == drop_key && s.kind == SymbolKind::Method
        });
        if let Some(drop_sym) = drop_sym {
            let key = SpecKey {
                fn_def_id: drop_sym.def_id,
                type_args: type_args.clone(),
            };
            if !seen.contains(&key) {
                seen.insert(key);
                result.push(Instantiation {
                    fn_def_id: drop_sym.def_id,
                    type_args: type_args.clone(),
                });
            }
        }
    }
}

fn collect_from_stmts(
    stmts: &[Stmt],
    resolved: &ResolveOutput,
    type_check: &TypeCheckOutput,
    result: &mut Vec<Instantiation>,
    seen: &mut std::collections::HashSet<SpecKey>,
) {
    for stmt in stmts {
        collect_from_stmt(stmt, resolved, type_check, result, seen);
    }
}

fn collect_from_stmt(
    stmt: &Stmt,
    resolved: &ResolveOutput,
    type_check: &TypeCheckOutput,
    result: &mut Vec<Instantiation>,
    seen: &mut std::collections::HashSet<SpecKey>,
) {
    match &stmt.kind {
        StmtKind::Let { value, .. } => {
            collect_from_expr(value, resolved, type_check, result, seen);
        }
        StmtKind::LetPattern { value, .. } => {
            collect_from_expr(value, resolved, type_check, result, seen);
        }
        StmtKind::Assign { target, value } => {
            collect_from_expr(target, resolved, type_check, result, seen);
            collect_from_expr(value, resolved, type_check, result, seen);
        }
        StmtKind::Expr(e) => {
            collect_from_expr(e, resolved, type_check, result, seen);
        }
        StmtKind::Return(opt) => {
            if let Some(e) = opt {
                collect_from_expr(e, resolved, type_check, result, seen);
            }
        }
        StmtKind::Break(opt) => {
            if let Some(e) = opt {
                collect_from_expr(e, resolved, type_check, result, seen);
            }
        }
        StmtKind::Continue => {}
        StmtKind::Assert { cond, message } => {
            collect_from_expr(cond, resolved, type_check, result, seen);
            if let Some(m) = message {
                collect_from_expr(m, resolved, type_check, result, seen);
            }
        }
    }
}

fn collect_from_expr(
    expr: &Expr,
    resolved: &ResolveOutput,
    type_check: &TypeCheckOutput,
    result: &mut Vec<Instantiation>,
    seen: &mut std::collections::HashSet<SpecKey>,
) {
    match &expr.kind {
        ExprKind::TypeApp { expr: inner, type_args } => {
            // This is a turbofish call: f[T](...)
            // Check if the inner expression refers to a generic function.
            if let ExprKind::Ident(_) = &inner.kind {
                if let Some(&fn_def_id) = resolved.resolutions.get(&inner.span.start) {
                    // Check that this is actually a generic function (has TypeParam symbols).
                    let fn_sym = resolved.symbols.iter().find(|s| s.def_id == fn_def_id);
                    if let Some(fn_sym) = fn_sym {
                        let is_generic = resolved.symbols.iter().any(|s| {
                            s.kind == SymbolKind::TypeParam
                                && s.name != "Self"
                                && s.span.start >= fn_sym.span.start
                                && s.span.end <= fn_sym.span.end
                        });

                        if is_generic {
                            // Lower type arguments to concrete types.
                            let concrete_args: Vec<Ty> = type_args
                                .iter()
                                .map(|ta| {
                                    let ta_span = type_expr_span(ta);
                                    type_check
                                        .expr_types
                                        .get(&ta_span.start)
                                        .cloned()
                                        .unwrap_or_else(|| lower_type_arg(ta, resolved))
                                })
                                .collect();

                            let key = SpecKey {
                                fn_def_id,
                                type_args: concrete_args.clone(),
                            };

                            if !seen.contains(&key) {
                                seen.insert(key);
                                result.push(Instantiation {
                                    fn_def_id,
                                    type_args: concrete_args,
                                });
                            }
                        }
                    }
                }
            }
            // Also recurse into inner and type_args.
            collect_from_expr(inner, resolved, type_check, result, seen);
        }
        ExprKind::Call { func, args } => {
            // Extract the field access from the func, handling optional TypeApp wrapping.
            // This covers both `obj.method(args)` and `obj.method[U](args)`.
            let field_info: Option<(&Expr, &str)> = match &func.kind {
                ExprKind::Field { expr: inner, name } => Some((inner, name.as_str())),
                ExprKind::TypeApp { expr: ta_inner, .. } => {
                    if let ExprKind::Field { expr: inner, name } = &ta_inner.kind {
                        Some((inner, name.as_str()))
                    } else {
                        None
                    }
                }
                _ => None,
            };
            // Check for method calls on generic receiver types.
            if let Some((inner, method_name)) = field_info {
                // Use method_receiver_types (which avoids span collision) first,
                // fall back to expr_types.
                let receiver_ty = type_check.method_receiver_types.get(&expr.span.start)
                    .or_else(|| type_check.expr_types.get(&inner.span.start));
                if let Some(inner_ty) = receiver_ty {
                    let type_args = match inner_ty {
                        Ty::Enum { type_args, .. } | Ty::Struct { type_args, .. } => type_args.clone(),
                        _ => vec![],
                    };
                    if !type_args.is_empty() {
                        let type_name = match inner_ty {
                            Ty::Enum { def_id, .. } | Ty::Struct { def_id, .. } => {
                                resolved.symbols.iter()
                                    .find(|s| s.def_id == *def_id)
                                    .map(|s| s.name.clone())
                            }
                            _ => None,
                        };
                        if let Some(type_name) = type_name {
                            let method_key = format!("{}.{}", type_name, method_name);
                            let method_sym = resolved.symbols.iter().find(|s| {
                                s.name == method_key
                                    && matches!(s.kind, SymbolKind::Method | SymbolKind::Constructor)
                            });
                            if let Some(method_sym) = method_sym {
                                // Combine receiver type_args with method-level turbofish args.
                                let mut combined_args = type_args.clone();
                                if let ExprKind::TypeApp { type_args: turbo_args, .. } = &func.kind {
                                    for ta in turbo_args {
                                        let ta_span = type_expr_span(ta);
                                        let concrete = type_check
                                            .expr_types
                                            .get(&ta_span.start)
                                            .cloned()
                                            .unwrap_or_else(|| lower_type_arg(ta, resolved));
                                        combined_args.push(concrete);
                                    }
                                }

                                let key = SpecKey {
                                    fn_def_id: method_sym.def_id,
                                    type_args: combined_args.clone(),
                                };

                                if !seen.contains(&key) {
                                    seen.insert(key);
                                    result.push(Instantiation {
                                        fn_def_id: method_sym.def_id,
                                        type_args: combined_args,
                                    });
                                }
                            }
                        }
                    }
                }
            }
            collect_from_expr(func, resolved, type_check, result, seen);
            for arg in args {
                collect_from_expr(&arg.expr, resolved, type_check, result, seen);
            }
        }
        ExprKind::BinOp { lhs, rhs, .. } => {
            collect_from_expr(lhs, resolved, type_check, result, seen);
            collect_from_expr(rhs, resolved, type_check, result, seen);
        }
        ExprKind::UnaryOp { operand, .. } => {
            collect_from_expr(operand, resolved, type_check, result, seen);
        }
        ExprKind::If { cond, then_branch, else_branch } => {
            collect_from_expr(cond, resolved, type_check, result, seen);
            collect_from_stmts(then_branch, resolved, type_check, result, seen);
            if let Some(els) = else_branch {
                collect_from_stmts(els, resolved, type_check, result, seen);
            }
        }
        ExprKind::While { cond, body } => {
            collect_from_expr(cond, resolved, type_check, result, seen);
            collect_from_stmts(body, resolved, type_check, result, seen);
        }
        ExprKind::Block(stmts) => {
            collect_from_stmts(stmts, resolved, type_check, result, seen);
        }
        ExprKind::Match { expr: scrutinee, arms } => {
            collect_from_expr(scrutinee, resolved, type_check, result, seen);
            for arm in arms {
                collect_from_stmts(&arm.body, resolved, type_check, result, seen);
            }
        }
        ExprKind::For { iter, body, .. } => {
            collect_from_expr(iter, resolved, type_check, result, seen);
            collect_from_stmts(body, resolved, type_check, result, seen);
        }
        ExprKind::Closure { body, .. } => {
            collect_from_stmts(body, resolved, type_check, result, seen);
        }
        ExprKind::Field { expr: inner, .. } | ExprKind::Ref(inner) | ExprKind::Try(inner) | ExprKind::Await(inner) => {
            collect_from_expr(inner, resolved, type_check, result, seen);
        }
        ExprKind::StructLit { fields, .. } => {
            for f in fields {
                collect_from_expr(&f.value, resolved, type_check, result, seen);
            }
        }
        ExprKind::TupleLit(elems) | ExprKind::SetLit(elems) => {
            for e in elems {
                collect_from_expr(e, resolved, type_check, result, seen);
            }
        }
        ExprKind::Range { start, end } => {
            if let Some(s) = start { collect_from_expr(s, resolved, type_check, result, seen); }
            if let Some(e) = end { collect_from_expr(e, resolved, type_check, result, seen); }
        }
        ExprKind::StringInterp { parts } => {
            for part in parts {
                if let StringInterpPart::Expr(e) = part {
                    collect_from_expr(e, resolved, type_check, result, seen);
                }
            }
        }
        ExprKind::MapLit(entries) => {
            for entry in entries {
                collect_from_expr(&entry.key, resolved, type_check, result, seen);
                collect_from_expr(&entry.value, resolved, type_check, result, seen);
            }
        }
        ExprKind::Handle { expr: inner, arms } => {
            collect_from_expr(inner, resolved, type_check, result, seen);
            for arm in arms {
                collect_from_stmts(&arm.body, resolved, type_check, result, seen);
            }
        }
        ExprKind::Assert { cond, message } => {
            collect_from_expr(cond, resolved, type_check, result, seen);
            if let Some(m) = message {
                collect_from_expr(m, resolved, type_check, result, seen);
            }
        }
        ExprKind::Cast { expr: inner, .. } => {
            collect_from_expr(inner, resolved, type_check, result, seen);
        }
        _ => {}
    }
}

/// Extract the span from a TypeExpr.
fn type_expr_span(te: &TypeExpr) -> Span {
    match te {
        TypeExpr::Named { span, .. }
        | TypeExpr::Tuple { span, .. }
        | TypeExpr::Fn { span, .. }
        | TypeExpr::Ref { span, .. }
        | TypeExpr::Slice { span, .. }
        | TypeExpr::Dyn { span, .. }
        | TypeExpr::Active { span, .. }
        | TypeExpr::Array { span, .. }
        | TypeExpr::DimApply { span, .. } => *span,
    }
}

/// Lower a TypeExpr to a Ty for type arguments.
fn lower_type_arg(te: &TypeExpr, resolved: &ResolveOutput) -> Ty {
    use axion_types::ty::PrimTy;
    match te {
        TypeExpr::Named { name, .. } => {
            // Try primitive types first.
            if let Some(prim) = PrimTy::from_name(name) {
                return Ty::Prim(prim);
            }
            // Look up in symbols.
            if let Some(&def_id) = resolved.resolutions.get(&type_expr_span(te).start) {
                let sym = resolved.symbols.iter().find(|s| s.def_id == def_id);
                if let Some(sym) = sym {
                    match sym.kind {
                        SymbolKind::Struct => return Ty::Struct { def_id, type_args: vec![] },
                        SymbolKind::Enum => return Ty::Enum { def_id, type_args: vec![] },
                        _ => {}
                    }
                }
            }
            Ty::Error
        }
        TypeExpr::Ref { inner, .. } => Ty::Ref(Box::new(lower_type_arg(inner, resolved))),
        _ => Ty::Error,
    }
}
