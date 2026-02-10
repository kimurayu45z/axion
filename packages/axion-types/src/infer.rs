use std::collections::HashMap;

use axion_diagnostics::Diagnostic;
use axion_resolve::def_id::{DefId, SymbolKind};
use axion_resolve::ResolveOutput;
use axion_syntax::*;

use crate::env::TypeEnv;
use crate::errors;
use crate::lower::lower_type_expr;
use crate::ty::{PrimTy, Ty};
use crate::unify::UnifyContext;

/// The inference context for type-checking a single function body.
pub(crate) struct InferCtx<'a> {
    pub env: &'a mut TypeEnv,
    pub unify: &'a mut UnifyContext,
    pub resolved: &'a ResolveOutput,
    pub diagnostics: &'a mut Vec<Diagnostic>,
    pub file_name: &'a str,
    pub source: &'a str,
    /// Expression types: span.start → Ty
    pub expr_types: &'a mut HashMap<u32, Ty>,
    /// Field resolution: span.start → field index
    pub field_resolutions: &'a mut HashMap<u32, usize>,
    /// Current function's return type.
    pub current_return_ty: Ty,
    /// Self type for methods (None for free functions).
    pub self_ty: Option<Ty>,
    /// Effects declared on the current function being checked.
    pub current_effects: Vec<String>,
    /// Effects that are handled in the current scope (via handle expressions).
    pub handled_effects: Vec<String>,
}

impl<'a> InferCtx<'a> {
    /// Infer the type of an expression.
    pub fn infer_expr(&mut self, expr: &Expr) -> Ty {
        let ty = self.infer_expr_inner(expr);
        self.expr_types.insert(expr.span.start, ty.clone());
        ty
    }

    fn infer_expr_inner(&mut self, expr: &Expr) -> Ty {
        match &expr.kind {
            ExprKind::IntLit(_, suffix) => self.infer_int_lit(suffix),
            ExprKind::FloatLit(_, suffix) => self.infer_float_lit(suffix),
            ExprKind::StringLit(_) => Ty::Prim(PrimTy::Str),
            ExprKind::CharLit(_) => Ty::Prim(PrimTy::Char),
            ExprKind::BoolLit(_) => Ty::Prim(PrimTy::Bool),
            ExprKind::Ident(_) => self.infer_ident(expr),
            ExprKind::BinOp { op, lhs, rhs } => self.infer_binop(*op, lhs, rhs, expr.span),
            ExprKind::UnaryOp { op, operand } => self.infer_unaryop(*op, operand, expr.span),
            ExprKind::Call { func, args } => self.infer_call(func, args, expr.span),
            ExprKind::Field { expr: inner, name } => {
                self.infer_field(inner, name, expr.span)
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => self.infer_if(cond, then_branch, else_branch.as_deref(), expr.span),
            ExprKind::While { cond, body } => self.infer_while(cond, body),
            ExprKind::Match { expr: scrutinee, arms } => {
                self.infer_match(scrutinee, arms, expr.span)
            }
            ExprKind::TupleLit(elems) => self.infer_tuple_lit(elems),
            ExprKind::StructLit { name, fields } => {
                self.infer_struct_lit(name, fields, expr.span)
            }
            ExprKind::For { pattern, iter, body } => {
                self.infer_for(pattern, iter, body)
            }
            ExprKind::Range { start, end } => self.infer_range(start, end, expr.span),
            ExprKind::Closure { params, body } => self.infer_closure(params, body),
            ExprKind::Block(stmts) => self.infer_block(stmts),
            ExprKind::Try(inner) => {
                // Deferred — just infer inner.
                self.infer_expr(inner)
            }
            ExprKind::Await(inner) => {
                // Deferred — just infer inner.
                self.infer_expr(inner)
            }
            ExprKind::Ref(inner) => {
                let inner_ty = self.infer_expr(inner);
                Ty::Ref(Box::new(inner_ty))
            }
            ExprKind::TypeApp { expr: inner, type_args } => {
                self.infer_type_app(inner, type_args, expr.span)
            }
            ExprKind::Assert { cond, message } => {
                let cond_ty = self.infer_expr(cond);
                self.expect_type(&cond_ty, &Ty::Prim(PrimTy::Bool), cond.span);
                if let Some(msg) = message {
                    self.infer_expr(msg);
                }
                Ty::Unit
            }
            ExprKind::Handle { expr: inner, arms } => {
                // Extract effect names from handle arms and add them to handled_effects.
                let mut new_handled: Vec<String> = Vec::new();
                for arm in arms {
                    new_handled.push(arm.effect.clone());
                }
                // Push handled effects before inferring inner expression.
                let prev_handled = self.handled_effects.clone();
                self.handled_effects.extend(new_handled);

                let ty = self.infer_expr(inner);

                // Infer arm bodies.
                for arm in arms {
                    self.infer_stmts(&arm.body);
                }

                // Restore handled effects.
                self.handled_effects = prev_handled;
                ty
            }
            ExprKind::StringInterp { parts } => {
                for part in parts {
                    if let StringInterpPart::Expr(e) = part {
                        self.infer_expr(e);
                    }
                }
                Ty::Prim(PrimTy::Str)
            }
            ExprKind::ArrayLit(elems) => self.infer_array_lit(elems),
            ExprKind::Index { expr: arr_expr, index } => {
                self.infer_index(arr_expr, index, expr.span)
            }
            ExprKind::MapLit(entries) => {
                for entry in entries {
                    self.infer_expr(&entry.key);
                    self.infer_expr(&entry.value);
                }
                Ty::Error // Map type deferred
            }
            ExprKind::SetLit(elems) => {
                for elem in elems {
                    self.infer_expr(elem);
                }
                Ty::Error // Set type deferred
            }
        }
    }

    fn infer_int_lit(&self, suffix: &Option<String>) -> Ty {
        match suffix.as_deref() {
            Some(s) => {
                if let Some(prim) = PrimTy::from_name(s) {
                    Ty::Prim(prim)
                } else {
                    Ty::Prim(PrimTy::I64)
                }
            }
            None => Ty::Prim(PrimTy::I64),
        }
    }

    fn infer_float_lit(&self, suffix: &Option<String>) -> Ty {
        match suffix.as_deref() {
            Some(s) => {
                if let Some(prim) = PrimTy::from_name(s) {
                    Ty::Prim(prim)
                } else {
                    Ty::Prim(PrimTy::F64)
                }
            }
            None => Ty::Prim(PrimTy::F64),
        }
    }

    fn infer_ident(&mut self, expr: &Expr) -> Ty {
        // Look up the resolution for this identifier.
        if let Some(&def_id) = self.resolved.resolutions.get(&expr.span.start) {
            // Check if this is a `self` reference — use self_ty if available.
            let sym = self.resolved.symbols.iter().find(|s| s.def_id == def_id);
            if let Some(sym) = sym {
                if sym.name == "self" && sym.kind == SymbolKind::Param {
                    if let Some(ref self_ty) = self.self_ty {
                        return self_ty.clone();
                    }
                }
            }

            if let Some(info) = self.env.defs.get(&def_id) {
                return info.ty.clone();
            }
            // If it's a symbol without a registered type, create an inference var.
            let var = self.unify.fresh_var();
            let ty = Ty::Infer(var);
            self.env.defs.insert(
                def_id,
                crate::env::TypeInfo { ty: ty.clone() },
            );
            ty
        } else {
            Ty::Error
        }
    }

    fn infer_binop(&mut self, op: BinOp, lhs: &Expr, rhs: &Expr, span: Span) -> Ty {
        let lhs_ty = self.infer_expr(lhs);
        let rhs_ty = self.infer_expr(rhs);

        match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                // Both sides should unify; result is the same type.
                if self.unify.unify(&lhs_ty, &rhs_ty).is_err() {
                    self.diagnostics.push(errors::type_mismatch(
                        &self.unify.resolve(&lhs_ty),
                        &self.unify.resolve(&rhs_ty),
                        self.file_name,
                        span,
                        self.source,
                    ));
                }
                self.unify.resolve(&lhs_ty)
            }
            BinOp::Eq | BinOp::NotEq | BinOp::Lt | BinOp::LtEq | BinOp::Gt | BinOp::GtEq => {
                // Both sides should unify; result is bool.
                if self.unify.unify(&lhs_ty, &rhs_ty).is_err() {
                    self.diagnostics.push(errors::type_mismatch(
                        &self.unify.resolve(&lhs_ty),
                        &self.unify.resolve(&rhs_ty),
                        self.file_name,
                        span,
                        self.source,
                    ));
                }
                Ty::Prim(PrimTy::Bool)
            }
            BinOp::And | BinOp::Or => {
                self.expect_type(&lhs_ty, &Ty::Prim(PrimTy::Bool), lhs.span);
                self.expect_type(&rhs_ty, &Ty::Prim(PrimTy::Bool), rhs.span);
                Ty::Prim(PrimTy::Bool)
            }
            BinOp::Pipe => {
                // rhs must be a function, result is rhs's return type.
                let resolved_rhs = self.unify.resolve(&rhs_ty);
                match &resolved_rhs {
                    Ty::Fn { ret, .. } => *ret.clone(),
                    Ty::Error => Ty::Error,
                    _ => {
                        self.diagnostics.push(errors::not_callable(
                            self.file_name,
                            rhs.span,
                            self.source,
                        ));
                        Ty::Error
                    }
                }
            }
        }
    }

    fn infer_unaryop(&mut self, op: UnaryOp, operand: &Expr, span: Span) -> Ty {
        let operand_ty = self.infer_expr(operand);
        match op {
            UnaryOp::Neg => {
                // Operand must be numeric; result is the same type.
                self.unify.resolve(&operand_ty)
            }
            UnaryOp::Not => {
                self.expect_type(&operand_ty, &Ty::Prim(PrimTy::Bool), span);
                Ty::Prim(PrimTy::Bool)
            }
        }
    }

    fn infer_call(&mut self, func: &Expr, args: &[CallArg], span: Span) -> Ty {
        let func_ty = self.infer_expr(func);
        let resolved_func = self.unify.resolve(&func_ty);

        match &resolved_func {
            Ty::Fn { params, ret } => {
                // For built-in variadic functions (params == [Error]), skip arg count check.
                let is_builtin_variadic =
                    params.len() == 1 && params[0] == Ty::Error;

                if !is_builtin_variadic {
                    if params.len() != args.len() {
                        self.diagnostics.push(errors::wrong_arg_count(
                            params.len(),
                            args.len(),
                            self.file_name,
                            span,
                            self.source,
                        ));
                        return *ret.clone();
                    }

                    // Unify each argument with the parameter type.
                    for (param_ty, arg) in params.iter().zip(args.iter()) {
                        let arg_ty = self.infer_expr(&arg.expr);
                        if self.unify.unify(param_ty, &arg_ty).is_err() {
                            self.diagnostics.push(errors::type_mismatch(
                                &self.unify.resolve(param_ty),
                                &self.unify.resolve(&arg_ty),
                                self.file_name,
                                arg.expr.span,
                                self.source,
                            ));
                        }
                    }

                    // Check parameter modifiers.
                    self.check_param_modifiers(func, args, span);

                    // Check effects.
                    self.check_call_effects(func, span);
                } else {
                    // Built-in: just infer arg types without checking.
                    for arg in args {
                        self.infer_expr(&arg.expr);
                    }
                }

                self.unify.resolve(ret)
            }
            Ty::Error => {
                // Poison — infer args but don't report more errors.
                for arg in args {
                    self.infer_expr(&arg.expr);
                }
                Ty::Error
            }
            _ => {
                self.diagnostics.push(errors::not_callable(
                    self.file_name,
                    func.span,
                    self.source,
                ));
                for arg in args {
                    self.infer_expr(&arg.expr);
                }
                Ty::Error
            }
        }
    }

    fn infer_field(&mut self, inner: &Expr, name: &str, span: Span) -> Ty {
        let inner_ty = self.infer_expr(inner);
        let resolved = self.unify.resolve(&inner_ty);

        // Check if the inner expression resolves to a type definition (for constructor calls)
        // vs. an instance (for method calls).
        let is_type_access = self.is_type_expr(inner);

        // Try to find a method/constructor: look up "TypeName.name" in values.
        if let Some(type_name) = self.get_type_name(&resolved, inner) {
            let key = format!("{type_name}.{name}");
            let method_sym = self.resolved.symbols.iter().find(|s| {
                s.name == key
                    && matches!(
                        s.kind,
                        SymbolKind::Method | SymbolKind::Constructor
                    )
            });
            if let Some(sym) = method_sym {
                if let Some(info) = self.env.defs.get(&sym.def_id) {
                    let method_ty = info.ty.clone();
                    // For instance method calls (not type-level), strip the self parameter.
                    if !is_type_access && sym.kind == SymbolKind::Method {
                        if let Ty::Fn { params, ret } = &method_ty {
                            if !params.is_empty() {
                                return Ty::Fn {
                                    params: params[1..].to_vec(),
                                    ret: ret.clone(),
                                };
                            }
                        }
                    }
                    return method_ty;
                }
            }
        }

        // Interface method lookup for type parameters with bounds.
        if let Ty::Param(param_def_id) = &resolved {
            if let Some(bounds) = self.env.type_param_bounds.get(param_def_id).cloned() {
                for iface_def_id in &bounds {
                    if let Some(methods) = self.env.interface_methods.get(iface_def_id).cloned() {
                        for (method_name, fn_ty) in &methods {
                            if method_name == name {
                                // Find interface's Self DefId for substitution.
                                let iface_self_def_id = self.resolved.symbols.iter()
                                    .find(|s| {
                                        s.kind == SymbolKind::TypeParam
                                            && s.name == "Self"
                                            && {
                                                let iface_sym = self.resolved.symbols.iter()
                                                    .find(|is| is.def_id == *iface_def_id);
                                                if let Some(is) = iface_sym {
                                                    s.span.start >= is.span.start && s.span.end <= is.span.end
                                                } else { false }
                                            }
                                    })
                                    .map(|s| s.def_id);

                                // Build substitution: interface Self → receiver Ty::Param.
                                let mut subst_map = HashMap::new();
                                if let Some(self_did) = iface_self_def_id {
                                    subst_map.insert(self_did, resolved.clone());
                                }

                                // Substitute interface type params with bound type args.
                                // e.g. for T: Iterator[i64], substitute Iterator's type param with i64.
                                if let Some(bound_args) = self.env.interface_bound_type_args.get(&(*param_def_id, *iface_def_id)).cloned() {
                                    let iface_sym = self.resolved.symbols.iter()
                                        .find(|s| s.def_id == *iface_def_id);
                                    if let Some(is) = iface_sym {
                                        let iface_type_params: Vec<_> = self.resolved.symbols.iter()
                                            .filter(|s| {
                                                s.kind == SymbolKind::TypeParam
                                                    && s.name != "Self"
                                                    && s.span.start >= is.span.start
                                                    && s.span.end <= is.span.end
                                            })
                                            .collect();
                                        for (tp, arg) in iface_type_params.iter().zip(bound_args.iter()) {
                                            subst_map.insert(tp.def_id, arg.clone());
                                        }
                                    }
                                }

                                // Substitute and strip self parameter.
                                let substituted = substitute(fn_ty, &subst_map);
                                if let Ty::Fn { params, ret } = &substituted {
                                    if !params.is_empty() {
                                        return Ty::Fn {
                                            params: params[1..].to_vec(),
                                            ret: ret.clone(),
                                        };
                                    }
                                }
                                return substituted;
                            }
                        }
                    }
                }
            }
        }

        // Check for enum variant access: e.g. Shape.Circle or Option[i64].Some
        if is_type_access {
            if let Ty::Enum { def_id, type_args } = &resolved {
                if let Some(variants) = self.env.enum_variants.get(def_id).cloned() {
                    if let Some((idx, (_, _, variant_fields))) = variants
                        .iter()
                        .enumerate()
                        .find(|(_, (vname, _, _))| vname == name)
                    {
                        self.field_resolutions.insert(span.start, idx);

                        // Build substitution map from enum type params to type args.
                        let subst = if !type_args.is_empty() {
                            let parent_sym = self.resolved.symbols.iter().find(|s| s.def_id == *def_id);
                            let param_ids: Vec<DefId> = if let Some(ps) = parent_sym {
                                self.resolved.symbols.iter()
                                    .filter(|s| {
                                        s.kind == SymbolKind::TypeParam
                                            && s.name != "Self"
                                            && s.span.start >= ps.span.start
                                            && s.span.end <= ps.span.end
                                    })
                                    .map(|s| s.def_id)
                                    .collect()
                            } else {
                                vec![]
                            };
                            let mut m = HashMap::new();
                            for (pid, arg) in param_ids.iter().zip(type_args.iter()) {
                                m.insert(*pid, arg.clone());
                            }
                            m
                        } else {
                            HashMap::new()
                        };

                        if variant_fields.is_empty() {
                            // Unit variant: return the enum type directly.
                            return resolved.clone();
                        } else {
                            // Data variant: return a constructor Fn type with substituted params.
                            let param_tys: Vec<Ty> = variant_fields.iter().map(|(_, ty)| {
                                if subst.is_empty() { ty.clone() } else { substitute(ty, &subst) }
                            }).collect();
                            return Ty::Fn {
                                params: param_tys,
                                ret: Box::new(resolved.clone()),
                            };
                        }
                    }
                }
            }
        }

        // Otherwise, try struct field access.
        match &resolved {
            Ty::Struct { def_id, type_args } => {
                if let Some(fields) = self.env.struct_fields.get(def_id) {
                    // Build substitution map from type params to type_args.
                    let subst = if !type_args.is_empty() {
                        let parent_sym = self
                            .resolved
                            .symbols
                            .iter()
                            .find(|s| s.def_id == *def_id);
                        let param_ids: Vec<DefId> = if let Some(ps) = parent_sym {
                            self.resolved
                                .symbols
                                .iter()
                                .filter(|s| {
                                    s.kind == SymbolKind::TypeParam
                                        && s.name != "Self"
                                        && s.span.start >= ps.span.start
                                        && s.span.end <= ps.span.end
                                })
                                .map(|s| s.def_id)
                                .collect()
                        } else {
                            vec![]
                        };
                        let mut m = HashMap::new();
                        for (pid, arg) in param_ids.iter().zip(type_args.iter()) {
                            m.insert(*pid, arg.clone());
                        }
                        m
                    } else {
                        HashMap::new()
                    };
                    for (i, (field_name, field_ty)) in fields.iter().enumerate() {
                        if field_name == name {
                            self.field_resolutions.insert(span.start, i);
                            let result_ty = if subst.is_empty() {
                                field_ty.clone()
                            } else {
                                substitute(field_ty, &subst)
                            };
                            return result_ty;
                        }
                    }
                }
                self.diagnostics.push(errors::no_such_field(
                    &resolved,
                    name,
                    self.file_name,
                    span,
                    self.source,
                ));
                Ty::Error
            }
            Ty::Tuple(elems) => {
                // Tuple field access by index (e.g. t.0, t.1)
                if let Ok(idx) = name.parse::<usize>() {
                    if idx < elems.len() {
                        self.field_resolutions.insert(span.start, idx);
                        return elems[idx].clone();
                    }
                }
                self.diagnostics.push(errors::no_such_field(
                    &resolved,
                    name,
                    self.file_name,
                    span,
                    self.source,
                ));
                Ty::Error
            }
            Ty::Error => Ty::Error,
            _ => {
                self.diagnostics.push(errors::no_such_field(
                    &resolved,
                    name,
                    self.file_name,
                    span,
                    self.source,
                ));
                Ty::Error
            }
        }
    }

    /// Get the type name for method/constructor lookups.
    fn get_type_name(&self, ty: &Ty, expr: &Expr) -> Option<String> {
        match ty {
            Ty::Struct { def_id, .. } => {
                self.resolved
                    .symbols
                    .iter()
                    .find(|s| s.def_id == *def_id)
                    .map(|s| s.name.clone())
            }
            Ty::Enum { def_id, .. } => {
                self.resolved
                    .symbols
                    .iter()
                    .find(|s| s.def_id == *def_id)
                    .map(|s| s.name.clone())
            }
            _ => {
                // The inner expression might be an Ident that refers to a type name.
                // E.g., `Point.origin()` where `Point` resolves to the Struct DefId.
                if let ExprKind::Ident(name) = &expr.kind {
                    if let Some(&def_id) = self.resolved.resolutions.get(&expr.span.start) {
                        let sym = self.resolved.symbols.iter().find(|s| s.def_id == def_id);
                        if let Some(sym) = sym {
                            if matches!(sym.kind, SymbolKind::Struct | SymbolKind::Enum) {
                                return Some(name.clone());
                            }
                        }
                    }
                }
                None
            }
        }
    }

    /// Check if an expression refers to a type definition (not an instance).
    fn is_type_expr(&self, expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::Ident(_) => {
                if let Some(&def_id) = self.resolved.resolutions.get(&expr.span.start) {
                    let sym = self.resolved.symbols.iter().find(|s| s.def_id == def_id);
                    if let Some(sym) = sym {
                        return matches!(
                            sym.kind,
                            SymbolKind::Struct | SymbolKind::Enum | SymbolKind::Interface
                        );
                    }
                }
                false
            }
            ExprKind::TypeApp { expr: inner, .. } => self.is_type_expr(inner),
            _ => false,
        }
    }

    /// Resolve a DefId that might be `Self` (TypeParam with parent) to the actual struct DefId.
    /// Returns (actual_def_id, is_struct).
    fn resolve_struct_def_id(&self, def_id: DefId) -> (DefId, bool) {
        let sym = self.resolved.symbols.iter().find(|s| s.def_id == def_id);
        if let Some(sym) = sym {
            match sym.kind {
                SymbolKind::Struct => (def_id, true),
                SymbolKind::TypeParam => {
                    // Self → struct: check parent
                    if let Some(parent_id) = sym.parent {
                        let parent = self.resolved.symbols.iter().find(|s| s.def_id == parent_id);
                        if let Some(p) = parent {
                            if p.kind == SymbolKind::Struct {
                                return (parent_id, true);
                            }
                        }
                    }
                    (def_id, false)
                }
                _ => (def_id, false),
            }
        } else {
            // Symbol not in local module — check TypeEnv for imported types.
            if let Some(info) = self.env.defs.get(&def_id) {
                if matches!(info.ty, Ty::Struct { .. }) {
                    return (def_id, true);
                }
            }
            (def_id, false)
        }
    }

    fn infer_if(
        &mut self,
        cond: &Expr,
        then_branch: &[Stmt],
        else_branch: Option<&[Stmt]>,
        span: Span,
    ) -> Ty {
        let cond_ty = self.infer_expr(cond);
        self.expect_type(&cond_ty, &Ty::Prim(PrimTy::Bool), cond.span);

        let then_ty = self.infer_block_ty(then_branch);

        if let Some(else_stmts) = else_branch {
            let else_ty = self.infer_block_ty(else_stmts);
            if self.unify.unify(&then_ty, &else_ty).is_err() {
                self.diagnostics.push(errors::type_mismatch(
                    &self.unify.resolve(&then_ty),
                    &self.unify.resolve(&else_ty),
                    self.file_name,
                    span,
                    self.source,
                ));
            }
            self.unify.resolve(&then_ty)
        } else {
            Ty::Unit
        }
    }

    fn infer_while(&mut self, cond: &Expr, body: &[Stmt]) -> Ty {
        let cond_ty = self.infer_expr(cond);
        self.expect_type(&cond_ty, &Ty::Prim(PrimTy::Bool), cond.span);
        self.infer_stmts(body);
        Ty::Unit
    }

    fn infer_match(&mut self, scrutinee: &Expr, arms: &[MatchArm], _span: Span) -> Ty {
        let scrutinee_ty = self.infer_expr(scrutinee);

        // Infer all arm body types and unify them.
        let mut result_ty: Option<Ty> = None;
        for arm in arms {
            // Type-check the pattern against the scrutinee type.
            self.infer_pattern_bindings(&arm.pattern, &scrutinee_ty);

            // Infer guard if present.
            if let Some(guard) = &arm.guard {
                let guard_ty = self.infer_expr(guard);
                self.expect_type(&guard_ty, &Ty::Prim(PrimTy::Bool), guard.span);
            }

            let arm_ty = self.infer_block_ty(&arm.body);
            if let Some(ref prev) = result_ty {
                if self.unify.unify(prev, &arm_ty).is_err() {
                    self.diagnostics.push(errors::type_mismatch(
                        &self.unify.resolve(prev),
                        &self.unify.resolve(&arm_ty),
                        self.file_name,
                        arm.span,
                        self.source,
                    ));
                }
            } else {
                result_ty = Some(arm_ty);
            }
        }

        result_ty
            .map(|t| self.unify.resolve(&t))
            .unwrap_or(Ty::Unit)
    }

    fn infer_tuple_lit(&mut self, elems: &[Expr]) -> Ty {
        if elems.is_empty() {
            Ty::Unit
        } else {
            let elem_tys: Vec<Ty> = elems.iter().map(|e| self.infer_expr(e)).collect();
            Ty::Tuple(elem_tys)
        }
    }

    fn infer_array_lit(&mut self, elems: &[Expr]) -> Ty {
        if elems.is_empty() {
            return Ty::Array {
                elem: Box::new(Ty::Error),
                len: 0,
            };
        }
        let first_ty = self.infer_expr(&elems[0]);
        for elem in &elems[1..] {
            let elem_ty = self.infer_expr(elem);
            if self.unify.unify(&first_ty, &elem_ty).is_err() {
                self.diagnostics.push(errors::type_mismatch(
                    &self.unify.resolve(&first_ty),
                    &self.unify.resolve(&elem_ty),
                    self.file_name,
                    elem.span,
                    self.source,
                ));
            }
        }
        Ty::Array {
            elem: Box::new(self.unify.resolve(&first_ty)),
            len: elems.len() as u64,
        }
    }

    fn infer_index(&mut self, arr_expr: &Expr, index: &Expr, span: Span) -> Ty {
        let arr_ty = self.infer_expr(arr_expr);
        let index_ty = self.infer_expr(index);
        let resolved_arr = self.unify.resolve(&arr_ty);

        // Check that index is an integer type.
        match &index_ty {
            Ty::Prim(p) if p.is_integer() => {}
            Ty::Infer(_) => {
                // Default to i64.
                let _ = self.unify.unify(&index_ty, &Ty::Prim(PrimTy::I64));
            }
            Ty::Error => {}
            _ => {
                self.diagnostics.push(errors::type_mismatch(
                    &Ty::Prim(PrimTy::I64),
                    &self.unify.resolve(&index_ty),
                    self.file_name,
                    index.span,
                    self.source,
                ));
            }
        }

        match &resolved_arr {
            Ty::Array { elem, .. } => *elem.clone(),
            Ty::Error => Ty::Error,
            _ => {
                self.diagnostics.push(errors::type_mismatch(
                    &Ty::Error,
                    &resolved_arr,
                    self.file_name,
                    span,
                    self.source,
                ));
                Ty::Error
            }
        }
    }

    fn infer_struct_lit(&mut self, name: &str, fields: &[FieldInit], span: Span) -> Ty {
        // Find the struct type via resolution.
        if let Some(&resolved_def_id) = self.resolved.resolutions.get(&span.start) {
            // Resolve to the actual struct DefId (handle Self → struct parent).
            let (def_id, is_struct) = self.resolve_struct_def_id(resolved_def_id);

            if !is_struct {
                self.diagnostics.push(errors::not_a_struct(
                    name,
                    self.file_name,
                    span,
                    self.source,
                ));
                return Ty::Error;
            }

            // Find type parameters for this struct and create fresh Infer vars.
            let parent_sym = self
                .resolved
                .symbols
                .iter()
                .find(|s| s.def_id == def_id);
            let type_param_defs: Vec<DefId> = if let Some(ps) = parent_sym {
                self.resolved
                    .symbols
                    .iter()
                    .filter(|s| {
                        s.kind == SymbolKind::TypeParam
                            && s.name != "Self"
                            && s.span.start >= ps.span.start
                            && s.span.end <= ps.span.end
                    })
                    .map(|s| s.def_id)
                    .collect()
            } else {
                vec![]
            };

            // Build substitution: Param(def_id) -> Infer(fresh_var) for each type param.
            let mut subst: HashMap<DefId, Ty> = HashMap::new();
            let mut infer_vars = Vec::new();
            for &param_def_id in &type_param_defs {
                let var = self.unify.fresh_var();
                infer_vars.push(Ty::Infer(var));
                subst.insert(param_def_id, Ty::Infer(var));
            }

            // Check fields.
            if let Some(expected_fields) = self.env.struct_fields.get(&def_id).cloned() {
                // Check for extra fields.
                for init in fields {
                    let found = expected_fields.iter().any(|(n, _)| n == &init.name);
                    if !found {
                        self.diagnostics.push(errors::extra_field(
                            &init.name,
                            self.file_name,
                            init.span,
                            self.source,
                        ));
                    }
                }

                // Check for missing fields.
                for (field_name, _) in &expected_fields {
                    let provided = fields.iter().any(|f| &f.name == field_name);
                    if !provided {
                        self.diagnostics.push(errors::missing_field(
                            field_name,
                            self.file_name,
                            span,
                            self.source,
                        ));
                    }
                }

                // Type-check provided fields, substituting type params with Infer vars.
                for init in fields {
                    let init_ty = self.infer_expr(&init.value);
                    if let Some((_, expected_ty)) =
                        expected_fields.iter().find(|(n, _)| n == &init.name)
                    {
                        let instantiated = if subst.is_empty() {
                            expected_ty.clone()
                        } else {
                            substitute(expected_ty, &subst)
                        };
                        if self.unify.unify(&instantiated, &init_ty).is_err() {
                            self.diagnostics.push(errors::type_mismatch(
                                &self.unify.resolve(&instantiated),
                                &self.unify.resolve(&init_ty),
                                self.file_name,
                                init.span,
                                self.source,
                            ));
                        }
                    }
                }
            } else {
                // No field info — just infer field expressions.
                for init in fields {
                    self.infer_expr(&init.value);
                }
            }

            // Resolve infer vars to get concrete type_args.
            let type_args: Vec<Ty> = infer_vars
                .iter()
                .map(|v| self.unify.resolve(v))
                .collect();

            Ty::Struct {
                def_id,
                type_args,
            }
        } else {
            // Unresolved struct name — infer field exprs to avoid cascading.
            for init in fields {
                self.infer_expr(&init.value);
            }
            Ty::Error
        }
    }

    fn infer_for(&mut self, _pattern: &Pattern, iter: &Expr, body: &[Stmt]) -> Ty {
        self.infer_expr(iter);
        self.infer_stmts(body);
        Ty::Unit
    }

    fn infer_range(&mut self, start: &Expr, end: &Expr, span: Span) -> Ty {
        let start_ty = self.infer_expr(start);
        let end_ty = self.infer_expr(end);
        if self.unify.unify(&start_ty, &end_ty).is_err() {
            self.diagnostics.push(errors::type_mismatch(
                &self.unify.resolve(&start_ty),
                &self.unify.resolve(&end_ty),
                self.file_name,
                span,
                self.source,
            ));
        }
        // Range type itself is deferred; return Error for now.
        Ty::Error
    }

    fn infer_closure(&mut self, params: &[ClosureParam], body: &[Stmt]) -> Ty {
        let mut param_tys = Vec::new();
        for param in params {
            let ty = if let Some(te) = &param.ty {
                lower_type_expr(te, &self.resolved.symbols, &self.resolved.resolutions)
            } else {
                let var = self.unify.fresh_var();
                Ty::Infer(var)
            };

            // Register closure param in env if resolved.
            if let Some(&def_id) = self.resolved.resolutions.get(&param.span.start) {
                self.env.defs.insert(def_id, crate::env::TypeInfo { ty: ty.clone() });
            }

            param_tys.push(ty);
        }

        let body_ty = self.infer_block_ty(body);

        Ty::Fn {
            params: param_tys,
            ret: Box::new(body_ty),
        }
    }

    fn infer_type_app(&mut self, inner: &Expr, type_args: &[TypeExpr], _span: Span) -> Ty {
        let base_ty = self.infer_expr(inner);
        let resolved_base = self.unify.resolve(&base_ty);

        // Lower type arguments.
        let ty_args: Vec<Ty> = type_args
            .iter()
            .map(|ta| lower_type_expr(ta, &self.resolved.symbols, &self.resolved.resolutions))
            .collect();

        match &resolved_base {
            Ty::Fn { params, ret } => {
                // Generic function instantiation:
                // Find the function's type parameter DefIds by looking at the function's
                // symbol span and finding TypeParam symbols registered within that span.
                if let Some(&def_id) = self.resolved.resolutions.get(&inner.span.start) {
                    let fn_sym = self.resolved.symbols.iter().find(|s| s.def_id == def_id);
                    if let Some(fn_sym) = fn_sym {
                        // Find TypeParam symbols whose span is within the function's span.
                        // These are the function's own type parameters.
                        let fn_span = fn_sym.span;
                        let type_param_defs: Vec<DefId> = self
                            .resolved
                            .symbols
                            .iter()
                            .filter(|s| {
                                s.kind == SymbolKind::TypeParam
                                    && s.name != "Self"
                                    && s.span.start >= fn_span.start
                                    && s.span.end <= fn_span.end
                            })
                            .map(|s| s.def_id)
                            .collect();

                        if !type_param_defs.is_empty() && type_param_defs.len() == ty_args.len() {
                            // Build substitution map: type_param DefId → concrete Ty
                            let mut subst: HashMap<DefId, Ty> = HashMap::new();
                            for (param_def_id, arg_ty) in
                                type_param_defs.iter().zip(ty_args.iter())
                            {
                                subst.insert(*param_def_id, arg_ty.clone());
                            }

                            // Check interface bounds for each type parameter.
                            for (param_def_id, arg_ty) in
                                type_param_defs.iter().zip(ty_args.iter())
                            {
                                self.check_interface_bounds(
                                    *param_def_id,
                                    arg_ty,
                                    _span,
                                );
                            }

                            // Apply substitution to the function type.
                            let new_params: Vec<Ty> =
                                params.iter().map(|p| substitute(p, &subst)).collect();
                            let new_ret = substitute(ret, &subst);

                            return Ty::Fn {
                                params: new_params,
                                ret: Box::new(new_ret),
                            };
                        }
                    }
                }

                // If we can't find type params, just return the original fn type.
                resolved_base
            }
            Ty::Enum { def_id, .. } => Ty::Enum {
                def_id: *def_id,
                type_args: ty_args,
            },
            Ty::Struct { def_id, .. } => Ty::Struct {
                def_id: *def_id,
                type_args: ty_args,
            },
            Ty::Error => Ty::Error,
            _ => resolved_base,
        }
    }

    fn infer_block(&mut self, stmts: &[Stmt]) -> Ty {
        self.infer_block_ty(stmts)
    }

    /// Infer the type of a block (list of statements).
    /// The type is the type of the last expression statement, or Unit.
    pub fn infer_block_ty(&mut self, stmts: &[Stmt]) -> Ty {
        let mut last_ty = Ty::Unit;
        for stmt in stmts {
            last_ty = self.infer_stmt(stmt);
        }
        last_ty
    }

    /// Infer/check a single statement. Returns the type of the statement
    /// (meaningful for expression statements).
    pub fn infer_stmt(&mut self, stmt: &Stmt) -> Ty {
        match &stmt.kind {
            StmtKind::Let {
                ty,
                value,
                ..
            } => {
                let val_ty = self.infer_expr(value);

                if let Some(te) = ty {
                    let ann_ty = lower_type_expr(
                        te,
                        &self.resolved.symbols,
                        &self.resolved.resolutions,
                    );
                    if self.unify.unify(&ann_ty, &val_ty).is_err() {
                        self.diagnostics.push(errors::type_mismatch(
                            &self.unify.resolve(&ann_ty),
                            &self.unify.resolve(&val_ty),
                            self.file_name,
                            stmt.span,
                            self.source,
                        ));
                    }
                    // Register the variable with the annotated type.
                    self.register_local_var(stmt.span.start, &self.unify.resolve(&ann_ty).clone());
                } else {
                    // Register with the inferred type.
                    self.register_local_var(stmt.span.start, &self.unify.resolve(&val_ty).clone());
                }

                Ty::Unit
            }

            StmtKind::LetPattern {
                pattern,
                ty,
                value,
                ..
            } => {
                let val_ty = self.infer_expr(value);

                if let Some(te) = ty {
                    let ann_ty = lower_type_expr(
                        te,
                        &self.resolved.symbols,
                        &self.resolved.resolutions,
                    );
                    if self.unify.unify(&ann_ty, &val_ty).is_err() {
                        self.diagnostics.push(errors::type_mismatch(
                            &self.unify.resolve(&ann_ty),
                            &self.unify.resolve(&val_ty),
                            self.file_name,
                            stmt.span,
                            self.source,
                        ));
                    }
                }

                // Distribute types to pattern bindings (simplified).
                self.infer_pattern_bindings(pattern, &val_ty);

                Ty::Unit
            }

            StmtKind::Assign { target, value } => {
                let target_ty = self.infer_expr(target);
                let value_ty = self.infer_expr(value);
                if self.unify.unify(&target_ty, &value_ty).is_err() {
                    self.diagnostics.push(errors::type_mismatch(
                        &self.unify.resolve(&target_ty),
                        &self.unify.resolve(&value_ty),
                        self.file_name,
                        stmt.span,
                        self.source,
                    ));
                }
                Ty::Unit
            }

            StmtKind::Expr(expr) => self.infer_expr(expr),

            StmtKind::Return(opt_expr) => {
                let ret_ty = if let Some(expr) = opt_expr {
                    self.infer_expr(expr)
                } else {
                    Ty::Unit
                };
                let expected = self.current_return_ty.clone();
                if self.unify.unify(&expected, &ret_ty).is_err() {
                    self.diagnostics.push(errors::return_type_mismatch(
                        &self.unify.resolve(&expected),
                        &self.unify.resolve(&ret_ty),
                        self.file_name,
                        stmt.span,
                        self.source,
                    ));
                }
                Ty::Prim(PrimTy::Never)
            }

            StmtKind::Break(opt_expr) => {
                if let Some(expr) = opt_expr {
                    self.infer_expr(expr);
                }
                Ty::Prim(PrimTy::Never)
            }

            StmtKind::Continue => Ty::Prim(PrimTy::Never),

            StmtKind::Assert { cond, message } => {
                let cond_ty = self.infer_expr(cond);
                self.expect_type(&cond_ty, &Ty::Prim(PrimTy::Bool), cond.span);
                if let Some(msg) = message {
                    self.infer_expr(msg);
                }
                Ty::Unit
            }
        }
    }

    /// Register a local variable's type by finding its DefId via the let statement span.
    fn register_local_var(&mut self, let_span_start: u32, ty: &Ty) {
        // The resolver records let variable DefIds; look up all LocalVar symbols
        // whose span overlaps with the let statement.
        // A simpler approach: find the DefId for a LocalVar symbol registered in the let stmt area.
        // We use the resolution map: for Let stmts, the variable name's span start maps to its DefId.
        // But the resolution records the ident reference, not the binding.
        // Instead, we search symbols for LocalVar symbols that overlap this let span.
        for sym in &self.resolved.symbols {
            if sym.kind == SymbolKind::LocalVar && sym.span.start >= let_span_start {
                // Only register if not already registered with a non-infer type.
                if !self.env.defs.contains_key(&sym.def_id) {
                    self.env.defs.insert(
                        sym.def_id,
                        crate::env::TypeInfo { ty: ty.clone() },
                    );
                    return;
                } else {
                    // Update if currently Infer.
                    let existing = &self.env.defs[&sym.def_id].ty;
                    if matches!(existing, Ty::Infer(_)) {
                        self.env.defs.insert(
                            sym.def_id,
                            crate::env::TypeInfo { ty: ty.clone() },
                        );
                    }
                    return;
                }
            }
        }
    }

    /// Distribute types to pattern bindings.
    fn infer_pattern_bindings(&mut self, pattern: &Pattern, ty: &Ty) {
        let resolved_ty = self.unify.resolve(ty);
        match &pattern.kind {
            PatternKind::Ident(_) => {
                if let Some(&def_id) = self.resolved.resolutions.get(&pattern.span.start) {
                    self.env.defs.insert(
                        def_id,
                        crate::env::TypeInfo { ty: resolved_ty.clone() },
                    );
                }
            }
            PatternKind::TuplePattern(pats) => {
                if let Ty::Tuple(elems) = &resolved_ty {
                    for (p, elem_ty) in pats.iter().zip(elems.iter()) {
                        self.infer_pattern_bindings(p, elem_ty);
                    }
                } else if !matches!(resolved_ty, Ty::Error | Ty::Infer(_)) {
                    self.diagnostics.push(errors::pattern_mismatch(
                        &resolved_ty,
                        self.file_name,
                        pattern.span,
                        self.source,
                    ));
                }
            }
            PatternKind::Wildcard => {}
            PatternKind::Constructor { path, type_args: _, fields } => {
                self.infer_constructor_pattern(path, fields, &resolved_ty, pattern.span);
            }
            PatternKind::Struct { name, fields, .. } => {
                self.infer_struct_pattern(name, fields, &resolved_ty, pattern.span);
            }
            PatternKind::Literal(expr) => {
                let lit_ty = self.infer_expr(expr);
                if self.unify.unify(&resolved_ty, &lit_ty).is_err() {
                    self.diagnostics.push(errors::pattern_mismatch(
                        &resolved_ty,
                        self.file_name,
                        pattern.span,
                        self.source,
                    ));
                }
            }
            PatternKind::Or(pats) => {
                for p in pats {
                    self.infer_pattern_bindings(p, &resolved_ty);
                }
            }
            PatternKind::List(pats) => {
                if let Ty::Slice(elem_ty) = &resolved_ty {
                    for p in pats {
                        if !matches!(p.kind, PatternKind::Rest(_)) {
                            self.infer_pattern_bindings(p, elem_ty);
                        } else if let PatternKind::Rest(Some(_)) = &p.kind {
                            // Named rest binds to the slice type.
                            self.infer_pattern_bindings(p, &resolved_ty);
                        }
                    }
                } else if !matches!(resolved_ty, Ty::Error | Ty::Infer(_)) {
                    self.diagnostics.push(errors::pattern_mismatch(
                        &resolved_ty,
                        self.file_name,
                        pattern.span,
                        self.source,
                    ));
                }
            }
            PatternKind::Rest(opt_name) => {
                if opt_name.is_some() {
                    if let Some(&def_id) = self.resolved.resolutions.get(&pattern.span.start) {
                        self.env.defs.insert(
                            def_id,
                            crate::env::TypeInfo { ty: resolved_ty.clone() },
                        );
                    }
                }
            }
        }
    }

    /// Type-check a Constructor pattern (e.g. `Shape.Circle(r)`).
    fn infer_constructor_pattern(
        &mut self,
        path: &[String],
        fields: &[Pattern],
        scrutinee_ty: &Ty,
        span: Span,
    ) {
        // path is e.g. ["Shape", "Circle"] — first element is enum name, last is variant name.
        if path.len() < 2 {
            return;
        }
        let variant_name = &path[path.len() - 1];

        // Try to find the enum DefId from the scrutinee type or from the path.
        let enum_def_id = match scrutinee_ty {
            Ty::Enum { def_id, .. } => Some(*def_id),
            _ => {
                // Try to find enum by name from the first path element.
                let enum_name = &path[0];
                self.resolved
                    .symbols
                    .iter()
                    .find(|s| &s.name == enum_name && s.kind == SymbolKind::Enum)
                    .map(|s| s.def_id)
            }
        };

        if let Some(enum_def_id) = enum_def_id {
            // Unify scrutinee with the enum type (preserve type args from scrutinee).
            let scrutinee_type_args = match scrutinee_ty {
                Ty::Enum { type_args, .. } => type_args.clone(),
                _ => vec![],
            };
            let enum_ty = Ty::Enum {
                def_id: enum_def_id,
                type_args: scrutinee_type_args.clone(),
            };
            if self.unify.unify(scrutinee_ty, &enum_ty).is_err() {
                self.diagnostics.push(errors::pattern_mismatch(
                    scrutinee_ty,
                    self.file_name,
                    span,
                    self.source,
                ));
                return;
            }

            // Build substitution map from enum type params to concrete type args.
            let subst = if !scrutinee_type_args.is_empty() {
                let parent_sym = self.resolved.symbols.iter().find(|s| s.def_id == enum_def_id);
                let param_ids: Vec<DefId> = if let Some(ps) = parent_sym {
                    self.resolved.symbols.iter()
                        .filter(|s| {
                            s.kind == SymbolKind::TypeParam
                                && s.name != "Self"
                                && s.span.start >= ps.span.start
                                && s.span.end <= ps.span.end
                        })
                        .map(|s| s.def_id)
                        .collect()
                } else {
                    vec![]
                };
                let mut m = HashMap::new();
                for (pid, arg) in param_ids.iter().zip(scrutinee_type_args.iter()) {
                    m.insert(*pid, arg.clone());
                }
                m
            } else {
                HashMap::new()
            };

            // Look up variant fields.
            if let Some(variants) = self.env.enum_variants.get(&enum_def_id).cloned() {
                if let Some((_, _, variant_fields)) =
                    variants.iter().find(|(name, _, _)| name == variant_name)
                {
                    // Distribute field types to sub-patterns (with substitution).
                    for (pat, (_field_name, field_ty)) in fields.iter().zip(variant_fields.iter()) {
                        let resolved_field_ty = if subst.is_empty() {
                            field_ty.clone()
                        } else {
                            substitute(field_ty, &subst)
                        };
                        self.infer_pattern_bindings(pat, &resolved_field_ty);
                    }
                } else {
                    self.diagnostics.push(errors::pattern_mismatch(
                        scrutinee_ty,
                        self.file_name,
                        span,
                        self.source,
                    ));
                }
            }
        } else {
            self.diagnostics.push(errors::pattern_mismatch(
                scrutinee_ty,
                self.file_name,
                span,
                self.source,
            ));
        }
    }

    /// Type-check a Struct pattern (e.g. `Point #{x, y}`).
    fn infer_struct_pattern(
        &mut self,
        name: &str,
        fields: &[FieldPattern],
        scrutinee_ty: &Ty,
        span: Span,
    ) {
        // Find the struct DefId.
        let struct_def_id = match scrutinee_ty {
            Ty::Struct { def_id, .. } => Some(*def_id),
            _ => {
                self.resolved
                    .symbols
                    .iter()
                    .find(|s| s.name == name && s.kind == SymbolKind::Struct)
                    .map(|s| s.def_id)
            }
        };

        if let Some(struct_def_id) = struct_def_id {
            // Unify scrutinee with the struct type.
            let struct_ty = Ty::Struct {
                def_id: struct_def_id,
                type_args: vec![],
            };
            if self.unify.unify(scrutinee_ty, &struct_ty).is_err() {
                self.diagnostics.push(errors::pattern_mismatch(
                    scrutinee_ty,
                    self.file_name,
                    span,
                    self.source,
                ));
                return;
            }

            // Look up struct fields and bind sub-patterns.
            if let Some(struct_fields) = self.env.struct_fields.get(&struct_def_id).cloned() {
                for fp in fields {
                    if let Some((_, field_ty)) =
                        struct_fields.iter().find(|(n, _)| n == &fp.name)
                    {
                        if let Some(ref sub_pat) = fp.pattern {
                            self.infer_pattern_bindings(sub_pat, field_ty);
                        } else {
                            // Shorthand: `#{name}` binds `name` to the field type.
                            if let Some(&def_id) =
                                self.resolved.resolutions.get(&fp.span.start)
                            {
                                self.env.defs.insert(
                                    def_id,
                                    crate::env::TypeInfo {
                                        ty: field_ty.clone(),
                                    },
                                );
                            }
                        }
                    }
                }
            }
        } else {
            self.diagnostics.push(errors::pattern_mismatch(
                scrutinee_ty,
                self.file_name,
                span,
                self.source,
            ));
        }
    }

    /// Check interface bounds for a type parameter's concrete type argument.
    fn check_interface_bounds(
        &mut self,
        param_def_id: DefId,
        concrete_ty: &Ty,
        span: Span,
    ) {
        let bounds = match self.env.type_param_bounds.get(&param_def_id) {
            Some(b) => b.clone(),
            None => return,
        };

        for iface_def_id in &bounds {
            let iface_name = self
                .resolved
                .symbols
                .iter()
                .find(|s| s.def_id == *iface_def_id)
                .map(|s| s.name.clone())
                .unwrap_or_else(|| "?".to_string());

            let required_methods = match self.env.interface_methods.get(iface_def_id) {
                Some(m) => m.clone(),
                None => continue,
            };

            // For each required method, check that the concrete type has it.
            for (method_name, _expected_fn_ty) in &required_methods {
                let type_name = self.get_concrete_type_name(concrete_ty);
                if let Some(ref type_name) = type_name {
                    let key = format!("{type_name}.{method_name}");
                    let has_method = self.resolved.symbols.iter().any(|s| {
                        s.name == key
                            && matches!(s.kind, SymbolKind::Method | SymbolKind::Constructor)
                    });
                    if !has_method {
                        self.diagnostics.push(errors::missing_method(
                            concrete_ty,
                            method_name,
                            &iface_name,
                            self.file_name,
                            span,
                            self.source,
                        ));
                        return;
                    }
                } else {
                    // Can't determine type name — report unsatisfied bound.
                    self.diagnostics.push(errors::unsatisfied_bound(
                        concrete_ty,
                        &iface_name,
                        self.file_name,
                        span,
                        self.source,
                    ));
                    return;
                }
            }
        }
    }

    /// Get the type name for a concrete type (for method lookup).
    fn get_concrete_type_name(&self, ty: &Ty) -> Option<String> {
        match ty {
            Ty::Struct { def_id, .. } | Ty::Enum { def_id, .. } => {
                self.resolved
                    .symbols
                    .iter()
                    .find(|s| s.def_id == *def_id)
                    .map(|s| s.name.clone())
            }
            _ => None,
        }
    }

    /// Check parameter modifiers match between call-site and definition.
    fn check_param_modifiers(&mut self, func: &Expr, args: &[CallArg], span: Span) {
        // Resolve the function's DefId.
        let fn_def_id = self.resolve_call_target(func);
        let Some(fn_def_id) = fn_def_id else { return };

        let expected_modifiers = match self.env.param_modifiers.get(&fn_def_id) {
            Some(m) => m.clone(),
            None => return,
        };

        for (i, arg) in args.iter().enumerate() {
            if let Some(expected) = expected_modifiers.get(i) {
                if &arg.modifier != expected {
                    let expected_str = modifier_to_str(expected);
                    let found_str = modifier_to_str(&arg.modifier);
                    self.diagnostics.push(errors::modifier_mismatch(
                        expected_str,
                        found_str,
                        self.file_name,
                        span,
                        self.source,
                    ));
                }
            }
        }
    }

    /// Resolve the DefId of the function being called.
    fn resolve_call_target(&self, func: &Expr) -> Option<DefId> {
        match &func.kind {
            ExprKind::Ident(_) => {
                self.resolved.resolutions.get(&func.span.start).copied()
            }
            ExprKind::Field { expr: inner, name, .. } => {
                // Method/constructor call: look up "TypeName.methodName".
                let inner_ty = self.expr_types.get(&inner.span.start);
                if let Some(inner_ty) = inner_ty {
                    if let Some(type_name) = self.get_concrete_type_name(inner_ty) {
                        let key = format!("{type_name}.{name}");
                        return self.resolved.symbols.iter().find(|s| {
                            s.name == key
                                && matches!(
                                    s.kind,
                                    SymbolKind::Method | SymbolKind::Constructor
                                )
                        }).map(|s| s.def_id);
                    }
                }
                // Also check if inner is a type identifier.
                if let ExprKind::Ident(type_name) = &inner.kind {
                    let key = format!("{type_name}.{name}");
                    return self.resolved.symbols.iter().find(|s| {
                        s.name == key
                            && matches!(
                                s.kind,
                                SymbolKind::Method | SymbolKind::Constructor
                            )
                    }).map(|s| s.def_id);
                }
                None
            }
            ExprKind::TypeApp { expr: inner, .. } => {
                // Generic instantiation: the target is the inner expression.
                self.resolve_call_target(inner)
            }
            _ => None,
        }
    }

    /// Check that effects on the called function are handled or declared.
    fn check_call_effects(&mut self, func: &Expr, span: Span) {
        let fn_def_id = self.resolve_call_target(func);
        let Some(fn_def_id) = fn_def_id else { return };

        let callee_effects = match self.env.fn_effects.get(&fn_def_id) {
            Some(e) => e.clone(),
            None => return,
        };

        // Get the callee name for error messages.
        let callee_name = self
            .resolved
            .symbols
            .iter()
            .find(|s| s.def_id == fn_def_id)
            .map(|s| s.name.clone())
            .unwrap_or_else(|| "?".to_string());

        for effect in &callee_effects {
            let is_declared = self.current_effects.contains(effect);
            let is_handled = self.handled_effects.contains(effect);

            if !is_declared && !is_handled {
                // Neither declared on current function nor handled by a handle expression.
                self.diagnostics.push(errors::unhandled_effect(
                    &callee_name,
                    effect,
                    self.file_name,
                    span,
                    self.source,
                ));
            }
        }
    }

    /// Check receiver modifier for method calls.
    fn check_receiver_modifier(&mut self, method_def_id: DefId, _inner_expr: &Expr, span: Span) {
        if let Some(expected) = self.env.receiver_modifiers.get(&method_def_id) {
            // For now, just check that Move receiver isn't called on a borrowed reference.
            // More detailed borrow checking would require tracking variable states.
            if *expected == ReceiverModifier::Move {
                // Report a warning-like diagnostic for callers to be aware.
                // In a full implementation, we'd check if the receiver is borrowed.
            }
            let _ = expected; // Suppress unused warnings for now.
        }
        let _ = span;
    }

    /// Expect a specific type, reporting a mismatch if unification fails.
    fn expect_type(&mut self, actual: &Ty, expected: &Ty, span: Span) {
        if self.unify.unify(actual, expected).is_err() {
            self.diagnostics.push(errors::type_mismatch(
                &self.unify.resolve(expected),
                &self.unify.resolve(actual),
                self.file_name,
                span,
                self.source,
            ));
        }
    }

    /// Infer types for a list of statements.
    pub fn infer_stmts(&mut self, stmts: &[Stmt]) {
        for stmt in stmts {
            self.infer_stmt(stmt);
        }
    }
}

/// Convert a ParamModifier to a human-readable string.
fn modifier_to_str(m: &ParamModifier) -> &'static str {
    match m {
        ParamModifier::None => "none",
        ParamModifier::Mut => "mut",
        ParamModifier::Move => "move",
        ParamModifier::MoveMut => "move mut",
    }
}

/// Substitute type parameters with concrete types.
fn substitute(ty: &Ty, subst: &HashMap<DefId, Ty>) -> Ty {
    match ty {
        Ty::Param(def_id) => subst.get(def_id).cloned().unwrap_or_else(|| ty.clone()),
        Ty::Struct { def_id, type_args } => Ty::Struct {
            def_id: *def_id,
            type_args: type_args.iter().map(|t| substitute(t, subst)).collect(),
        },
        Ty::Enum { def_id, type_args } => Ty::Enum {
            def_id: *def_id,
            type_args: type_args.iter().map(|t| substitute(t, subst)).collect(),
        },
        Ty::Tuple(elems) => Ty::Tuple(elems.iter().map(|t| substitute(t, subst)).collect()),
        Ty::Fn { params, ret } => Ty::Fn {
            params: params.iter().map(|t| substitute(t, subst)).collect(),
            ret: Box::new(substitute(ret, subst)),
        },
        Ty::Ref(inner) => Ty::Ref(Box::new(substitute(inner, subst))),
        Ty::Slice(inner) => Ty::Slice(Box::new(substitute(inner, subst))),
        Ty::Array { elem, len } => Ty::Array {
            elem: Box::new(substitute(elem, subst)),
            len: *len,
        },
        _ => ty.clone(),
    }
}
