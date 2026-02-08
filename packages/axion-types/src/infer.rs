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
            ExprKind::StringLit(_) => Ty::Error, // String type deferred
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
                let ty = self.infer_expr(inner);
                for arm in arms {
                    self.infer_stmts(&arm.body);
                }
                ty
            }
            ExprKind::StringInterp { parts } => {
                for part in parts {
                    if let StringInterpPart::Expr(e) = part {
                        self.infer_expr(e);
                    }
                }
                Ty::Error // String type deferred
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

        // Otherwise, try struct field access.
        match &resolved {
            Ty::Struct { def_id, .. } => {
                if let Some(fields) = self.env.struct_fields.get(def_id) {
                    for (i, (field_name, field_ty)) in fields.iter().enumerate() {
                        if field_name == name {
                            self.field_resolutions.insert(span.start, i);
                            return field_ty.clone();
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
        if let ExprKind::Ident(_) = &expr.kind {
            if let Some(&def_id) = self.resolved.resolutions.get(&expr.span.start) {
                let sym = self.resolved.symbols.iter().find(|s| s.def_id == def_id);
                if let Some(sym) = sym {
                    return matches!(
                        sym.kind,
                        SymbolKind::Struct | SymbolKind::Enum | SymbolKind::Interface
                    );
                }
            }
        }
        false
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
        let _scrutinee_ty = self.infer_expr(scrutinee);

        // Infer all arm body types and unify them.
        let mut result_ty: Option<Ty> = None;
        for arm in arms {
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

                // Type-check provided fields.
                for init in fields {
                    let init_ty = self.infer_expr(&init.value);
                    if let Some((_, expected_ty)) =
                        expected_fields.iter().find(|(n, _)| n == &init.name)
                    {
                        if self.unify.unify(expected_ty, &init_ty).is_err() {
                            self.diagnostics.push(errors::type_mismatch(
                                &self.unify.resolve(expected_ty),
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

            Ty::Struct {
                def_id,
                type_args: vec![],
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

    /// Distribute types to pattern bindings (simplified — full pattern typing deferred).
    fn infer_pattern_bindings(&mut self, pattern: &Pattern, ty: &Ty) {
        match &pattern.kind {
            PatternKind::Ident(_) => {
                if let Some(&def_id) = self.resolved.resolutions.get(&pattern.span.start) {
                    self.env.defs.insert(
                        def_id,
                        crate::env::TypeInfo { ty: ty.clone() },
                    );
                }
            }
            PatternKind::TuplePattern(pats) => {
                if let Ty::Tuple(elems) = ty {
                    for (p, elem_ty) in pats.iter().zip(elems.iter()) {
                        self.infer_pattern_bindings(p, elem_ty);
                    }
                }
            }
            PatternKind::Wildcard => {}
            _ => {
                // Other patterns — deferred
            }
        }
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
        _ => ty.clone(),
    }
}
