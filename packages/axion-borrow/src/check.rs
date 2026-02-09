use axion_diagnostics::Diagnostic;
use axion_resolve::def_id::{DefId, SymbolKind};
use axion_resolve::ResolveOutput;
use axion_syntax::*;
use axion_types::env::TypeEnv;
use axion_types::TypeCheckOutput;

use crate::errors;
use crate::state::{StateMap, VarState};

/// Context for borrow checking a single function body.
pub struct BorrowCtx<'a> {
    pub resolved: &'a ResolveOutput,
    pub type_check: &'a TypeCheckOutput,
    pub type_env: &'a TypeEnv,
    pub state: StateMap,
    pub diagnostics: Vec<Diagnostic>,
    pub file_name: &'a str,
    pub source: &'a str,
}

impl<'a> BorrowCtx<'a> {
    pub fn new(
        resolved: &'a ResolveOutput,
        type_check: &'a TypeCheckOutput,
        type_env: &'a TypeEnv,
        file_name: &'a str,
        source: &'a str,
    ) -> Self {
        Self {
            resolved,
            type_check,
            type_env,
            state: StateMap::new(),
            diagnostics: Vec::new(),
            file_name,
            source,
        }
    }

    /// Check a function body.
    pub fn check_fn(&mut self, params: &[Param], body: &[Stmt]) {
        // Register params as Owned.
        for param in params {
            let param_sym = self
                .resolved
                .symbols
                .iter()
                .find(|s| s.kind == SymbolKind::Param && s.span == param.span);
            if let Some(sym) = param_sym {
                let is_mut = matches!(param.modifier, ParamModifier::Mut | ParamModifier::MoveMut);
                self.state.declare(sym.def_id, is_mut);
            }
        }

        self.check_stmts(body);
    }

    /// Check a list of statements.
    pub fn check_stmts(&mut self, stmts: &[Stmt]) {
        for stmt in stmts {
            self.check_stmt(stmt);
        }
    }

    fn check_stmt(&mut self, stmt: &Stmt) {
        match &stmt.kind {
            StmtKind::Let {
                is_mut,
                name: _,
                value,
                ..
            } => {
                // Check the value expression first.
                self.check_expr(value);

                // Register the new variable.
                let def_id = self
                    .resolved
                    .symbols
                    .iter()
                    .find(|s| s.kind == SymbolKind::LocalVar && s.span == stmt.span)
                    .map(|s| s.def_id);
                if let Some(def_id) = def_id {
                    self.state.declare(def_id, *is_mut);
                }
            }
            StmtKind::LetPattern {
                is_mut, value, ..
            } => {
                self.check_expr(value);
                // Pattern variables are harder to track; register any LocalVar symbols
                // found in the pattern span.
                for sym in &self.resolved.symbols {
                    if sym.kind == SymbolKind::LocalVar
                        && sym.span.start >= stmt.span.start
                        && sym.span.end <= stmt.span.end
                    {
                        self.state.declare(sym.def_id, *is_mut);
                    }
                }
            }
            StmtKind::Assign { target, value } => {
                // Check that the target is mutable.
                if let ExprKind::Ident(name) = &target.kind {
                    if let Some(&def_id) = self.resolved.resolutions.get(&target.span.start) {
                        if !self.state.is_mut(&def_id) && self.state.get(&def_id).is_some() {
                            self.diagnostics.push(errors::assign_to_immutable(
                                name,
                                self.file_name,
                                stmt.span,
                                self.source,
                            ));
                        }
                        // Check the value expression.
                        self.check_expr(value);
                        // Reassigning resets the state to Owned.
                        self.state.set(def_id, VarState::Owned);
                    } else {
                        self.check_expr(value);
                    }
                } else {
                    self.check_expr(target);
                    self.check_expr(value);
                }
            }
            StmtKind::Expr(expr) => {
                self.check_expr(expr);
            }
            StmtKind::Return(opt_expr) => {
                if let Some(expr) = opt_expr {
                    self.check_expr(expr);
                }
            }
            StmtKind::Break(opt_expr) => {
                if let Some(expr) = opt_expr {
                    self.check_expr(expr);
                }
            }
            StmtKind::Continue => {}
            StmtKind::Assert { cond, message } => {
                self.check_expr(cond);
                if let Some(msg) = message {
                    self.check_expr(msg);
                }
            }
        }
    }

    fn check_expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Ident(name) => {
                // Check for use-after-move.
                if let Some(&def_id) = self.resolved.resolutions.get(&expr.span.start) {
                    if let Some(state) = self.state.get(&def_id) {
                        if *state == VarState::Moved {
                            self.diagnostics.push(errors::use_after_move(
                                name,
                                self.file_name,
                                expr.span,
                                self.source,
                            ));
                        }
                    }
                }
            }
            ExprKind::BinOp { lhs, rhs, .. } => {
                self.check_expr(lhs);
                self.check_expr(rhs);
            }
            ExprKind::UnaryOp { operand, .. } => {
                self.check_expr(operand);
            }
            ExprKind::Call { func, args } => {
                self.check_expr(func);

                // Check arguments with modifiers.
                let func_def_id = match &func.kind {
                    ExprKind::Ident(_) => {
                        self.resolved.resolutions.get(&func.span.start).copied()
                    }
                    _ => None,
                };

                let param_modifiers = func_def_id
                    .and_then(|did| self.type_env.param_modifiers.get(&did))
                    .cloned();

                for (i, arg) in args.iter().enumerate() {
                    let modifier = param_modifiers
                        .as_ref()
                        .and_then(|mods| mods.get(i))
                        .cloned()
                        .unwrap_or(ParamModifier::None);

                    self.check_expr(&arg.expr);

                    // Handle move semantics.
                    if matches!(modifier, ParamModifier::Move | ParamModifier::MoveMut) {
                        if let ExprKind::Ident(arg_name) = &arg.expr.kind {
                            if let Some(&arg_def_id) =
                                self.resolved.resolutions.get(&arg.expr.span.start)
                            {
                                self.perform_move(arg_def_id, arg_name, arg.expr.span);
                            }
                        }
                    }
                }
            }
            ExprKind::Field { expr: inner, .. } => {
                self.check_expr(inner);
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                self.check_expr(cond);

                let snapshot = self.state.snapshot();

                self.check_stmts(then_branch);
                let then_states = self.state.snapshot();

                // Restore for else branch.
                self.state.states = snapshot.clone();
                let else_states = if let Some(else_stmts) = else_branch {
                    self.check_stmts(else_stmts);
                    self.state.snapshot()
                } else {
                    snapshot.clone()
                };

                // Merge branches.
                self.state.merge_branches(&then_states, &else_states);
            }
            ExprKind::While { cond, body } => {
                self.check_expr(cond);
                let snapshot = self.state.snapshot();
                self.check_stmts(body);
                // Check for moves in loop body (second iteration would use-after-move).
                for (def_id, state) in &self.state.states {
                    if *state == VarState::Moved {
                        if let Some(VarState::Owned | VarState::Borrowed(_)) = snapshot.get(def_id) {
                            // Variable was moved inside the loop body.
                            // On second iteration, this would be use-after-move.
                            let name = self.find_name(*def_id);
                            if let Some(name) = name {
                                self.diagnostics.push(errors::use_after_move(
                                    &name,
                                    self.file_name,
                                    // Use a dummy span since we don't have the exact use site.
                                    Span::new(0, 0),
                                    self.source,
                                ));
                            }
                        }
                    }
                }
                self.state.restore_borrows(&snapshot);
            }
            ExprKind::Block(stmts) => {
                let snapshot = self.state.snapshot();
                self.check_stmts(stmts);
                self.state.restore_borrows(&snapshot);
            }
            ExprKind::Match { expr: scrutinee, arms } => {
                self.check_expr(scrutinee);
                for arm in arms {
                    self.check_stmts(&arm.body);
                }
            }
            ExprKind::For { iter, body, .. } => {
                self.check_expr(iter);
                self.check_stmts(body);
            }
            ExprKind::Range { start, end } => {
                self.check_expr(start);
                self.check_expr(end);
            }
            ExprKind::Closure { body, .. } => {
                for stmt in body {
                    self.check_stmt(stmt);
                }
            }
            ExprKind::Ref(inner) => {
                // Immutable borrow.
                if let ExprKind::Ident(name) = &inner.kind {
                    if let Some(&def_id) = self.resolved.resolutions.get(&inner.span.start) {
                        self.perform_borrow(def_id, name, inner.span);
                    }
                }
                self.check_expr(inner);
            }
            ExprKind::StructLit { fields, .. } => {
                for f in fields {
                    self.check_expr(&f.value);
                }
            }
            ExprKind::TupleLit(elems) => {
                for e in elems {
                    self.check_expr(e);
                }
            }
            ExprKind::StringInterp { parts } => {
                for part in parts {
                    if let StringInterpPart::Expr(e) = part {
                        self.check_expr(e);
                    }
                }
            }
            ExprKind::TypeApp { expr: inner, .. } => {
                self.check_expr(inner);
            }
            ExprKind::Assert { cond, message } => {
                self.check_expr(cond);
                if let Some(m) = message {
                    self.check_expr(m);
                }
            }
            ExprKind::Try(inner) | ExprKind::Await(inner) => {
                self.check_expr(inner);
            }
            ExprKind::Handle { expr: inner, arms } => {
                self.check_expr(inner);
                for arm in arms {
                    self.check_stmts(&arm.body);
                }
            }
            ExprKind::MapLit(entries) => {
                for entry in entries {
                    self.check_expr(&entry.key);
                    self.check_expr(&entry.value);
                }
            }
            ExprKind::SetLit(elems) => {
                for e in elems {
                    self.check_expr(e);
                }
            }
            ExprKind::ArrayLit(elems) => {
                for e in elems {
                    self.check_expr(e);
                }
            }
            ExprKind::Index { expr: inner, index } => {
                self.check_expr(inner);
                self.check_expr(index);
            }
            // Literals don't need borrow checking.
            ExprKind::IntLit(..)
            | ExprKind::FloatLit(..)
            | ExprKind::BoolLit(_)
            | ExprKind::CharLit(_)
            | ExprKind::StringLit(_) => {}
        }
    }

    /// Mark a variable as moved.
    fn perform_move(&mut self, def_id: DefId, name: &str, span: Span) {
        match self.state.get(&def_id) {
            Some(VarState::Moved) => {
                self.diagnostics.push(errors::double_move(
                    name,
                    self.file_name,
                    span,
                    self.source,
                ));
            }
            Some(VarState::Borrowed(_)) | Some(VarState::BorrowedMut) => {
                self.diagnostics.push(errors::move_of_borrowed(
                    name,
                    self.file_name,
                    span,
                    self.source,
                ));
            }
            Some(VarState::Owned) => {
                self.state.set(def_id, VarState::Moved);
            }
            None => {
                // Unknown variable, skip.
            }
        }
    }

    /// Add an immutable borrow.
    fn perform_borrow(&mut self, def_id: DefId, name: &str, span: Span) {
        match self.state.get(&def_id).cloned() {
            Some(VarState::Moved) => {
                self.diagnostics.push(errors::use_after_move(
                    name,
                    self.file_name,
                    span,
                    self.source,
                ));
            }
            Some(VarState::BorrowedMut) => {
                // Immutable borrow while mut borrowed — conflict.
                self.diagnostics.push(errors::mutable_borrow_conflict(
                    name,
                    self.file_name,
                    span,
                    self.source,
                ));
            }
            Some(VarState::Borrowed(count)) => {
                self.state.set(def_id, VarState::Borrowed(count + 1));
            }
            Some(VarState::Owned) => {
                self.state.set(def_id, VarState::Borrowed(1));
            }
            None => {}
        }
    }

    /// Add a mutable borrow.
    pub fn perform_mut_borrow(&mut self, def_id: DefId, name: &str, span: Span) {
        // Check mutability.
        if !self.state.is_mut(&def_id) && self.state.get(&def_id).is_some() {
            self.diagnostics.push(errors::mut_borrow_immutable(
                name,
                self.file_name,
                span,
                self.source,
            ));
            return;
        }

        match self.state.get(&def_id).cloned() {
            Some(VarState::Moved) => {
                self.diagnostics.push(errors::use_after_move(
                    name,
                    self.file_name,
                    span,
                    self.source,
                ));
            }
            Some(VarState::Borrowed(_)) => {
                self.diagnostics.push(errors::mutable_borrow_conflict(
                    name,
                    self.file_name,
                    span,
                    self.source,
                ));
            }
            Some(VarState::BorrowedMut) => {
                self.diagnostics.push(errors::multiple_mut_borrows(
                    name,
                    self.file_name,
                    span,
                    self.source,
                ));
            }
            Some(VarState::Owned) => {
                self.state.set(def_id, VarState::BorrowedMut);
            }
            None => {}
        }
    }

    fn find_name(&self, def_id: DefId) -> Option<String> {
        self.resolved
            .symbols
            .iter()
            .find(|s| s.def_id == def_id)
            .map(|s| s.name.clone())
    }
}
