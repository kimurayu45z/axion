use axion_resolve::def_id::SymbolKind;
use axion_syntax::*;

use crate::context::CodegenCtx;
use crate::expr::compile_expr;

/// Compile a statement.
pub fn compile_stmt<'ctx>(ctx: &mut CodegenCtx<'ctx>, stmt: &Stmt) {
    match &stmt.kind {
        StmtKind::Let {
            is_mut: _,
            name,
            ty: _,
            value,
        } => compile_let(ctx, stmt, name, value),
        StmtKind::LetPattern { .. } => {
            // Pattern destructuring not yet implemented in codegen.
        }
        StmtKind::Assign { target, value } => compile_assign(ctx, target, value),
        StmtKind::Expr(expr) => {
            compile_expr(ctx, expr);
        }
        StmtKind::Return(opt_expr) => compile_return(ctx, opt_expr.as_ref()),
        StmtKind::Break(_opt_expr) => compile_break(ctx),
        StmtKind::Continue => compile_continue(ctx),
        StmtKind::Assert { cond, message } => {
            compile_expr(
                ctx,
                &Expr {
                    kind: ExprKind::Assert {
                        cond: Box::new(cond.clone()),
                        message: message.clone().map(Box::new),
                    },
                    span: stmt.span,
                },
            );
        }
    }
}

fn compile_let<'ctx>(ctx: &mut CodegenCtx<'ctx>, stmt: &Stmt, name: &str, value: &Expr) {
    let val = compile_expr(ctx, value);

    // Find the DefId for this let binding.
    let def_id = ctx
        .resolved
        .symbols
        .iter()
        .find(|s| s.kind == SymbolKind::LocalVar && s.span == stmt.span)
        .map(|s| s.def_id);

    let Some(def_id) = def_id else { return };

    if let Some(val) = val {
        let val_ty = val.get_type();
        let alloca = ctx
            .builder
            .build_alloca(val_ty, name)
            .unwrap();
        ctx.builder.build_store(alloca, val).unwrap();
        ctx.locals.insert(def_id, alloca);
        ctx.local_types.insert(def_id, val_ty);
    }
}

fn compile_assign<'ctx>(ctx: &mut CodegenCtx<'ctx>, target: &Expr, value: &Expr) {
    let val = compile_expr(ctx, value);

    // The target should be an identifier we can resolve.
    if let ExprKind::Ident(_) = &target.kind {
        if let Some(def_id) = ctx.resolved.resolutions.get(&target.span.start) {
            if let Some(&alloca) = ctx.locals.get(def_id) {
                if let Some(val) = val {
                    ctx.builder.build_store(alloca, val).unwrap();
                }
            }
        }
    }
}

fn compile_return<'ctx>(ctx: &mut CodegenCtx<'ctx>, opt_expr: Option<&Expr>) {
    if let Some(expr) = opt_expr {
        let val = compile_expr(ctx, expr);
        if let Some(val) = val {
            ctx.builder.build_return(Some(&val)).unwrap();
        } else {
            ctx.builder.build_return(None).unwrap();
        }
    } else {
        ctx.builder.build_return(None).unwrap();
    }
}

fn compile_break<'ctx>(ctx: &mut CodegenCtx<'ctx>) {
    if let Some(exit_bb) = ctx.loop_exit_block {
        ctx.builder.build_unconditional_branch(exit_bb).unwrap();
    }
}

fn compile_continue<'ctx>(ctx: &mut CodegenCtx<'ctx>) {
    if let Some(header_bb) = ctx.loop_header_block {
        ctx.builder
            .build_unconditional_branch(header_bb)
            .unwrap();
    }
}
