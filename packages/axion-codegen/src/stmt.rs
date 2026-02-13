use axion_resolve::def_id::SymbolKind;
use axion_types::ty::Ty;
use axion_syntax::*;
use inkwell::values::BasicValueEnum;

use crate::context::CodegenCtx;
use crate::expr::{compile_expr, compile_expr_addr, get_obj_llvm_ty, resolve_arr_ty};
use crate::function::emit_cleanup;
use crate::layout::{ty_to_llvm, build_subst_map, variant_struct_type};

/// Compile a statement.
pub fn compile_stmt<'ctx>(ctx: &mut CodegenCtx<'ctx>, stmt: &Stmt) {
    match &stmt.kind {
        StmtKind::Let {
            is_mut: _,
            name,
            ty: _,
            value,
        } => compile_let(ctx, stmt, name, value),
        StmtKind::LetPattern {
            pattern, value, ..
        } => compile_let_pattern(ctx, pattern, value),
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

        // Store the semantic Ty for this local (after substitution).
        let expr_ty = ctx
            .type_check
            .expr_types
            .get(&value.span.start)
            .cloned()
            .unwrap_or(Ty::Unit);
        let semantic_ty = if ctx.current_subst.is_empty() {
            expr_ty.clone()
        } else {
            axion_mono::specialize::substitute(&expr_ty, &ctx.current_subst)
        };
        ctx.local_tys.insert(def_id, semantic_ty);

        // Check if the value's type has a `drop` method; if so, register for cleanup.
        register_drop_if_needed(ctx, alloca, val_ty, &expr_ty);
    }
}

/// Check if a type has a `drop` method and register the local for cleanup.
fn register_drop_if_needed<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    alloca: inkwell::values::PointerValue<'ctx>,
    llvm_ty: inkwell::types::BasicTypeEnum<'ctx>,
    ty: &Ty,
) {
    let type_name = match ty {
        Ty::Struct { def_id, .. } | Ty::Enum { def_id, .. } => {
            ctx.resolved
                .symbols
                .iter()
                .find(|s| s.def_id == *def_id)
                .map(|s| s.name.clone())
        }
        _ => None,
    };
    let Some(type_name) = type_name else { return };

    let drop_key = format!("{}.drop", type_name);
    let drop_def_id = ctx
        .resolved
        .symbols
        .iter()
        .find(|s| s.name == drop_key && s.kind == SymbolKind::Method)
        .map(|s| s.def_id);
    let Some(drop_def_id) = drop_def_id else { return };

    if let Some(&drop_fn) = ctx.functions.get(&drop_def_id) {
        ctx.drop_locals.push((alloca, llvm_ty, drop_fn));
    }
}

fn compile_assign<'ctx>(ctx: &mut CodegenCtx<'ctx>, target: &Expr, value: &Expr) {
    let val = compile_expr(ctx, value);

    match &target.kind {
        ExprKind::Ident(_) => {
            if let Some(def_id) = ctx.resolved.resolutions.get(&target.span.start) {
                if let Some(&alloca) = ctx.locals.get(def_id) {
                    if let Some(val) = val {
                        ctx.builder.build_store(alloca, val).unwrap();
                    }
                }
            }
        }
        ExprKind::Field { expr: obj, name: _ } => {
            // Field assignment: obj.field = value
            if let Some(val) = val {
                if let Some(obj_ptr) = compile_expr_addr(ctx, obj) {
                    if let Some(&field_idx) = ctx.type_check.field_resolutions.get(&target.span.start) {
                        let llvm_ty = get_obj_llvm_ty(ctx, obj);
                        let gep = ctx
                            .builder
                            .build_struct_gep(llvm_ty, obj_ptr, field_idx as u32, "field_assign")
                            .unwrap();
                        ctx.builder.build_store(gep, val).unwrap();
                    }
                }
            }
        }
        ExprKind::Index { expr: arr_expr, index } => {
            if let Some(val) = val {
                let arr_ty = resolve_arr_ty(ctx, arr_expr);
                match &arr_ty {
                    Ty::Array { .. } => {
                        // FixedArray: GEP(arr_alloca, [0, idx]) → store
                        let arr_ptr = compile_expr_addr(ctx, arr_expr);
                        let idx = compile_expr(ctx, index);
                        if let (Some(arr_ptr), Some(idx)) = (arr_ptr, idx) {
                            let arr_llvm_ty = get_obj_llvm_ty(ctx, arr_expr);
                            let zero = ctx.context.i64_type().const_zero();
                            let gep = unsafe {
                                ctx.builder
                                    .build_in_bounds_gep(arr_llvm_ty, arr_ptr, &[zero, idx.into_int_value()], "arr_assign")
                                    .unwrap()
                            };
                            ctx.builder.build_store(gep, val).unwrap();
                        }
                    }
                    Ty::Slice(elem) => {
                        // Slice: extract ptr, GEP(ptr, [idx]) → store
                        let slice_val = compile_expr(ctx, arr_expr);
                        let idx = compile_expr(ctx, index);
                        if let (Some(slice_val), Some(idx)) = (slice_val, idx) {
                            let ptr = ctx.builder.build_extract_value(slice_val.into_struct_value(), 0, "slice_ptr")
                                .unwrap().into_pointer_value();
                            let elem_llvm_ty = ty_to_llvm(ctx, elem);
                            let elem_ptr = unsafe {
                                ctx.builder.build_in_bounds_gep(elem_llvm_ty, ptr, &[idx.into_int_value()], "slice_assign").unwrap()
                            };
                            ctx.builder.build_store(elem_ptr, val).unwrap();
                        }
                    }
                    _ => {}
                }
            }
        }
        _ => {}
    }
}

fn compile_return<'ctx>(ctx: &mut CodegenCtx<'ctx>, opt_expr: Option<&Expr>) {
    if let Some(expr) = opt_expr {
        let val = compile_expr(ctx, expr);
        emit_cleanup(ctx);
        if let Some(val) = val {
            ctx.builder.build_return(Some(&val)).unwrap();
        } else {
            ctx.builder.build_return(None).unwrap();
        }
    } else {
        emit_cleanup(ctx);
        ctx.builder.build_return(None).unwrap();
    }
}

fn compile_let_pattern<'ctx>(ctx: &mut CodegenCtx<'ctx>, pattern: &Pattern, value: &Expr) {
    let val = compile_expr(ctx, value);
    if let Some(val) = val {
        let val_ty = ctx
            .type_check
            .expr_types
            .get(&value.span.start)
            .cloned()
            .unwrap_or(Ty::Unit);
        let val_ty = if ctx.current_subst.is_empty() {
            val_ty
        } else {
            axion_mono::specialize::substitute(&val_ty, &ctx.current_subst)
        };
        bind_pattern_value(ctx, pattern, val, &val_ty);
    }
}

/// Recursively bind pattern variables to parts of a value.
pub fn bind_pattern_value<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    pattern: &Pattern,
    val: BasicValueEnum<'ctx>,
    ty: &Ty,
) {
    match &pattern.kind {
        PatternKind::Wildcard => {}
        PatternKind::Ident(name) => {
            let def_id = ctx
                .resolved
                .symbols
                .iter()
                .find(|s| s.kind == SymbolKind::LocalVar && s.span == pattern.span)
                .map(|s| s.def_id);
            if let Some(def_id) = def_id {
                let val_ty = val.get_type();
                let alloca = ctx.builder.build_alloca(val_ty, name).unwrap();
                ctx.builder.build_store(alloca, val).unwrap();
                ctx.locals.insert(def_id, alloca);
                ctx.local_types.insert(def_id, val_ty);
            }
        }
        PatternKind::TuplePattern(pats) => {
            if let Ty::Tuple(elem_tys) = ty {
                for (i, (pat, elem_ty)) in pats.iter().zip(elem_tys.iter()).enumerate() {
                    let elem_val = ctx
                        .builder
                        .build_extract_value(val.into_struct_value(), i as u32, "tup_elem")
                        .unwrap();
                    bind_pattern_value(ctx, pat, elem_val, elem_ty);
                }
            }
        }
        PatternKind::Constructor { path, type_args: _, fields } => {
            if path.len() < 2 || fields.is_empty() {
                return;
            }
            let variant_name = &path[path.len() - 1];
            let enum_def_id = match ty {
                Ty::Enum { def_id, .. } => *def_id,
                _ => return,
            };
            let type_args = match ty {
                Ty::Enum { type_args, .. } => type_args.clone(),
                _ => vec![],
            };
            let variants = match ctx.type_env.enum_variants.get(&enum_def_id) {
                Some(v) => v.clone(),
                None => return,
            };
            let variant_info = variants
                .iter()
                .enumerate()
                .find(|(_, (vname, _, _))| vname == variant_name);
            let (_variant_idx, variant_fields) = match variant_info {
                Some((idx, (_, _, vfields))) => (idx, vfields.clone()),
                None => return,
            };
            let subst = build_subst_map(ctx, enum_def_id, &type_args);
            let vs_ty = variant_struct_type(ctx, &variant_fields, &subst);
            let enum_llvm_ty = ty_to_llvm(ctx, ty);

            let alloca = ctx.builder.build_alloca(enum_llvm_ty, "let_enum").unwrap();
            ctx.builder.build_store(alloca, val).unwrap();
            let payload_ptr = ctx
                .builder
                .build_struct_gep(enum_llvm_ty, alloca, 1, "payload_ptr")
                .unwrap();

            for (fi, pat) in fields.iter().enumerate() {
                if fi >= variant_fields.len() {
                    break;
                }
                let (_, ref field_ty) = variant_fields[fi];
                let resolved_field_ty = if subst.is_empty() {
                    field_ty.clone()
                } else {
                    axion_mono::specialize::substitute(field_ty, &subst)
                };
                let field_llvm_ty = ty_to_llvm(ctx, &resolved_field_ty);
                let field_ptr = ctx
                    .builder
                    .build_struct_gep(vs_ty, payload_ptr, fi as u32, "field_ptr")
                    .unwrap();
                let field_val = ctx
                    .builder
                    .build_load(field_llvm_ty, field_ptr, "field_val")
                    .unwrap();
                bind_pattern_value(ctx, pat, field_val, &resolved_field_ty);
            }
        }
        PatternKind::Struct {
            name: _,
            fields: field_pats,
            ..
        } => {
            let struct_def_id = match ty {
                Ty::Struct { def_id, .. } => *def_id,
                _ => return,
            };
            let type_fields = match ctx.type_env.struct_fields.get(&struct_def_id) {
                Some(f) => f.clone(),
                None => return,
            };
            let type_args = match ty {
                Ty::Struct { type_args, .. } => type_args.clone(),
                _ => vec![],
            };
            let subst = build_subst_map(ctx, struct_def_id, &type_args);

            for fp in field_pats {
                let field_idx = type_fields
                    .iter()
                    .position(|(fname, _)| fname == &fp.name);
                let Some(idx) = field_idx else { continue };
                let (_, ref field_ty) = type_fields[idx];
                let resolved_field_ty = if subst.is_empty() {
                    field_ty.clone()
                } else {
                    axion_mono::specialize::substitute(field_ty, &subst)
                };

                let field_val = ctx
                    .builder
                    .build_extract_value(val.into_struct_value(), idx as u32, &fp.name)
                    .unwrap();

                if let Some(ref inner_pat) = fp.pattern {
                    bind_pattern_value(ctx, inner_pat, field_val, &resolved_field_ty);
                } else {
                    // Shorthand: bind field name as local variable.
                    let def_id = ctx
                        .resolved
                        .symbols
                        .iter()
                        .find(|s| s.kind == SymbolKind::LocalVar && s.span == fp.span)
                        .map(|s| s.def_id);
                    if let Some(def_id) = def_id {
                        let fval_ty = field_val.get_type();
                        let alloca = ctx.builder.build_alloca(fval_ty, &fp.name).unwrap();
                        ctx.builder.build_store(alloca, field_val).unwrap();
                        ctx.locals.insert(def_id, alloca);
                        ctx.local_types.insert(def_id, fval_ty);
                    }
                }
            }
        }
        _ => {}
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
