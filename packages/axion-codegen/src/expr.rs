use axion_types::ty::{PrimTy, Ty};
use axion_syntax::*;
use inkwell::values::{BasicMetadataValueEnum, BasicValueEnum};
use inkwell::IntPredicate;
use inkwell::FloatPredicate;

use crate::context::CodegenCtx;
use crate::intrinsics::build_printf_call;
use crate::layout::{is_void_ty, ty_to_llvm};
use crate::stmt::compile_stmt;

/// Compile an expression and return its LLVM value (None for void expressions).
pub fn compile_expr<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    expr: &Expr,
) -> Option<BasicValueEnum<'ctx>> {
    match &expr.kind {
        ExprKind::IntLit(val, _suffix) => compile_int_lit(ctx, expr, *val),
        ExprKind::FloatLit(val, _suffix) => compile_float_lit(ctx, expr, *val),
        ExprKind::BoolLit(b) => {
            Some(ctx.context.i8_type().const_int(*b as u64, false).into())
        }
        ExprKind::CharLit(c) => {
            Some(ctx.context.i32_type().const_int(*c as u64, false).into())
        }
        ExprKind::StringLit(s) => compile_string_lit(ctx, s),
        ExprKind::Ident(name) => compile_ident(ctx, expr, name),
        ExprKind::BinOp { op, lhs, rhs } => compile_binop(ctx, expr, *op, lhs, rhs),
        ExprKind::UnaryOp { op, operand } => compile_unary_op(ctx, *op, operand),
        ExprKind::Call { func, args } => compile_call(ctx, expr, func, args),
        ExprKind::Field { expr: obj, name } => compile_field(ctx, expr, obj, name),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => compile_if(ctx, expr, cond, then_branch, else_branch),
        ExprKind::While { cond, body } => {
            compile_while(ctx, cond, body);
            None
        }
        ExprKind::Block(stmts) => compile_block(ctx, stmts),
        ExprKind::StructLit { name: _, fields } => compile_struct_lit(ctx, expr, fields),
        ExprKind::TupleLit(elems) => compile_tuple_lit(ctx, elems),
        ExprKind::Match { expr: scrutinee, arms } => compile_match(ctx, expr, scrutinee, arms),
        ExprKind::For { .. } => {
            // For loops not yet implemented in codegen.
            None
        }
        ExprKind::Range { .. } => None,
        ExprKind::Closure { .. } => None,
        ExprKind::Assert { cond, message } => {
            compile_assert(ctx, cond, message.as_deref());
            None
        }
        ExprKind::Ref(inner) => compile_expr(ctx, inner),
        ExprKind::StringInterp { .. } => None,
        ExprKind::TypeApp { expr: inner, .. } => compile_expr(ctx, inner),
        ExprKind::MapLit(_) | ExprKind::SetLit(_) => None,
        ExprKind::Handle { .. } | ExprKind::Try(_) | ExprKind::Await(_) => None,
    }
}

fn compile_int_lit<'ctx>(
    ctx: &CodegenCtx<'ctx>,
    expr: &Expr,
    val: i128,
) -> Option<BasicValueEnum<'ctx>> {
    let ty = ctx.type_check.expr_types.get(&expr.span.start);
    match ty {
        Some(Ty::Prim(PrimTy::I8)) | Some(Ty::Prim(PrimTy::U8)) => {
            Some(ctx.context.i8_type().const_int(val as u64, false).into())
        }
        Some(Ty::Prim(PrimTy::I16)) | Some(Ty::Prim(PrimTy::U16)) => {
            Some(ctx.context.i16_type().const_int(val as u64, false).into())
        }
        Some(Ty::Prim(PrimTy::I32)) | Some(Ty::Prim(PrimTy::U32)) => {
            Some(ctx.context.i32_type().const_int(val as u64, false).into())
        }
        Some(Ty::Prim(PrimTy::I128)) | Some(Ty::Prim(PrimTy::U128)) => {
            Some(ctx.context.i128_type().const_int(val as u64, false).into())
        }
        Some(Ty::Prim(PrimTy::F32)) => {
            Some(ctx.context.f32_type().const_float(val as f64).into())
        }
        Some(Ty::Prim(PrimTy::F64)) => {
            Some(ctx.context.f64_type().const_float(val as f64).into())
        }
        _ => {
            // Default to i64.
            Some(ctx.context.i64_type().const_int(val as u64, false).into())
        }
    }
}

fn compile_float_lit<'ctx>(
    ctx: &CodegenCtx<'ctx>,
    expr: &Expr,
    val: f64,
) -> Option<BasicValueEnum<'ctx>> {
    let ty = ctx.type_check.expr_types.get(&expr.span.start);
    match ty {
        Some(Ty::Prim(PrimTy::F32)) => {
            Some(ctx.context.f32_type().const_float(val).into())
        }
        _ => {
            Some(ctx.context.f64_type().const_float(val).into())
        }
    }
}

fn compile_string_lit<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    s: &str,
) -> Option<BasicValueEnum<'ctx>> {
    // Return a {ptr, i64 len} struct for str type.
    let ptr = if let Some(&cached) = ctx.string_literals.get(s) {
        cached
    } else {
        let global = ctx
            .builder
            .build_global_string_ptr(s, "str_lit")
            .unwrap();
        let ptr = global.as_pointer_value();
        ctx.string_literals.insert(s.to_string(), ptr);
        ptr
    };
    let len = ctx
        .context
        .i64_type()
        .const_int(s.len() as u64, false);
    let str_struct_ty = ctx.context.struct_type(
        &[
            ctx.context
                .ptr_type(inkwell::AddressSpace::default())
                .into(),
            ctx.context.i64_type().into(),
        ],
        false,
    );
    let mut str_val = str_struct_ty.const_zero();
    str_val = ctx
        .builder
        .build_insert_value(str_val, ptr, 0, "str_ptr")
        .unwrap()
        .into_struct_value();
    str_val = ctx
        .builder
        .build_insert_value(str_val, len, 1, "str_len")
        .unwrap()
        .into_struct_value();
    Some(str_val.into())
}

fn compile_ident<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    expr: &Expr,
    _name: &str,
) -> Option<BasicValueEnum<'ctx>> {
    // Look up the DefId via resolution.
    let def_id = ctx.resolved.resolutions.get(&expr.span.start)?;

    // Check if it's a local variable or param.
    if let Some(&alloca) = ctx.locals.get(def_id) {
        // Get the pointee type from the alloca's stored value type.
        // We track the actual LLVM type stored in the alloca from compile_let/param setup.
        // Note: expr_types[span.start] can be wrong when a parent expr shares the same
        // span.start (e.g., `i` in `i <= 10` gets the Bool type of the comparison).
        // So we derive the type from what was actually stored.
        let pointee_ty = ctx.local_types.get(def_id).copied()
            .unwrap_or_else(|| ty_to_llvm(ctx, &get_expr_ty(ctx, expr)));
        let loaded = ctx
            .builder
            .build_load(pointee_ty, alloca, "load")
            .unwrap();
        return Some(loaded);
    }

    // Check if it's a function reference.
    if let Some(&fn_val) = ctx.functions.get(def_id) {
        return Some(fn_val.as_global_value().as_pointer_value().into());
    }

    None
}

fn get_expr_ty<'ctx>(ctx: &CodegenCtx<'ctx>, expr: &Expr) -> Ty {
    ctx.type_check
        .expr_types
        .get(&expr.span.start)
        .cloned()
        .unwrap_or(Ty::Unit)
}

fn compile_binop<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    expr: &Expr,
    op: BinOp,
    lhs: &Expr,
    rhs: &Expr,
) -> Option<BasicValueEnum<'ctx>> {
    let lhs_val = compile_expr(ctx, lhs)?;
    let rhs_val = compile_expr(ctx, rhs)?;

    // Determine whether it's float/signed from the actual LLVM value types.
    let is_float = lhs_val.is_float_value();

    // For signed-ness, check the type-checker's type for the LHS.
    // Use the resolved DefId type if the LHS is an ident, since span-based lookup
    // may be overwritten by the parent expression's type.
    let lhs_ty = if let ExprKind::Ident(_) = &lhs.kind {
        ctx.resolved
            .resolutions
            .get(&lhs.span.start)
            .and_then(|def_id| ctx.type_env.defs.get(def_id))
            .map(|info| info.ty.clone())
            .unwrap_or_else(|| get_expr_ty(ctx, lhs))
    } else {
        get_expr_ty(ctx, lhs)
    };

    let is_signed = matches!(
        lhs_ty,
        Ty::Prim(PrimTy::I8)
            | Ty::Prim(PrimTy::I16)
            | Ty::Prim(PrimTy::I32)
            | Ty::Prim(PrimTy::I64)
            | Ty::Prim(PrimTy::I128)
    );

    if is_float {
        compile_float_binop(ctx, op, lhs_val, rhs_val)
    } else {
        compile_int_binop(ctx, expr, op, lhs_val, rhs_val, is_signed)
    }
}

fn compile_int_binop<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    _expr: &Expr,
    op: BinOp,
    lhs: BasicValueEnum<'ctx>,
    rhs: BasicValueEnum<'ctx>,
    is_signed: bool,
) -> Option<BasicValueEnum<'ctx>> {
    let lhs_int = lhs.into_int_value();
    let rhs_int = rhs.into_int_value();

    match op {
        BinOp::Add => Some(
            ctx.builder
                .build_int_add(lhs_int, rhs_int, "add")
                .unwrap()
                .into(),
        ),
        BinOp::Sub => Some(
            ctx.builder
                .build_int_sub(lhs_int, rhs_int, "sub")
                .unwrap()
                .into(),
        ),
        BinOp::Mul => Some(
            ctx.builder
                .build_int_mul(lhs_int, rhs_int, "mul")
                .unwrap()
                .into(),
        ),
        BinOp::Div => {
            if is_signed {
                Some(
                    ctx.builder
                        .build_int_signed_div(lhs_int, rhs_int, "sdiv")
                        .unwrap()
                        .into(),
                )
            } else {
                Some(
                    ctx.builder
                        .build_int_unsigned_div(lhs_int, rhs_int, "udiv")
                        .unwrap()
                        .into(),
                )
            }
        }
        BinOp::Mod => {
            if is_signed {
                Some(
                    ctx.builder
                        .build_int_signed_rem(lhs_int, rhs_int, "srem")
                        .unwrap()
                        .into(),
                )
            } else {
                Some(
                    ctx.builder
                        .build_int_unsigned_rem(lhs_int, rhs_int, "urem")
                        .unwrap()
                        .into(),
                )
            }
        }
        BinOp::Eq => Some(
            ctx.builder
                .build_int_compare(IntPredicate::EQ, lhs_int, rhs_int, "eq")
                .unwrap()
                .into(),
        ),
        BinOp::NotEq => Some(
            ctx.builder
                .build_int_compare(IntPredicate::NE, lhs_int, rhs_int, "ne")
                .unwrap()
                .into(),
        ),
        BinOp::Lt => {
            let pred = if is_signed {
                IntPredicate::SLT
            } else {
                IntPredicate::ULT
            };
            Some(
                ctx.builder
                    .build_int_compare(pred, lhs_int, rhs_int, "lt")
                    .unwrap()
                    .into(),
            )
        }
        BinOp::LtEq => {
            let pred = if is_signed {
                IntPredicate::SLE
            } else {
                IntPredicate::ULE
            };
            Some(
                ctx.builder
                    .build_int_compare(pred, lhs_int, rhs_int, "le")
                    .unwrap()
                    .into(),
            )
        }
        BinOp::Gt => {
            let pred = if is_signed {
                IntPredicate::SGT
            } else {
                IntPredicate::UGT
            };
            Some(
                ctx.builder
                    .build_int_compare(pred, lhs_int, rhs_int, "gt")
                    .unwrap()
                    .into(),
            )
        }
        BinOp::GtEq => {
            let pred = if is_signed {
                IntPredicate::SGE
            } else {
                IntPredicate::UGE
            };
            Some(
                ctx.builder
                    .build_int_compare(pred, lhs_int, rhs_int, "ge")
                    .unwrap()
                    .into(),
            )
        }
        BinOp::And => Some(
            ctx.builder
                .build_and(lhs_int, rhs_int, "and")
                .unwrap()
                .into(),
        ),
        BinOp::Or => Some(
            ctx.builder
                .build_or(lhs_int, rhs_int, "or")
                .unwrap()
                .into(),
        ),
        BinOp::Pipe => {
            // Pipe operator: `x |> f` = `f(x)` — not easily done at IR level,
            // should be desugared before codegen. Fall back to returning lhs.
            Some(lhs)
        }
    }
}

fn compile_float_binop<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    op: BinOp,
    lhs: BasicValueEnum<'ctx>,
    rhs: BasicValueEnum<'ctx>,
) -> Option<BasicValueEnum<'ctx>> {
    let lhs_f = lhs.into_float_value();
    let rhs_f = rhs.into_float_value();

    match op {
        BinOp::Add => Some(
            ctx.builder
                .build_float_add(lhs_f, rhs_f, "fadd")
                .unwrap()
                .into(),
        ),
        BinOp::Sub => Some(
            ctx.builder
                .build_float_sub(lhs_f, rhs_f, "fsub")
                .unwrap()
                .into(),
        ),
        BinOp::Mul => Some(
            ctx.builder
                .build_float_mul(lhs_f, rhs_f, "fmul")
                .unwrap()
                .into(),
        ),
        BinOp::Div => Some(
            ctx.builder
                .build_float_div(lhs_f, rhs_f, "fdiv")
                .unwrap()
                .into(),
        ),
        BinOp::Mod => Some(
            ctx.builder
                .build_float_rem(lhs_f, rhs_f, "frem")
                .unwrap()
                .into(),
        ),
        BinOp::Eq => Some(
            ctx.builder
                .build_float_compare(FloatPredicate::OEQ, lhs_f, rhs_f, "feq")
                .unwrap()
                .into(),
        ),
        BinOp::NotEq => Some(
            ctx.builder
                .build_float_compare(FloatPredicate::ONE, lhs_f, rhs_f, "fne")
                .unwrap()
                .into(),
        ),
        BinOp::Lt => Some(
            ctx.builder
                .build_float_compare(FloatPredicate::OLT, lhs_f, rhs_f, "flt")
                .unwrap()
                .into(),
        ),
        BinOp::LtEq => Some(
            ctx.builder
                .build_float_compare(FloatPredicate::OLE, lhs_f, rhs_f, "fle")
                .unwrap()
                .into(),
        ),
        BinOp::Gt => Some(
            ctx.builder
                .build_float_compare(FloatPredicate::OGT, lhs_f, rhs_f, "fgt")
                .unwrap()
                .into(),
        ),
        BinOp::GtEq => Some(
            ctx.builder
                .build_float_compare(FloatPredicate::OGE, lhs_f, rhs_f, "fge")
                .unwrap()
                .into(),
        ),
        _ => Some(lhs),
    }
}

fn compile_unary_op<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    op: UnaryOp,
    operand: &Expr,
) -> Option<BasicValueEnum<'ctx>> {
    let val = compile_expr(ctx, operand)?;
    let operand_ty = get_expr_ty(ctx, operand);
    let is_float = matches!(
        operand_ty,
        Ty::Prim(PrimTy::F32) | Ty::Prim(PrimTy::F64)
    );

    match op {
        UnaryOp::Neg => {
            if is_float {
                Some(
                    ctx.builder
                        .build_float_neg(val.into_float_value(), "fneg")
                        .unwrap()
                        .into(),
                )
            } else {
                Some(
                    ctx.builder
                        .build_int_neg(val.into_int_value(), "neg")
                        .unwrap()
                        .into(),
                )
            }
        }
        UnaryOp::Not => Some(
            ctx.builder
                .build_not(val.into_int_value(), "not")
                .unwrap()
                .into(),
        ),
    }
}

fn compile_call<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    call_expr: &Expr,
    func: &Expr,
    args: &[CallArg],
) -> Option<BasicValueEnum<'ctx>> {
    // Check for built-in functions: println, print.
    if let ExprKind::Ident(name) = &func.kind {
        match name.as_str() {
            "println" => {
                compile_println(ctx, args);
                return None;
            }
            "print" => {
                compile_print(ctx, args);
                return None;
            }
            _ => {}
        }
    }

    // Resolve the function DefId.
    let def_id = match &func.kind {
        ExprKind::Ident(_) => ctx.resolved.resolutions.get(&func.span.start).copied(),
        _ => None,
    };

    let fn_value = def_id.and_then(|did| ctx.functions.get(&did).copied());

    let Some(fn_value) = fn_value else {
        return None;
    };

    // Compile arguments.
    let mut compiled_args: Vec<BasicMetadataValueEnum> = Vec::new();
    for arg in args {
        if let Some(val) = compile_expr(ctx, &arg.expr) {
            compiled_args.push(val.into());
        }
    }

    // Check if return type is void.
    let ret_ty = get_expr_ty(ctx, call_expr);
    if is_void_ty(&ret_ty) {
        ctx.builder
            .build_call(fn_value, &compiled_args, "call")
            .unwrap();
        None
    } else {
        let call_val = ctx
            .builder
            .build_call(fn_value, &compiled_args, "call")
            .unwrap();
        call_val.try_as_basic_value().left()
    }
}

fn compile_println<'ctx>(ctx: &mut CodegenCtx<'ctx>, args: &[CallArg]) {
    if args.is_empty() {
        build_printf_call(ctx, "\n", &[]);
        return;
    }

    let arg = &args[0];
    let arg_ty = get_expr_ty(ctx, &arg.expr);

    match &arg_ty {
        Ty::Prim(PrimTy::Str) => {
            if let Some(val) = compile_expr(ctx, &arg.expr) {
                // Extract ptr and len from {ptr, i64} struct.
                let str_struct = val.into_struct_value();
                let ptr = ctx
                    .builder
                    .build_extract_value(str_struct, 0, "str_ptr")
                    .unwrap();
                let len = ctx
                    .builder
                    .build_extract_value(str_struct, 1, "str_len")
                    .unwrap();
                build_printf_call(ctx, "%.*s\n", &[len.into(), ptr.into()]);
            }
        }
        Ty::Prim(PrimTy::I64) | Ty::Prim(PrimTy::I32) | Ty::Prim(PrimTy::U64) | Ty::Prim(PrimTy::U32) | Ty::Prim(PrimTy::Usize) => {
            if let Some(val) = compile_expr(ctx, &arg.expr) {
                build_printf_call(ctx, "%lld\n", &[val.into()]);
            }
        }
        Ty::Prim(PrimTy::Bool) => {
            if let Some(val) = compile_expr(ctx, &arg.expr) {
                // bool: print "true" or "false"
                let bool_val = val.into_int_value();
                let true_str = ctx
                    .builder
                    .build_global_string_ptr("true", "true_str")
                    .unwrap();
                let false_str = ctx
                    .builder
                    .build_global_string_ptr("false", "false_str")
                    .unwrap();
                let selected = ctx
                    .builder
                    .build_select(
                        bool_val,
                        true_str.as_pointer_value(),
                        false_str.as_pointer_value(),
                        "bool_str",
                    )
                    .unwrap();
                build_printf_call(ctx, "%s\n", &[selected.into()]);
            }
        }
        Ty::Prim(PrimTy::F64) | Ty::Prim(PrimTy::F32) => {
            if let Some(val) = compile_expr(ctx, &arg.expr) {
                build_printf_call(ctx, "%f\n", &[val.into()]);
            }
        }
        Ty::Prim(PrimTy::Char) => {
            if let Some(val) = compile_expr(ctx, &arg.expr) {
                build_printf_call(ctx, "%c\n", &[val.into()]);
            }
        }
        _ => {
            // Default: try as i64.
            if let Some(val) = compile_expr(ctx, &arg.expr) {
                build_printf_call(ctx, "%lld\n", &[val.into()]);
            }
        }
    }
}

fn compile_print<'ctx>(ctx: &mut CodegenCtx<'ctx>, args: &[CallArg]) {
    if args.is_empty() {
        return;
    }

    let arg = &args[0];
    let arg_ty = get_expr_ty(ctx, &arg.expr);

    match &arg_ty {
        Ty::Prim(PrimTy::Str) => {
            if let Some(val) = compile_expr(ctx, &arg.expr) {
                let str_struct = val.into_struct_value();
                let ptr = ctx
                    .builder
                    .build_extract_value(str_struct, 0, "str_ptr")
                    .unwrap();
                let len = ctx
                    .builder
                    .build_extract_value(str_struct, 1, "str_len")
                    .unwrap();
                build_printf_call(ctx, "%.*s", &[len.into(), ptr.into()]);
            }
        }
        Ty::Prim(PrimTy::I64) | Ty::Prim(PrimTy::I32) | Ty::Prim(PrimTy::U64) | Ty::Prim(PrimTy::U32) | Ty::Prim(PrimTy::Usize) => {
            if let Some(val) = compile_expr(ctx, &arg.expr) {
                build_printf_call(ctx, "%lld", &[val.into()]);
            }
        }
        Ty::Prim(PrimTy::Bool) => {
            if let Some(val) = compile_expr(ctx, &arg.expr) {
                let bool_val = val.into_int_value();
                let true_str = ctx
                    .builder
                    .build_global_string_ptr("true", "true_str")
                    .unwrap();
                let false_str = ctx
                    .builder
                    .build_global_string_ptr("false", "false_str")
                    .unwrap();
                let selected = ctx
                    .builder
                    .build_select(
                        bool_val,
                        true_str.as_pointer_value(),
                        false_str.as_pointer_value(),
                        "bool_str",
                    )
                    .unwrap();
                build_printf_call(ctx, "%s", &[selected.into()]);
            }
        }
        Ty::Prim(PrimTy::F64) | Ty::Prim(PrimTy::F32) => {
            if let Some(val) = compile_expr(ctx, &arg.expr) {
                build_printf_call(ctx, "%f", &[val.into()]);
            }
        }
        _ => {
            if let Some(val) = compile_expr(ctx, &arg.expr) {
                build_printf_call(ctx, "%lld", &[val.into()]);
            }
        }
    }
}

fn compile_field<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    expr: &Expr,
    obj: &Expr,
    _name: &str,
) -> Option<BasicValueEnum<'ctx>> {
    let obj_val = compile_expr(ctx, obj)?;
    let field_idx = ctx.type_check.field_resolutions.get(&expr.span.start)?;

    // The object should be a struct value. We need to extract the field.
    if obj_val.is_struct_value() {
        let struct_val = obj_val.into_struct_value();
        let field_val = ctx
            .builder
            .build_extract_value(struct_val, *field_idx as u32, "field")
            .unwrap();
        Some(field_val)
    } else if obj_val.is_pointer_value() {
        // Load through pointer (struct stored as alloca).
        let obj_ty = get_expr_ty(ctx, obj);
        let llvm_ty = ty_to_llvm(ctx, &obj_ty);
        let gep = ctx
            .builder
            .build_struct_gep(llvm_ty, obj_val.into_pointer_value(), *field_idx as u32, "field_ptr")
            .unwrap();
        let field_ty = get_expr_ty(ctx, expr);
        let field_llvm_ty = ty_to_llvm(ctx, &field_ty);
        let loaded = ctx
            .builder
            .build_load(field_llvm_ty, gep, "field_load")
            .unwrap();
        Some(loaded)
    } else {
        None
    }
}

fn compile_if<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    if_expr: &Expr,
    cond: &Expr,
    then_branch: &[Stmt],
    else_branch: &Option<Vec<Stmt>>,
) -> Option<BasicValueEnum<'ctx>> {
    let cond_val = compile_expr(ctx, cond)?;
    let cond_int = cond_val.into_int_value();

    // Compare: cond != 0
    let cond_bool = ctx
        .builder
        .build_int_compare(
            IntPredicate::NE,
            cond_int,
            cond_int.get_type().const_zero(),
            "ifcond",
        )
        .unwrap();

    let fn_val = ctx
        .builder
        .get_insert_block()
        .unwrap()
        .get_parent()
        .unwrap();

    let then_bb = ctx.context.append_basic_block(fn_val, "then");
    let else_bb = ctx.context.append_basic_block(fn_val, "else");
    let merge_bb = ctx.context.append_basic_block(fn_val, "ifmerge");

    ctx.builder
        .build_conditional_branch(cond_bool, then_bb, else_bb)
        .unwrap();

    // Then block.
    ctx.builder.position_at_end(then_bb);
    let then_val = compile_block_stmts(ctx, then_branch);
    let then_terminated = ctx
        .builder
        .get_insert_block()
        .unwrap()
        .get_terminator()
        .is_some();
    let then_end_bb = ctx.builder.get_insert_block().unwrap();
    if !then_terminated {
        ctx.builder.build_unconditional_branch(merge_bb).unwrap();
    }

    // Else block.
    ctx.builder.position_at_end(else_bb);
    let else_val = if let Some(else_stmts) = else_branch {
        compile_block_stmts(ctx, else_stmts)
    } else {
        None
    };
    let else_terminated = ctx
        .builder
        .get_insert_block()
        .unwrap()
        .get_terminator()
        .is_some();
    let else_end_bb = ctx.builder.get_insert_block().unwrap();
    if !else_terminated {
        ctx.builder.build_unconditional_branch(merge_bb).unwrap();
    }

    // Merge block.
    ctx.builder.position_at_end(merge_bb);

    // Build phi if both branches produce values and neither is terminated.
    let result_ty = get_expr_ty(ctx, if_expr);
    if !is_void_ty(&result_ty) && !then_terminated && !else_terminated {
        if let (Some(tv), Some(ev)) = (then_val, else_val) {
            let phi = ctx
                .builder
                .build_phi(ty_to_llvm(ctx, &result_ty), "ifval")
                .unwrap();
            phi.add_incoming(&[(&tv, then_end_bb), (&ev, else_end_bb)]);
            return Some(phi.as_basic_value());
        }
    }

    None
}

fn compile_while<'ctx>(ctx: &mut CodegenCtx<'ctx>, cond: &Expr, body: &[Stmt]) {
    let fn_val = ctx
        .builder
        .get_insert_block()
        .unwrap()
        .get_parent()
        .unwrap();

    let header_bb = ctx.context.append_basic_block(fn_val, "while_header");
    let body_bb = ctx.context.append_basic_block(fn_val, "while_body");
    let exit_bb = ctx.context.append_basic_block(fn_val, "while_exit");

    ctx.builder.build_unconditional_branch(header_bb).unwrap();

    // Header: evaluate condition.
    ctx.builder.position_at_end(header_bb);
    let cond_val = compile_expr(ctx, cond);
    if let Some(cv) = cond_val {
        let cond_int = cv.into_int_value();
        let cond_bool = ctx
            .builder
            .build_int_compare(
                IntPredicate::NE,
                cond_int,
                cond_int.get_type().const_zero(),
                "whilecond",
            )
            .unwrap();
        ctx.builder
            .build_conditional_branch(cond_bool, body_bb, exit_bb)
            .unwrap();
    } else {
        ctx.builder.build_unconditional_branch(exit_bb).unwrap();
    }

    // Body.
    let prev_exit = ctx.loop_exit_block.take();
    let prev_header = ctx.loop_header_block.take();
    ctx.loop_exit_block = Some(exit_bb);
    ctx.loop_header_block = Some(header_bb);

    ctx.builder.position_at_end(body_bb);
    for stmt in body {
        compile_stmt(ctx, stmt);
        if ctx
            .builder
            .get_insert_block()
            .unwrap()
            .get_terminator()
            .is_some()
        {
            break;
        }
    }
    if ctx
        .builder
        .get_insert_block()
        .unwrap()
        .get_terminator()
        .is_none()
    {
        ctx.builder.build_unconditional_branch(header_bb).unwrap();
    }

    // Restore loop context.
    ctx.loop_exit_block = prev_exit;
    ctx.loop_header_block = prev_header;

    ctx.builder.position_at_end(exit_bb);
}

fn compile_block<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    stmts: &[Stmt],
) -> Option<BasicValueEnum<'ctx>> {
    compile_block_stmts(ctx, stmts)
}

fn compile_block_stmts<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    stmts: &[Stmt],
) -> Option<BasicValueEnum<'ctx>> {
    let mut last_val = None;
    for (i, stmt) in stmts.iter().enumerate() {
        let is_last = i == stmts.len() - 1;
        if is_last {
            if let StmtKind::Expr(expr) = &stmt.kind {
                last_val = compile_expr(ctx, expr);
            } else {
                compile_stmt(ctx, stmt);
            }
        } else {
            compile_stmt(ctx, stmt);
        }
        if ctx
            .builder
            .get_insert_block()
            .unwrap()
            .get_terminator()
            .is_some()
        {
            break;
        }
    }
    last_val
}

fn compile_struct_lit<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    expr: &Expr,
    fields: &[FieldInit],
) -> Option<BasicValueEnum<'ctx>> {
    let result_ty = get_expr_ty(ctx, expr);
    let llvm_ty = ty_to_llvm(ctx, &result_ty);

    // Build the struct value by inserting each field.
    let mut struct_val = llvm_ty.into_struct_type().const_zero();

    // Get field order from TypeEnv if available.
    if let Ty::Struct { def_id, .. } = &result_ty {
        if let Some(type_fields) = ctx.type_env.struct_fields.get(def_id) {
            for field_init in fields {
                // Find the index of this field in the struct definition.
                let idx = type_fields
                    .iter()
                    .position(|(name, _)| name == &field_init.name);
                if let Some(idx) = idx {
                    if let Some(val) = compile_expr(ctx, &field_init.value) {
                        struct_val = ctx
                            .builder
                            .build_insert_value(struct_val, val, idx as u32, &field_init.name)
                            .unwrap()
                            .into_struct_value();
                    }
                }
            }
            return Some(struct_val.into());
        }
    }

    // Fallback: insert fields in order.
    for (i, field_init) in fields.iter().enumerate() {
        if let Some(val) = compile_expr(ctx, &field_init.value) {
            struct_val = ctx
                .builder
                .build_insert_value(struct_val, val, i as u32, &field_init.name)
                .unwrap()
                .into_struct_value();
        }
    }
    Some(struct_val.into())
}

fn compile_tuple_lit<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    elems: &[Expr],
) -> Option<BasicValueEnum<'ctx>> {
    let field_types: Vec<inkwell::types::BasicTypeEnum<'ctx>> = elems
        .iter()
        .filter_map(|e| {
            let ty = get_expr_ty(ctx, e);
            Some(ty_to_llvm(ctx, &ty))
        })
        .collect();
    let tuple_ty = ctx.context.struct_type(&field_types, false);
    let mut tuple_val = tuple_ty.const_zero();
    for (i, elem) in elems.iter().enumerate() {
        if let Some(val) = compile_expr(ctx, elem) {
            tuple_val = ctx
                .builder
                .build_insert_value(tuple_val, val, i as u32, "tuple_elem")
                .unwrap()
                .into_struct_value();
        }
    }
    Some(tuple_val.into())
}

fn compile_match<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    match_expr: &Expr,
    scrutinee: &Expr,
    arms: &[MatchArm],
) -> Option<BasicValueEnum<'ctx>> {
    let scrutinee_val = compile_expr(ctx, scrutinee)?;

    let fn_val = ctx
        .builder
        .get_insert_block()
        .unwrap()
        .get_parent()
        .unwrap();

    let merge_bb = ctx.context.append_basic_block(fn_val, "match_merge");

    let result_ty = get_expr_ty(ctx, match_expr);
    let has_value = !is_void_ty(&result_ty);

    let mut incoming: Vec<(BasicValueEnum<'ctx>, inkwell::basic_block::BasicBlock<'ctx>)> =
        Vec::new();

    for (i, arm) in arms.iter().enumerate() {
        let arm_bb = ctx
            .context
            .append_basic_block(fn_val, &format!("match_arm_{}", i));
        let next_bb = if i + 1 < arms.len() {
            ctx.context
                .append_basic_block(fn_val, &format!("match_test_{}", i + 1))
        } else {
            merge_bb
        };

        // Test the pattern.
        match &arm.pattern.kind {
            PatternKind::Wildcard | PatternKind::Ident(_) => {
                // Always matches.
                ctx.builder.build_unconditional_branch(arm_bb).unwrap();
            }
            PatternKind::Literal(lit_expr) => {
                if let Some(lit_val) = compile_expr(ctx, lit_expr) {
                    let cmp = ctx
                        .builder
                        .build_int_compare(
                            IntPredicate::EQ,
                            scrutinee_val.into_int_value(),
                            lit_val.into_int_value(),
                            "match_cmp",
                        )
                        .unwrap();
                    ctx.builder
                        .build_conditional_branch(cmp, arm_bb, next_bb)
                        .unwrap();
                } else {
                    ctx.builder.build_unconditional_branch(arm_bb).unwrap();
                }
            }
            _ => {
                // For other pattern kinds, just branch unconditionally for now.
                ctx.builder.build_unconditional_branch(arm_bb).unwrap();
            }
        }

        // Compile arm body.
        ctx.builder.position_at_end(arm_bb);

        // Bind pattern variables.
        if let PatternKind::Ident(name) = &arm.pattern.kind {
            let alloca = ctx
                .builder
                .build_alloca(scrutinee_val.get_type(), name)
                .unwrap();
            ctx.builder.build_store(alloca, scrutinee_val).unwrap();
            // Find the DefId for this pattern binding.
            if let Some(def_id) = ctx.resolved.resolutions.get(&arm.pattern.span.start) {
                ctx.locals.insert(*def_id, alloca);
            }
        }

        let arm_val = compile_block_stmts(ctx, &arm.body);
        let arm_terminated = ctx
            .builder
            .get_insert_block()
            .unwrap()
            .get_terminator()
            .is_some();
        let arm_end_bb = ctx.builder.get_insert_block().unwrap();

        if !arm_terminated {
            ctx.builder.build_unconditional_branch(merge_bb).unwrap();
            if has_value {
                if let Some(val) = arm_val {
                    incoming.push((val, arm_end_bb));
                }
            }
        }

        if i + 1 < arms.len() {
            ctx.builder.position_at_end(next_bb);
        }
    }

    ctx.builder.position_at_end(merge_bb);

    if has_value && !incoming.is_empty() {
        let phi = ctx
            .builder
            .build_phi(ty_to_llvm(ctx, &result_ty), "match_val")
            .unwrap();
        let refs: Vec<(&dyn inkwell::values::BasicValue, inkwell::basic_block::BasicBlock)> =
            incoming.iter().map(|(v, bb)| (v as &dyn inkwell::values::BasicValue, *bb)).collect();
        phi.add_incoming(&refs);
        Some(phi.as_basic_value())
    } else {
        None
    }
}

fn compile_assert<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    cond: &Expr,
    _message: Option<&Expr>,
) {
    let cond_val = match compile_expr(ctx, cond) {
        Some(v) => v,
        None => return,
    };

    let cond_int = cond_val.into_int_value();
    let cond_bool = ctx
        .builder
        .build_int_compare(
            IntPredicate::NE,
            cond_int,
            cond_int.get_type().const_zero(),
            "assert_cond",
        )
        .unwrap();

    let fn_val = ctx
        .builder
        .get_insert_block()
        .unwrap()
        .get_parent()
        .unwrap();

    let pass_bb = ctx.context.append_basic_block(fn_val, "assert_pass");
    let fail_bb = ctx.context.append_basic_block(fn_val, "assert_fail");

    ctx.builder
        .build_conditional_branch(cond_bool, pass_bb, fail_bb)
        .unwrap();

    // Fail block: print message and exit.
    ctx.builder.position_at_end(fail_bb);
    build_printf_call(ctx, "assertion failed\n", &[]);
    if let Some(exit_fn) = ctx.module.get_function("exit") {
        ctx.builder
            .build_call(
                exit_fn,
                &[ctx.context.i32_type().const_int(1, false).into()],
                "exit",
            )
            .unwrap();
    }
    ctx.builder.build_unreachable().unwrap();

    ctx.builder.position_at_end(pass_bb);
}
