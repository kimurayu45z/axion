use axion_resolve::def_id::{DefId, SymbolKind};
use axion_types::ty::{PrimTy, Ty};
use axion_syntax::*;
use inkwell::types::BasicType;
use inkwell::values::{BasicMetadataValueEnum, BasicValueEnum, PointerValue};
use inkwell::IntPredicate;
use inkwell::FloatPredicate;
use inkwell::AddressSpace;

use crate::context::CodegenCtx;
use crate::intrinsics::build_printf_call;
use crate::layout::{is_void_ty, ty_to_llvm, ty_to_llvm_metadata, variant_struct_type, enum_max_payload_bytes, build_subst_map};
use crate::stmt::{compile_stmt, bind_pattern_value};

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
        ExprKind::Field { expr: obj, name } => {
            // Check for enum unit variant access: e.g. Color.Red
            let inner_ty = get_expr_ty(ctx, obj);
            if let Ty::Enum { def_id, .. } = &inner_ty {
                // Check if the result type is the enum itself (unit variant) vs Fn (data variant).
                let result_ty = get_expr_ty(ctx, expr);
                if matches!(result_ty, Ty::Enum { .. }) {
                    return compile_enum_unit_variant(ctx, *def_id, expr);
                }
                // If it's a Fn type, this will be wrapped in a Call — handled there.
                return None;
            }
            compile_field(ctx, expr, obj, name)
        }
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
        ExprKind::For { pattern, iter, body } => {
            compile_for(ctx, pattern, iter, body);
            None
        }
        ExprKind::Range { start, end } => {
            match (start, end) {
                (Some(s), Some(e)) => {
                    let start_val = compile_expr(ctx, s)?;
                    let end_val = compile_expr(ctx, e)?;
                    let range_ty = get_expr_ty(ctx, expr);
                    let llvm_ty = ty_to_llvm(ctx, &range_ty);
                    let mut struct_val = llvm_ty.into_struct_type().const_zero();
                    struct_val = ctx.builder.build_insert_value(struct_val, start_val, 0, "range_start")
                        .unwrap().into_struct_value();
                    struct_val = ctx.builder.build_insert_value(struct_val, end_val, 1, "range_end")
                        .unwrap().into_struct_value();
                    Some(struct_val.into())
                }
                _ => None, // Partial ranges only valid inside Index
            }
        }
        ExprKind::Closure { params, body } => compile_closure(ctx, expr, params, body),
        ExprKind::Assert { cond, message } => {
            compile_assert(ctx, cond, message.as_deref());
            None
        }
        ExprKind::Ref(inner) => {
            compile_expr(ctx, inner)
        }
        ExprKind::StringInterp { parts } => compile_string_interp(ctx, parts),
        ExprKind::TypeApp { expr: inner, .. } => compile_expr(ctx, inner),
        ExprKind::ArrayLit(elems) => compile_array_lit(ctx, expr, elems),
        ExprKind::Index { expr: arr_expr, index } => compile_index(ctx, expr, arr_expr, index),
        ExprKind::Cast { expr: inner, target } => compile_cast(ctx, inner, target),
        ExprKind::SizeOf(type_expr) => compile_sizeof(ctx, type_expr),
        ExprKind::MapLit(_) | ExprKind::SetLit(_) => None,
        ExprKind::Handle { expr: inner, .. } => compile_expr(ctx, inner),
        ExprKind::Try(_) | ExprKind::Await(_) => None,
    }
}

/// Get the address (pointer) of an expression, for pass-by-reference.
pub fn compile_expr_addr<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    expr: &Expr,
) -> Option<PointerValue<'ctx>> {
    match &expr.kind {
        ExprKind::Ident(_) => {
            let def_id = ctx.resolved.resolutions.get(&expr.span.start)?;
            ctx.locals.get(def_id).copied()
        }
        ExprKind::Field { expr: obj, name: _ } => {
            // GEP into struct field.
            let obj_ptr = compile_expr_addr(ctx, obj)?;
            let field_idx = ctx.type_check.field_resolutions.get(&expr.span.start)?;
            let llvm_ty = get_obj_llvm_ty(ctx, obj);
            let gep = ctx
                .builder
                .build_struct_gep(llvm_ty, obj_ptr, *field_idx as u32, "field_addr")
                .ok()?;
            Some(gep)
        }
        _ => {
            // Fallback: compile to value, store in temp alloca.
            let val = compile_expr(ctx, expr)?;
            let alloca = ctx
                .builder
                .build_alloca(val.get_type(), "tmp_ref")
                .unwrap();
            ctx.builder.build_store(alloca, val).unwrap();
            Some(alloca)
        }
    }
}

/// Get the LLVM type for an object expression, resolving via DefId when possible
/// to avoid span collisions in expr_types.
pub fn get_obj_llvm_ty<'ctx>(
    ctx: &CodegenCtx<'ctx>,
    obj: &Expr,
) -> inkwell::types::BasicTypeEnum<'ctx> {
    // For identifiers, resolve through DefId to avoid span collision.
    if let ExprKind::Ident(_) = &obj.kind {
        if let Some(&def_id) = ctx.resolved.resolutions.get(&obj.span.start) {
            // Use local_types if available (already the correct LLVM type).
            if let Some(&llvm_ty) = ctx.local_types.get(&def_id) {
                return llvm_ty;
            }
            // Otherwise resolve through type_env.
            if let Some(info) = ctx.type_env.defs.get(&def_id) {
                return ty_to_llvm(ctx, &info.ty);
            }
        }
    }
    // Fallback to get_expr_ty.
    ty_to_llvm(ctx, &get_expr_ty(ctx, obj))
}

fn compile_int_lit<'ctx>(
    ctx: &CodegenCtx<'ctx>,
    expr: &Expr,
    val: i128,
) -> Option<BasicValueEnum<'ctx>> {
    let ty = get_expr_ty(ctx, expr);
    match &ty {
        Ty::Prim(PrimTy::I8) | Ty::Prim(PrimTy::U8) => {
            Some(ctx.context.i8_type().const_int(val as u64, false).into())
        }
        Ty::Prim(PrimTy::I16) | Ty::Prim(PrimTy::U16) => {
            Some(ctx.context.i16_type().const_int(val as u64, false).into())
        }
        Ty::Prim(PrimTy::I32) | Ty::Prim(PrimTy::U32) => {
            Some(ctx.context.i32_type().const_int(val as u64, false).into())
        }
        Ty::Prim(PrimTy::I128) | Ty::Prim(PrimTy::U128) => {
            Some(ctx.context.i128_type().const_int(val as u64, false).into())
        }
        Ty::Prim(PrimTy::F32) => {
            Some(ctx.context.f32_type().const_float(val as f64).into())
        }
        Ty::Prim(PrimTy::F64) => {
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

fn compile_cast<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    inner: &Expr,
    _target: &TypeExpr,
) -> Option<BasicValueEnum<'ctx>> {
    let val = compile_expr(ctx, inner)?;
    let source_ty = get_expr_ty(ctx, inner);
    // The cast expression's overall type is the target type (already computed by infer).
    // We recover it by looking up the parent expr's type. Since we don't have the parent
    // expr here, we use the TypeExpr to determine the target. But since lower_type_expr
    // is pub(crate) in axion_types, we reconstruct the target Ty from the inferred type
    // environment. The target_ty is whatever the type system says the Cast expr produces.
    // Actually the caller already resolved types — we need the target from the overall
    // expression type. Let's use a simpler approach: determine from the source and target.

    // For now, resolve the target type by matching on _target TypeExpr.
    let mut target_ty = resolve_cast_target_ty(ctx, _target);
    if !ctx.current_subst.is_empty() {
        target_ty = axion_mono::specialize::substitute(&target_ty, &ctx.current_subst);
    }
    let target_llvm = ty_to_llvm(ctx, &target_ty);

    match (&source_ty, &target_ty) {
        // Ptr -> integer: ptrtoint
        (Ty::Ptr(_), Ty::Prim(p)) if p.is_integer() => {
            let int_ty = target_llvm.into_int_type();
            Some(ctx.builder.build_ptr_to_int(val.into_pointer_value(), int_ty, "ptrtoint").unwrap().into())
        }
        // integer -> Ptr: inttoptr
        (Ty::Prim(p), Ty::Ptr(_)) if p.is_integer() => {
            let ptr_ty = ctx.context.ptr_type(AddressSpace::default());
            Some(ctx.builder.build_int_to_ptr(val.into_int_value(), ptr_ty, "inttoptr").unwrap().into())
        }
        // Ptr -> Ptr: no-op (LLVM opaque pointers)
        (Ty::Ptr(_), Ty::Ptr(_)) => Some(val),
        // int -> int: trunc or extend
        (Ty::Prim(src_p), Ty::Prim(dst_p)) if src_p.is_integer() && dst_p.is_integer() => {
            let src_bits = val.into_int_value().get_type().get_bit_width();
            let dst_ty = target_llvm.into_int_type();
            let dst_bits = dst_ty.get_bit_width();
            if src_bits == dst_bits {
                Some(val)
            } else if src_bits < dst_bits {
                if src_p.is_signed() {
                    Some(ctx.builder.build_int_s_extend(val.into_int_value(), dst_ty, "sext").unwrap().into())
                } else {
                    Some(ctx.builder.build_int_z_extend(val.into_int_value(), dst_ty, "zext").unwrap().into())
                }
            } else {
                Some(ctx.builder.build_int_truncate(val.into_int_value(), dst_ty, "trunc").unwrap().into())
            }
        }
        // float -> int
        (Ty::Prim(src_p), Ty::Prim(dst_p)) if src_p.is_float() && dst_p.is_integer() => {
            let dst_ty = target_llvm.into_int_type();
            if dst_p.is_signed() {
                Some(ctx.builder.build_float_to_signed_int(val.into_float_value(), dst_ty, "fptosi").unwrap().into())
            } else {
                Some(ctx.builder.build_float_to_unsigned_int(val.into_float_value(), dst_ty, "fptoui").unwrap().into())
            }
        }
        // int -> float
        (Ty::Prim(src_p), Ty::Prim(dst_p)) if src_p.is_integer() && dst_p.is_float() => {
            let dst_ty = target_llvm.into_float_type();
            if src_p.is_signed() {
                Some(ctx.builder.build_signed_int_to_float(val.into_int_value(), dst_ty, "sitofp").unwrap().into())
            } else {
                Some(ctx.builder.build_unsigned_int_to_float(val.into_int_value(), dst_ty, "uitofp").unwrap().into())
            }
        }
        // float -> float
        (Ty::Prim(src_p), Ty::Prim(dst_p)) if src_p.is_float() && dst_p.is_float() => {
            let dst_ty = target_llvm.into_float_type();
            Some(ctx.builder.build_float_cast(val.into_float_value(), dst_ty, "fpcast").unwrap().into())
        }
        // Fallback: bitcast / no-op
        _ => Some(val),
    }
}

/// Resolve the target type of a cast expression from the TypeExpr.
fn resolve_cast_target_ty(ctx: &CodegenCtx, target: &TypeExpr) -> Ty {
    match target {
        TypeExpr::Named { name, args, span } => {
            if name == "Ptr" {
                let inner = args.first()
                    .map(|a| resolve_cast_target_ty(ctx, a))
                    .unwrap_or(Ty::Unit);
                return Ty::Ptr(Box::new(inner));
            }
            if let Some(prim) = PrimTy::from_name(name) {
                return Ty::Prim(prim);
            }
            if let Some(&def_id) = ctx.resolved.resolutions.get(&span.start) {
                let lowered_args: Vec<Ty> = args.iter()
                    .map(|a| resolve_cast_target_ty(ctx, a))
                    .collect();
                if let Some(sym) = ctx.resolved.symbols.iter().find(|s| s.def_id == def_id) {
                    match sym.kind {
                        SymbolKind::Struct => return Ty::Struct { def_id, type_args: lowered_args },
                        SymbolKind::Enum => return Ty::Enum { def_id, type_args: lowered_args },
                        SymbolKind::TypeParam => return Ty::Param(def_id),
                        _ => {}
                    }
                }
            }
            Ty::Error
        }
        TypeExpr::Tuple { elements, .. } => {
            if elements.is_empty() {
                Ty::Unit
            } else {
                Ty::Tuple(elements.iter().map(|e| resolve_cast_target_ty(ctx, e)).collect())
            }
        }
        _ => Ty::Error,
    }
}

fn compile_sizeof<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    type_expr: &TypeExpr,
) -> Option<BasicValueEnum<'ctx>> {
    let mut ty = resolve_cast_target_ty(ctx, type_expr);
    if !ctx.current_subst.is_empty() {
        ty = axion_mono::specialize::substitute(&ty, &ctx.current_subst);
    }
    let llvm_ty = ty_to_llvm(ctx, &ty);
    let size = llvm_ty.size_of().unwrap();
    let cast = ctx.builder.build_int_cast(size, ctx.context.i64_type(), "sizeof").unwrap();
    Some(cast.into())
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

/// Get the String struct Ty from the resolved symbols.
fn get_string_struct_ty_codegen<'ctx>(ctx: &CodegenCtx<'ctx>) -> Option<Ty> {
    ctx.resolved
        .symbols
        .iter()
        .find(|s| s.name == "String" && matches!(s.kind, SymbolKind::Struct))
        .map(|s| Ty::Struct { def_id: s.def_id, type_args: vec![] })
}

/// Get the type name for method/constructor lookups (mirrors type checker logic).
fn get_type_name_for_method_ctx<'ctx>(ctx: &CodegenCtx<'ctx>, ty: &Ty) -> Option<String> {
    match ty {
        Ty::Struct { def_id, .. } | Ty::Enum { def_id, .. } => {
            ctx.resolved
                .symbols
                .iter()
                .find(|s| s.def_id == *def_id)
                .map(|s| s.name.clone())
        }
        Ty::Prim(p) => Some(format!("{}", p)),
        _ => None,
    }
}

/// Check if an expression refers to a type definition (for variant construction),
/// not to a value/instance (for method calls).
fn is_type_level_expr<'ctx>(ctx: &CodegenCtx<'ctx>, expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Ident(_) => {
            if let Some(&def_id) = ctx.resolved.resolutions.get(&expr.span.start) {
                ctx.resolved
                    .symbols
                    .iter()
                    .find(|s| s.def_id == def_id)
                    .map(|s| matches!(s.kind, SymbolKind::Struct | SymbolKind::Enum))
                    .unwrap_or(false)
            } else {
                false
            }
        }
        ExprKind::TypeApp { expr: inner, .. } => is_type_level_expr(ctx, inner),
        _ => false,
    }
}

/// Resolve the type of an expression by walking the AST structure, avoiding span-collision
/// in expr_types. For Ident, uses local_tys/type_env. For Field, recurses on the object
/// and looks up the field type from struct definition. Falls back to get_expr_ty.
pub fn resolve_inner_ty<'ctx>(ctx: &CodegenCtx<'ctx>, expr: &Expr) -> Ty {
    match &expr.kind {
        ExprKind::Ident(_) => {
            if let Some(&def_id) = ctx.resolved.resolutions.get(&expr.span.start) {
                if let Some(ty) = ctx.local_tys.get(&def_id) {
                    return ty.clone();
                }
                if let Some(info) = ctx.type_env.defs.get(&def_id) {
                    let ty = info.ty.clone();
                    if !ctx.current_subst.is_empty() {
                        return axion_mono::specialize::substitute(&ty, &ctx.current_subst);
                    }
                    return ty;
                }
            }
            get_expr_ty(ctx, expr)
        }
        ExprKind::Field { expr: obj, name } => {
            let obj_ty = resolve_inner_ty(ctx, obj);
            // Look up the field type from the struct definition.
            if let Ty::Struct { def_id, type_args } = &obj_ty {
                if let Some(fields) = ctx.type_env.struct_fields.get(def_id) {
                    if let Some((_, field_ty)) = fields.iter().find(|(fname, _)| fname == name) {
                        let mut result_ty = field_ty.clone();
                        // Apply type_args substitution.
                        if !type_args.is_empty() {
                            // Collect Param DefIds from all field types to build subst.
                            let mut param_defs = Vec::new();
                            for (_, fty) in fields {
                                axion_mono::specialize::collect_param_def_ids(fty, &mut param_defs);
                            }
                            // Deduplicate preserving order.
                            let mut seen = std::collections::HashSet::new();
                            param_defs.retain(|d| seen.insert(*d));
                            // Build subst: param DefId → concrete type arg.
                            let mut subst = std::collections::HashMap::new();
                            for (pd, ta) in param_defs.iter().zip(type_args.iter()) {
                                subst.insert(*pd, ta.clone());
                            }
                            result_ty = axion_mono::specialize::substitute(&result_ty, &subst);
                        }
                        if !ctx.current_subst.is_empty() {
                            result_ty = axion_mono::specialize::substitute(&result_ty, &ctx.current_subst);
                        }
                        return result_ty;
                    }
                }
            }
            // For Ptr[T], built-in field methods don't apply here (they're methods not fields).
            get_expr_ty(ctx, expr)
        }
        ExprKind::TypeApp { expr: inner, .. } => {
            // TypeApp on a type name: Array[i64] → Struct { type_args: [i64] }
            resolve_inner_ty(ctx, inner)
        }
        _ => get_expr_ty(ctx, expr),
    }
}

pub fn get_expr_ty<'ctx>(ctx: &CodegenCtx<'ctx>, expr: &Expr) -> Ty {
    let ty = ctx
        .type_check
        .expr_types
        .get(&expr.span.start)
        .cloned()
        .unwrap_or(Ty::Unit);
    if ctx.current_subst.is_empty() {
        ty
    } else {
        axion_mono::specialize::substitute(&ty, &ctx.current_subst)
    }
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
        let mut ty = ctx.resolved
            .resolutions
            .get(&lhs.span.start)
            .and_then(|def_id| {
                ctx.local_tys.get(def_id).cloned().or_else(|| {
                    ctx.type_env.defs.get(def_id).map(|info| info.ty.clone())
                })
            })
            .unwrap_or_else(|| get_expr_ty(ctx, lhs));
        // Apply current substitution for monomorphized generic functions.
        if !ctx.current_subst.is_empty() {
            ty = axion_mono::specialize::substitute(&ty, &ctx.current_subst);
        }
        ty
    } else if matches!(&lhs.kind, ExprKind::StringLit(_)) {
        Ty::Prim(PrimTy::Str)
    } else if matches!(&lhs.kind, ExprKind::StringInterp { .. }) {
        // StringInterp (backtick template literals) produces String struct
        get_string_struct_ty_codegen(ctx).unwrap_or(Ty::Prim(PrimTy::Str))
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

    // String + String → concat
    if matches!(op, BinOp::Add) {
        if let Some(name) = get_type_name_for_method_ctx(ctx, &lhs_ty) {
            if name == "String" {
                return compile_string_concat(ctx, lhs_val, rhs_val);
            }
        }
    }

    // str + str → String (concatenation)
    if matches!(op, BinOp::Add) && matches!(lhs_ty, Ty::Prim(PrimTy::Str)) {
        return compile_str_concat(ctx, lhs_val, rhs_val);
    }

    // String == / != → memcmp comparison
    if matches!(op, BinOp::Eq | BinOp::NotEq) {
        if let Some(name) = get_type_name_for_method_ctx(ctx, &lhs_ty) {
            if name == "String" {
                return compile_string_compare(ctx, op, lhs_val, rhs_val);
            }
        }
    }

    // str == / != → memcmp comparison
    if matches!(op, BinOp::Eq | BinOp::NotEq) && matches!(lhs_ty, Ty::Prim(PrimTy::Str)) {
        return compile_str_compare(ctx, op, lhs_val, rhs_val);
    }

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

    // Check for enum variant construction: Shape.Circle(5.0)
    // or method call: obj.method(args)
    if let ExprKind::Field { expr: inner, name: field_name } = &func.kind {
        // Resolve inner type via definition to avoid span collision with the Call/Field expr.
        // First try method_receiver_types (populated by type checker, avoids span collision).
        let inner_ty = if let Some(recv_ty) = ctx.type_check.method_receiver_types.get(&call_expr.span.start) {
            let ty = recv_ty.clone();
            if ctx.current_subst.is_empty() { ty } else { axion_mono::specialize::substitute(&ty, &ctx.current_subst) }
        } else if matches!(&inner.kind, ExprKind::StringLit(_)) {
            Ty::Prim(PrimTy::Str)
        } else if matches!(&inner.kind, ExprKind::StringInterp { .. }) {
            get_string_struct_ty_codegen(ctx).unwrap_or(Ty::Prim(PrimTy::Str))
        } else {
            resolve_inner_ty(ctx, inner)
        };
        // Enum variant construction only applies when the inner expr refers to the enum
        // type itself (e.g., Option[i64].Some(10)), not to an instance (e.g., x.method()).
        let is_type_access = is_type_level_expr(ctx, inner);
        if is_type_access {
            if let Ty::Enum { def_id, .. } = &inner_ty {
                return compile_enum_data_variant(ctx, *def_id, func, args);
            }
        }
        // Ptr[T] intrinsic methods
        if let Ty::Ptr(ref inner_pointee) = inner_ty {
            let elem_llvm_ty = ty_to_llvm(ctx, inner_pointee);
            match field_name.as_str() {
                "read" => {
                    let ptr = compile_expr(ctx, inner)?.into_pointer_value();
                    return Some(ctx.builder.build_load(elem_llvm_ty, ptr, "ptr_read").unwrap());
                }
                "write" => {
                    let ptr = compile_expr(ctx, inner)?.into_pointer_value();
                    let val = compile_expr(ctx, &args[0].expr)?;
                    ctx.builder.build_store(ptr, val).unwrap();
                    return None;
                }
                "offset" => {
                    let ptr = compile_expr(ctx, inner)?.into_pointer_value();
                    let offset_val = compile_expr(ctx, &args[0].expr)?.into_int_value();
                    let new_ptr = unsafe {
                        ctx.builder.build_in_bounds_gep(elem_llvm_ty, ptr, &[offset_val], "ptr_offset").unwrap()
                    };
                    return Some(new_ptr.into());
                }
                "is_null" => {
                    let ptr = compile_expr(ctx, inner)?.into_pointer_value();
                    let result = ctx.builder.build_is_null(ptr, "is_null").unwrap();
                    let i8_val = ctx.builder.build_int_z_extend(result, ctx.context.i8_type(), "bool_ext").unwrap();
                    return Some(i8_val.into());
                }
                _ => {}
            }
        }

        // String intrinsic methods
        if let Some(type_name) = get_type_name_for_method_ctx(ctx, &inner_ty) {
            if type_name == "String" {
                match field_name.as_str() {
                    "new" if is_type_access => return compile_string_new(ctx),
                    "from" if is_type_access => return compile_string_from(ctx, args),
                    "len" => return compile_string_len(ctx, inner),
                    "is_empty" => return compile_string_is_empty(ctx, inner),
                    "push" => return compile_string_push(ctx, inner, args),
                    "as_str" => return compile_string_as_str(ctx, inner),
                    "byte_at" => return compile_string_byte_at(ctx, inner, args),
                    "contains" => return compile_string_contains(ctx, inner, args),
                    "starts_with" => return compile_string_starts_with(ctx, inner, args),
                    "ends_with" => return compile_string_ends_with(ctx, inner, args),
                    "substring" => return compile_string_substring(ctx, inner, args),
                    "clear" => return compile_string_clear(ctx, inner),
                    "repeat" => return compile_string_repeat(ctx, inner, args),
                    "trim" => return compile_string_trim(ctx, inner),
                    "trim_start" => return compile_string_trim_start(ctx, inner),
                    "trim_end" => return compile_string_trim_end(ctx, inner),
                    _ => {}
                }
            }
        }

        // HashMap[K, V] intrinsic methods
        if let Some(type_name) = get_type_name_for_method_ctx(ctx, &inner_ty) {
            if type_name == "HashMap" {
                let (key_ty, val_ty) = match &inner_ty {
                    Ty::Struct { type_args, .. } if type_args.len() >= 2 => {
                        (type_args[0].clone(), type_args[1].clone())
                    }
                    _ => (Ty::Prim(PrimTy::I64), Ty::Prim(PrimTy::I64)),
                };
                match field_name.as_str() {
                    "new" if is_type_access => return compile_hashmap_new(ctx),
                    "len" => return compile_hashmap_len(ctx, inner),
                    "is_empty" => return compile_hashmap_is_empty(ctx, inner),
                    "insert" => return compile_hashmap_insert(ctx, inner, args, &key_ty, &val_ty),
                    "get" => return compile_hashmap_get(ctx, call_expr, inner, args, &key_ty, &val_ty),
                    "contains_key" => return compile_hashmap_contains_key(ctx, inner, args, &key_ty),
                    "remove" => return compile_hashmap_remove(ctx, call_expr, inner, args, &key_ty, &val_ty),
                    _ => {}
                }
            }
        }

        // FixedArray built-in method calls
        if let Ty::Array { elem: _, len } = inner_ty {
            match field_name.as_str() {
                "len" => {
                    let len_val = ctx.context.i64_type().const_int(len, false);
                    return Some(len_val.into());
                }
                "first" => {
                    let arr_val = compile_expr(ctx, inner)?;
                    let extracted = ctx
                        .builder
                        .build_extract_value(arr_val.into_array_value(), 0, "first")
                        .unwrap();
                    return Some(extracted);
                }
                "last" => {
                    let arr_val = compile_expr(ctx, inner)?;
                    let extracted = ctx
                        .builder
                        .build_extract_value(
                            arr_val.into_array_value(),
                            (len - 1) as u32,
                            "last",
                        )
                        .unwrap();
                    return Some(extracted);
                }
                _ => {}
            }
        }
        // Slice built-in method calls
        if let Ty::Slice(ref elem) = inner_ty {
            match field_name.as_str() {
                "len" => {
                    let slice_val = compile_expr(ctx, inner)?;
                    let len = ctx.builder.build_extract_value(
                        slice_val.into_struct_value(), 1, "slice_len"
                    ).unwrap();
                    return Some(len.into());
                }
                "first" => {
                    let slice_val = compile_expr(ctx, inner)?;
                    let ptr = ctx.builder.build_extract_value(slice_val.into_struct_value(), 0, "slice_ptr")
                        .unwrap().into_pointer_value();
                    let elem_llvm_ty = ty_to_llvm(ctx, elem);
                    let zero = ctx.context.i64_type().const_zero();
                    let elem_ptr = unsafe {
                        ctx.builder.build_in_bounds_gep(elem_llvm_ty, ptr, &[zero], "first_ptr").unwrap()
                    };
                    return Some(ctx.builder.build_load(elem_llvm_ty, elem_ptr, "first").unwrap());
                }
                "last" => {
                    let slice_val = compile_expr(ctx, inner)?;
                    let ptr = ctx.builder.build_extract_value(slice_val.into_struct_value(), 0, "slice_ptr")
                        .unwrap().into_pointer_value();
                    let len = ctx.builder.build_extract_value(slice_val.into_struct_value(), 1, "slice_len")
                        .unwrap().into_int_value();
                    let elem_llvm_ty = ty_to_llvm(ctx, elem);
                    let one = ctx.context.i64_type().const_int(1, false);
                    let last_idx = ctx.builder.build_int_sub(len, one, "last_idx").unwrap();
                    let elem_ptr = unsafe {
                        ctx.builder.build_in_bounds_gep(elem_llvm_ty, ptr, &[last_idx], "last_ptr").unwrap()
                    };
                    return Some(ctx.builder.build_load(elem_llvm_ty, elem_ptr, "last").unwrap());
                }
                "is_empty" => {
                    let slice_val = compile_expr(ctx, inner)?;
                    let len = ctx.builder.build_extract_value(slice_val.into_struct_value(), 1, "slice_len")
                        .unwrap().into_int_value();
                    let zero = ctx.context.i64_type().const_zero();
                    let cmp = ctx.builder.build_int_compare(IntPredicate::EQ, len, zero, "is_empty").unwrap();
                    return Some(cmp.into());
                }
                _ => {}
            }
        }

        // str built-in method calls
        if let Ty::Prim(PrimTy::Str) = inner_ty {
            match field_name.as_str() {
                "len" => return compile_str_len(ctx, inner),
                "is_empty" => return compile_str_is_empty(ctx, inner),
                "byte_at" => return compile_str_byte_at(ctx, inner, args),
                "contains" => return compile_str_contains(ctx, inner, args),
                "starts_with" => return compile_str_starts_with(ctx, inner, args),
                "ends_with" => return compile_str_ends_with(ctx, inner, args),
                "slice" | "substring" => return compile_str_slice(ctx, inner, args),
                "to_string" => return compile_str_to_string(ctx, inner),
                "trim" => return compile_str_trim(ctx, inner),
                "trim_start" => return compile_str_trim_start(ctx, inner),
                "trim_end" => return compile_str_trim_end(ctx, inner),
                _ => {}
            }
        }

        // Check for method call.
        if let Some(type_name) = get_type_name_for_method_ctx(ctx, &inner_ty) {
            let method_key = format!("{}.{}", type_name, field_name);
            let method_def_id = ctx
                .resolved
                .symbols
                .iter()
                .find(|s| s.name == method_key && matches!(s.kind, SymbolKind::Method | SymbolKind::Constructor))
                .map(|s| s.def_id);
            if let Some(def_id) = method_def_id {
                // Try monomorphized version first for generic receiver types.
                let type_args = match &inner_ty {
                    Ty::Enum { type_args, .. } | Ty::Struct { type_args, .. } => type_args.clone(),
                    _ => vec![],
                };
                let mono_fn = if !type_args.is_empty() {
                    if let Some(mono) = ctx.mono_output {
                        mono.lookup(def_id, &type_args)
                            .and_then(|mangled| ctx.mono_fn_values.get(mangled).copied())
                    } else {
                        None
                    }
                } else {
                    None
                };

                let fn_value_opt = mono_fn.or_else(|| ctx.functions.get(&def_id).copied());


                if let Some(fn_value) = fn_value_opt {
                    // Compile receiver (self) as first arg.
                    let mut compiled_args: Vec<BasicMetadataValueEnum> = Vec::new();
                    // Check if receiver should be passed by reference.
                    let recv_mod = ctx.type_env.receiver_modifiers.get(&def_id).cloned();
                    let pass_by_ref = matches!(recv_mod, Some(ReceiverModifier::Mut) | Some(ReceiverModifier::Borrow));
                    if pass_by_ref {
                        if let Some(ptr) = compile_expr_addr(ctx, inner) {
                            compiled_args.push(ptr.into());
                        }
                    } else if let Some(receiver) = compile_expr(ctx, inner) {
                        compiled_args.push(receiver.into());
                    }
                    for arg in args {
                        if let Some(val) = compile_expr(ctx, &arg.expr) {
                            compiled_args.push(val.into());
                        }
                    }
                    let ret_ty = get_expr_ty(ctx, call_expr);

                    if is_void_ty(&ret_ty) {
                        ctx.builder
                            .build_call(fn_value, &compiled_args, "mcall")
                            .unwrap();
                        return None;
                    } else {
                        let call_val = ctx
                            .builder
                            .build_call(fn_value, &compiled_args, "mcall")
                            .unwrap();
                        return call_val.try_as_basic_value().left();
                    }
                }
            }
        }
    }

    // Check for method call with turbofish: x.method[U](...)
    // where func is TypeApp { expr: Field { expr: inner, name }, type_args }
    if let ExprKind::TypeApp { expr: type_app_inner, type_args: turbo_type_args } = &func.kind {
        if let ExprKind::Field { expr: inner, name: field_name } = &type_app_inner.kind {
            let inner_ty = resolve_inner_ty(ctx, inner);
            if let Some(type_name) = get_type_name_for_method_ctx(ctx, &inner_ty) {
                let method_key = format!("{}.{}", type_name, field_name);
                let method_def_id = ctx
                    .resolved
                    .symbols
                    .iter()
                    .find(|s| s.name == method_key && matches!(s.kind, SymbolKind::Method | SymbolKind::Constructor))
                    .map(|s| s.def_id);
                if let Some(def_id) = method_def_id {
                    // Combine receiver type_args with turbofish type_args.
                    let mut type_args = match &inner_ty {
                        Ty::Enum { type_args, .. } | Ty::Struct { type_args, .. } => type_args.clone(),
                        _ => vec![],
                    };
                    for ta in turbo_type_args {
                        let ta_ty = lower_type_arg_codegen(ta, ctx.resolved);
                        type_args.push(ta_ty);
                    }
                    let mono_fn = if !type_args.is_empty() {
                        if let Some(mono) = ctx.mono_output {
                            mono.lookup(def_id, &type_args)
                                .and_then(|mangled| ctx.mono_fn_values.get(mangled).copied())
                        } else {
                            None
                        }
                    } else {
                        None
                    };
                    let fn_value_opt = mono_fn.or_else(|| ctx.functions.get(&def_id).copied());
                    if let Some(fn_value) = fn_value_opt {
                        let mut compiled_args: Vec<BasicMetadataValueEnum> = Vec::new();
                        let recv_mod = ctx.type_env.receiver_modifiers.get(&def_id).cloned();
                        let pass_by_ref = matches!(recv_mod, Some(ReceiverModifier::Mut) | Some(ReceiverModifier::Borrow));
                        if pass_by_ref {
                            if let Some(ptr) = compile_expr_addr(ctx, inner) {
                                compiled_args.push(ptr.into());
                            }
                        } else if let Some(receiver) = compile_expr(ctx, inner) {
                            compiled_args.push(receiver.into());
                        }
                        for arg in args {
                            if let Some(val) = compile_expr(ctx, &arg.expr) {
                                compiled_args.push(val.into());
                            }
                        }
                        let ret_ty = get_expr_ty(ctx, call_expr);
                        if is_void_ty(&ret_ty) {
                            ctx.builder
                                .build_call(fn_value, &compiled_args, "mcall")
                                .unwrap();
                            return None;
                        } else {
                            let call_val = ctx
                                .builder
                                .build_call(fn_value, &compiled_args, "mcall")
                                .unwrap();
                            return call_val.try_as_basic_value().left();
                        }
                    }
                }
            }
        }
    }

    // Check for monomorphized TypeApp call: f[T](...)
    if let ExprKind::TypeApp { expr: inner, type_args } = &func.kind {
        if let Some(specialized_fn) = resolve_mono_call(ctx, inner, type_args) {
            // Compile arguments.
            let mut compiled_args: Vec<BasicMetadataValueEnum> = Vec::new();
            for arg in args {
                if let Some(val) = compile_expr(ctx, &arg.expr) {
                    compiled_args.push(val.into());
                }
            }
            let ret_ty = get_expr_ty(ctx, call_expr);
            if is_void_ty(&ret_ty) {
                ctx.builder
                    .build_call(specialized_fn, &compiled_args, "call")
                    .unwrap();
                return None;
            } else {
                let call_val = ctx
                    .builder
                    .build_call(specialized_fn, &compiled_args, "call")
                    .unwrap();
                return call_val.try_as_basic_value().left();
            }
        }
    }

    // Resolve the function DefId.
    let def_id = match &func.kind {
        ExprKind::Ident(_) => ctx.resolved.resolutions.get(&func.span.start).copied(),
        _ => None,
    };

    let fn_value = def_id.and_then(|did| ctx.functions.get(&did).copied());

    // Compile arguments.
    let mut compiled_args: Vec<BasicMetadataValueEnum> = Vec::new();
    for arg in args {
        if let Some(val) = compile_expr(ctx, &arg.expr) {
            compiled_args.push(val.into());
        }
    }

    // Check if return type is void.
    let ret_ty = get_expr_ty(ctx, call_expr);

    if let Some(fn_value) = fn_value {
        // Direct call to a known function.
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
    } else {
        // Indirect call: the callee is a variable holding a function pointer
        // or a capturing closure struct { fn_ptr, env_ptr }.
        // Note: we cannot use get_expr_ty(func) because the call expr and func ident
        // share the same span.start, so expr_types would give the call result type.
        // Instead, look up the callee's type via its DefId in type_env, or reconstruct
        // the Fn type from the call arg types and return type.
        let callee_ty = def_id
            .and_then(|did| ctx.type_env.defs.get(&did))
            .map(|info| info.ty.clone())
            .unwrap_or_else(|| {
                // Reconstruct Fn type from arg types and return type.
                let arg_tys: Vec<Ty> = args.iter().map(|a| get_expr_ty(ctx, &a.expr)).collect();
                Ty::Fn { params: arg_tys, ret: Box::new(ret_ty.clone()) }
            });

        // Unwrap the function through TypeApp if needed.
        let actual_func = match &func.kind {
            ExprKind::TypeApp { expr: inner, .. } => inner.as_ref(),
            _ => func,
        };

        let callee_val = compile_expr(ctx, actual_func)?;

        // Build LLVM function type from the callee type.
        if let Ty::Fn { params, ret } = &callee_ty {
            // Check if callee is a capturing closure struct { fn_ptr, env_ptr }
            // by checking if the LLVM value is a struct (not a pointer).
            if callee_val.is_struct_value() {
                let closure_struct = callee_val.into_struct_value();
                let fn_ptr = ctx
                    .builder
                    .build_extract_value(closure_struct, 0, "closure_fn")
                    .unwrap()
                    .into_pointer_value();
                let env_ptr = ctx
                    .builder
                    .build_extract_value(closure_struct, 1, "closure_env")
                    .unwrap();

                // Build fn type with env_ptr as first arg.
                let ptr_ty = ctx.context.ptr_type(AddressSpace::default());
                let mut fn_param_types: Vec<inkwell::types::BasicMetadataTypeEnum> = vec![ptr_ty.into()];
                for t in params {
                    fn_param_types.push(ty_to_llvm_metadata(ctx, t));
                }

                let fn_type = if is_void_ty(ret) {
                    ctx.context.void_type().fn_type(&fn_param_types, false)
                } else {
                    ty_to_llvm(ctx, ret).fn_type(&fn_param_types, false)
                };

                // Prepend env_ptr to args.
                let mut full_args: Vec<BasicMetadataValueEnum> = vec![env_ptr.into()];
                full_args.extend(compiled_args);

                let call_val = ctx
                    .builder
                    .build_indirect_call(fn_type, fn_ptr, &full_args, "closure_call")
                    .unwrap();

                if is_void_ty(&ret_ty) {
                    None
                } else {
                    call_val.try_as_basic_value().left()
                }
            } else {
                // Non-capturing closure or function pointer: simple indirect call.
                let fn_ptr = callee_val.into_pointer_value();

                let param_types: Vec<inkwell::types::BasicMetadataTypeEnum> = params
                    .iter()
                    .map(|t| ty_to_llvm_metadata(ctx, t))
                    .collect();

                let fn_type = if is_void_ty(ret) {
                    ctx.context.void_type().fn_type(&param_types, false)
                } else {
                    ty_to_llvm(ctx, ret).fn_type(&param_types, false)
                };

                let call_val = ctx
                    .builder
                    .build_indirect_call(fn_type, fn_ptr, &compiled_args, "indirect_call")
                    .unwrap();

                if is_void_ty(&ret_ty) {
                    None
                } else {
                    call_val.try_as_basic_value().left()
                }
            }
        } else {
            None
        }
    }
}

/// Compile a closure expression.
///
/// Non-capturing closures are compiled as hidden LLVM functions and return a function pointer.
/// Capturing closures allocate an environment struct on the heap and return a {fn_ptr, env_ptr} pair.
fn compile_closure<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    expr: &Expr,
    params: &[ClosureParam],
    body: &[Stmt],
) -> Option<BasicValueEnum<'ctx>> {
    let closure_ty = get_expr_ty(ctx, expr);
    let (param_tys, ret_ty) = match &closure_ty {
        Ty::Fn { params, ret } => (params.clone(), (**ret).clone()),
        _ => return None,
    };

    // Determine which outer variables are captured.
    let mut captures: Vec<(DefId, Ty)> = Vec::new();

    // Collect DefIds of closure params so we can exclude them.
    let closure_param_def_ids: Vec<DefId> = params
        .iter()
        .filter_map(|p| ctx.resolved.resolutions.get(&p.span.start).copied())
        .collect();

    // Scan closure body for identifiers that reference outer locals.
    collect_captures(ctx, body, &closure_param_def_ids, &mut captures);

    // Generate a unique name for the closure function.
    let closure_name = format!("__closure_{}", ctx.closure_counter);
    ctx.closure_counter += 1;

    let ptr_ty = ctx.context.ptr_type(AddressSpace::default());

    if captures.is_empty() {
        // --- Non-capturing closure: compile as a plain function, return fn ptr ---

        let llvm_param_types: Vec<inkwell::types::BasicMetadataTypeEnum> = param_tys
            .iter()
            .map(|t| ty_to_llvm_metadata(ctx, t))
            .collect();

        let fn_type = if is_void_ty(&ret_ty) {
            ctx.context.void_type().fn_type(&llvm_param_types, false)
        } else {
            ty_to_llvm(ctx, &ret_ty).fn_type(&llvm_param_types, false)
        };

        let fn_value = ctx.module.add_function(&closure_name, fn_type, None);

        // Save current builder state.
        let saved_block = ctx.builder.get_insert_block();
        let saved_locals = ctx.locals.clone();
        let saved_local_types = ctx.local_types.clone();
        let saved_loop_exit = ctx.loop_exit_block.take();
        let saved_loop_header = ctx.loop_header_block.take();

        // Create entry block for the closure function.
        let entry_bb = ctx.context.append_basic_block(fn_value, "entry");
        ctx.builder.position_at_end(entry_bb);
        ctx.locals.clear();
        ctx.local_types.clear();

        // Alloca params.
        for (i, param) in params.iter().enumerate() {
            let param_sym = ctx
                .resolved
                .symbols
                .iter()
                .find(|s| s.kind == SymbolKind::ClosureParam && s.span == param.span);
            if let Some(sym) = param_sym {
                if let Some(param_val) = fn_value.get_nth_param(i as u32) {
                    let val_ty = param_val.get_type();
                    let alloca = ctx.builder.build_alloca(val_ty, &param.name).unwrap();
                    ctx.builder.build_store(alloca, param_val).unwrap();
                    ctx.locals.insert(sym.def_id, alloca);
                    ctx.local_types.insert(sym.def_id, val_ty);
                }
            }
        }

        // Compile body.
        let mut last_val = None;
        for (i, stmt) in body.iter().enumerate() {
            let is_last = i == body.len() - 1;
            if is_last {
                if let StmtKind::Expr(e) = &stmt.kind {
                    last_val = compile_expr(ctx, e);
                } else {
                    compile_stmt(ctx, stmt);
                }
            } else {
                compile_stmt(ctx, stmt);
            }
            if ctx.builder.get_insert_block().unwrap().get_terminator().is_some() {
                break;
            }
        }

        // Insert return.
        if ctx.builder.get_insert_block().unwrap().get_terminator().is_none() {
            if is_void_ty(&ret_ty) {
                ctx.builder.build_return(None).unwrap();
            } else if let Some(val) = last_val {
                ctx.builder.build_return(Some(&val)).unwrap();
            } else {
                let ret_llvm = ty_to_llvm(ctx, &ret_ty);
                ctx.builder.build_return(Some(&ret_llvm.const_zero())).unwrap();
            }
        }

        // Restore builder state.
        ctx.locals = saved_locals;
        ctx.local_types = saved_local_types;
        ctx.loop_exit_block = saved_loop_exit;
        ctx.loop_header_block = saved_loop_header;
        if let Some(bb) = saved_block {
            ctx.builder.position_at_end(bb);
        }

        // Return the function pointer.
        Some(fn_value.as_global_value().as_pointer_value().into())
    } else {
        // --- Capturing closure: env struct + hidden function ---

        // Build env struct type from captured variable types.
        let env_field_types: Vec<inkwell::types::BasicTypeEnum<'ctx>> = captures
            .iter()
            .map(|(_, ty)| ty_to_llvm(ctx, ty))
            .collect();
        let env_struct_ty = ctx.context.struct_type(&env_field_types, false);

        // Hidden function takes (env_ptr, params...).
        let mut fn_param_types: Vec<inkwell::types::BasicMetadataTypeEnum> = vec![ptr_ty.into()];
        for t in &param_tys {
            fn_param_types.push(ty_to_llvm_metadata(ctx, t));
        }

        let fn_type = if is_void_ty(&ret_ty) {
            ctx.context.void_type().fn_type(&fn_param_types, false)
        } else {
            ty_to_llvm(ctx, &ret_ty).fn_type(&fn_param_types, false)
        };

        let fn_value = ctx.module.add_function(&closure_name, fn_type, None);

        // Save state.
        let saved_block = ctx.builder.get_insert_block();
        let saved_locals = ctx.locals.clone();
        let saved_local_types = ctx.local_types.clone();
        let saved_loop_exit = ctx.loop_exit_block.take();
        let saved_loop_header = ctx.loop_header_block.take();

        let entry_bb = ctx.context.append_basic_block(fn_value, "entry");
        ctx.builder.position_at_end(entry_bb);
        ctx.locals.clear();
        ctx.local_types.clear();

        // Load captures from env_ptr (arg 0).
        let env_ptr = fn_value.get_nth_param(0).unwrap().into_pointer_value();
        for (i, (cap_def_id, cap_ty)) in captures.iter().enumerate() {
            let field_ptr = ctx
                .builder
                .build_struct_gep(env_struct_ty, env_ptr, i as u32, "cap_ptr")
                .unwrap();
            let field_llvm_ty = ty_to_llvm(ctx, cap_ty);
            let loaded = ctx
                .builder
                .build_load(field_llvm_ty, field_ptr, "cap_load")
                .unwrap();
            let alloca = ctx.builder.build_alloca(field_llvm_ty, "cap_local").unwrap();
            ctx.builder.build_store(alloca, loaded).unwrap();
            ctx.locals.insert(*cap_def_id, alloca);
            ctx.local_types.insert(*cap_def_id, field_llvm_ty);
        }

        // Alloca closure params (starting from arg index 1).
        for (i, param) in params.iter().enumerate() {
            let param_sym = ctx
                .resolved
                .symbols
                .iter()
                .find(|s| s.kind == SymbolKind::ClosureParam && s.span == param.span);
            if let Some(sym) = param_sym {
                if let Some(param_val) = fn_value.get_nth_param((i + 1) as u32) {
                    let val_ty = param_val.get_type();
                    let alloca = ctx.builder.build_alloca(val_ty, &param.name).unwrap();
                    ctx.builder.build_store(alloca, param_val).unwrap();
                    ctx.locals.insert(sym.def_id, alloca);
                    ctx.local_types.insert(sym.def_id, val_ty);
                }
            }
        }

        // Compile body.
        let mut last_val = None;
        for (i, stmt) in body.iter().enumerate() {
            let is_last = i == body.len() - 1;
            if is_last {
                if let StmtKind::Expr(e) = &stmt.kind {
                    last_val = compile_expr(ctx, e);
                } else {
                    compile_stmt(ctx, stmt);
                }
            } else {
                compile_stmt(ctx, stmt);
            }
            if ctx.builder.get_insert_block().unwrap().get_terminator().is_some() {
                break;
            }
        }

        if ctx.builder.get_insert_block().unwrap().get_terminator().is_none() {
            if is_void_ty(&ret_ty) {
                ctx.builder.build_return(None).unwrap();
            } else if let Some(val) = last_val {
                ctx.builder.build_return(Some(&val)).unwrap();
            } else {
                let ret_llvm = ty_to_llvm(ctx, &ret_ty);
                ctx.builder.build_return(Some(&ret_llvm.const_zero())).unwrap();
            }
        }

        // Restore state.
        ctx.locals = saved_locals;
        ctx.local_types = saved_local_types;
        ctx.loop_exit_block = saved_loop_exit;
        ctx.loop_header_block = saved_loop_header;
        if let Some(bb) = saved_block {
            ctx.builder.position_at_end(bb);
        }

        // Allocate environment struct and store captured values.
        let malloc = ctx.module.get_function("malloc")?;
        let env_size = env_field_types.iter().map(|t| estimate_basic_type_size(*t)).sum::<u64>();
        let env_size_val = ctx.context.i64_type().const_int(env_size.max(1), false);
        let raw_ptr = ctx
            .builder
            .build_call(malloc, &[env_size_val.into()], "env_alloc")
            .unwrap()
            .try_as_basic_value()
            .left()?
            .into_pointer_value();

        // Track this heap allocation for cleanup.
        ctx.heap_allocs.push(raw_ptr);

        // Store each captured value into the environment.
        for (i, (cap_def_id, cap_ty)) in captures.iter().enumerate() {
            let field_ptr = ctx
                .builder
                .build_struct_gep(env_struct_ty, raw_ptr, i as u32, "env_field_ptr")
                .unwrap();
            // Load the captured variable's current value.
            if let Some(&alloca) = ctx.locals.get(cap_def_id) {
                let field_llvm_ty = ty_to_llvm(ctx, cap_ty);
                let val = ctx.builder.build_load(field_llvm_ty, alloca, "cap_val").unwrap();
                ctx.builder.build_store(field_ptr, val).unwrap();
            }
        }

        // Build the closure struct: { fn_ptr, env_ptr }.
        let closure_struct_ty = ctx.context.struct_type(&[ptr_ty.into(), ptr_ty.into()], false);
        let mut closure_val = closure_struct_ty.const_zero();
        closure_val = ctx
            .builder
            .build_insert_value(closure_val, fn_value.as_global_value().as_pointer_value(), 0, "fn_ptr")
            .unwrap()
            .into_struct_value();
        closure_val = ctx
            .builder
            .build_insert_value(closure_val, raw_ptr, 1, "env_ptr")
            .unwrap()
            .into_struct_value();

        Some(closure_val.into())
    }
}

/// Resolve a monomorphized call: look up the specialized function for a TypeApp call.
/// Returns the LLVM FunctionValue if a specialization exists.
fn resolve_mono_call<'ctx>(
    ctx: &CodegenCtx<'ctx>,
    inner: &Expr,
    type_args: &[TypeExpr],
) -> Option<inkwell::values::FunctionValue<'ctx>> {
    let mono = ctx.mono_output?;

    // Get the function DefId from the inner ident.
    let fn_def_id = match &inner.kind {
        ExprKind::Ident(_) => ctx.resolved.resolutions.get(&inner.span.start).copied()?,
        _ => return None,
    };

    // Convert TypeExpr to concrete Ty.
    let concrete_args: Vec<Ty> = type_args
        .iter()
        .map(|ta| {
            let span = type_expr_span(ta);
            ctx.type_check
                .expr_types
                .get(&span.start)
                .cloned()
                .unwrap_or_else(|| lower_type_arg_codegen(ta, ctx.resolved))
        })
        .collect();

    // Look up mangled name.
    let mangled_name = mono.lookup(fn_def_id, &concrete_args)?;
    ctx.mono_fn_values.get(mangled_name).copied()
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

/// Lower a TypeExpr to a Ty for type argument lookup (fallback when not in expr_types).
fn lower_type_arg_codegen(te: &TypeExpr, resolved: &axion_resolve::ResolveOutput) -> Ty {
    use axion_types::ty::PrimTy;
    match te {
        TypeExpr::Named { name, .. } => {
            if let Some(prim) = PrimTy::from_name(name) {
                return Ty::Prim(prim);
            }
            if let Some(&def_id) = resolved.resolutions.get(&type_expr_span(te).start) {
                let sym = resolved.symbols.iter().find(|s| s.def_id == def_id);
                if let Some(sym) = sym {
                    match sym.kind {
                        axion_resolve::def_id::SymbolKind::Struct => {
                            return Ty::Struct { def_id, type_args: vec![] }
                        }
                        axion_resolve::def_id::SymbolKind::Enum => {
                            return Ty::Enum { def_id, type_args: vec![] }
                        }
                        _ => {}
                    }
                }
            }
            Ty::Error
        }
        TypeExpr::Ref { inner, .. } => {
            Ty::Ref(Box::new(lower_type_arg_codegen(inner, resolved)))
        }
        _ => Ty::Error,
    }
}

/// Estimate size of a basic type in bytes (for malloc).
fn estimate_basic_type_size(ty: inkwell::types::BasicTypeEnum) -> u64 {
    match ty {
        inkwell::types::BasicTypeEnum::IntType(i) => ((i.get_bit_width() + 7) / 8) as u64,
        inkwell::types::BasicTypeEnum::FloatType(_) => 8,
        inkwell::types::BasicTypeEnum::PointerType(_) => 8,
        inkwell::types::BasicTypeEnum::StructType(s) => {
            (0..s.count_fields())
                .map(|i| estimate_basic_type_size(s.get_field_type_at_index(i).unwrap()))
                .sum()
        }
        inkwell::types::BasicTypeEnum::ArrayType(a) => {
            estimate_basic_type_size(a.get_element_type()) * a.len() as u64
        }
        inkwell::types::BasicTypeEnum::VectorType(_) => 16,
    }
}

/// Collect captured variables from closure body.
/// Finds identifiers that resolve to outer DefIds not in `closure_param_ids`.
fn collect_captures<'ctx>(
    ctx: &CodegenCtx<'ctx>,
    body: &[Stmt],
    closure_param_ids: &[DefId],
    captures: &mut Vec<(DefId, Ty)>,
) {
    let mut seen = std::collections::HashSet::new();
    for stmt in body {
        collect_captures_stmt(ctx, stmt, closure_param_ids, captures, &mut seen);
    }
}

fn collect_captures_stmt<'ctx>(
    ctx: &CodegenCtx<'ctx>,
    stmt: &Stmt,
    closure_param_ids: &[DefId],
    captures: &mut Vec<(DefId, Ty)>,
    seen: &mut std::collections::HashSet<DefId>,
) {
    match &stmt.kind {
        StmtKind::Let { value, .. } => {
            collect_captures_expr(ctx, value, closure_param_ids, captures, seen);
        }
        StmtKind::LetPattern { value, .. } => {
            collect_captures_expr(ctx, value, closure_param_ids, captures, seen);
        }
        StmtKind::Assign { target, value } => {
            collect_captures_expr(ctx, target, closure_param_ids, captures, seen);
            collect_captures_expr(ctx, value, closure_param_ids, captures, seen);
        }
        StmtKind::Expr(e) => {
            collect_captures_expr(ctx, e, closure_param_ids, captures, seen);
        }
        StmtKind::Return(opt) => {
            if let Some(e) = opt {
                collect_captures_expr(ctx, e, closure_param_ids, captures, seen);
            }
        }
        StmtKind::Break(opt) => {
            if let Some(e) = opt {
                collect_captures_expr(ctx, e, closure_param_ids, captures, seen);
            }
        }
        StmtKind::Continue => {}
        StmtKind::Assert { cond, message } => {
            collect_captures_expr(ctx, cond, closure_param_ids, captures, seen);
            if let Some(m) = message {
                collect_captures_expr(ctx, m, closure_param_ids, captures, seen);
            }
        }
    }
}

fn collect_captures_expr<'ctx>(
    ctx: &CodegenCtx<'ctx>,
    expr: &Expr,
    closure_param_ids: &[DefId],
    captures: &mut Vec<(DefId, Ty)>,
    seen: &mut std::collections::HashSet<DefId>,
) {
    match &expr.kind {
        ExprKind::Ident(_) => {
            if let Some(&def_id) = ctx.resolved.resolutions.get(&expr.span.start) {
                // Check if this is an outer local (not a closure param, not a function).
                if !closure_param_ids.contains(&def_id)
                    && ctx.locals.contains_key(&def_id)
                    && !ctx.functions.contains_key(&def_id)
                    && !seen.contains(&def_id)
                {
                    // Get the type of the captured variable.
                    if let Some(info) = ctx.type_env.defs.get(&def_id) {
                        captures.push((def_id, info.ty.clone()));
                        seen.insert(def_id);
                    } else if let Some(ty) = ctx.type_check.expr_types.get(&expr.span.start) {
                        captures.push((def_id, ty.clone()));
                        seen.insert(def_id);
                    }
                }
            }
        }
        ExprKind::BinOp { lhs, rhs, .. } => {
            collect_captures_expr(ctx, lhs, closure_param_ids, captures, seen);
            collect_captures_expr(ctx, rhs, closure_param_ids, captures, seen);
        }
        ExprKind::UnaryOp { operand, .. } => {
            collect_captures_expr(ctx, operand, closure_param_ids, captures, seen);
        }
        ExprKind::Call { func, args } => {
            collect_captures_expr(ctx, func, closure_param_ids, captures, seen);
            for arg in args {
                collect_captures_expr(ctx, &arg.expr, closure_param_ids, captures, seen);
            }
        }
        ExprKind::Field { expr: inner, .. } => {
            collect_captures_expr(ctx, inner, closure_param_ids, captures, seen);
        }
        ExprKind::If { cond, then_branch, else_branch } => {
            collect_captures_expr(ctx, cond, closure_param_ids, captures, seen);
            for s in then_branch {
                collect_captures_stmt(ctx, s, closure_param_ids, captures, seen);
            }
            if let Some(els) = else_branch {
                for s in els {
                    collect_captures_stmt(ctx, s, closure_param_ids, captures, seen);
                }
            }
        }
        ExprKind::While { cond, body } => {
            collect_captures_expr(ctx, cond, closure_param_ids, captures, seen);
            for s in body {
                collect_captures_stmt(ctx, s, closure_param_ids, captures, seen);
            }
        }
        ExprKind::Block(stmts) => {
            for s in stmts {
                collect_captures_stmt(ctx, s, closure_param_ids, captures, seen);
            }
        }
        ExprKind::Ref(inner) => {
            collect_captures_expr(ctx, inner, closure_param_ids, captures, seen);
        }
        ExprKind::TypeApp { expr: inner, .. } => {
            collect_captures_expr(ctx, inner, closure_param_ids, captures, seen);
        }
        ExprKind::TupleLit(elems) => {
            for e in elems {
                collect_captures_expr(ctx, e, closure_param_ids, captures, seen);
            }
        }
        ExprKind::Match { expr: scrutinee, arms } => {
            collect_captures_expr(ctx, scrutinee, closure_param_ids, captures, seen);
            for arm in arms {
                for s in &arm.body {
                    collect_captures_stmt(ctx, s, closure_param_ids, captures, seen);
                }
            }
        }
        ExprKind::For { iter, body, .. } => {
            collect_captures_expr(ctx, iter, closure_param_ids, captures, seen);
            for s in body {
                collect_captures_stmt(ctx, s, closure_param_ids, captures, seen);
            }
        }
        ExprKind::Range { start, end } => {
            if let Some(s) = start { collect_captures_expr(ctx, s, closure_param_ids, captures, seen); }
            if let Some(e) = end { collect_captures_expr(ctx, e, closure_param_ids, captures, seen); }
        }
        ExprKind::StructLit { fields, .. } => {
            for f in fields {
                collect_captures_expr(ctx, &f.value, closure_param_ids, captures, seen);
            }
        }
        ExprKind::StringInterp { parts } => {
            for part in parts {
                if let StringInterpPart::Expr(e) = part {
                    collect_captures_expr(ctx, e, closure_param_ids, captures, seen);
                }
            }
        }
        ExprKind::Assert { cond, message } => {
            collect_captures_expr(ctx, cond, closure_param_ids, captures, seen);
            if let Some(m) = message {
                collect_captures_expr(ctx, m, closure_param_ids, captures, seen);
            }
        }
        ExprKind::ArrayLit(elems) => {
            for e in elems {
                collect_captures_expr(ctx, e, closure_param_ids, captures, seen);
            }
        }
        ExprKind::Index { expr: inner, index } => {
            collect_captures_expr(ctx, inner, closure_param_ids, captures, seen);
            collect_captures_expr(ctx, index, closure_param_ids, captures, seen);
        }
        ExprKind::Closure { body, .. } => {
            for s in body {
                collect_captures_stmt(ctx, s, closure_param_ids, captures, seen);
            }
        }
        _ => {}
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
        Ty::Struct { def_id, .. } => {
            let name = ctx.resolved.symbols.iter().find(|s| s.def_id == *def_id).map(|s| s.name.as_str());
            if name == Some("String") {
                if let Some(val) = compile_expr(ctx, &arg.expr) {
                    let sv = val.into_struct_value();
                    let ptr = ctx.builder.build_extract_value(sv, 0, "str_ptr").unwrap();
                    let len = ctx.builder.build_extract_value(sv, 1, "str_len").unwrap();
                    build_printf_call(ctx, "%.*s\n", &[len.into(), ptr.into()]);
                }
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
        Ty::Struct { def_id, .. } => {
            let name = ctx.resolved.symbols.iter().find(|s| s.def_id == *def_id).map(|s| s.name.as_str());
            if name == Some("String") {
                if let Some(val) = compile_expr(ctx, &arg.expr) {
                    let sv = val.into_struct_value();
                    let ptr = ctx.builder.build_extract_value(sv, 0, "str_ptr").unwrap();
                    let len = ctx.builder.build_extract_value(sv, 1, "str_len").unwrap();
                    build_printf_call(ctx, "%.*s", &[len.into(), ptr.into()]);
                }
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

fn compile_array_lit<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    expr: &Expr,
    elems: &[Expr],
) -> Option<BasicValueEnum<'ctx>> {
    let arr_ty = get_expr_ty(ctx, expr);
    let llvm_ty = ty_to_llvm(ctx, &arr_ty);
    let arr_llvm_ty = llvm_ty.into_array_type();
    let mut arr_val = arr_llvm_ty.const_zero();
    for (i, elem) in elems.iter().enumerate() {
        if let Some(val) = compile_expr(ctx, elem) {
            arr_val = ctx
                .builder
                .build_insert_value(arr_val, val, i as u32, "arr_elem")
                .unwrap()
                .into_array_value();
        }
    }
    Some(arr_val.into())
}

pub fn resolve_arr_ty<'ctx>(ctx: &CodegenCtx<'ctx>, arr_expr: &Expr) -> Ty {
    if let ExprKind::Ident(_) = &arr_expr.kind {
        ctx.resolved
            .resolutions
            .get(&arr_expr.span.start)
            .and_then(|def_id| {
                ctx.local_tys.get(def_id).cloned().or_else(|| {
                    ctx.type_env.defs.get(def_id).map(|info| info.ty.clone())
                })
            })
            .unwrap_or_else(|| get_expr_ty(ctx, arr_expr))
    } else {
        get_expr_ty(ctx, arr_expr)
    }
}

fn compile_index<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    whole_expr: &Expr,
    arr_expr: &Expr,
    index: &Expr,
) -> Option<BasicValueEnum<'ctx>> {
    // Check if index is a Range → slice creation
    if let ExprKind::Range { ref start, ref end } = index.kind {
        let arr_ty = resolve_arr_ty(ctx, arr_expr);
        return match &arr_ty {
            Ty::Array { elem, len } => {
                let arr_ptr = compile_expr_addr(ctx, arr_expr)?;
                let elem_llvm_ty = ty_to_llvm(ctx, elem);
                let i64_ty = ctx.context.i64_type();
                let (data_ptr, slice_len) = match (start, end) {
                    (None, None) => {
                        // arr[..] → full slice
                        let zero = i64_ty.const_zero();
                        let gep = unsafe {
                            ctx.builder.build_in_bounds_gep(elem_llvm_ty, arr_ptr, &[zero], "slice_base").unwrap()
                        };
                        (gep, i64_ty.const_int(*len, false))
                    }
                    (Some(s), Some(e)) => {
                        let s_val = compile_expr(ctx, s)?.into_int_value();
                        let e_val = compile_expr(ctx, e)?.into_int_value();
                        let offset_ptr = unsafe {
                            ctx.builder.build_in_bounds_gep(elem_llvm_ty, arr_ptr, &[s_val], "slice_off").unwrap()
                        };
                        let len = ctx.builder.build_int_sub(e_val, s_val, "slice_len").unwrap();
                        (offset_ptr, len)
                    }
                    (None, Some(e)) => {
                        let e_val = compile_expr(ctx, e)?.into_int_value();
                        let zero = i64_ty.const_zero();
                        let gep = unsafe {
                            ctx.builder.build_in_bounds_gep(elem_llvm_ty, arr_ptr, &[zero], "slice_base").unwrap()
                        };
                        (gep, e_val)
                    }
                    (Some(s), None) => {
                        let s_val = compile_expr(ctx, s)?.into_int_value();
                        let full_len = i64_ty.const_int(*len, false);
                        let offset_ptr = unsafe {
                            ctx.builder.build_in_bounds_gep(elem_llvm_ty, arr_ptr, &[s_val], "slice_off").unwrap()
                        };
                        let len = ctx.builder.build_int_sub(full_len, s_val, "slice_len").unwrap();
                        (offset_ptr, len)
                    }
                };
                // Build fat pointer { ptr, i64 }
                let slice_ty = get_expr_ty(ctx, whole_expr);
                let slice_llvm_ty = ty_to_llvm(ctx, &slice_ty);
                let mut sv = slice_llvm_ty.into_struct_type().const_zero();
                sv = ctx.builder.build_insert_value(sv, data_ptr, 0, "sp").unwrap().into_struct_value();
                sv = ctx.builder.build_insert_value(sv, slice_len, 1, "sl").unwrap().into_struct_value();
                Some(sv.into())
            }
            Ty::Slice(elem) => {
                // Sub-slice of slice
                let slice_val = compile_expr(ctx, arr_expr)?;
                let base_ptr = ctx.builder.build_extract_value(slice_val.into_struct_value(), 0, "slice_ptr")
                    .unwrap().into_pointer_value();
                let base_len = ctx.builder.build_extract_value(slice_val.into_struct_value(), 1, "slice_len")
                    .unwrap().into_int_value();
                let elem_llvm_ty = ty_to_llvm(ctx, elem);
                let (data_ptr, slice_len) = match (start, end) {
                    (None, None) => (base_ptr, base_len),
                    (Some(s), Some(e)) => {
                        let s_val = compile_expr(ctx, s)?.into_int_value();
                        let e_val = compile_expr(ctx, e)?.into_int_value();
                        let offset_ptr = unsafe {
                            ctx.builder.build_in_bounds_gep(elem_llvm_ty, base_ptr, &[s_val], "slice_off").unwrap()
                        };
                        let len = ctx.builder.build_int_sub(e_val, s_val, "slice_len").unwrap();
                        (offset_ptr, len)
                    }
                    (None, Some(e)) => {
                        let e_val = compile_expr(ctx, e)?.into_int_value();
                        (base_ptr, e_val)
                    }
                    (Some(s), None) => {
                        let s_val = compile_expr(ctx, s)?.into_int_value();
                        let offset_ptr = unsafe {
                            ctx.builder.build_in_bounds_gep(elem_llvm_ty, base_ptr, &[s_val], "slice_off").unwrap()
                        };
                        let len = ctx.builder.build_int_sub(base_len, s_val, "slice_len").unwrap();
                        (offset_ptr, len)
                    }
                };
                let slice_ty = get_expr_ty(ctx, whole_expr);
                let slice_llvm_ty = ty_to_llvm(ctx, &slice_ty);
                let mut sv = slice_llvm_ty.into_struct_type().const_zero();
                sv = ctx.builder.build_insert_value(sv, data_ptr, 0, "sp").unwrap().into_struct_value();
                sv = ctx.builder.build_insert_value(sv, slice_len, 1, "sl").unwrap().into_struct_value();
                Some(sv.into())
            }
            // Array[T] range indexing → Slice
            _ if is_array_struct_ty(ctx, &arr_ty) => {
                let elem_ty = get_array_elem_ty(&arr_ty);
                let elem_llvm_ty = ty_to_llvm(ctx, &elem_ty);
                let arr_val = compile_expr(ctx, arr_expr)?;
                let sv = arr_val.into_struct_value();
                let base_ptr = ctx.builder.build_extract_value(sv, 0, "arr_ptr")
                    .unwrap().into_pointer_value();
                let base_len = ctx.builder.build_extract_value(sv, 1, "arr_len")
                    .unwrap().into_int_value();
                let i64_ty = ctx.context.i64_type();
                let (data_ptr, slice_len) = match (start, end) {
                    (None, None) => (base_ptr, base_len),
                    (Some(s), Some(e)) => {
                        let s_val = compile_expr(ctx, s)?.into_int_value();
                        let e_val = compile_expr(ctx, e)?.into_int_value();
                        let offset_ptr = unsafe {
                            ctx.builder.build_in_bounds_gep(elem_llvm_ty, base_ptr, &[s_val], "arr_slice_off").unwrap()
                        };
                        let len = ctx.builder.build_int_sub(e_val, s_val, "arr_slice_len").unwrap();
                        (offset_ptr, len)
                    }
                    (None, Some(e)) => {
                        let e_val = compile_expr(ctx, e)?.into_int_value();
                        (base_ptr, e_val)
                    }
                    (Some(s), None) => {
                        let s_val = compile_expr(ctx, s)?.into_int_value();
                        let offset_ptr = unsafe {
                            ctx.builder.build_in_bounds_gep(elem_llvm_ty, base_ptr, &[s_val], "arr_slice_off").unwrap()
                        };
                        let len = ctx.builder.build_int_sub(base_len, s_val, "arr_slice_len").unwrap();
                        (offset_ptr, len)
                    }
                };
                let ptr_ty = ctx.context.ptr_type(AddressSpace::default());
                let slice_struct_ty = ctx.context.struct_type(&[ptr_ty.into(), i64_ty.into()], false);
                let mut result = slice_struct_ty.const_zero();
                result = ctx.builder.build_insert_value(result, data_ptr, 0, "sp").unwrap().into_struct_value();
                result = ctx.builder.build_insert_value(result, slice_len, 1, "sl").unwrap().into_struct_value();
                Some(result.into())
            }
            _ => None,
        };
    }

    let index_val = compile_expr(ctx, index)?;

    // Check for Array[T] element indexing: arr[i]
    let arr_ty = resolve_arr_ty(ctx, arr_expr);
    if is_array_struct_ty(ctx, &arr_ty) {
        let arr_val = compile_expr(ctx, arr_expr)?;
        let ptr = ctx.builder.build_extract_value(arr_val.into_struct_value(), 0, "arr_ptr")
            .unwrap().into_pointer_value();
        let elem_ty = get_array_elem_ty(&arr_ty);
        let elem_llvm_ty = ty_to_llvm(ctx, &elem_ty);
        let idx = index_val.into_int_value();
        let elem_ptr = unsafe {
            ctx.builder.build_in_bounds_gep(elem_llvm_ty, ptr, &[idx], "arr_idx").unwrap()
        };
        return Some(ctx.builder.build_load(elem_llvm_ty, elem_ptr, "arr_elem").unwrap());
    }

    // Check for Slice indexing: s[i] where s is &[T]
    if let Ty::Slice(ref elem) = arr_ty {
        let slice_val = compile_expr(ctx, arr_expr)?;
        let ptr = ctx.builder.build_extract_value(slice_val.into_struct_value(), 0, "slice_ptr")
            .unwrap().into_pointer_value();
        let elem_llvm_ty = ty_to_llvm(ctx, elem);
        let idx = index_val.into_int_value();
        let elem_ptr = unsafe {
            ctx.builder.build_in_bounds_gep(elem_llvm_ty, ptr, &[idx], "slice_idx").unwrap()
        };
        return Some(ctx.builder.build_load(elem_llvm_ty, elem_ptr, "slice_elem").unwrap());
    }

    // For index access, we need the alloca directly (to GEP into it).
    // Get the alloca and its LLVM type from the local variable.
    if let ExprKind::Ident(_) = &arr_expr.kind {
        let def_id = ctx.resolved.resolutions.get(&arr_expr.span.start)?;
        let alloca = ctx.locals.get(def_id).copied()?;
        let arr_llvm_ty = ctx.local_types.get(def_id).copied()?;

        // Verify it's an array type
        if !arr_llvm_ty.is_array_type() {
            return None;
        }
        let elem_llvm_ty = arr_llvm_ty.into_array_type().get_element_type();

        let zero = ctx.context.i64_type().const_zero();
        let idx = index_val.into_int_value();
        let elem_ptr = unsafe {
            ctx.builder
                .build_in_bounds_gep(arr_llvm_ty, alloca, &[zero, idx], "arr_idx")
                .unwrap()
        };

        let loaded = ctx
            .builder
            .build_load(elem_llvm_ty, elem_ptr, "arr_elem")
            .unwrap();
        return Some(loaded);
    }

    // Fallback for non-ident array expressions: compile, alloca + store, then GEP
    let arr_val = compile_expr(ctx, arr_expr)?;
    let arr_llvm_ty = arr_val.get_type();
    if !arr_llvm_ty.is_array_type() {
        return None;
    }
    let elem_llvm_ty = arr_llvm_ty.into_array_type().get_element_type();

    let alloca = ctx
        .builder
        .build_alloca(arr_llvm_ty, "arr_tmp")
        .unwrap();
    ctx.builder.build_store(alloca, arr_val).unwrap();

    let zero = ctx.context.i64_type().const_zero();
    let idx = index_val.into_int_value();
    let elem_ptr = unsafe {
        ctx.builder
            .build_in_bounds_gep(arr_llvm_ty, alloca, &[zero, idx], "arr_idx")
            .unwrap()
    };

    let loaded = ctx
        .builder
        .build_load(elem_llvm_ty, elem_ptr, "arr_elem")
        .unwrap();
    Some(loaded)
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

    let scrutinee_ty = get_expr_ty(ctx, scrutinee);
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
            // For the last arm, if it has a conditional pattern (Constructor/Literal),
            // the "no match" branch should go to an unreachable block, not merge_bb.
            // This prevents merge_bb from having an unaccounted predecessor.
            let is_conditional = matches!(
                &arm.pattern.kind,
                PatternKind::Constructor { .. } | PatternKind::Literal(_)
            );
            if is_conditional {
                let cur_bb = ctx.builder.get_insert_block();
                let unreach_bb = ctx.context.append_basic_block(fn_val, "match_unreachable");
                ctx.builder.position_at_end(unreach_bb);
                ctx.builder.build_unreachable().unwrap();
                if let Some(bb) = cur_bb {
                    ctx.builder.position_at_end(bb);
                }
                unreach_bb
            } else {
                merge_bb
            }
        };

        // Test the pattern and bind variables.
        match &arm.pattern.kind {
            PatternKind::Wildcard => {
                ctx.builder.build_unconditional_branch(arm_bb).unwrap();
                ctx.builder.position_at_end(arm_bb);
            }
            PatternKind::Ident(name) => {
                ctx.builder.build_unconditional_branch(arm_bb).unwrap();
                ctx.builder.position_at_end(arm_bb);
                // Bind the scrutinee to the pattern variable.
                let alloca = ctx
                    .builder
                    .build_alloca(scrutinee_val.get_type(), name)
                    .unwrap();
                ctx.builder.build_store(alloca, scrutinee_val).unwrap();
                // Pattern variables are definition sites — look up in symbols, not resolutions.
                let def_id = ctx
                    .resolved
                    .symbols
                    .iter()
                    .find(|s| s.kind == SymbolKind::LocalVar && s.span == arm.pattern.span)
                    .map(|s| s.def_id);
                if let Some(def_id) = def_id {
                    ctx.locals.insert(def_id, alloca);
                    ctx.local_types.insert(def_id, scrutinee_val.get_type());
                }
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
                ctx.builder.position_at_end(arm_bb);
            }
            PatternKind::Constructor { path, type_args: _, fields } => {
                compile_match_constructor(
                    ctx,
                    &scrutinee_ty,
                    &scrutinee_val,
                    path,
                    fields,
                    arm_bb,
                    next_bb,
                );
                ctx.builder.position_at_end(arm_bb);
            }
            PatternKind::TuplePattern(_) | PatternKind::Struct { .. } => {
                // Tuple and struct patterns always match (no condition check).
                ctx.builder.build_unconditional_branch(arm_bb).unwrap();
                ctx.builder.position_at_end(arm_bb);
                bind_pattern_value(ctx, &arm.pattern, scrutinee_val, &scrutinee_ty);
            }
            _ => {
                ctx.builder.build_unconditional_branch(arm_bb).unwrap();
                ctx.builder.position_at_end(arm_bb);
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

// ---------------------------------------------------------------------------
// Enum match: constructor pattern
// ---------------------------------------------------------------------------

/// Handle a `PatternKind::Constructor` in a match arm.
/// Extracts the tag from the scrutinee, compares with the expected variant index,
/// and binds sub-pattern variables to the variant's payload fields.
fn compile_match_constructor<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    scrutinee_ty: &Ty,
    scrutinee_val: &BasicValueEnum<'ctx>,
    path: &[String],
    fields: &[Pattern],
    arm_bb: inkwell::basic_block::BasicBlock<'ctx>,
    next_bb: inkwell::basic_block::BasicBlock<'ctx>,
) {
    // path is ["EnumName", "VariantName"]
    if path.len() < 2 {
        ctx.builder.build_unconditional_branch(arm_bb).unwrap();
        return;
    }
    let variant_name = &path[path.len() - 1];

    // Find the enum DefId.
    let enum_def_id = match scrutinee_ty {
        Ty::Enum { def_id, .. } => *def_id,
        _ => {
            ctx.builder.build_unconditional_branch(arm_bb).unwrap();
            return;
        }
    };

    // Find the variant index and fields from TypeEnv.
    let variants = match ctx.type_env.enum_variants.get(&enum_def_id) {
        Some(v) => v.clone(),
        None => {
            ctx.builder.build_unconditional_branch(arm_bb).unwrap();
            return;
        }
    };
    let variant_info = variants
        .iter()
        .enumerate()
        .find(|(_, (vname, _, _))| vname == variant_name);
    let (variant_idx, variant_fields) = match variant_info {
        Some((idx, (_, _, vfields))) => (idx, vfields.clone()),
        None => {
            ctx.builder.build_unconditional_branch(arm_bb).unwrap();
            return;
        }
    };

    // Extract the tag from the scrutinee.
    let enum_llvm_ty = ty_to_llvm(ctx, scrutinee_ty);

    // We need the scrutinee in memory to GEP into it.
    let alloca = ctx
        .builder
        .build_alloca(enum_llvm_ty, "scrutinee_tmp")
        .unwrap();
    ctx.builder.build_store(alloca, *scrutinee_val).unwrap();

    let tag_ptr = ctx
        .builder
        .build_struct_gep(enum_llvm_ty, alloca, 0, "tag_ptr")
        .unwrap();
    let tag_val = ctx
        .builder
        .build_load(ctx.context.i8_type(), tag_ptr, "tag")
        .unwrap()
        .into_int_value();

    // Compare tag with expected variant index.
    let expected_tag = ctx
        .context
        .i8_type()
        .const_int(variant_idx as u64, false);
    let cmp = ctx
        .builder
        .build_int_compare(IntPredicate::EQ, tag_val, expected_tag, "tag_cmp")
        .unwrap();
    ctx.builder
        .build_conditional_branch(cmp, arm_bb, next_bb)
        .unwrap();

    // In the arm block, extract payload fields and bind to pattern variables.
    ctx.builder.position_at_end(arm_bb);

    if !variant_fields.is_empty() && !fields.is_empty() {
        let type_args = match scrutinee_ty {
            Ty::Enum { type_args, .. } => type_args.clone(),
            _ => vec![],
        };
        let subst = build_subst_map(ctx, enum_def_id, &type_args);
        let variant_struct_ty = variant_struct_type(ctx, &variant_fields, &subst);

        // Get pointer to the payload area (index 1 in enum struct).
        let payload_ptr = ctx
            .builder
            .build_struct_gep(enum_llvm_ty, alloca, 1, "payload_ptr")
            .unwrap();

        // Extract each field and bind to the sub-pattern.
        for (fi, pat) in fields.iter().enumerate() {
            if fi >= variant_fields.len() {
                break;
            }
            let (_, ref field_ty) = variant_fields[fi];
            let resolved_field_ty = if subst.is_empty() { field_ty.clone() } else { axion_mono::specialize::substitute(field_ty, &subst) };
            let field_llvm_ty = ty_to_llvm(ctx, &resolved_field_ty);

            let field_ptr = ctx
                .builder
                .build_struct_gep(variant_struct_ty, payload_ptr, fi as u32, "field_ptr")
                .unwrap();
            let field_val = ctx
                .builder
                .build_load(field_llvm_ty, field_ptr, "field_val")
                .unwrap();

            // Bind the field value to the pattern variable.
            if let PatternKind::Ident(name) = &pat.kind {
                let field_alloca = ctx
                    .builder
                    .build_alloca(field_llvm_ty, name)
                    .unwrap();
                ctx.builder.build_store(field_alloca, field_val).unwrap();
                // Pattern variables are definition sites — look up in symbols, not resolutions.
                let def_id = ctx
                    .resolved
                    .symbols
                    .iter()
                    .find(|s| s.kind == SymbolKind::LocalVar && s.span == pat.span)
                    .map(|s| s.def_id);
                if let Some(def_id) = def_id {
                    ctx.locals.insert(def_id, field_alloca);
                    ctx.local_types.insert(def_id, field_llvm_ty);
                }
            }
            // Wildcard patterns: skip binding
        }
    }
}

// ---------------------------------------------------------------------------
// Enum construction
// ---------------------------------------------------------------------------

/// Compile a unit enum variant (no fields), e.g. `Color.Red`.
fn compile_enum_unit_variant<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    enum_def_id: DefId,
    field_expr: &Expr,
) -> Option<BasicValueEnum<'ctx>> {
    let variant_idx = ctx.type_check.field_resolutions.get(&field_expr.span.start)?;
    let expr_ty = get_expr_ty(ctx, field_expr);
    let type_args = match &expr_ty {
        Ty::Enum { type_args, .. } => type_args.clone(),
        _ => vec![],
    };
    let enum_ty = ty_to_llvm(ctx, &Ty::Enum { def_id: enum_def_id, type_args: type_args.clone() });

    let max_bytes = enum_max_payload_bytes(ctx, enum_def_id, &type_args);
    if max_bytes == 0 {
        // Tag-only enum: { i8 }
        let mut val = enum_ty.into_struct_type().const_zero();
        val = ctx
            .builder
            .build_insert_value(
                val,
                ctx.context.i8_type().const_int(*variant_idx as u64, false),
                0,
                "tag",
            )
            .unwrap()
            .into_struct_value();
        Some(val.into())
    } else {
        // { i8 tag, [N x i8] payload }
        let alloca = ctx.builder.build_alloca(enum_ty, "enum_val").unwrap();
        // Store tag.
        let tag_ptr = ctx
            .builder
            .build_struct_gep(enum_ty, alloca, 0, "tag_ptr")
            .unwrap();
        ctx.builder
            .build_store(
                tag_ptr,
                ctx.context.i8_type().const_int(*variant_idx as u64, false),
            )
            .unwrap();
        // Payload is zeroed (unit variant has no data).
        let loaded = ctx.builder.build_load(enum_ty, alloca, "enum_load").unwrap();
        Some(loaded)
    }
}

/// Compile a data enum variant construction, e.g. `Shape.Circle(5.0)`.
fn compile_enum_data_variant<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    enum_def_id: DefId,
    func_expr: &Expr,
    args: &[CallArg],
) -> Option<BasicValueEnum<'ctx>> {
    let variant_idx = ctx.type_check.field_resolutions.get(&func_expr.span.start)?;
    // Get the enum's type_args from the result type of this call expression.
    // The func_expr (e.g. Shape.Circle) resolves to a Fn type, but its parent
    // call expression has the Enum type. We look up the parent call's type_args.
    let call_ty = get_expr_ty(ctx, func_expr);
    let type_args = match &call_ty {
        Ty::Enum { type_args, .. } => type_args.clone(),
        Ty::Fn { ret, .. } => match ret.as_ref() {
            Ty::Enum { type_args, .. } => type_args.clone(),
            _ => vec![],
        },
        _ => vec![],
    };
    let enum_ty = ty_to_llvm(ctx, &Ty::Enum { def_id: enum_def_id, type_args: type_args.clone() });

    // Get the variant's field types.
    let variants = ctx.type_env.enum_variants.get(&enum_def_id)?;
    let (_, _, variant_fields) = variants.get(*variant_idx)?;
    let subst = build_subst_map(ctx, enum_def_id, &type_args);
    let variant_struct_ty = variant_struct_type(ctx, variant_fields, &subst);

    // Alloca the enum on the stack.
    let alloca = ctx.builder.build_alloca(enum_ty, "enum_val").unwrap();

    // Store tag.
    let tag_ptr = ctx
        .builder
        .build_struct_gep(enum_ty, alloca, 0, "tag_ptr")
        .unwrap();
    ctx.builder
        .build_store(
            tag_ptr,
            ctx.context.i8_type().const_int(*variant_idx as u64, false),
        )
        .unwrap();

    // Store payload: get pointer to payload area, bitcast to variant struct, store fields.
    let payload_ptr = ctx
        .builder
        .build_struct_gep(enum_ty, alloca, 1, "payload_ptr")
        .unwrap();

    // Compile each argument and store into the variant struct via the payload pointer.
    for (i, arg) in args.iter().enumerate() {
        if let Some(val) = compile_expr(ctx, &arg.expr) {
            let field_ptr = ctx
                .builder
                .build_struct_gep(variant_struct_ty, payload_ptr, i as u32, "field_ptr")
                .unwrap();
            ctx.builder.build_store(field_ptr, val).unwrap();
        }
    }

    let loaded = ctx.builder.build_load(enum_ty, alloca, "enum_load").unwrap();
    Some(loaded)
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

// ---------------------------------------------------------------------------
// String intrinsic methods
// ---------------------------------------------------------------------------

/// Compile `String.new()` → `{ null_ptr, 0, 0 }`
fn compile_string_new<'ctx>(ctx: &CodegenCtx<'ctx>) -> Option<BasicValueEnum<'ctx>> {
    let ptr_ty = ctx.context.ptr_type(AddressSpace::default());
    let i64_ty = ctx.context.i64_type();
    let struct_ty = ctx.context.struct_type(&[ptr_ty.into(), i64_ty.into(), i64_ty.into()], false);
    let null = ptr_ty.const_null();
    let zero = i64_ty.const_zero();
    let mut sv = struct_ty.get_undef();
    sv = ctx.builder.build_insert_value(sv, null, 0, "str_ptr").unwrap().into_struct_value();
    sv = ctx.builder.build_insert_value(sv, zero, 1, "str_len").unwrap().into_struct_value();
    sv = ctx.builder.build_insert_value(sv, zero, 2, "str_cap").unwrap().into_struct_value();
    Some(sv.into())
}

/// Compile `String.from(s)` → malloc + memcpy
fn compile_string_from<'ctx>(ctx: &mut CodegenCtx<'ctx>, args: &[CallArg]) -> Option<BasicValueEnum<'ctx>> {
    let malloc = ctx.module.get_function("malloc")?;
    let memcpy = ctx.module.get_function("memcpy")?;
    let ptr_ty = ctx.context.ptr_type(AddressSpace::default());
    let i64_ty = ctx.context.i64_type();
    let struct_ty = ctx.context.struct_type(&[ptr_ty.into(), i64_ty.into(), i64_ty.into()], false);

    let src_val = compile_expr(ctx, &args[0].expr)?;
    let src_struct = src_val.into_struct_value();
    let src_ptr = ctx.builder.build_extract_value(src_struct, 0, "src_ptr").unwrap();
    let src_len = ctx.builder.build_extract_value(src_struct, 1, "src_len").unwrap();

    // malloc(len)
    let buf = ctx.builder.build_call(malloc, &[src_len.into()], "buf").unwrap()
        .try_as_basic_value().left().unwrap().into_pointer_value();

    // memcpy(buf, src_ptr, len)
    ctx.builder.build_call(memcpy, &[buf.into(), src_ptr.into(), src_len.into()], "").unwrap();

    // Build { buf, len, len }
    let mut sv = struct_ty.get_undef();
    sv = ctx.builder.build_insert_value(sv, buf, 0, "str_ptr").unwrap().into_struct_value();
    sv = ctx.builder.build_insert_value(sv, src_len, 1, "str_len").unwrap().into_struct_value();
    sv = ctx.builder.build_insert_value(sv, src_len, 2, "str_cap").unwrap().into_struct_value();
    Some(sv.into())
}

/// Compile `a + b` for String values → allocate new buffer, memcpy both sides.
fn compile_string_concat<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    lhs_val: BasicValueEnum<'ctx>,
    rhs_val: BasicValueEnum<'ctx>,
) -> Option<BasicValueEnum<'ctx>> {
    let malloc = ctx.module.get_function("malloc")?;
    let memcpy = ctx.module.get_function("memcpy")?;
    let ptr_ty = ctx.context.ptr_type(AddressSpace::default());
    let i64_ty = ctx.context.i64_type();
    let struct_ty = ctx.context.struct_type(&[ptr_ty.into(), i64_ty.into(), i64_ty.into()], false);

    // Extract ptr and len from lhs
    let lhs_struct = lhs_val.into_struct_value();
    let lhs_ptr = ctx.builder.build_extract_value(lhs_struct, 0, "lhs_ptr").unwrap().into_pointer_value();
    let lhs_len = ctx.builder.build_extract_value(lhs_struct, 1, "lhs_len").unwrap().into_int_value();

    // Extract ptr and len from rhs
    let rhs_struct = rhs_val.into_struct_value();
    let rhs_ptr = ctx.builder.build_extract_value(rhs_struct, 0, "rhs_ptr").unwrap().into_pointer_value();
    let rhs_len = ctx.builder.build_extract_value(rhs_struct, 1, "rhs_len").unwrap().into_int_value();

    // new_len = lhs_len + rhs_len
    let new_len = ctx.builder.build_int_add(lhs_len, rhs_len, "new_len").unwrap();

    // malloc(new_len)
    let buf = ctx.builder.build_call(malloc, &[new_len.into()], "concat_buf").unwrap()
        .try_as_basic_value().left().unwrap().into_pointer_value();

    // memcpy(buf, lhs_ptr, lhs_len)
    ctx.builder.build_call(memcpy, &[buf.into(), lhs_ptr.into(), lhs_len.into()], "").unwrap();

    // memcpy(buf + lhs_len, rhs_ptr, rhs_len)
    let dst = unsafe { ctx.builder.build_gep(ctx.context.i8_type(), buf, &[lhs_len], "concat_dst").unwrap() };
    ctx.builder.build_call(memcpy, &[dst.into(), rhs_ptr.into(), rhs_len.into()], "").unwrap();

    // Build { buf, new_len, new_len }
    let mut sv = struct_ty.get_undef();
    sv = ctx.builder.build_insert_value(sv, buf, 0, "cat_ptr").unwrap().into_struct_value();
    sv = ctx.builder.build_insert_value(sv, new_len, 1, "cat_len").unwrap().into_struct_value();
    sv = ctx.builder.build_insert_value(sv, new_len, 2, "cat_cap").unwrap().into_struct_value();
    Some(sv.into())
}

/// Compile String == / != via memcmp.
fn compile_string_compare<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    op: BinOp,
    lhs_val: BasicValueEnum<'ctx>,
    rhs_val: BasicValueEnum<'ctx>,
) -> Option<BasicValueEnum<'ctx>> {
    let memcmp = ctx.module.get_function("memcmp")?;

    // Extract ptr and len from lhs
    let lhs_struct = lhs_val.into_struct_value();
    let lhs_ptr = ctx.builder.build_extract_value(lhs_struct, 0, "lhs_ptr").unwrap().into_pointer_value();
    let lhs_len = ctx.builder.build_extract_value(lhs_struct, 1, "lhs_len").unwrap().into_int_value();

    // Extract ptr and len from rhs
    let rhs_struct = rhs_val.into_struct_value();
    let rhs_ptr = ctx.builder.build_extract_value(rhs_struct, 0, "rhs_ptr").unwrap().into_pointer_value();
    let rhs_len = ctx.builder.build_extract_value(rhs_struct, 1, "rhs_len").unwrap().into_int_value();

    // Fast path: lengths must be equal
    let len_equal = ctx.builder.build_int_compare(IntPredicate::EQ, lhs_len, rhs_len, "len_eq").unwrap();

    // memcmp(lhs_ptr, rhs_ptr, lhs_len)
    let cmp_result = ctx.builder.build_call(
        memcmp,
        &[lhs_ptr.into(), rhs_ptr.into(), lhs_len.into()],
        "memcmp_ret",
    ).unwrap().try_as_basic_value().left().unwrap().into_int_value();

    let zero_i32 = ctx.context.i32_type().const_zero();
    let content_equal = ctx.builder.build_int_compare(IntPredicate::EQ, cmp_result, zero_i32, "content_eq").unwrap();

    // result = len_equal AND content_equal
    let result = ctx.builder.build_and(len_equal, content_equal, "str_eq").unwrap();

    match op {
        BinOp::Eq => Some(result.into()),
        BinOp::NotEq => {
            let negated = ctx.builder.build_not(result, "str_ne").unwrap();
            Some(negated.into())
        }
        _ => unreachable!(),
    }
}

/// Compile `s.len()` → extract field 1
fn compile_string_len<'ctx>(ctx: &mut CodegenCtx<'ctx>, inner: &Expr) -> Option<BasicValueEnum<'ctx>> {
    let val = compile_expr(ctx, inner)?;
    let sv = val.into_struct_value();
    Some(ctx.builder.build_extract_value(sv, 1, "str_len").unwrap().into())
}

/// Compile `s.is_empty()` → field 1 == 0
fn compile_string_is_empty<'ctx>(ctx: &mut CodegenCtx<'ctx>, inner: &Expr) -> Option<BasicValueEnum<'ctx>> {
    let val = compile_expr(ctx, inner)?;
    let sv = val.into_struct_value();
    let len = ctx.builder.build_extract_value(sv, 1, "str_len").unwrap().into_int_value();
    let zero = ctx.context.i64_type().const_zero();
    let cmp = ctx.builder.build_int_compare(IntPredicate::EQ, len, zero, "is_empty").unwrap();
    Some(cmp.into())
}

/// Compile `s.push(arg)` — mutates String in-place via pointer.
fn compile_string_push<'ctx>(ctx: &mut CodegenCtx<'ctx>, inner: &Expr, args: &[CallArg]) -> Option<BasicValueEnum<'ctx>> {
    let realloc = ctx.module.get_function("realloc")?;
    let memcpy = ctx.module.get_function("memcpy")?;
    let ptr_ty = ctx.context.ptr_type(AddressSpace::default());
    let i64_ty = ctx.context.i64_type();
    let string_ty = ctx.context.struct_type(&[ptr_ty.into(), i64_ty.into(), i64_ty.into()], false);

    // Get pointer to String struct
    let string_ptr = compile_expr_addr(ctx, inner)?;

    // Load current ptr, len, cap via GEP
    let ptr_field = ctx.builder.build_struct_gep(string_ty, string_ptr, 0, "ptr_field").unwrap();
    let len_field = ctx.builder.build_struct_gep(string_ty, string_ptr, 1, "len_field").unwrap();
    let cap_field = ctx.builder.build_struct_gep(string_ty, string_ptr, 2, "cap_field").unwrap();

    let cur_ptr = ctx.builder.build_load(ptr_ty, ptr_field, "cur_ptr").unwrap().into_pointer_value();
    let cur_len = ctx.builder.build_load(i64_ty, len_field, "cur_len").unwrap().into_int_value();
    let cur_cap = ctx.builder.build_load(i64_ty, cap_field, "cur_cap").unwrap().into_int_value();

    // Get source str (arg)
    let src_val = compile_expr(ctx, &args[0].expr)?;
    let src_struct = src_val.into_struct_value();
    let src_ptr = ctx.builder.build_extract_value(src_struct, 0, "src_ptr").unwrap().into_pointer_value();
    let src_len = ctx.builder.build_extract_value(src_struct, 1, "src_len").unwrap().into_int_value();

    // new_len = cur_len + src_len
    let new_len = ctx.builder.build_int_add(cur_len, src_len, "new_len").unwrap();

    // if new_len > cur_cap → grow
    let fn_val = ctx.builder.get_insert_block().unwrap().get_parent().unwrap();
    let entry_bb = ctx.builder.get_insert_block().unwrap();
    let grow_bb = ctx.context.append_basic_block(fn_val, "push_grow");
    let copy_bb = ctx.context.append_basic_block(fn_val, "push_copy");

    let needs_grow = ctx.builder.build_int_compare(IntPredicate::UGT, new_len, cur_cap, "needs_grow").unwrap();
    ctx.builder.build_conditional_branch(needs_grow, grow_bb, copy_bb).unwrap();

    // grow block
    ctx.builder.position_at_end(grow_bb);
    // new_cap = max(new_len, cap * 2)
    let cap_doubled = ctx.builder.build_int_mul(cur_cap, i64_ty.const_int(2, false), "cap_x2").unwrap();
    let use_doubled = ctx.builder.build_int_compare(IntPredicate::UGT, cap_doubled, new_len, "use_doubled").unwrap();
    let new_cap = ctx.builder.build_select(use_doubled, cap_doubled, new_len, "new_cap").unwrap().into_int_value();
    // realloc(ptr, new_cap)
    let new_buf = ctx.builder.build_call(realloc, &[cur_ptr.into(), new_cap.into()], "new_buf").unwrap()
        .try_as_basic_value().left().unwrap().into_pointer_value();
    // store new ptr and cap
    ctx.builder.build_store(ptr_field, new_buf).unwrap();
    ctx.builder.build_store(cap_field, new_cap).unwrap();
    ctx.builder.build_unconditional_branch(copy_bb).unwrap();

    // copy block
    ctx.builder.position_at_end(copy_bb);
    // Reload ptr after potential realloc (phi)
    let phi_ptr = ctx.builder.build_phi(ptr_ty, "ptr_phi").unwrap();
    phi_ptr.add_incoming(&[
        (&cur_ptr, entry_bb),
        (&new_buf, grow_bb),
    ]);
    let final_ptr = phi_ptr.as_basic_value().into_pointer_value();

    // memcpy(ptr + cur_len, src_ptr, src_len)
    let dest = unsafe {
        ctx.builder.build_in_bounds_gep(ctx.context.i8_type(), final_ptr, &[cur_len], "dest").unwrap()
    };
    ctx.builder.build_call(memcpy, &[dest.into(), src_ptr.into(), src_len.into()], "").unwrap();

    // store new len
    ctx.builder.build_store(len_field, new_len).unwrap();

    None
}

/// Compile `s.as_str()` → extract ptr and len, build `{ptr, len}` str struct.
fn compile_string_as_str<'ctx>(ctx: &mut CodegenCtx<'ctx>, inner: &Expr) -> Option<BasicValueEnum<'ctx>> {
    let val = compile_expr(ctx, inner)?;
    let sv = val.into_struct_value();
    let ptr = ctx.builder.build_extract_value(sv, 0, "str_ptr").unwrap();
    let len = ctx.builder.build_extract_value(sv, 1, "str_len").unwrap();
    let ptr_ty = ctx.context.ptr_type(AddressSpace::default());
    let i64_ty = ctx.context.i64_type();
    let str_ty = ctx.context.struct_type(&[ptr_ty.into(), i64_ty.into()], false);
    let mut result = str_ty.get_undef();
    result = ctx.builder.build_insert_value(result, ptr, 0, "as_ptr").unwrap().into_struct_value();
    result = ctx.builder.build_insert_value(result, len, 1, "as_len").unwrap().into_struct_value();
    Some(result.into())
}

// ---------------------------------------------------------------------------
// str built-in methods
// ---------------------------------------------------------------------------

/// Helper: extract (ptr, len) from a str value.
fn extract_str_parts<'ctx>(
    ctx: &CodegenCtx<'ctx>,
    str_val: BasicValueEnum<'ctx>,
) -> (inkwell::values::PointerValue<'ctx>, inkwell::values::IntValue<'ctx>) {
    let sv = str_val.into_struct_value();
    let ptr = ctx.builder.build_extract_value(sv, 0, "str_ptr").unwrap().into_pointer_value();
    let len = ctx.builder.build_extract_value(sv, 1, "str_len").unwrap().into_int_value();
    (ptr, len)
}

/// Helper: build a str struct { ptr, len }.
fn build_str_struct<'ctx>(
    ctx: &CodegenCtx<'ctx>,
    ptr: inkwell::values::PointerValue<'ctx>,
    len: inkwell::values::IntValue<'ctx>,
) -> BasicValueEnum<'ctx> {
    let ptr_ty = ctx.context.ptr_type(AddressSpace::default());
    let i64_ty = ctx.context.i64_type();
    let str_ty = ctx.context.struct_type(&[ptr_ty.into(), i64_ty.into()], false);
    let mut result = str_ty.get_undef();
    result = ctx.builder.build_insert_value(result, ptr, 0, "s_ptr").unwrap().into_struct_value();
    result = ctx.builder.build_insert_value(result, len, 1, "s_len").unwrap().into_struct_value();
    result.into()
}

/// Helper: extract (ptr, len) from a String value (fields 0 and 1).
fn extract_string_as_str_parts<'ctx>(
    ctx: &CodegenCtx<'ctx>,
    string_val: BasicValueEnum<'ctx>,
) -> (inkwell::values::PointerValue<'ctx>, inkwell::values::IntValue<'ctx>) {
    let sv = string_val.into_struct_value();
    let ptr = ctx.builder.build_extract_value(sv, 0, "str_ptr").unwrap().into_pointer_value();
    let len = ctx.builder.build_extract_value(sv, 1, "str_len").unwrap().into_int_value();
    (ptr, len)
}

/// Compile `s.len()` for str → extract field 1
fn compile_str_len<'ctx>(ctx: &mut CodegenCtx<'ctx>, inner: &Expr) -> Option<BasicValueEnum<'ctx>> {
    let val = compile_expr(ctx, inner)?;
    let (_, len) = extract_str_parts(ctx, val);
    Some(len.into())
}

/// Compile `s.is_empty()` for str → field 1 == 0
fn compile_str_is_empty<'ctx>(ctx: &mut CodegenCtx<'ctx>, inner: &Expr) -> Option<BasicValueEnum<'ctx>> {
    let val = compile_expr(ctx, inner)?;
    let (_, len) = extract_str_parts(ctx, val);
    let zero = ctx.context.i64_type().const_zero();
    let cmp = ctx.builder.build_int_compare(IntPredicate::EQ, len, zero, "is_empty").unwrap();
    Some(cmp.into())
}

/// Compile `s.byte_at(i)` for str → GEP + load i8 + zext to i64
fn compile_str_byte_at<'ctx>(ctx: &mut CodegenCtx<'ctx>, inner: &Expr, args: &[CallArg]) -> Option<BasicValueEnum<'ctx>> {
    let val = compile_expr(ctx, inner)?;
    let (ptr, _) = extract_str_parts(ctx, val);
    let idx = compile_expr(ctx, &args[0].expr)?.into_int_value();
    let elem_ptr = unsafe {
        ctx.builder.build_in_bounds_gep(ctx.context.i8_type(), ptr, &[idx], "byte_ptr").unwrap()
    };
    let byte = ctx.builder.build_load(ctx.context.i8_type(), elem_ptr, "byte").unwrap().into_int_value();
    let result = ctx.builder.build_int_z_extend(byte, ctx.context.i64_type(), "byte_i64").unwrap();
    Some(result.into())
}

/// Compile `s.slice(start, end)` for str → GEP + new {ptr, len}
fn compile_str_slice<'ctx>(ctx: &mut CodegenCtx<'ctx>, inner: &Expr, args: &[CallArg]) -> Option<BasicValueEnum<'ctx>> {
    let val = compile_expr(ctx, inner)?;
    let (ptr, _) = extract_str_parts(ctx, val);
    let start = compile_expr(ctx, &args[0].expr)?.into_int_value();
    let end = compile_expr(ctx, &args[1].expr)?.into_int_value();
    let new_len = ctx.builder.build_int_sub(end, start, "slice_len").unwrap();
    let new_ptr = unsafe {
        ctx.builder.build_in_bounds_gep(ctx.context.i8_type(), ptr, &[start], "slice_ptr").unwrap()
    };
    Some(build_str_struct(ctx, new_ptr, new_len))
}

/// Compile `a == b` / `a != b` for str via memcmp.
fn compile_str_compare<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    op: BinOp,
    lhs_val: BasicValueEnum<'ctx>,
    rhs_val: BasicValueEnum<'ctx>,
) -> Option<BasicValueEnum<'ctx>> {
    let memcmp = ctx.module.get_function("memcmp")?;
    let (lhs_ptr, lhs_len) = extract_str_parts(ctx, lhs_val);
    let (rhs_ptr, rhs_len) = extract_str_parts(ctx, rhs_val);

    let len_equal = ctx.builder.build_int_compare(IntPredicate::EQ, lhs_len, rhs_len, "len_eq").unwrap();
    let cmp_result = ctx.builder.build_call(
        memcmp,
        &[lhs_ptr.into(), rhs_ptr.into(), lhs_len.into()],
        "memcmp_ret",
    ).unwrap().try_as_basic_value().left().unwrap().into_int_value();
    let zero_i32 = ctx.context.i32_type().const_zero();
    let content_equal = ctx.builder.build_int_compare(IntPredicate::EQ, cmp_result, zero_i32, "content_eq").unwrap();
    let result = ctx.builder.build_and(len_equal, content_equal, "str_eq").unwrap();

    match op {
        BinOp::Eq => Some(result.into()),
        BinOp::NotEq => Some(ctx.builder.build_not(result, "str_ne").unwrap().into()),
        _ => unreachable!(),
    }
}

/// Compile `a + b` for str values → allocate new String buffer, memcpy both sides.
fn compile_str_concat<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    lhs_val: BasicValueEnum<'ctx>,
    rhs_val: BasicValueEnum<'ctx>,
) -> Option<BasicValueEnum<'ctx>> {
    let malloc = ctx.module.get_function("malloc")?;
    let memcpy = ctx.module.get_function("memcpy")?;
    let ptr_ty = ctx.context.ptr_type(AddressSpace::default());
    let i64_ty = ctx.context.i64_type();
    let string_ty = ctx.context.struct_type(&[ptr_ty.into(), i64_ty.into(), i64_ty.into()], false);

    let (lhs_ptr, lhs_len) = extract_str_parts(ctx, lhs_val);
    let (rhs_ptr, rhs_len) = extract_str_parts(ctx, rhs_val);

    let new_len = ctx.builder.build_int_add(lhs_len, rhs_len, "new_len").unwrap();
    let buf = ctx.builder.build_call(malloc, &[new_len.into()], "concat_buf").unwrap()
        .try_as_basic_value().left().unwrap().into_pointer_value();
    ctx.builder.build_call(memcpy, &[buf.into(), lhs_ptr.into(), lhs_len.into()], "").unwrap();
    let dst = unsafe { ctx.builder.build_gep(ctx.context.i8_type(), buf, &[lhs_len], "concat_dst").unwrap() };
    ctx.builder.build_call(memcpy, &[dst.into(), rhs_ptr.into(), rhs_len.into()], "").unwrap();

    let mut sv = string_ty.get_undef();
    sv = ctx.builder.build_insert_value(sv, buf, 0, "cat_ptr").unwrap().into_struct_value();
    sv = ctx.builder.build_insert_value(sv, new_len, 1, "cat_len").unwrap().into_struct_value();
    sv = ctx.builder.build_insert_value(sv, new_len, 2, "cat_cap").unwrap().into_struct_value();
    Some(sv.into())
}

/// Compile `s.contains(needle)` for str — loop + memcmp.
fn compile_str_contains_impl<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    haystack_ptr: inkwell::values::PointerValue<'ctx>,
    haystack_len: inkwell::values::IntValue<'ctx>,
    needle_ptr: inkwell::values::PointerValue<'ctx>,
    needle_len: inkwell::values::IntValue<'ctx>,
) -> Option<BasicValueEnum<'ctx>> {
    let memcmp = ctx.module.get_function("memcmp")?;
    let i64_ty = ctx.context.i64_type();
    let i1_ty = ctx.context.bool_type();

    let fn_val = ctx.builder.get_insert_block().unwrap().get_parent().unwrap();
    let check_empty_bb = ctx.context.append_basic_block(fn_val, "contains_check_empty");
    let loop_header_bb = ctx.context.append_basic_block(fn_val, "contains_loop_header");
    let loop_body_bb = ctx.context.append_basic_block(fn_val, "contains_loop_body");
    let found_bb = ctx.context.append_basic_block(fn_val, "contains_found");
    let not_found_bb = ctx.context.append_basic_block(fn_val, "contains_not_found");
    let merge_bb = ctx.context.append_basic_block(fn_val, "contains_merge");

    ctx.builder.build_unconditional_branch(check_empty_bb).unwrap();

    // Empty needle → always true
    ctx.builder.position_at_end(check_empty_bb);
    let needle_empty = ctx.builder.build_int_compare(IntPredicate::EQ, needle_len, i64_ty.const_zero(), "needle_empty").unwrap();
    ctx.builder.build_conditional_branch(needle_empty, found_bb, loop_header_bb).unwrap();

    // Loop header: i = 0..=(haystack_len - needle_len)
    ctx.builder.position_at_end(loop_header_bb);
    let phi_i = ctx.builder.build_phi(i64_ty, "i").unwrap();
    phi_i.add_incoming(&[(&i64_ty.const_zero(), check_empty_bb)]);
    let i = phi_i.as_basic_value().into_int_value();

    // max_i = haystack_len - needle_len + 1
    let max_i = ctx.builder.build_int_sub(haystack_len, needle_len, "max_i_sub").unwrap();
    let max_i = ctx.builder.build_int_add(max_i, i64_ty.const_int(1, false), "max_i").unwrap();
    let cond = ctx.builder.build_int_compare(IntPredicate::ULT, i, max_i, "loop_cond").unwrap();
    ctx.builder.build_conditional_branch(cond, loop_body_bb, not_found_bb).unwrap();

    // Loop body: memcmp(haystack + i, needle, needle_len)
    ctx.builder.position_at_end(loop_body_bb);
    let hay_offset = unsafe {
        ctx.builder.build_in_bounds_gep(ctx.context.i8_type(), haystack_ptr, &[i], "hay_offset").unwrap()
    };
    let cmp = ctx.builder.build_call(
        memcmp,
        &[hay_offset.into(), needle_ptr.into(), needle_len.into()],
        "cmp",
    ).unwrap().try_as_basic_value().left().unwrap().into_int_value();
    let is_match = ctx.builder.build_int_compare(IntPredicate::EQ, cmp, ctx.context.i32_type().const_zero(), "is_match").unwrap();
    // Compute next_i BEFORE the terminator
    let next_i = ctx.builder.build_int_add(i, i64_ty.const_int(1, false), "next_i").unwrap();
    phi_i.add_incoming(&[(&next_i, loop_body_bb)]);
    ctx.builder.build_conditional_branch(is_match, found_bb, loop_header_bb).unwrap();

    // found
    ctx.builder.position_at_end(found_bb);
    ctx.builder.build_unconditional_branch(merge_bb).unwrap();

    // not found
    ctx.builder.position_at_end(not_found_bb);
    ctx.builder.build_unconditional_branch(merge_bb).unwrap();

    // merge
    ctx.builder.position_at_end(merge_bb);
    let phi_result = ctx.builder.build_phi(i1_ty, "contains_result").unwrap();
    phi_result.add_incoming(&[
        (&i1_ty.const_int(1, false), found_bb),
        (&i1_ty.const_zero(), not_found_bb),
    ]);
    Some(phi_result.as_basic_value())
}

fn compile_str_contains<'ctx>(ctx: &mut CodegenCtx<'ctx>, inner: &Expr, args: &[CallArg]) -> Option<BasicValueEnum<'ctx>> {
    let val = compile_expr(ctx, inner)?;
    let (hay_ptr, hay_len) = extract_str_parts(ctx, val);
    let needle = compile_expr(ctx, &args[0].expr)?;
    let (needle_ptr, needle_len) = extract_str_parts(ctx, needle);
    compile_str_contains_impl(ctx, hay_ptr, hay_len, needle_ptr, needle_len)
}

/// Compile `s.starts_with(prefix)` for str.
fn compile_str_starts_with_impl<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    hay_ptr: inkwell::values::PointerValue<'ctx>,
    hay_len: inkwell::values::IntValue<'ctx>,
    prefix_ptr: inkwell::values::PointerValue<'ctx>,
    prefix_len: inkwell::values::IntValue<'ctx>,
) -> Option<BasicValueEnum<'ctx>> {
    let memcmp = ctx.module.get_function("memcmp")?;
    // if prefix_len > hay_len → false; else memcmp(hay, prefix, prefix_len) == 0
    let too_long = ctx.builder.build_int_compare(IntPredicate::UGT, prefix_len, hay_len, "too_long").unwrap();

    let fn_val = ctx.builder.get_insert_block().unwrap().get_parent().unwrap();
    let cmp_bb = ctx.context.append_basic_block(fn_val, "sw_cmp");
    let merge_bb = ctx.context.append_basic_block(fn_val, "sw_merge");
    let short_bb = ctx.builder.get_insert_block().unwrap();
    ctx.builder.build_conditional_branch(too_long, merge_bb, cmp_bb).unwrap();

    ctx.builder.position_at_end(cmp_bb);
    let cmp = ctx.builder.build_call(
        memcmp,
        &[hay_ptr.into(), prefix_ptr.into(), prefix_len.into()],
        "sw_cmp",
    ).unwrap().try_as_basic_value().left().unwrap().into_int_value();
    let matches = ctx.builder.build_int_compare(IntPredicate::EQ, cmp, ctx.context.i32_type().const_zero(), "sw_match").unwrap();
    let cmp_end_bb = ctx.builder.get_insert_block().unwrap();
    ctx.builder.build_unconditional_branch(merge_bb).unwrap();

    ctx.builder.position_at_end(merge_bb);
    let phi = ctx.builder.build_phi(ctx.context.bool_type(), "sw_result").unwrap();
    phi.add_incoming(&[
        (&ctx.context.bool_type().const_zero(), short_bb),
        (&matches, cmp_end_bb),
    ]);
    Some(phi.as_basic_value())
}

fn compile_str_starts_with<'ctx>(ctx: &mut CodegenCtx<'ctx>, inner: &Expr, args: &[CallArg]) -> Option<BasicValueEnum<'ctx>> {
    let val = compile_expr(ctx, inner)?;
    let (hay_ptr, hay_len) = extract_str_parts(ctx, val);
    let prefix = compile_expr(ctx, &args[0].expr)?;
    let (prefix_ptr, prefix_len) = extract_str_parts(ctx, prefix);
    compile_str_starts_with_impl(ctx, hay_ptr, hay_len, prefix_ptr, prefix_len)
}

/// Compile `s.ends_with(suffix)` for str.
fn compile_str_ends_with_impl<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    hay_ptr: inkwell::values::PointerValue<'ctx>,
    hay_len: inkwell::values::IntValue<'ctx>,
    suffix_ptr: inkwell::values::PointerValue<'ctx>,
    suffix_len: inkwell::values::IntValue<'ctx>,
) -> Option<BasicValueEnum<'ctx>> {
    let memcmp = ctx.module.get_function("memcmp")?;
    let too_long = ctx.builder.build_int_compare(IntPredicate::UGT, suffix_len, hay_len, "too_long").unwrap();

    let fn_val = ctx.builder.get_insert_block().unwrap().get_parent().unwrap();
    let cmp_bb = ctx.context.append_basic_block(fn_val, "ew_cmp");
    let merge_bb = ctx.context.append_basic_block(fn_val, "ew_merge");
    let short_bb = ctx.builder.get_insert_block().unwrap();
    ctx.builder.build_conditional_branch(too_long, merge_bb, cmp_bb).unwrap();

    ctx.builder.position_at_end(cmp_bb);
    let offset = ctx.builder.build_int_sub(hay_len, suffix_len, "ew_offset").unwrap();
    let hay_end = unsafe {
        ctx.builder.build_in_bounds_gep(ctx.context.i8_type(), hay_ptr, &[offset], "ew_ptr").unwrap()
    };
    let cmp = ctx.builder.build_call(
        memcmp,
        &[hay_end.into(), suffix_ptr.into(), suffix_len.into()],
        "ew_cmp",
    ).unwrap().try_as_basic_value().left().unwrap().into_int_value();
    let matches = ctx.builder.build_int_compare(IntPredicate::EQ, cmp, ctx.context.i32_type().const_zero(), "ew_match").unwrap();
    let cmp_end_bb = ctx.builder.get_insert_block().unwrap();
    ctx.builder.build_unconditional_branch(merge_bb).unwrap();

    ctx.builder.position_at_end(merge_bb);
    let phi = ctx.builder.build_phi(ctx.context.bool_type(), "ew_result").unwrap();
    phi.add_incoming(&[
        (&ctx.context.bool_type().const_zero(), short_bb),
        (&matches, cmp_end_bb),
    ]);
    Some(phi.as_basic_value())
}

fn compile_str_ends_with<'ctx>(ctx: &mut CodegenCtx<'ctx>, inner: &Expr, args: &[CallArg]) -> Option<BasicValueEnum<'ctx>> {
    let val = compile_expr(ctx, inner)?;
    let (hay_ptr, hay_len) = extract_str_parts(ctx, val);
    let suffix = compile_expr(ctx, &args[0].expr)?;
    let (suffix_ptr, suffix_len) = extract_str_parts(ctx, suffix);
    compile_str_ends_with_impl(ctx, hay_ptr, hay_len, suffix_ptr, suffix_len)
}

/// Compile `s.to_string()` for str → malloc + memcpy, return String { ptr, len, cap }.
fn compile_str_to_string<'ctx>(ctx: &mut CodegenCtx<'ctx>, inner: &Expr) -> Option<BasicValueEnum<'ctx>> {
    let malloc = ctx.module.get_function("malloc")?;
    let memcpy = ctx.module.get_function("memcpy")?;
    let ptr_ty = ctx.context.ptr_type(AddressSpace::default());
    let i64_ty = ctx.context.i64_type();
    let string_ty = ctx.context.struct_type(&[ptr_ty.into(), i64_ty.into(), i64_ty.into()], false);

    let val = compile_expr(ctx, inner)?;
    let (src_ptr, src_len) = extract_str_parts(ctx, val);

    let buf = ctx.builder.build_call(malloc, &[src_len.into()], "buf").unwrap()
        .try_as_basic_value().left().unwrap().into_pointer_value();
    ctx.builder.build_call(memcpy, &[buf.into(), src_ptr.into(), src_len.into()], "").unwrap();

    let mut sv = string_ty.get_undef();
    sv = ctx.builder.build_insert_value(sv, buf, 0, "str_ptr").unwrap().into_struct_value();
    sv = ctx.builder.build_insert_value(sv, src_len, 1, "str_len").unwrap().into_struct_value();
    sv = ctx.builder.build_insert_value(sv, src_len, 2, "str_cap").unwrap().into_struct_value();
    Some(sv.into())
}

/// Helper: trim_start implementation — returns (new_ptr, new_len) skipping leading whitespace.
fn compile_trim_start_impl<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    ptr: inkwell::values::PointerValue<'ctx>,
    len: inkwell::values::IntValue<'ctx>,
) -> (inkwell::values::PointerValue<'ctx>, inkwell::values::IntValue<'ctx>) {
    let i64_ty = ctx.context.i64_type();
    let i8_ty = ctx.context.i8_type();
    let fn_val = ctx.builder.get_insert_block().unwrap().get_parent().unwrap();

    let entry_bb = ctx.builder.get_insert_block().unwrap();
    let loop_bb = ctx.context.append_basic_block(fn_val, "trim_s_loop");
    let body_bb = ctx.context.append_basic_block(fn_val, "trim_s_body");
    let end_bb = ctx.context.append_basic_block(fn_val, "trim_s_end");

    ctx.builder.build_unconditional_branch(loop_bb).unwrap();

    // Loop: find first non-whitespace
    ctx.builder.position_at_end(loop_bb);
    let phi_i = ctx.builder.build_phi(i64_ty, "ts_i").unwrap();
    phi_i.add_incoming(&[(&i64_ty.const_zero(), entry_bb)]);
    let i = phi_i.as_basic_value().into_int_value();
    let in_range = ctx.builder.build_int_compare(IntPredicate::ULT, i, len, "ts_in_range").unwrap();
    ctx.builder.build_conditional_branch(in_range, body_bb, end_bb).unwrap();

    ctx.builder.position_at_end(body_bb);
    let byte_ptr = unsafe {
        ctx.builder.build_in_bounds_gep(i8_ty, ptr, &[i], "ts_byte_ptr").unwrap()
    };
    let byte = ctx.builder.build_load(i8_ty, byte_ptr, "ts_byte").unwrap().into_int_value();
    // Check for space (32), tab (9), newline (10), carriage return (13)
    let is_space = ctx.builder.build_int_compare(IntPredicate::EQ, byte, i8_ty.const_int(32, false), "is_sp").unwrap();
    let is_tab = ctx.builder.build_int_compare(IntPredicate::EQ, byte, i8_ty.const_int(9, false), "is_tab").unwrap();
    let is_nl = ctx.builder.build_int_compare(IntPredicate::EQ, byte, i8_ty.const_int(10, false), "is_nl").unwrap();
    let is_cr = ctx.builder.build_int_compare(IntPredicate::EQ, byte, i8_ty.const_int(13, false), "is_cr").unwrap();
    let ws1 = ctx.builder.build_or(is_space, is_tab, "ws1").unwrap();
    let ws2 = ctx.builder.build_or(is_nl, is_cr, "ws2").unwrap();
    let is_ws = ctx.builder.build_or(ws1, ws2, "is_ws").unwrap();
    let next_i = ctx.builder.build_int_add(i, i64_ty.const_int(1, false), "ts_next").unwrap();
    phi_i.add_incoming(&[(&next_i, body_bb)]);
    ctx.builder.build_conditional_branch(is_ws, loop_bb, end_bb).unwrap();

    ctx.builder.position_at_end(end_bb);
    let phi_start = ctx.builder.build_phi(i64_ty, "trim_start_idx").unwrap();
    phi_start.add_incoming(&[(&i, loop_bb), (&i, body_bb)]);
    let start_idx = phi_start.as_basic_value().into_int_value();
    let new_ptr = unsafe {
        ctx.builder.build_in_bounds_gep(i8_ty, ptr, &[start_idx], "trimmed_ptr").unwrap()
    };
    let new_len = ctx.builder.build_int_sub(len, start_idx, "trimmed_len").unwrap();
    (new_ptr, new_len)
}

/// Helper: trim_end implementation — returns new_len with trailing whitespace removed.
fn compile_trim_end_impl<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    ptr: inkwell::values::PointerValue<'ctx>,
    len: inkwell::values::IntValue<'ctx>,
) -> inkwell::values::IntValue<'ctx> {
    let i64_ty = ctx.context.i64_type();
    let i8_ty = ctx.context.i8_type();
    let fn_val = ctx.builder.get_insert_block().unwrap().get_parent().unwrap();

    let entry_bb = ctx.builder.get_insert_block().unwrap();
    let loop_bb = ctx.context.append_basic_block(fn_val, "trim_e_loop");
    let body_bb = ctx.context.append_basic_block(fn_val, "trim_e_body");
    let end_bb = ctx.context.append_basic_block(fn_val, "trim_e_end");

    ctx.builder.build_unconditional_branch(loop_bb).unwrap();

    // Loop: decrement from end
    ctx.builder.position_at_end(loop_bb);
    let phi_end = ctx.builder.build_phi(i64_ty, "te_end").unwrap();
    phi_end.add_incoming(&[(&len, entry_bb)]);
    let cur_end = phi_end.as_basic_value().into_int_value();
    let has_more = ctx.builder.build_int_compare(IntPredicate::UGT, cur_end, i64_ty.const_zero(), "te_more").unwrap();
    ctx.builder.build_conditional_branch(has_more, body_bb, end_bb).unwrap();

    ctx.builder.position_at_end(body_bb);
    let prev_idx = ctx.builder.build_int_sub(cur_end, i64_ty.const_int(1, false), "te_prev").unwrap();
    let byte_ptr = unsafe {
        ctx.builder.build_in_bounds_gep(i8_ty, ptr, &[prev_idx], "te_byte_ptr").unwrap()
    };
    let byte = ctx.builder.build_load(i8_ty, byte_ptr, "te_byte").unwrap().into_int_value();
    let is_space = ctx.builder.build_int_compare(IntPredicate::EQ, byte, i8_ty.const_int(32, false), "is_sp").unwrap();
    let is_tab = ctx.builder.build_int_compare(IntPredicate::EQ, byte, i8_ty.const_int(9, false), "is_tab").unwrap();
    let is_nl = ctx.builder.build_int_compare(IntPredicate::EQ, byte, i8_ty.const_int(10, false), "is_nl").unwrap();
    let is_cr = ctx.builder.build_int_compare(IntPredicate::EQ, byte, i8_ty.const_int(13, false), "is_cr").unwrap();
    let ws1 = ctx.builder.build_or(is_space, is_tab, "ws1").unwrap();
    let ws2 = ctx.builder.build_or(is_nl, is_cr, "ws2").unwrap();
    let is_ws = ctx.builder.build_or(ws1, ws2, "is_ws").unwrap();
    phi_end.add_incoming(&[(&prev_idx, body_bb)]);
    ctx.builder.build_conditional_branch(is_ws, loop_bb, end_bb).unwrap();

    ctx.builder.position_at_end(end_bb);
    let phi_result = ctx.builder.build_phi(i64_ty, "trim_end_len").unwrap();
    phi_result.add_incoming(&[(&cur_end, loop_bb), (&cur_end, body_bb)]);
    phi_result.as_basic_value().into_int_value()
}

fn compile_str_trim_start<'ctx>(ctx: &mut CodegenCtx<'ctx>, inner: &Expr) -> Option<BasicValueEnum<'ctx>> {
    let val = compile_expr(ctx, inner)?;
    let (ptr, len) = extract_str_parts(ctx, val);
    let (new_ptr, new_len) = compile_trim_start_impl(ctx, ptr, len);
    Some(build_str_struct(ctx, new_ptr, new_len))
}

fn compile_str_trim_end<'ctx>(ctx: &mut CodegenCtx<'ctx>, inner: &Expr) -> Option<BasicValueEnum<'ctx>> {
    let val = compile_expr(ctx, inner)?;
    let (ptr, len) = extract_str_parts(ctx, val);
    let new_len = compile_trim_end_impl(ctx, ptr, len);
    Some(build_str_struct(ctx, ptr, new_len))
}

fn compile_str_trim<'ctx>(ctx: &mut CodegenCtx<'ctx>, inner: &Expr) -> Option<BasicValueEnum<'ctx>> {
    let val = compile_expr(ctx, inner)?;
    let (ptr, len) = extract_str_parts(ctx, val);
    let (new_ptr, trimmed_start_len) = compile_trim_start_impl(ctx, ptr, len);
    let new_len = compile_trim_end_impl(ctx, new_ptr, trimmed_start_len);
    Some(build_str_struct(ctx, new_ptr, new_len))
}

// ---------------------------------------------------------------------------
// String new intrinsic methods (byte_at, contains, starts_with, ends_with,
// substring, clear, repeat, trim, trim_start, trim_end)
// ---------------------------------------------------------------------------

fn compile_string_byte_at<'ctx>(ctx: &mut CodegenCtx<'ctx>, inner: &Expr, args: &[CallArg]) -> Option<BasicValueEnum<'ctx>> {
    let val = compile_expr(ctx, inner)?;
    let (ptr, _) = extract_string_as_str_parts(ctx, val);
    let idx = compile_expr(ctx, &args[0].expr)?.into_int_value();
    let elem_ptr = unsafe {
        ctx.builder.build_in_bounds_gep(ctx.context.i8_type(), ptr, &[idx], "byte_ptr").unwrap()
    };
    let byte = ctx.builder.build_load(ctx.context.i8_type(), elem_ptr, "byte").unwrap().into_int_value();
    let result = ctx.builder.build_int_z_extend(byte, ctx.context.i64_type(), "byte_i64").unwrap();
    Some(result.into())
}

fn compile_string_contains<'ctx>(ctx: &mut CodegenCtx<'ctx>, inner: &Expr, args: &[CallArg]) -> Option<BasicValueEnum<'ctx>> {
    let val = compile_expr(ctx, inner)?;
    let (hay_ptr, hay_len) = extract_string_as_str_parts(ctx, val);
    let needle = compile_expr(ctx, &args[0].expr)?;
    let (needle_ptr, needle_len) = extract_str_parts(ctx, needle);
    compile_str_contains_impl(ctx, hay_ptr, hay_len, needle_ptr, needle_len)
}

fn compile_string_starts_with<'ctx>(ctx: &mut CodegenCtx<'ctx>, inner: &Expr, args: &[CallArg]) -> Option<BasicValueEnum<'ctx>> {
    let val = compile_expr(ctx, inner)?;
    let (hay_ptr, hay_len) = extract_string_as_str_parts(ctx, val);
    let prefix = compile_expr(ctx, &args[0].expr)?;
    let (prefix_ptr, prefix_len) = extract_str_parts(ctx, prefix);
    compile_str_starts_with_impl(ctx, hay_ptr, hay_len, prefix_ptr, prefix_len)
}

fn compile_string_ends_with<'ctx>(ctx: &mut CodegenCtx<'ctx>, inner: &Expr, args: &[CallArg]) -> Option<BasicValueEnum<'ctx>> {
    let val = compile_expr(ctx, inner)?;
    let (hay_ptr, hay_len) = extract_string_as_str_parts(ctx, val);
    let suffix = compile_expr(ctx, &args[0].expr)?;
    let (suffix_ptr, suffix_len) = extract_str_parts(ctx, suffix);
    compile_str_ends_with_impl(ctx, hay_ptr, hay_len, suffix_ptr, suffix_len)
}

fn compile_string_substring<'ctx>(ctx: &mut CodegenCtx<'ctx>, inner: &Expr, args: &[CallArg]) -> Option<BasicValueEnum<'ctx>> {
    let val = compile_expr(ctx, inner)?;
    let (ptr, _) = extract_string_as_str_parts(ctx, val);
    let start = compile_expr(ctx, &args[0].expr)?.into_int_value();
    let end = compile_expr(ctx, &args[1].expr)?.into_int_value();
    let new_len = ctx.builder.build_int_sub(end, start, "sub_len").unwrap();
    let new_ptr = unsafe {
        ctx.builder.build_in_bounds_gep(ctx.context.i8_type(), ptr, &[start], "sub_ptr").unwrap()
    };
    Some(build_str_struct(ctx, new_ptr, new_len))
}

fn compile_string_clear<'ctx>(ctx: &mut CodegenCtx<'ctx>, inner: &Expr) -> Option<BasicValueEnum<'ctx>> {
    let ptr_ty = ctx.context.ptr_type(AddressSpace::default());
    let i64_ty = ctx.context.i64_type();
    let string_ty = ctx.context.struct_type(&[ptr_ty.into(), i64_ty.into(), i64_ty.into()], false);
    let string_ptr = compile_expr_addr(ctx, inner)?;
    let len_field = ctx.builder.build_struct_gep(string_ty, string_ptr, 1, "len_field").unwrap();
    ctx.builder.build_store(len_field, i64_ty.const_zero()).unwrap();
    None
}

fn compile_string_repeat<'ctx>(ctx: &mut CodegenCtx<'ctx>, inner: &Expr, args: &[CallArg]) -> Option<BasicValueEnum<'ctx>> {
    let malloc = ctx.module.get_function("malloc")?;
    let memcpy = ctx.module.get_function("memcpy")?;
    let ptr_ty = ctx.context.ptr_type(AddressSpace::default());
    let i64_ty = ctx.context.i64_type();
    let string_ty = ctx.context.struct_type(&[ptr_ty.into(), i64_ty.into(), i64_ty.into()], false);

    let val = compile_expr(ctx, inner)?;
    let (src_ptr, src_len) = extract_string_as_str_parts(ctx, val);
    let n = compile_expr(ctx, &args[0].expr)?.into_int_value();

    // total_len = src_len * n
    let total_len = ctx.builder.build_int_mul(src_len, n, "total_len").unwrap();
    let buf = ctx.builder.build_call(malloc, &[total_len.into()], "repeat_buf").unwrap()
        .try_as_basic_value().left().unwrap().into_pointer_value();

    // Loop: copy src_len bytes n times
    let fn_val = ctx.builder.get_insert_block().unwrap().get_parent().unwrap();
    let entry_bb = ctx.builder.get_insert_block().unwrap();
    let loop_bb = ctx.context.append_basic_block(fn_val, "repeat_loop");
    let body_bb = ctx.context.append_basic_block(fn_val, "repeat_body");
    let end_bb = ctx.context.append_basic_block(fn_val, "repeat_end");

    ctx.builder.build_unconditional_branch(loop_bb).unwrap();

    ctx.builder.position_at_end(loop_bb);
    let phi_i = ctx.builder.build_phi(i64_ty, "rep_i").unwrap();
    phi_i.add_incoming(&[(&i64_ty.const_zero(), entry_bb)]);
    let i = phi_i.as_basic_value().into_int_value();
    let cond = ctx.builder.build_int_compare(IntPredicate::ULT, i, n, "rep_cond").unwrap();
    ctx.builder.build_conditional_branch(cond, body_bb, end_bb).unwrap();

    ctx.builder.position_at_end(body_bb);
    let offset = ctx.builder.build_int_mul(i, src_len, "rep_offset").unwrap();
    let dst = unsafe {
        ctx.builder.build_in_bounds_gep(ctx.context.i8_type(), buf, &[offset], "rep_dst").unwrap()
    };
    ctx.builder.build_call(memcpy, &[dst.into(), src_ptr.into(), src_len.into()], "").unwrap();
    let next_i = ctx.builder.build_int_add(i, i64_ty.const_int(1, false), "rep_next").unwrap();
    phi_i.add_incoming(&[(&next_i, body_bb)]);
    ctx.builder.build_unconditional_branch(loop_bb).unwrap();

    ctx.builder.position_at_end(end_bb);
    let mut sv = string_ty.get_undef();
    sv = ctx.builder.build_insert_value(sv, buf, 0, "rep_ptr").unwrap().into_struct_value();
    sv = ctx.builder.build_insert_value(sv, total_len, 1, "rep_len").unwrap().into_struct_value();
    sv = ctx.builder.build_insert_value(sv, total_len, 2, "rep_cap").unwrap().into_struct_value();
    Some(sv.into())
}

fn compile_string_trim<'ctx>(ctx: &mut CodegenCtx<'ctx>, inner: &Expr) -> Option<BasicValueEnum<'ctx>> {
    let val = compile_expr(ctx, inner)?;
    let (ptr, len) = extract_string_as_str_parts(ctx, val);
    let (new_ptr, trimmed_start_len) = compile_trim_start_impl(ctx, ptr, len);
    let new_len = compile_trim_end_impl(ctx, new_ptr, trimmed_start_len);
    Some(build_str_struct(ctx, new_ptr, new_len))
}

fn compile_string_trim_start<'ctx>(ctx: &mut CodegenCtx<'ctx>, inner: &Expr) -> Option<BasicValueEnum<'ctx>> {
    let val = compile_expr(ctx, inner)?;
    let (ptr, len) = extract_string_as_str_parts(ctx, val);
    let (new_ptr, new_len) = compile_trim_start_impl(ctx, ptr, len);
    Some(build_str_struct(ctx, new_ptr, new_len))
}

fn compile_string_trim_end<'ctx>(ctx: &mut CodegenCtx<'ctx>, inner: &Expr) -> Option<BasicValueEnum<'ctx>> {
    let val = compile_expr(ctx, inner)?;
    let (ptr, len) = extract_string_as_str_parts(ctx, val);
    let new_len = compile_trim_end_impl(ctx, ptr, len);
    Some(build_str_struct(ctx, ptr, new_len))
}

// ---------------------------------------------------------------------------
// Array[T] intrinsic methods
// ---------------------------------------------------------------------------

/// Helper: check if a Ty is Array[T] struct.
pub fn is_array_struct_ty(ctx: &CodegenCtx, ty: &Ty) -> bool {
    if let Ty::Struct { def_id, .. } = ty {
        ctx.resolved.symbols.iter()
            .any(|s| s.def_id == *def_id && s.name == "Array")
    } else {
        false
    }
}

/// Helper: get the element type T from Array[T].
fn get_array_elem_ty(ty: &Ty) -> Ty {
    match ty {
        Ty::Struct { type_args, .. } if !type_args.is_empty() => type_args[0].clone(),
        _ => Ty::Prim(PrimTy::I64),
    }
}

// ---------------------------------------------------------------------------
// HashMap[K, V] intrinsics
// ---------------------------------------------------------------------------

/// Get the LLVM struct type for HashMap: { ptr, ptr, ptr, i64, i64 }
fn hashmap_llvm_ty<'ctx>(ctx: &CodegenCtx<'ctx>) -> inkwell::types::StructType<'ctx> {
    let ptr_ty = ctx.context.ptr_type(AddressSpace::default());
    let i64_ty = ctx.context.i64_type();
    ctx.context.struct_type(
        &[ptr_ty.into(), ptr_ty.into(), ptr_ty.into(), i64_ty.into(), i64_ty.into()],
        false,
    )
}

/// Compile `HashMap[K, V].new()` → `{ null, null, null, 0, 0 }`
fn compile_hashmap_new<'ctx>(ctx: &CodegenCtx<'ctx>) -> Option<BasicValueEnum<'ctx>> {
    let hm_ty = hashmap_llvm_ty(ctx);
    let ptr_ty = ctx.context.ptr_type(AddressSpace::default());
    let i64_ty = ctx.context.i64_type();
    let null = ptr_ty.const_null();
    let zero = i64_ty.const_zero();
    let mut sv = hm_ty.get_undef();
    sv = ctx.builder.build_insert_value(sv, null, 0, "hm_keys").unwrap().into_struct_value();
    sv = ctx.builder.build_insert_value(sv, null, 1, "hm_vals").unwrap().into_struct_value();
    sv = ctx.builder.build_insert_value(sv, null, 2, "hm_states").unwrap().into_struct_value();
    sv = ctx.builder.build_insert_value(sv, zero, 3, "hm_size").unwrap().into_struct_value();
    sv = ctx.builder.build_insert_value(sv, zero, 4, "hm_cap").unwrap().into_struct_value();
    Some(sv.into())
}

/// Compile `m.len()` → extract field 3 (_size)
fn compile_hashmap_len<'ctx>(ctx: &mut CodegenCtx<'ctx>, inner: &Expr) -> Option<BasicValueEnum<'ctx>> {
    let val = compile_expr(ctx, inner)?;
    let sv = val.into_struct_value();
    Some(ctx.builder.build_extract_value(sv, 3, "hm_size").unwrap().into())
}

/// Compile `m.is_empty()` → field 3 == 0
fn compile_hashmap_is_empty<'ctx>(ctx: &mut CodegenCtx<'ctx>, inner: &Expr) -> Option<BasicValueEnum<'ctx>> {
    let val = compile_expr(ctx, inner)?;
    let sv = val.into_struct_value();
    let size = ctx.builder.build_extract_value(sv, 3, "hm_size").unwrap().into_int_value();
    let zero = ctx.context.i64_type().const_zero();
    let cmp = ctx.builder.build_int_compare(IntPredicate::EQ, size, zero, "is_empty").unwrap();
    Some(cmp.into())
}

/// Emit a hash computation for a key. Returns an i64 hash value.
fn emit_hash_key<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    key_val: BasicValueEnum<'ctx>,
    _key_ty: &Ty,
) -> inkwell::values::IntValue<'ctx> {
    let i64_ty = ctx.context.i64_type();
    // Knuth multiplicative hash: key * 2654435761 >> 16
    // Works for integer types. For other types, cast to i64 first.
    let key_int = if key_val.is_int_value() {
        let iv = key_val.into_int_value();
        if iv.get_type().get_bit_width() != 64 {
            ctx.builder.build_int_z_extend_or_bit_cast(iv, i64_ty, "key_i64").unwrap()
        } else {
            iv
        }
    } else if key_val.is_float_value() {
        ctx.builder.build_float_to_signed_int(key_val.into_float_value(), i64_ty, "key_i64").unwrap()
    } else if key_val.is_struct_value() {
        // String key: FNV-1a hash
        return emit_fnv1a_hash(ctx, key_val);
    } else {
        i64_ty.const_zero()
    };
    let mul_const = i64_ty.const_int(2654435761, false);
    let product = ctx.builder.build_int_mul(key_int, mul_const, "hash_mul").unwrap();
    let shift = i64_ty.const_int(16, false);
    ctx.builder.build_right_shift(product, shift, false, "hash").unwrap()
}

/// Emit FNV-1a hash for String keys.
fn emit_fnv1a_hash<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    key_val: BasicValueEnum<'ctx>,
) -> inkwell::values::IntValue<'ctx> {
    let i64_ty = ctx.context.i64_type();
    let i8_ty = ctx.context.i8_type();

    let sv = key_val.into_struct_value();
    let ptr = ctx.builder.build_extract_value(sv, 0, "str_ptr").unwrap().into_pointer_value();
    let len = ctx.builder.build_extract_value(sv, 1, "str_len").unwrap().into_int_value();

    let fn_val = ctx.builder.get_insert_block().unwrap().get_parent().unwrap();

    // FNV offset basis
    let offset_basis = i64_ty.const_int(14695981039346656037u64, false);
    let fnv_prime = i64_ty.const_int(1099511628211, false);

    let preloop_bb = ctx.builder.get_insert_block().unwrap();
    let loop_bb = ctx.context.append_basic_block(fn_val, "fnv_loop");
    let done_bb = ctx.context.append_basic_block(fn_val, "fnv_done");

    let zero = i64_ty.const_zero();
    ctx.builder.build_unconditional_branch(loop_bb).unwrap();

    // Loop body
    ctx.builder.position_at_end(loop_bb);
    let idx_phi = ctx.builder.build_phi(i64_ty, "idx").unwrap();
    let hash_phi = ctx.builder.build_phi(i64_ty, "hash").unwrap();
    idx_phi.add_incoming(&[(&zero, preloop_bb)]);
    hash_phi.add_incoming(&[(&offset_basis, preloop_bb)]);

    let idx = idx_phi.as_basic_value().into_int_value();
    let hash = hash_phi.as_basic_value().into_int_value();

    let at_end = ctx.builder.build_int_compare(IntPredicate::UGE, idx, len, "at_end").unwrap();
    let body_bb = ctx.context.append_basic_block(fn_val, "fnv_body");
    ctx.builder.build_conditional_branch(at_end, done_bb, body_bb).unwrap();

    ctx.builder.position_at_end(body_bb);
    let byte_ptr = unsafe { ctx.builder.build_in_bounds_gep(i8_ty, ptr, &[idx], "byte_ptr").unwrap() };
    let byte = ctx.builder.build_load(i8_ty, byte_ptr, "byte").unwrap().into_int_value();
    let byte_ext = ctx.builder.build_int_z_extend(byte, i64_ty, "byte_ext").unwrap();
    let xored = ctx.builder.build_xor(hash, byte_ext, "xor").unwrap();
    let new_hash = ctx.builder.build_int_mul(xored, fnv_prime, "mul").unwrap();
    let one = i64_ty.const_int(1, false);
    let next_idx = ctx.builder.build_int_add(idx, one, "next_idx").unwrap();
    idx_phi.add_incoming(&[(&next_idx, body_bb)]);
    hash_phi.add_incoming(&[(&new_hash, body_bb)]);
    ctx.builder.build_unconditional_branch(loop_bb).unwrap();

    // Done
    ctx.builder.position_at_end(done_bb);
    hash_phi.as_basic_value().into_int_value()
}

/// Emit key comparison. Returns i1.
fn emit_key_equal<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    key_a: BasicValueEnum<'ctx>,
    key_b: BasicValueEnum<'ctx>,
    key_ty: &Ty,
) -> inkwell::values::IntValue<'ctx> {
    if let Some(name) = get_type_name_for_method_ctx(ctx, key_ty) {
        if name == "String" {
            // Use compile_string_compare logic inline
            return emit_string_equal(ctx, key_a, key_b);
        }
    }
    // For integers and bools
    if key_a.is_int_value() {
        return ctx.builder.build_int_compare(
            IntPredicate::EQ,
            key_a.into_int_value(),
            key_b.into_int_value(),
            "key_eq",
        ).unwrap();
    }
    if key_a.is_float_value() {
        return ctx.builder.build_float_compare(
            FloatPredicate::OEQ,
            key_a.into_float_value(),
            key_b.into_float_value(),
            "key_eq",
        ).unwrap();
    }
    // Fallback
    ctx.context.bool_type().const_zero()
}

/// String equality without going through the BinOp path.
fn emit_string_equal<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    lhs: BasicValueEnum<'ctx>,
    rhs: BasicValueEnum<'ctx>,
) -> inkwell::values::IntValue<'ctx> {
    let memcmp = ctx.module.get_function("memcmp").unwrap();
    let lhs_struct = lhs.into_struct_value();
    let lhs_ptr = ctx.builder.build_extract_value(lhs_struct, 0, "l_ptr").unwrap().into_pointer_value();
    let lhs_len = ctx.builder.build_extract_value(lhs_struct, 1, "l_len").unwrap().into_int_value();
    let rhs_struct = rhs.into_struct_value();
    let rhs_ptr = ctx.builder.build_extract_value(rhs_struct, 0, "r_ptr").unwrap().into_pointer_value();
    let rhs_len = ctx.builder.build_extract_value(rhs_struct, 1, "r_len").unwrap().into_int_value();

    let len_eq = ctx.builder.build_int_compare(IntPredicate::EQ, lhs_len, rhs_len, "len_eq").unwrap();
    let cmp_result = ctx.builder.build_call(
        memcmp, &[lhs_ptr.into(), rhs_ptr.into(), lhs_len.into()], "memcmp",
    ).unwrap().try_as_basic_value().left().unwrap().into_int_value();
    let zero_i32 = ctx.context.i32_type().const_zero();
    let content_eq = ctx.builder.build_int_compare(IntPredicate::EQ, cmp_result, zero_i32, "content_eq").unwrap();
    ctx.builder.build_and(len_eq, content_eq, "str_eq").unwrap()
}

/// Build an Option[V] LLVM value wrapping Some(val) or None.
fn build_option_value<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    call_expr: &Expr,
    val: Option<BasicValueEnum<'ctx>>,
    _val_ty: &Ty,
) -> Option<BasicValueEnum<'ctx>> {
    let option_ty = get_expr_ty(ctx, call_expr);
    let option_llvm_ty = ty_to_llvm(ctx, &option_ty);
    let (option_def_id, option_type_args) = match &option_ty {
        Ty::Enum { def_id, type_args, .. } => (*def_id, type_args.clone()),
        _ => return None,
    };
    let variants = ctx.type_env.enum_variants.get(&option_def_id)?.clone();
    let max_bytes = enum_max_payload_bytes(ctx, option_def_id, &option_type_args);

    let alloca = ctx.builder.build_alloca(option_llvm_ty, "option_val").unwrap();

    let tag_ptr = ctx.builder.build_struct_gep(option_llvm_ty, alloca, 0, "tag_ptr").unwrap();

    match val {
        Some(v) => {
            // Some variant (index 0)
            ctx.builder.build_store(tag_ptr, ctx.context.i8_type().const_int(0, false)).unwrap();
            if max_bytes > 0 {
                let payload_ptr = ctx.builder.build_struct_gep(option_llvm_ty, alloca, 1, "payload_ptr").unwrap();
                let some_fields = &variants[0].2;
                let subst = build_subst_map(ctx, option_def_id, &option_type_args);
                let vs_ty = variant_struct_type(ctx, some_fields, &subst);
                let value_ptr = ctx.builder.build_struct_gep(vs_ty, payload_ptr, 0, "value_ptr").unwrap();
                ctx.builder.build_store(value_ptr, v).unwrap();
            }
        }
        None => {
            // None variant (index 1)
            ctx.builder.build_store(tag_ptr, ctx.context.i8_type().const_int(1, false)).unwrap();
        }
    }

    Some(ctx.builder.build_load(option_llvm_ty, alloca, "option_load").unwrap())
}

/// Emit the grow/init logic for HashMap. Works on the struct pointer.
/// Ensures capacity is sufficient. If cap is 0, initializes with cap=8.
fn emit_hashmap_grow<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    hm_ptr: PointerValue<'ctx>,
    key_ty: &Ty,
    val_ty: &Ty,
) {
    let ptr_ty = ctx.context.ptr_type(AddressSpace::default());
    let i64_ty = ctx.context.i64_type();
    let i8_ty = ctx.context.i8_type();
    let hm_ty = hashmap_llvm_ty(ctx);
    let malloc = ctx.module.get_function("malloc").unwrap();
    let free_fn = ctx.module.get_function("free").unwrap();

    let key_llvm_ty = ty_to_llvm(ctx, key_ty);
    let val_llvm_ty = ty_to_llvm(ctx, val_ty);

    // Load current size and cap
    let size_field = ctx.builder.build_struct_gep(hm_ty, hm_ptr, 3, "size_field").unwrap();
    let cap_field = ctx.builder.build_struct_gep(hm_ty, hm_ptr, 4, "cap_field").unwrap();
    let cur_size = ctx.builder.build_load(i64_ty, size_field, "cur_size").unwrap().into_int_value();
    let cur_cap = ctx.builder.build_load(i64_ty, cap_field, "cur_cap").unwrap().into_int_value();

    // Check: size * 2 >= cap → need grow
    let two = i64_ty.const_int(2, false);
    let size_x2 = ctx.builder.build_int_mul(cur_size, two, "size_x2").unwrap();
    let needs_grow = ctx.builder.build_int_compare(IntPredicate::UGE, size_x2, cur_cap, "needs_grow").unwrap();

    let fn_val = ctx.builder.get_insert_block().unwrap().get_parent().unwrap();
    let grow_bb = ctx.context.append_basic_block(fn_val, "hm_grow");
    let done_bb = ctx.context.append_basic_block(fn_val, "hm_grow_done");
    ctx.builder.build_conditional_branch(needs_grow, grow_bb, done_bb).unwrap();

    ctx.builder.position_at_end(grow_bb);

    // new_cap = max(cap * 2, 8)
    let cap_doubled = ctx.builder.build_int_mul(cur_cap, two, "cap_x2").unwrap();
    let eight = i64_ty.const_int(8, false);
    let use_doubled = ctx.builder.build_int_compare(IntPredicate::UGT, cap_doubled, eight, "use_d").unwrap();
    let new_cap = ctx.builder.build_select(use_doubled, cap_doubled, eight, "new_cap").unwrap().into_int_value();

    // Allocate new arrays
    let key_size = key_llvm_ty.size_of().unwrap();
    let key_size_i64 = ctx.builder.build_int_cast(key_size, i64_ty, "key_sz").unwrap();
    let keys_bytes = ctx.builder.build_int_mul(new_cap, key_size_i64, "keys_bytes").unwrap();
    let new_keys = ctx.builder.build_call(malloc, &[keys_bytes.into()], "new_keys").unwrap()
        .try_as_basic_value().left().unwrap().into_pointer_value();

    let val_size = val_llvm_ty.size_of().unwrap();
    let val_size_i64 = ctx.builder.build_int_cast(val_size, i64_ty, "val_sz").unwrap();
    let vals_bytes = ctx.builder.build_int_mul(new_cap, val_size_i64, "vals_bytes").unwrap();
    let new_vals = ctx.builder.build_call(malloc, &[vals_bytes.into()], "new_vals").unwrap()
        .try_as_basic_value().left().unwrap().into_pointer_value();

    let new_states = ctx.builder.build_call(malloc, &[new_cap.into()], "new_states").unwrap()
        .try_as_basic_value().left().unwrap().into_pointer_value();

    // Zero out states (all empty = 0)
    // Memset-like loop
    let memset_pre = ctx.builder.get_insert_block().unwrap();
    let memset_loop = ctx.context.append_basic_block(fn_val, "memset_loop");
    let memset_done = ctx.context.append_basic_block(fn_val, "memset_done");
    let zero_i64 = i64_ty.const_zero();
    ctx.builder.build_unconditional_branch(memset_loop).unwrap();

    ctx.builder.position_at_end(memset_loop);
    let ms_idx = ctx.builder.build_phi(i64_ty, "ms_idx").unwrap();
    ms_idx.add_incoming(&[(&zero_i64, memset_pre)]);
    let ms_i = ms_idx.as_basic_value().into_int_value();
    let ms_done = ctx.builder.build_int_compare(IntPredicate::UGE, ms_i, new_cap, "ms_done").unwrap();
    let ms_body = ctx.context.append_basic_block(fn_val, "ms_body");
    ctx.builder.build_conditional_branch(ms_done, memset_done, ms_body).unwrap();

    ctx.builder.position_at_end(ms_body);
    let state_ptr = unsafe { ctx.builder.build_in_bounds_gep(i8_ty, new_states, &[ms_i], "st_ptr").unwrap() };
    ctx.builder.build_store(state_ptr, i8_ty.const_zero()).unwrap();
    let one = i64_ty.const_int(1, false);
    let ms_next = ctx.builder.build_int_add(ms_i, one, "ms_next").unwrap();
    ms_idx.add_incoming(&[(&ms_next, ms_body)]);
    ctx.builder.build_unconditional_branch(memset_loop).unwrap();

    ctx.builder.position_at_end(memset_done);

    // Rehash old entries into new arrays
    let old_keys_field = ctx.builder.build_struct_gep(hm_ty, hm_ptr, 0, "old_keys_f").unwrap();
    let old_vals_field = ctx.builder.build_struct_gep(hm_ty, hm_ptr, 1, "old_vals_f").unwrap();
    let old_states_field = ctx.builder.build_struct_gep(hm_ty, hm_ptr, 2, "old_states_f").unwrap();
    let old_keys = ctx.builder.build_load(ptr_ty, old_keys_field, "old_keys").unwrap().into_pointer_value();
    let old_vals = ctx.builder.build_load(ptr_ty, old_vals_field, "old_vals").unwrap().into_pointer_value();
    let old_states = ctx.builder.build_load(ptr_ty, old_states_field, "old_states").unwrap().into_pointer_value();

    // Check if old_keys is null (first init, no rehash needed)
    let old_is_null = ctx.builder.build_is_null(old_keys, "old_null").unwrap();
    let rehash_bb = ctx.context.append_basic_block(fn_val, "rehash");
    let store_new_bb = ctx.context.append_basic_block(fn_val, "store_new");
    ctx.builder.build_conditional_branch(old_is_null, store_new_bb, rehash_bb).unwrap();

    // Rehash loop
    ctx.builder.position_at_end(rehash_bb);
    let rh_pre = ctx.builder.get_insert_block().unwrap();
    let rh_loop = ctx.context.append_basic_block(fn_val, "rh_loop");
    let rh_done = ctx.context.append_basic_block(fn_val, "rh_done");
    ctx.builder.build_unconditional_branch(rh_loop).unwrap();

    ctx.builder.position_at_end(rh_loop);
    let rh_idx = ctx.builder.build_phi(i64_ty, "rh_idx").unwrap();
    rh_idx.add_incoming(&[(&zero_i64, rh_pre)]);
    let rh_i = rh_idx.as_basic_value().into_int_value();
    let rh_end = ctx.builder.build_int_compare(IntPredicate::UGE, rh_i, cur_cap, "rh_end").unwrap();
    let rh_body = ctx.context.append_basic_block(fn_val, "rh_body");
    ctx.builder.build_conditional_branch(rh_end, rh_done, rh_body).unwrap();

    ctx.builder.position_at_end(rh_body);
    // Check if old state[i] == 1 (occupied)
    let old_st_ptr = unsafe { ctx.builder.build_in_bounds_gep(i8_ty, old_states, &[rh_i], "old_st").unwrap() };
    let old_st = ctx.builder.build_load(i8_ty, old_st_ptr, "old_st_v").unwrap().into_int_value();
    let is_occupied = ctx.builder.build_int_compare(IntPredicate::EQ, old_st, i8_ty.const_int(1, false), "is_occ").unwrap();
    let rh_insert = ctx.context.append_basic_block(fn_val, "rh_insert");
    let rh_next = ctx.context.append_basic_block(fn_val, "rh_next");
    ctx.builder.build_conditional_branch(is_occupied, rh_insert, rh_next).unwrap();

    ctx.builder.position_at_end(rh_insert);
    // Load old key and value
    let old_key_ptr = unsafe { ctx.builder.build_in_bounds_gep(key_llvm_ty, old_keys, &[rh_i], "old_k_ptr").unwrap() };
    let old_key = ctx.builder.build_load(key_llvm_ty, old_key_ptr, "old_key").unwrap();
    let old_val_ptr = unsafe { ctx.builder.build_in_bounds_gep(val_llvm_ty, old_vals, &[rh_i], "old_v_ptr").unwrap() };
    let old_val = ctx.builder.build_load(val_llvm_ty, old_val_ptr, "old_val").unwrap();

    // Hash the old key and probe into new arrays
    let hash = emit_hash_key(ctx, old_key, key_ty);
    let slot = ctx.builder.build_int_unsigned_rem(hash, new_cap, "slot").unwrap();

    // Linear probe to find empty slot in new arrays
    let probe_pre = ctx.builder.get_insert_block().unwrap();
    let probe_loop = ctx.context.append_basic_block(fn_val, "rh_probe");
    let probe_store = ctx.context.append_basic_block(fn_val, "rh_probe_store");
    ctx.builder.build_unconditional_branch(probe_loop).unwrap();

    ctx.builder.position_at_end(probe_loop);
    let probe_idx = ctx.builder.build_phi(i64_ty, "pr_idx").unwrap();
    probe_idx.add_incoming(&[(&slot, probe_pre)]);
    let pr_i = probe_idx.as_basic_value().into_int_value();
    let new_st_ptr = unsafe { ctx.builder.build_in_bounds_gep(i8_ty, new_states, &[pr_i], "new_st").unwrap() };
    let new_st = ctx.builder.build_load(i8_ty, new_st_ptr, "new_st_v").unwrap().into_int_value();
    let slot_empty = ctx.builder.build_int_compare(IntPredicate::EQ, new_st, i8_ty.const_zero(), "slot_empty").unwrap();
    let probe_advance = ctx.context.append_basic_block(fn_val, "rh_probe_adv");
    ctx.builder.build_conditional_branch(slot_empty, probe_store, probe_advance).unwrap();

    ctx.builder.position_at_end(probe_advance);
    let next_pr = ctx.builder.build_int_add(pr_i, one, "next_pr").unwrap();
    let wrapped = ctx.builder.build_int_unsigned_rem(next_pr, new_cap, "wrapped").unwrap();
    probe_idx.add_incoming(&[(&wrapped, probe_advance)]);
    ctx.builder.build_unconditional_branch(probe_loop).unwrap();

    ctx.builder.position_at_end(probe_store);
    // Store key, value, state=1
    let nk_ptr = unsafe { ctx.builder.build_in_bounds_gep(key_llvm_ty, new_keys, &[pr_i], "nk_ptr").unwrap() };
    ctx.builder.build_store(nk_ptr, old_key).unwrap();
    let nv_ptr = unsafe { ctx.builder.build_in_bounds_gep(val_llvm_ty, new_vals, &[pr_i], "nv_ptr").unwrap() };
    ctx.builder.build_store(nv_ptr, old_val).unwrap();
    ctx.builder.build_store(new_st_ptr, i8_ty.const_int(1, false)).unwrap();
    ctx.builder.build_unconditional_branch(rh_next).unwrap();

    ctx.builder.position_at_end(rh_next);
    let rh_next_i = ctx.builder.build_int_add(rh_i, one, "rh_next_i").unwrap();
    rh_idx.add_incoming(&[(&rh_next_i, rh_next)]);
    ctx.builder.build_unconditional_branch(rh_loop).unwrap();

    // After rehash, free old arrays
    ctx.builder.position_at_end(rh_done);
    ctx.builder.build_call(free_fn, &[old_keys.into()], "").unwrap();
    ctx.builder.build_call(free_fn, &[old_vals.into()], "").unwrap();
    ctx.builder.build_call(free_fn, &[old_states.into()], "").unwrap();
    ctx.builder.build_unconditional_branch(store_new_bb).unwrap();

    // Store new pointers and cap
    ctx.builder.position_at_end(store_new_bb);
    ctx.builder.build_store(old_keys_field, new_keys).unwrap();
    ctx.builder.build_store(old_vals_field, new_vals).unwrap();
    ctx.builder.build_store(old_states_field, new_states).unwrap();
    ctx.builder.build_store(cap_field, new_cap).unwrap();

    ctx.builder.build_unconditional_branch(done_bb).unwrap();
    ctx.builder.position_at_end(done_bb);
}

/// Compile `m.insert(key, value)`.
fn compile_hashmap_insert<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    inner: &Expr,
    args: &[CallArg],
    key_ty: &Ty,
    val_ty: &Ty,
) -> Option<BasicValueEnum<'ctx>> {
    let ptr_ty = ctx.context.ptr_type(AddressSpace::default());
    let i64_ty = ctx.context.i64_type();
    let i8_ty = ctx.context.i8_type();
    let hm_ty = hashmap_llvm_ty(ctx);
    let key_llvm_ty = ty_to_llvm(ctx, key_ty);
    let val_llvm_ty = ty_to_llvm(ctx, val_ty);

    let hm_ptr = compile_expr_addr(ctx, inner)?;
    let key_val = compile_expr(ctx, &args[0].expr)?;
    let value_val = compile_expr(ctx, &args[1].expr)?;

    // Grow if needed
    emit_hashmap_grow(ctx, hm_ptr, key_ty, val_ty);

    // Load current state
    let keys_field = ctx.builder.build_struct_gep(hm_ty, hm_ptr, 0, "keys_f").unwrap();
    let vals_field = ctx.builder.build_struct_gep(hm_ty, hm_ptr, 1, "vals_f").unwrap();
    let states_field = ctx.builder.build_struct_gep(hm_ty, hm_ptr, 2, "states_f").unwrap();
    let size_field = ctx.builder.build_struct_gep(hm_ty, hm_ptr, 3, "size_f").unwrap();
    let cap_field = ctx.builder.build_struct_gep(hm_ty, hm_ptr, 4, "cap_f").unwrap();

    let keys_ptr = ctx.builder.build_load(ptr_ty, keys_field, "keys").unwrap().into_pointer_value();
    let vals_ptr = ctx.builder.build_load(ptr_ty, vals_field, "vals").unwrap().into_pointer_value();
    let states_ptr = ctx.builder.build_load(ptr_ty, states_field, "states").unwrap().into_pointer_value();
    let cap = ctx.builder.build_load(i64_ty, cap_field, "cap").unwrap().into_int_value();

    // Hash and find slot
    let hash = emit_hash_key(ctx, key_val, key_ty);
    let slot = ctx.builder.build_int_unsigned_rem(hash, cap, "slot").unwrap();

    let fn_val = ctx.builder.get_insert_block().unwrap().get_parent().unwrap();
    let probe_pre = ctx.builder.get_insert_block().unwrap();
    let probe_loop = ctx.context.append_basic_block(fn_val, "ins_probe");
    let store_new = ctx.context.append_basic_block(fn_val, "ins_store_new");
    let overwrite = ctx.context.append_basic_block(fn_val, "ins_overwrite");
    let done = ctx.context.append_basic_block(fn_val, "ins_done");
    ctx.builder.build_unconditional_branch(probe_loop).unwrap();

    // Probe loop
    ctx.builder.position_at_end(probe_loop);
    let p_idx = ctx.builder.build_phi(i64_ty, "p_idx").unwrap();
    p_idx.add_incoming(&[(&slot, probe_pre)]);
    let pi = p_idx.as_basic_value().into_int_value();

    let st_ptr = unsafe { ctx.builder.build_in_bounds_gep(i8_ty, states_ptr, &[pi], "st").unwrap() };
    let state = ctx.builder.build_load(i8_ty, st_ptr, "state").unwrap().into_int_value();

    // state == 0 (empty) or state == 2 (tombstone) → store new
    let is_empty = ctx.builder.build_int_compare(IntPredicate::EQ, state, i8_ty.const_zero(), "is_empty").unwrap();
    let is_tombstone = ctx.builder.build_int_compare(IntPredicate::EQ, state, i8_ty.const_int(2, false), "is_tomb").unwrap();
    let can_store = ctx.builder.build_or(is_empty, is_tombstone, "can_store").unwrap();

    let check_key = ctx.context.append_basic_block(fn_val, "ins_check_key");
    ctx.builder.build_conditional_branch(can_store, store_new, check_key).unwrap();

    // Check if occupied slot has matching key
    ctx.builder.position_at_end(check_key);
    let existing_key_ptr = unsafe { ctx.builder.build_in_bounds_gep(key_llvm_ty, keys_ptr, &[pi], "ek_ptr").unwrap() };
    let existing_key = ctx.builder.build_load(key_llvm_ty, existing_key_ptr, "ek").unwrap();
    let keys_match = emit_key_equal(ctx, key_val, existing_key, key_ty);
    let advance = ctx.context.append_basic_block(fn_val, "ins_advance");
    ctx.builder.build_conditional_branch(keys_match, overwrite, advance).unwrap();

    // Advance probe
    ctx.builder.position_at_end(advance);
    let one = i64_ty.const_int(1, false);
    let next = ctx.builder.build_int_add(pi, one, "next").unwrap();
    let wrapped = ctx.builder.build_int_unsigned_rem(next, cap, "wrapped").unwrap();
    p_idx.add_incoming(&[(&wrapped, advance)]);
    ctx.builder.build_unconditional_branch(probe_loop).unwrap();

    // Store new entry
    ctx.builder.position_at_end(store_new);
    let k_ptr = unsafe { ctx.builder.build_in_bounds_gep(key_llvm_ty, keys_ptr, &[pi], "k_ptr").unwrap() };
    ctx.builder.build_store(k_ptr, key_val).unwrap();
    let v_ptr = unsafe { ctx.builder.build_in_bounds_gep(val_llvm_ty, vals_ptr, &[pi], "v_ptr").unwrap() };
    ctx.builder.build_store(v_ptr, value_val).unwrap();
    ctx.builder.build_store(st_ptr, i8_ty.const_int(1, false)).unwrap();
    // size++
    let cur_size = ctx.builder.build_load(i64_ty, size_field, "cur_sz").unwrap().into_int_value();
    let new_size = ctx.builder.build_int_add(cur_size, one, "new_sz").unwrap();
    ctx.builder.build_store(size_field, new_size).unwrap();
    ctx.builder.build_unconditional_branch(done).unwrap();

    // Overwrite existing
    ctx.builder.position_at_end(overwrite);
    let v_ptr2 = unsafe { ctx.builder.build_in_bounds_gep(val_llvm_ty, vals_ptr, &[pi], "v_ptr2").unwrap() };
    ctx.builder.build_store(v_ptr2, value_val).unwrap();
    ctx.builder.build_unconditional_branch(done).unwrap();

    ctx.builder.position_at_end(done);
    None
}

/// Compile `m.get(key) -> Option[V]`.
fn compile_hashmap_get<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    call_expr: &Expr,
    inner: &Expr,
    args: &[CallArg],
    key_ty: &Ty,
    val_ty: &Ty,
) -> Option<BasicValueEnum<'ctx>> {
    let i64_ty = ctx.context.i64_type();
    let i8_ty = ctx.context.i8_type();
    let key_llvm_ty = ty_to_llvm(ctx, key_ty);
    let val_llvm_ty = ty_to_llvm(ctx, val_ty);

    let hm_val = compile_expr(ctx, inner)?;
    let hm_sv = hm_val.into_struct_value();
    let keys_ptr = ctx.builder.build_extract_value(hm_sv, 0, "keys").unwrap().into_pointer_value();
    let vals_ptr = ctx.builder.build_extract_value(hm_sv, 1, "vals").unwrap().into_pointer_value();
    let states_ptr = ctx.builder.build_extract_value(hm_sv, 2, "states").unwrap().into_pointer_value();
    let cap = ctx.builder.build_extract_value(hm_sv, 4, "cap").unwrap().into_int_value();

    let key_val = compile_expr(ctx, &args[0].expr)?;

    // If cap == 0, return None immediately
    let cap_zero = ctx.builder.build_int_compare(IntPredicate::EQ, cap, i64_ty.const_zero(), "cap_zero").unwrap();
    let fn_val = ctx.builder.get_insert_block().unwrap().get_parent().unwrap();
    let search_bb = ctx.context.append_basic_block(fn_val, "get_search");
    let none_bb = ctx.context.append_basic_block(fn_val, "get_none");
    let some_bb = ctx.context.append_basic_block(fn_val, "get_some");
    let done_bb = ctx.context.append_basic_block(fn_val, "get_done");
    ctx.builder.build_conditional_branch(cap_zero, none_bb, search_bb).unwrap();

    // Search
    ctx.builder.position_at_end(search_bb);
    let hash = emit_hash_key(ctx, key_val, key_ty);
    let slot = ctx.builder.build_int_unsigned_rem(hash, cap, "slot").unwrap();

    let probe_pre = ctx.builder.get_insert_block().unwrap();
    let probe_loop = ctx.context.append_basic_block(fn_val, "get_probe");
    ctx.builder.build_unconditional_branch(probe_loop).unwrap();

    ctx.builder.position_at_end(probe_loop);
    let p_idx = ctx.builder.build_phi(i64_ty, "p_idx").unwrap();
    p_idx.add_incoming(&[(&slot, probe_pre)]);
    let pi = p_idx.as_basic_value().into_int_value();

    let st_ptr = unsafe { ctx.builder.build_in_bounds_gep(i8_ty, states_ptr, &[pi], "st").unwrap() };
    let state = ctx.builder.build_load(i8_ty, st_ptr, "state").unwrap().into_int_value();

    // empty → not found
    let is_empty = ctx.builder.build_int_compare(IntPredicate::EQ, state, i8_ty.const_zero(), "is_empty").unwrap();
    let check_occ = ctx.context.append_basic_block(fn_val, "get_check_occ");
    ctx.builder.build_conditional_branch(is_empty, none_bb, check_occ).unwrap();

    ctx.builder.position_at_end(check_occ);
    let is_occupied = ctx.builder.build_int_compare(IntPredicate::EQ, state, i8_ty.const_int(1, false), "is_occ").unwrap();
    let check_key = ctx.context.append_basic_block(fn_val, "get_check_key");
    let advance = ctx.context.append_basic_block(fn_val, "get_advance");
    ctx.builder.build_conditional_branch(is_occupied, check_key, advance).unwrap();

    ctx.builder.position_at_end(check_key);
    let existing_key_ptr = unsafe { ctx.builder.build_in_bounds_gep(key_llvm_ty, keys_ptr, &[pi], "ek_ptr").unwrap() };
    let existing_key = ctx.builder.build_load(key_llvm_ty, existing_key_ptr, "ek").unwrap();
    let keys_match = emit_key_equal(ctx, key_val, existing_key, key_ty);
    ctx.builder.build_conditional_branch(keys_match, some_bb, advance).unwrap();

    ctx.builder.position_at_end(advance);
    let one = i64_ty.const_int(1, false);
    let next = ctx.builder.build_int_add(pi, one, "next").unwrap();
    let wrapped = ctx.builder.build_int_unsigned_rem(next, cap, "wrapped").unwrap();
    p_idx.add_incoming(&[(&wrapped, advance)]);
    ctx.builder.build_unconditional_branch(probe_loop).unwrap();

    // Found → Some(value)
    ctx.builder.position_at_end(some_bb);
    let found_val_ptr = unsafe { ctx.builder.build_in_bounds_gep(val_llvm_ty, vals_ptr, &[pi], "fv_ptr").unwrap() };
    let found_val = ctx.builder.build_load(val_llvm_ty, found_val_ptr, "found_val").unwrap();
    let some_result = build_option_value(ctx, call_expr, Some(found_val), val_ty)?;
    ctx.builder.build_unconditional_branch(done_bb).unwrap();
    let some_end_bb = ctx.builder.get_insert_block().unwrap();

    // Not found → None
    ctx.builder.position_at_end(none_bb);
    let none_result = build_option_value(ctx, call_expr, None, val_ty)?;
    ctx.builder.build_unconditional_branch(done_bb).unwrap();
    let none_end_bb = ctx.builder.get_insert_block().unwrap();

    // Merge
    ctx.builder.position_at_end(done_bb);
    let option_llvm_ty = ty_to_llvm(ctx, &get_expr_ty(ctx, call_expr));
    let phi = ctx.builder.build_phi(option_llvm_ty, "get_result").unwrap();
    phi.add_incoming(&[(&some_result, some_end_bb), (&none_result, none_end_bb)]);
    Some(phi.as_basic_value())
}

/// Compile `m.contains_key(key) -> bool`.
fn compile_hashmap_contains_key<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    inner: &Expr,
    args: &[CallArg],
    key_ty: &Ty,
) -> Option<BasicValueEnum<'ctx>> {
    let i64_ty = ctx.context.i64_type();
    let i8_ty = ctx.context.i8_type();
    let key_llvm_ty = ty_to_llvm(ctx, key_ty);

    let hm_val = compile_expr(ctx, inner)?;
    let hm_sv = hm_val.into_struct_value();
    let keys_ptr = ctx.builder.build_extract_value(hm_sv, 0, "keys").unwrap().into_pointer_value();
    let states_ptr = ctx.builder.build_extract_value(hm_sv, 2, "states").unwrap().into_pointer_value();
    let cap = ctx.builder.build_extract_value(hm_sv, 4, "cap").unwrap().into_int_value();

    let key_val = compile_expr(ctx, &args[0].expr)?;

    let cap_zero = ctx.builder.build_int_compare(IntPredicate::EQ, cap, i64_ty.const_zero(), "cap_zero").unwrap();
    let fn_val = ctx.builder.get_insert_block().unwrap().get_parent().unwrap();
    let search_bb = ctx.context.append_basic_block(fn_val, "ck_search");
    let false_bb = ctx.context.append_basic_block(fn_val, "ck_false");
    let true_bb = ctx.context.append_basic_block(fn_val, "ck_true");
    let done_bb = ctx.context.append_basic_block(fn_val, "ck_done");
    ctx.builder.build_conditional_branch(cap_zero, false_bb, search_bb).unwrap();

    ctx.builder.position_at_end(search_bb);
    let hash = emit_hash_key(ctx, key_val, key_ty);
    let slot = ctx.builder.build_int_unsigned_rem(hash, cap, "slot").unwrap();

    let probe_pre = ctx.builder.get_insert_block().unwrap();
    let probe_loop = ctx.context.append_basic_block(fn_val, "ck_probe");
    ctx.builder.build_unconditional_branch(probe_loop).unwrap();

    ctx.builder.position_at_end(probe_loop);
    let p_idx = ctx.builder.build_phi(i64_ty, "p_idx").unwrap();
    p_idx.add_incoming(&[(&slot, probe_pre)]);
    let pi = p_idx.as_basic_value().into_int_value();

    let st_ptr = unsafe { ctx.builder.build_in_bounds_gep(i8_ty, states_ptr, &[pi], "st").unwrap() };
    let state = ctx.builder.build_load(i8_ty, st_ptr, "state").unwrap().into_int_value();

    let is_empty = ctx.builder.build_int_compare(IntPredicate::EQ, state, i8_ty.const_zero(), "is_empty").unwrap();
    let check_occ = ctx.context.append_basic_block(fn_val, "ck_check_occ");
    ctx.builder.build_conditional_branch(is_empty, false_bb, check_occ).unwrap();

    ctx.builder.position_at_end(check_occ);
    let is_occupied = ctx.builder.build_int_compare(IntPredicate::EQ, state, i8_ty.const_int(1, false), "is_occ").unwrap();
    let check_key = ctx.context.append_basic_block(fn_val, "ck_check_key");
    let advance = ctx.context.append_basic_block(fn_val, "ck_advance");
    ctx.builder.build_conditional_branch(is_occupied, check_key, advance).unwrap();

    ctx.builder.position_at_end(check_key);
    let existing_key_ptr = unsafe { ctx.builder.build_in_bounds_gep(key_llvm_ty, keys_ptr, &[pi], "ek_ptr").unwrap() };
    let existing_key = ctx.builder.build_load(key_llvm_ty, existing_key_ptr, "ek").unwrap();
    let keys_match = emit_key_equal(ctx, key_val, existing_key, key_ty);
    ctx.builder.build_conditional_branch(keys_match, true_bb, advance).unwrap();

    ctx.builder.position_at_end(advance);
    let one = i64_ty.const_int(1, false);
    let next = ctx.builder.build_int_add(pi, one, "next").unwrap();
    let wrapped = ctx.builder.build_int_unsigned_rem(next, cap, "wrapped").unwrap();
    p_idx.add_incoming(&[(&wrapped, advance)]);
    ctx.builder.build_unconditional_branch(probe_loop).unwrap();

    ctx.builder.position_at_end(true_bb);
    ctx.builder.build_unconditional_branch(done_bb).unwrap();

    ctx.builder.position_at_end(false_bb);
    ctx.builder.build_unconditional_branch(done_bb).unwrap();

    ctx.builder.position_at_end(done_bb);
    let bool_ty = ctx.context.i8_type();
    let phi = ctx.builder.build_phi(bool_ty, "ck_result").unwrap();
    phi.add_incoming(&[
        (&bool_ty.const_int(1, false), true_bb),
        (&bool_ty.const_zero(), false_bb),
    ]);
    Some(phi.as_basic_value())
}

/// Compile `m.remove(key) -> Option[V]`.
fn compile_hashmap_remove<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    call_expr: &Expr,
    inner: &Expr,
    args: &[CallArg],
    key_ty: &Ty,
    val_ty: &Ty,
) -> Option<BasicValueEnum<'ctx>> {
    let ptr_ty = ctx.context.ptr_type(AddressSpace::default());
    let i64_ty = ctx.context.i64_type();
    let i8_ty = ctx.context.i8_type();
    let hm_ty = hashmap_llvm_ty(ctx);
    let key_llvm_ty = ty_to_llvm(ctx, key_ty);
    let val_llvm_ty = ty_to_llvm(ctx, val_ty);

    let hm_ptr = compile_expr_addr(ctx, inner)?;
    let key_val = compile_expr(ctx, &args[0].expr)?;

    let keys_field = ctx.builder.build_struct_gep(hm_ty, hm_ptr, 0, "keys_f").unwrap();
    let vals_field = ctx.builder.build_struct_gep(hm_ty, hm_ptr, 1, "vals_f").unwrap();
    let states_field = ctx.builder.build_struct_gep(hm_ty, hm_ptr, 2, "states_f").unwrap();
    let size_field = ctx.builder.build_struct_gep(hm_ty, hm_ptr, 3, "size_f").unwrap();
    let cap_field = ctx.builder.build_struct_gep(hm_ty, hm_ptr, 4, "cap_f").unwrap();

    let keys_ptr = ctx.builder.build_load(ptr_ty, keys_field, "keys").unwrap().into_pointer_value();
    let vals_ptr = ctx.builder.build_load(ptr_ty, vals_field, "vals").unwrap().into_pointer_value();
    let states_ptr = ctx.builder.build_load(ptr_ty, states_field, "states").unwrap().into_pointer_value();
    let cap = ctx.builder.build_load(i64_ty, cap_field, "cap").unwrap().into_int_value();

    let cap_zero = ctx.builder.build_int_compare(IntPredicate::EQ, cap, i64_ty.const_zero(), "cap_zero").unwrap();
    let fn_val = ctx.builder.get_insert_block().unwrap().get_parent().unwrap();
    let search_bb = ctx.context.append_basic_block(fn_val, "rm_search");
    let none_bb = ctx.context.append_basic_block(fn_val, "rm_none");
    let found_bb = ctx.context.append_basic_block(fn_val, "rm_found");
    let done_bb = ctx.context.append_basic_block(fn_val, "rm_done");
    ctx.builder.build_conditional_branch(cap_zero, none_bb, search_bb).unwrap();

    ctx.builder.position_at_end(search_bb);
    let hash = emit_hash_key(ctx, key_val, key_ty);
    let slot = ctx.builder.build_int_unsigned_rem(hash, cap, "slot").unwrap();

    let probe_pre = ctx.builder.get_insert_block().unwrap();
    let probe_loop = ctx.context.append_basic_block(fn_val, "rm_probe");
    ctx.builder.build_unconditional_branch(probe_loop).unwrap();

    ctx.builder.position_at_end(probe_loop);
    let p_idx = ctx.builder.build_phi(i64_ty, "p_idx").unwrap();
    p_idx.add_incoming(&[(&slot, probe_pre)]);
    let pi = p_idx.as_basic_value().into_int_value();

    let st_ptr = unsafe { ctx.builder.build_in_bounds_gep(i8_ty, states_ptr, &[pi], "st").unwrap() };
    let state = ctx.builder.build_load(i8_ty, st_ptr, "state").unwrap().into_int_value();

    let is_empty = ctx.builder.build_int_compare(IntPredicate::EQ, state, i8_ty.const_zero(), "is_empty").unwrap();
    let check_occ = ctx.context.append_basic_block(fn_val, "rm_check_occ");
    ctx.builder.build_conditional_branch(is_empty, none_bb, check_occ).unwrap();

    ctx.builder.position_at_end(check_occ);
    let is_occupied = ctx.builder.build_int_compare(IntPredicate::EQ, state, i8_ty.const_int(1, false), "is_occ").unwrap();
    let check_key = ctx.context.append_basic_block(fn_val, "rm_check_key");
    let advance = ctx.context.append_basic_block(fn_val, "rm_advance");
    ctx.builder.build_conditional_branch(is_occupied, check_key, advance).unwrap();

    ctx.builder.position_at_end(check_key);
    let existing_key_ptr = unsafe { ctx.builder.build_in_bounds_gep(key_llvm_ty, keys_ptr, &[pi], "ek_ptr").unwrap() };
    let existing_key = ctx.builder.build_load(key_llvm_ty, existing_key_ptr, "ek").unwrap();
    let keys_match = emit_key_equal(ctx, key_val, existing_key, key_ty);
    ctx.builder.build_conditional_branch(keys_match, found_bb, advance).unwrap();

    ctx.builder.position_at_end(advance);
    let one = i64_ty.const_int(1, false);
    let next = ctx.builder.build_int_add(pi, one, "next").unwrap();
    let wrapped = ctx.builder.build_int_unsigned_rem(next, cap, "wrapped").unwrap();
    p_idx.add_incoming(&[(&wrapped, advance)]);
    ctx.builder.build_unconditional_branch(probe_loop).unwrap();

    // Found → set tombstone, decrement size, return Some(val)
    ctx.builder.position_at_end(found_bb);
    let found_val_ptr = unsafe { ctx.builder.build_in_bounds_gep(val_llvm_ty, vals_ptr, &[pi], "fv_ptr").unwrap() };
    let found_val = ctx.builder.build_load(val_llvm_ty, found_val_ptr, "found_val").unwrap();
    // Set tombstone
    ctx.builder.build_store(st_ptr, i8_ty.const_int(2, false)).unwrap();
    // size--
    let cur_size = ctx.builder.build_load(i64_ty, size_field, "cur_sz").unwrap().into_int_value();
    let new_size = ctx.builder.build_int_sub(cur_size, one, "new_sz").unwrap();
    ctx.builder.build_store(size_field, new_size).unwrap();
    let some_result = build_option_value(ctx, call_expr, Some(found_val), val_ty)?;
    ctx.builder.build_unconditional_branch(done_bb).unwrap();
    let found_end_bb = ctx.builder.get_insert_block().unwrap();

    ctx.builder.position_at_end(none_bb);
    let none_result = build_option_value(ctx, call_expr, None, val_ty)?;
    ctx.builder.build_unconditional_branch(done_bb).unwrap();
    let none_end_bb = ctx.builder.get_insert_block().unwrap();

    ctx.builder.position_at_end(done_bb);
    let option_llvm_ty = ty_to_llvm(ctx, &get_expr_ty(ctx, call_expr));
    let phi = ctx.builder.build_phi(option_llvm_ty, "rm_result").unwrap();
    phi.add_incoming(&[(&some_result, found_end_bb), (&none_result, none_end_bb)]);
    Some(phi.as_basic_value())
}

// ---------------------------------------------------------------------------
// String interpolation
// ---------------------------------------------------------------------------

/// Compile a backtick template literal, e.g. `` `Hello, {name}!` ``.
/// Uses snprintf to build the result as a `{ptr, len, cap}` String struct.
fn compile_string_interp<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    parts: &[StringInterpPart],
) -> Option<BasicValueEnum<'ctx>> {
    let snprintf = ctx.module.get_function("snprintf")?;
    let malloc = ctx.module.get_function("malloc")?;
    let ptr_ty = ctx.context.ptr_type(inkwell::AddressSpace::default());

    // Build the format string and collect argument values.
    let mut fmt = String::new();
    let mut args: Vec<inkwell::values::BasicMetadataValueEnum<'ctx>> = Vec::new();

    for part in parts {
        match part {
            StringInterpPart::Literal(s) => {
                // Escape % as %% in the format string.
                fmt.push_str(&s.replace('%', "%%"));
            }
            StringInterpPart::Expr(expr) => {
                let expr_ty = get_expr_ty(ctx, expr);
                let val = compile_expr(ctx, expr);
                match &expr_ty {
                    Ty::Prim(PrimTy::Str) => {
                        fmt.push_str("%.*s");
                        if let Some(v) = val {
                            let str_struct = v.into_struct_value();
                            let len = ctx
                                .builder
                                .build_extract_value(str_struct, 1, "interp_len")
                                .unwrap();
                            let ptr = ctx
                                .builder
                                .build_extract_value(str_struct, 0, "interp_ptr")
                                .unwrap();
                            args.push(len.into());
                            args.push(ptr.into());
                        }
                    }
                    Ty::Prim(PrimTy::I64)
                    | Ty::Prim(PrimTy::I32)
                    | Ty::Prim(PrimTy::U64)
                    | Ty::Prim(PrimTy::U32)
                    | Ty::Prim(PrimTy::Usize) => {
                        fmt.push_str("%lld");
                        if let Some(v) = val {
                            args.push(v.into());
                        }
                    }
                    Ty::Prim(PrimTy::Bool) => {
                        // Bool: format as "true"/"false" using %s with select.
                        fmt.push_str("%s");
                        if let Some(v) = val {
                            let bool_val = v.into_int_value();
                            let true_str = ctx
                                .builder
                                .build_global_string_ptr("true", "true_s")
                                .unwrap();
                            let false_str = ctx
                                .builder
                                .build_global_string_ptr("false", "false_s")
                                .unwrap();
                            let selected = ctx
                                .builder
                                .build_select(
                                    bool_val,
                                    true_str.as_pointer_value(),
                                    false_str.as_pointer_value(),
                                    "bool_s",
                                )
                                .unwrap();
                            args.push(selected.into());
                        }
                    }
                    Ty::Prim(PrimTy::F64) | Ty::Prim(PrimTy::F32) => {
                        fmt.push_str("%f");
                        if let Some(v) = val {
                            args.push(v.into());
                        }
                    }
                    Ty::Prim(PrimTy::Char) => {
                        fmt.push_str("%c");
                        if let Some(v) = val {
                            args.push(v.into());
                        }
                    }
                    Ty::Struct { def_id, .. } => {
                        let name = ctx.resolved.symbols.iter().find(|s| s.def_id == *def_id).map(|s| s.name.as_str());
                        if name == Some("String") {
                            fmt.push_str("%.*s");
                            if let Some(v) = val {
                                let sv = v.into_struct_value();
                                let len = ctx.builder.build_extract_value(sv, 1, "interp_len").unwrap();
                                let ptr = ctx.builder.build_extract_value(sv, 0, "interp_ptr").unwrap();
                                args.push(len.into());
                                args.push(ptr.into());
                            }
                        } else {
                            fmt.push_str("%lld");
                            if let Some(v) = val {
                                args.push(v.into());
                            }
                        }
                    }
                    _ => {
                        fmt.push_str("%lld");
                        if let Some(v) = val {
                            args.push(v.into());
                        }
                    }
                }
            }
        }
    }

    // First pass: snprintf(NULL, 0, fmt, ...) to compute length.
    let fmt_global = ctx
        .builder
        .build_global_string_ptr(&fmt, "interp_fmt")
        .unwrap();
    let null_ptr = ptr_ty.const_null();
    let zero = ctx.context.i64_type().const_zero();
    let mut size_args: Vec<inkwell::values::BasicMetadataValueEnum<'ctx>> =
        vec![null_ptr.into(), zero.into(), fmt_global.as_pointer_value().into()];
    size_args.extend(args.iter().cloned());
    let len_result = ctx
        .builder
        .build_call(snprintf, &size_args, "interp_len")
        .unwrap();
    let len_i32 = len_result.try_as_basic_value().left()?.into_int_value();
    let len_i64 = ctx
        .builder
        .build_int_z_extend(len_i32, ctx.context.i64_type(), "len_ext")
        .unwrap();

    // Allocate buffer: malloc(len + 1).
    let one = ctx.context.i64_type().const_int(1, false);
    let buf_size = ctx.builder.build_int_add(len_i64, one, "buf_size").unwrap();
    let buf_ptr = ctx
        .builder
        .build_call(malloc, &[buf_size.into()], "buf")
        .unwrap()
        .try_as_basic_value()
        .left()?
        .into_pointer_value();

    // Track this heap allocation for cleanup.
    ctx.heap_allocs.push(buf_ptr);

    // Second pass: snprintf(buf, buf_size, fmt, ...) to write the string.
    let mut write_args: Vec<inkwell::values::BasicMetadataValueEnum<'ctx>> =
        vec![buf_ptr.into(), buf_size.into(), fmt_global.as_pointer_value().into()];
    write_args.extend(args.iter().cloned());
    ctx.builder
        .build_call(snprintf, &write_args, "interp_write")
        .unwrap();

    // Return {ptr, len, cap} String struct.
    // cap = len + 1 (the malloc allocated len+1 bytes for the null terminator).
    let string_struct_ty = ctx.context.struct_type(
        &[ptr_ty.into(), ctx.context.i64_type().into(), ctx.context.i64_type().into()],
        false,
    );
    let cap = ctx
        .builder
        .build_int_add(len_i64, ctx.context.i64_type().const_int(1, false), "cap")
        .unwrap();
    let mut string_val = string_struct_ty.const_zero();
    string_val = ctx
        .builder
        .build_insert_value(string_val, buf_ptr, 0, "str_ptr")
        .unwrap()
        .into_struct_value();
    string_val = ctx
        .builder
        .build_insert_value(string_val, len_i64, 1, "str_len")
        .unwrap()
        .into_struct_value();
    string_val = ctx
        .builder
        .build_insert_value(string_val, cap, 2, "str_cap")
        .unwrap()
        .into_struct_value();
    Some(string_val.into())
}

// ---------------------------------------------------------------------------
// For loop
// ---------------------------------------------------------------------------

/// Compile a for loop: `for i in start..end`, `for x in arr`, or `for x in iter`.
fn compile_for<'ctx>(
    ctx: &mut CodegenCtx<'ctx>,
    pattern: &Pattern,
    iter: &Expr,
    body: &[Stmt],
) {
    // --- Branch 1: Range iterator: `for i in start..end` ---
    if let ExprKind::Range { start: Some(start), end: Some(end) } = &iter.kind {
        let start_val = match compile_expr(ctx, start) {
            Some(v) => v,
            None => return,
        };
        let end_val = match compile_expr(ctx, end) {
            Some(v) => v,
            None => return,
        };

        let fn_val = ctx
            .builder
            .get_insert_block()
            .unwrap()
            .get_parent()
            .unwrap();

        // Create the loop counter variable.
        let counter_ty = start_val.get_type();
        let counter_alloca = ctx
            .builder
            .build_alloca(counter_ty, "for_counter")
            .unwrap();
        ctx.builder.build_store(counter_alloca, start_val).unwrap();

        // Bind the pattern variable to the counter.
        if let PatternKind::Ident(_name) = &pattern.kind {
            let def_id = ctx
                .resolved
                .symbols
                .iter()
                .find(|s| s.kind == SymbolKind::LocalVar && s.span == pattern.span)
                .map(|s| s.def_id);
            if let Some(def_id) = def_id {
                ctx.locals.insert(def_id, counter_alloca);
                ctx.local_types.insert(def_id, counter_ty);
            }
        }

        let header_bb = ctx.context.append_basic_block(fn_val, "for_header");
        let body_bb = ctx.context.append_basic_block(fn_val, "for_body");
        let exit_bb = ctx.context.append_basic_block(fn_val, "for_exit");

        ctx.builder.build_unconditional_branch(header_bb).unwrap();

        // Header: check counter < end.
        ctx.builder.position_at_end(header_bb);
        let current = ctx
            .builder
            .build_load(counter_ty, counter_alloca, "counter")
            .unwrap()
            .into_int_value();
        let end_int = end_val.into_int_value();
        let cond = ctx
            .builder
            .build_int_compare(IntPredicate::SLT, current, end_int, "for_cond")
            .unwrap();
        ctx.builder
            .build_conditional_branch(cond, body_bb, exit_bb)
            .unwrap();

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
        // Increment counter.
        if ctx
            .builder
            .get_insert_block()
            .unwrap()
            .get_terminator()
            .is_none()
        {
            let current = ctx
                .builder
                .build_load(counter_ty, counter_alloca, "counter")
                .unwrap()
                .into_int_value();
            let one = current.get_type().const_int(1, false);
            let next = ctx.builder.build_int_add(current, one, "next").unwrap();
            ctx.builder.build_store(counter_alloca, next).unwrap();
            ctx.builder.build_unconditional_branch(header_bb).unwrap();
        }

        ctx.loop_exit_block = prev_exit;
        ctx.loop_header_block = prev_header;
        ctx.builder.position_at_end(exit_bb);
        return;
    }

    // --- Branch 1.5: Range struct variable: `for i in range_var` ---
    let iter_ty = get_expr_ty(ctx, iter);
    if let Ty::Struct { def_id, .. } = &iter_ty {
        let is_range = ctx.resolved.symbols.iter()
            .any(|s| s.def_id == *def_id && s.name == "Range" && matches!(s.kind, SymbolKind::Struct));
        if is_range {
            let range_val = match compile_expr(ctx, iter) {
                Some(v) => v,
                None => return,
            };
            let start_val = ctx.builder.build_extract_value(range_val.into_struct_value(), 0, "range_start")
                .unwrap();
            let end_val = ctx.builder.build_extract_value(range_val.into_struct_value(), 1, "range_end")
                .unwrap();

            let fn_val = ctx
                .builder
                .get_insert_block()
                .unwrap()
                .get_parent()
                .unwrap();

            let counter_ty = start_val.get_type();
            let counter_alloca = ctx
                .builder
                .build_alloca(counter_ty, "for_counter")
                .unwrap();
            ctx.builder.build_store(counter_alloca, start_val).unwrap();

            // Bind the pattern variable to the counter.
            if let PatternKind::Ident(_name) = &pattern.kind {
                let def_id = ctx
                    .resolved
                    .symbols
                    .iter()
                    .find(|s| s.kind == SymbolKind::LocalVar && s.span == pattern.span)
                    .map(|s| s.def_id);
                if let Some(def_id) = def_id {
                    ctx.locals.insert(def_id, counter_alloca);
                    ctx.local_types.insert(def_id, counter_ty);
                }
            }

            let header_bb = ctx.context.append_basic_block(fn_val, "for_header");
            let body_bb = ctx.context.append_basic_block(fn_val, "for_body");
            let exit_bb = ctx.context.append_basic_block(fn_val, "for_exit");

            ctx.builder.build_unconditional_branch(header_bb).unwrap();

            // Header: check counter < end.
            ctx.builder.position_at_end(header_bb);
            let current = ctx
                .builder
                .build_load(counter_ty, counter_alloca, "counter")
                .unwrap()
                .into_int_value();
            let end_int = end_val.into_int_value();
            let cond = ctx
                .builder
                .build_int_compare(IntPredicate::SLT, current, end_int, "for_cond")
                .unwrap();
            ctx.builder
                .build_conditional_branch(cond, body_bb, exit_bb)
                .unwrap();

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
            // Increment counter.
            if ctx
                .builder
                .get_insert_block()
                .unwrap()
                .get_terminator()
                .is_none()
            {
                let current = ctx
                    .builder
                    .build_load(counter_ty, counter_alloca, "counter")
                    .unwrap()
                    .into_int_value();
                let one = current.get_type().const_int(1, false);
                let next = ctx.builder.build_int_add(current, one, "next").unwrap();
                ctx.builder.build_store(counter_alloca, next).unwrap();
                ctx.builder.build_unconditional_branch(header_bb).unwrap();
            }

            ctx.loop_exit_block = prev_exit;
            ctx.loop_header_block = prev_header;
            ctx.builder.position_at_end(exit_bb);
            return;
        }
    }

    // --- Branch 2: FixedArray: `for x in arr` ---
    if let Ty::Array { ref elem, len } = iter_ty {
        let arr_val = match compile_expr(ctx, iter) {
            Some(v) => v,
            None => return,
        };
        let arr_llvm_ty = arr_val.get_type();
        let arr_alloca = ctx.builder.build_alloca(arr_llvm_ty, "for_arr").unwrap();
        ctx.builder.build_store(arr_alloca, arr_val).unwrap();

        let fn_val = ctx
            .builder
            .get_insert_block()
            .unwrap()
            .get_parent()
            .unwrap();
        let i64_ty = ctx.context.i64_type();
        let counter_alloca = ctx.builder.build_alloca(i64_ty, "for_idx").unwrap();
        ctx.builder
            .build_store(counter_alloca, i64_ty.const_zero())
            .unwrap();
        let len_val = i64_ty.const_int(len, false);

        // Element LLVM type (apply current substitution for generics).
        let resolved_elem = if ctx.current_subst.is_empty() {
            *elem.clone()
        } else {
            axion_mono::specialize::substitute(elem, &ctx.current_subst)
        };
        let elem_llvm_ty = ty_to_llvm(ctx, &resolved_elem);

        let header_bb = ctx.context.append_basic_block(fn_val, "for_arr_hdr");
        let body_bb = ctx.context.append_basic_block(fn_val, "for_arr_body");
        let exit_bb = ctx.context.append_basic_block(fn_val, "for_arr_exit");

        ctx.builder.build_unconditional_branch(header_bb).unwrap();

        // Header: idx < len
        ctx.builder.position_at_end(header_bb);
        let idx = ctx
            .builder
            .build_load(i64_ty, counter_alloca, "idx")
            .unwrap()
            .into_int_value();
        let cond = ctx
            .builder
            .build_int_compare(IntPredicate::SLT, idx, len_val, "cond")
            .unwrap();
        ctx.builder
            .build_conditional_branch(cond, body_bb, exit_bb)
            .unwrap();

        // Body: GEP to get element, bind pattern variable.
        ctx.builder.position_at_end(body_bb);
        let zero = i64_ty.const_zero();
        let elem_ptr = unsafe {
            ctx.builder
                .build_in_bounds_gep(arr_llvm_ty, arr_alloca, &[zero, idx], "elem_ptr")
                .unwrap()
        };
        let elem_val = ctx
            .builder
            .build_load(elem_llvm_ty, elem_ptr, "elem")
            .unwrap();

        // Bind pattern variable.
        if let PatternKind::Ident(name) = &pattern.kind {
            let elem_alloca = ctx.builder.build_alloca(elem_llvm_ty, name).unwrap();
            ctx.builder.build_store(elem_alloca, elem_val).unwrap();
            let def_id = ctx
                .resolved
                .symbols
                .iter()
                .find(|s| s.kind == SymbolKind::LocalVar && s.span == pattern.span)
                .map(|s| s.def_id);
            if let Some(def_id) = def_id {
                ctx.locals.insert(def_id, elem_alloca);
                ctx.local_types.insert(def_id, elem_llvm_ty);
            }
        }

        // Loop context + body + counter increment.
        let prev_exit = ctx.loop_exit_block.take();
        let prev_header = ctx.loop_header_block.take();
        ctx.loop_exit_block = Some(exit_bb);
        ctx.loop_header_block = Some(header_bb);

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

        // idx++
        if ctx
            .builder
            .get_insert_block()
            .unwrap()
            .get_terminator()
            .is_none()
        {
            let cur = ctx
                .builder
                .build_load(i64_ty, counter_alloca, "idx")
                .unwrap()
                .into_int_value();
            let one = i64_ty.const_int(1, false);
            let next = ctx.builder.build_int_add(cur, one, "next_idx").unwrap();
            ctx.builder.build_store(counter_alloca, next).unwrap();
            ctx.builder.build_unconditional_branch(header_bb).unwrap();
        }

        ctx.loop_exit_block = prev_exit;
        ctx.loop_header_block = prev_header;
        ctx.builder.position_at_end(exit_bb);
        return;
    }

    // --- Branch 2.5: Slice: `for x in slice` ---
    if let Ty::Slice(ref elem) = iter_ty {
        let slice_val = match compile_expr(ctx, iter) {
            Some(v) => v,
            None => return,
        };
        let data_ptr = ctx.builder.build_extract_value(slice_val.into_struct_value(), 0, "slice_data")
            .unwrap().into_pointer_value();
        let len_val = ctx.builder.build_extract_value(slice_val.into_struct_value(), 1, "slice_len")
            .unwrap().into_int_value();

        let resolved_elem = if ctx.current_subst.is_empty() {
            *elem.clone()
        } else {
            axion_mono::specialize::substitute(elem, &ctx.current_subst)
        };
        let elem_llvm_ty = ty_to_llvm(ctx, &resolved_elem);

        let fn_val = ctx
            .builder
            .get_insert_block()
            .unwrap()
            .get_parent()
            .unwrap();
        let i64_ty = ctx.context.i64_type();
        let counter_alloca = ctx.builder.build_alloca(i64_ty, "for_idx").unwrap();
        ctx.builder
            .build_store(counter_alloca, i64_ty.const_zero())
            .unwrap();

        let header_bb = ctx.context.append_basic_block(fn_val, "for_slice_hdr");
        let body_bb = ctx.context.append_basic_block(fn_val, "for_slice_body");
        let exit_bb = ctx.context.append_basic_block(fn_val, "for_slice_exit");

        ctx.builder.build_unconditional_branch(header_bb).unwrap();

        // Header: idx < len
        ctx.builder.position_at_end(header_bb);
        let idx = ctx
            .builder
            .build_load(i64_ty, counter_alloca, "idx")
            .unwrap()
            .into_int_value();
        let cond = ctx
            .builder
            .build_int_compare(IntPredicate::SLT, idx, len_val, "cond")
            .unwrap();
        ctx.builder
            .build_conditional_branch(cond, body_bb, exit_bb)
            .unwrap();

        // Body: GEP to get element, bind pattern variable.
        ctx.builder.position_at_end(body_bb);
        let elem_ptr = unsafe {
            ctx.builder
                .build_in_bounds_gep(elem_llvm_ty, data_ptr, &[idx], "elem_ptr")
                .unwrap()
        };
        let elem_val = ctx
            .builder
            .build_load(elem_llvm_ty, elem_ptr, "elem")
            .unwrap();

        // Bind pattern variable.
        if let PatternKind::Ident(name) = &pattern.kind {
            let elem_alloca = ctx.builder.build_alloca(elem_llvm_ty, name).unwrap();
            ctx.builder.build_store(elem_alloca, elem_val).unwrap();
            let def_id = ctx
                .resolved
                .symbols
                .iter()
                .find(|s| s.kind == SymbolKind::LocalVar && s.span == pattern.span)
                .map(|s| s.def_id);
            if let Some(def_id) = def_id {
                ctx.locals.insert(def_id, elem_alloca);
                ctx.local_types.insert(def_id, elem_llvm_ty);
            }
        }

        // Loop context + body + counter increment.
        let prev_exit = ctx.loop_exit_block.take();
        let prev_header = ctx.loop_header_block.take();
        ctx.loop_exit_block = Some(exit_bb);
        ctx.loop_header_block = Some(header_bb);

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

        // idx++
        if ctx
            .builder
            .get_insert_block()
            .unwrap()
            .get_terminator()
            .is_none()
        {
            let cur = ctx
                .builder
                .build_load(i64_ty, counter_alloca, "idx")
                .unwrap()
                .into_int_value();
            let one = i64_ty.const_int(1, false);
            let next = ctx.builder.build_int_add(cur, one, "next_idx").unwrap();
            ctx.builder.build_store(counter_alloca, next).unwrap();
            ctx.builder.build_unconditional_branch(header_bb).unwrap();
        }

        ctx.loop_exit_block = prev_exit;
        ctx.loop_header_block = prev_header;
        ctx.builder.position_at_end(exit_bb);
        return;
    }

    // --- Branch 2.7: Array[T]: `for x in arr` ---
    if is_array_struct_ty(ctx, &iter_ty) {
        let elem_ty = get_array_elem_ty(&iter_ty);
        let arr_val = match compile_expr(ctx, iter) {
            Some(v) => v,
            None => return,
        };
        let data_ptr = ctx.builder.build_extract_value(arr_val.into_struct_value(), 0, "arr_data")
            .unwrap().into_pointer_value();
        let len_val = ctx.builder.build_extract_value(arr_val.into_struct_value(), 1, "arr_len")
            .unwrap().into_int_value();

        let resolved_elem = if ctx.current_subst.is_empty() {
            elem_ty
        } else {
            axion_mono::specialize::substitute(&elem_ty, &ctx.current_subst)
        };
        let elem_llvm_ty = ty_to_llvm(ctx, &resolved_elem);

        let fn_val = ctx
            .builder
            .get_insert_block()
            .unwrap()
            .get_parent()
            .unwrap();
        let i64_ty = ctx.context.i64_type();
        let counter_alloca = ctx.builder.build_alloca(i64_ty, "for_idx").unwrap();
        ctx.builder
            .build_store(counter_alloca, i64_ty.const_zero())
            .unwrap();

        let header_bb = ctx.context.append_basic_block(fn_val, "for_arr_hdr");
        let body_bb = ctx.context.append_basic_block(fn_val, "for_arr_body");
        let exit_bb = ctx.context.append_basic_block(fn_val, "for_arr_exit");

        ctx.builder.build_unconditional_branch(header_bb).unwrap();

        // Header: idx < len
        ctx.builder.position_at_end(header_bb);
        let idx = ctx
            .builder
            .build_load(i64_ty, counter_alloca, "idx")
            .unwrap()
            .into_int_value();
        let cond = ctx
            .builder
            .build_int_compare(IntPredicate::SLT, idx, len_val, "cond")
            .unwrap();
        ctx.builder
            .build_conditional_branch(cond, body_bb, exit_bb)
            .unwrap();

        // Body: GEP to get element, bind pattern variable.
        ctx.builder.position_at_end(body_bb);
        let elem_ptr = unsafe {
            ctx.builder
                .build_in_bounds_gep(elem_llvm_ty, data_ptr, &[idx], "elem_ptr")
                .unwrap()
        };
        let elem_val = ctx
            .builder
            .build_load(elem_llvm_ty, elem_ptr, "elem")
            .unwrap();

        // Bind pattern variable.
        if let PatternKind::Ident(name) = &pattern.kind {
            let elem_alloca = ctx.builder.build_alloca(elem_llvm_ty, name).unwrap();
            ctx.builder.build_store(elem_alloca, elem_val).unwrap();
            let def_id = ctx
                .resolved
                .symbols
                .iter()
                .find(|s| s.kind == SymbolKind::LocalVar && s.span == pattern.span)
                .map(|s| s.def_id);
            if let Some(def_id) = def_id {
                ctx.locals.insert(def_id, elem_alloca);
                ctx.local_types.insert(def_id, elem_llvm_ty);
            }
        }

        // Loop context + body + counter increment.
        let prev_exit = ctx.loop_exit_block.take();
        let prev_header = ctx.loop_header_block.take();
        ctx.loop_exit_block = Some(exit_bb);
        ctx.loop_header_block = Some(header_bb);

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

        // idx++
        if ctx
            .builder
            .get_insert_block()
            .unwrap()
            .get_terminator()
            .is_none()
        {
            let cur = ctx
                .builder
                .build_load(i64_ty, counter_alloca, "idx")
                .unwrap()
                .into_int_value();
            let one = i64_ty.const_int(1, false);
            let next = ctx.builder.build_int_add(cur, one, "next_idx").unwrap();
            ctx.builder.build_store(counter_alloca, next).unwrap();
            ctx.builder.build_unconditional_branch(header_bb).unwrap();
        }

        ctx.loop_exit_block = prev_exit;
        ctx.loop_header_block = prev_header;
        ctx.builder.position_at_end(exit_bb);
        return;
    }

    // --- Branch 3: Iter[T]: `for x in iter_expr` ---
    if let Some(type_name) = get_type_name_for_method_ctx(ctx, &iter_ty) {
        let method_key = format!("{}.next", type_name);
        let method_def_id = ctx
            .resolved
            .symbols
            .iter()
            .find(|s| {
                s.name == method_key
                    && matches!(s.kind, SymbolKind::Method | SymbolKind::Constructor)
            })
            .map(|s| s.def_id);

        if let Some(def_id) = method_def_id {
            // Look up monomorphized or plain function value.
            let type_args = match &iter_ty {
                Ty::Enum { type_args, .. } | Ty::Struct { type_args, .. } => type_args.clone(),
                _ => vec![],
            };
            let mono_fn = if !type_args.is_empty() {
                if let Some(mono) = ctx.mono_output {
                    mono.lookup(def_id, &type_args)
                        .and_then(|mangled| ctx.mono_fn_values.get(mangled).copied())
                } else {
                    None
                }
            } else {
                None
            };
            let fn_value_opt = mono_fn.or_else(|| ctx.functions.get(&def_id).copied());

            if let Some(fn_value) = fn_value_opt {
                // 1. Store iterator in alloca (mut self → pass by pointer).
                let iter_val = match compile_expr(ctx, iter) {
                    Some(v) => v,
                    None => return,
                };
                let iter_llvm_ty = iter_val.get_type();
                let iter_alloca = ctx.builder.build_alloca(iter_llvm_ty, "for_iter").unwrap();
                ctx.builder.build_store(iter_alloca, iter_val).unwrap();

                // 2. Determine the Option[T] return type from next().
                let method_info = ctx.type_env.defs.get(&def_id);
                let option_ty = if let Some(info) = method_info {
                    if let Ty::Fn { ret, .. } = &info.ty {
                        let mut resolved_ret = *ret.clone();
                        if !type_args.is_empty() {
                            let subst = build_subst_map(ctx, match &iter_ty { Ty::Struct { def_id, .. } | Ty::Enum { def_id, .. } => *def_id, _ => return }, &type_args);
                            if !subst.is_empty() {
                                resolved_ret = axion_mono::specialize::substitute(&resolved_ret, &subst);
                            }
                        }
                        // Also apply current_subst if present.
                        if !ctx.current_subst.is_empty() {
                            resolved_ret = axion_mono::specialize::substitute(&resolved_ret, &ctx.current_subst);
                        }
                        resolved_ret
                    } else {
                        return;
                    }
                } else {
                    return;
                };

                let option_llvm_ty = ty_to_llvm(ctx, &option_ty);
                let (option_def_id, option_type_args) = match &option_ty {
                    Ty::Enum { def_id, type_args, .. } => (*def_id, type_args.clone()),
                    _ => return,
                };

                // 3. Get Option variant info (Some=0, None=1).
                let variants = match ctx.type_env.enum_variants.get(&option_def_id) {
                    Some(v) => v.clone(),
                    None => return,
                };

                // 4. Build loop structure.
                let fn_val = ctx
                    .builder
                    .get_insert_block()
                    .unwrap()
                    .get_parent()
                    .unwrap();

                let header_bb = ctx.context.append_basic_block(fn_val, "for_iter_hdr");
                let body_bb = ctx.context.append_basic_block(fn_val, "for_iter_body");
                let exit_bb = ctx.context.append_basic_block(fn_val, "for_iter_exit");

                ctx.builder.build_unconditional_branch(header_bb).unwrap();

                // Header: call next(mut self), check tag.
                ctx.builder.position_at_end(header_bb);
                let next_result = ctx
                    .builder
                    .build_call(fn_value, &[iter_alloca.into()], "next")
                    .unwrap();
                let option_val = match next_result.try_as_basic_value().left() {
                    Some(v) => v,
                    None => return,
                };

                let option_alloca = ctx
                    .builder
                    .build_alloca(option_llvm_ty, "option_tmp")
                    .unwrap();
                ctx.builder.build_store(option_alloca, option_val).unwrap();

                let tag_ptr = ctx
                    .builder
                    .build_struct_gep(option_llvm_ty, option_alloca, 0, "tag_ptr")
                    .unwrap();
                let tag = ctx
                    .builder
                    .build_load(ctx.context.i8_type(), tag_ptr, "tag")
                    .unwrap()
                    .into_int_value();
                let is_some = ctx
                    .builder
                    .build_int_compare(
                        IntPredicate::EQ,
                        tag,
                        ctx.context.i8_type().const_int(0, false),
                        "is_some",
                    )
                    .unwrap();
                ctx.builder
                    .build_conditional_branch(is_some, body_bb, exit_bb)
                    .unwrap();

                // Body: extract payload from Some variant.
                ctx.builder.position_at_end(body_bb);

                // Find the Some variant's fields.
                let some_fields = if !variants.is_empty() {
                    variants[0].2.clone()
                } else {
                    vec![]
                };

                if !some_fields.is_empty() {
                    let subst = build_subst_map(ctx, option_def_id, &option_type_args);
                    let variant_struct_ty = variant_struct_type(ctx, &some_fields, &subst);

                    let payload_ptr = ctx
                        .builder
                        .build_struct_gep(option_llvm_ty, option_alloca, 1, "payload_ptr")
                        .unwrap();

                    let (_, ref field_ty) = some_fields[0];
                    let resolved_field_ty = if subst.is_empty() {
                        field_ty.clone()
                    } else {
                        axion_mono::specialize::substitute(field_ty, &subst)
                    };
                    let field_llvm_ty = ty_to_llvm(ctx, &resolved_field_ty);

                    let value_ptr = ctx
                        .builder
                        .build_struct_gep(variant_struct_ty, payload_ptr, 0, "value_ptr")
                        .unwrap();
                    let elem_val = ctx
                        .builder
                        .build_load(field_llvm_ty, value_ptr, "elem")
                        .unwrap();

                    // Bind pattern variable.
                    if let PatternKind::Ident(name) = &pattern.kind {
                        let elem_alloca =
                            ctx.builder.build_alloca(field_llvm_ty, name).unwrap();
                        ctx.builder.build_store(elem_alloca, elem_val).unwrap();
                        let pat_def_id = ctx
                            .resolved
                            .symbols
                            .iter()
                            .find(|s| {
                                s.kind == SymbolKind::LocalVar && s.span == pattern.span
                            })
                            .map(|s| s.def_id);
                        if let Some(pat_def_id) = pat_def_id {
                            ctx.locals.insert(pat_def_id, elem_alloca);
                            ctx.local_types.insert(pat_def_id, field_llvm_ty);
                        }
                    }
                }

                // Loop context + body + branch to header.
                let prev_exit = ctx.loop_exit_block.take();
                let prev_header = ctx.loop_header_block.take();
                ctx.loop_exit_block = Some(exit_bb);
                ctx.loop_header_block = Some(header_bb);

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

                ctx.loop_exit_block = prev_exit;
                ctx.loop_header_block = prev_header;
                ctx.builder.position_at_end(exit_bb);
            }
        }
    }
}
