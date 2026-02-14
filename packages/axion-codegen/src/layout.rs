use std::collections::HashMap;

use axion_mono::specialize::substitute;
use axion_resolve::def_id::{DefId, SymbolKind};
use axion_types::ty::{PrimTy, Ty};
use inkwell::context::Context;
use inkwell::types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum};
use inkwell::AddressSpace;

use crate::context::CodegenCtx;

/// Get the type parameter DefIds for a struct or enum definition.
fn get_type_param_def_ids(ctx: &CodegenCtx, def_id: DefId) -> Vec<DefId> {
    let parent_sym = ctx
        .resolved
        .symbols
        .iter()
        .find(|s| s.def_id == def_id);
    let Some(parent_sym) = parent_sym else {
        return vec![];
    };
    ctx.resolved
        .symbols
        .iter()
        .filter(|s| {
            s.kind == SymbolKind::TypeParam
                && s.name != "Self"
                && s.span.start >= parent_sym.span.start
                && s.span.end <= parent_sym.span.end
        })
        .map(|s| s.def_id)
        .collect()
}

/// Build a substitution map from a struct/enum's type parameters to concrete type arguments.
pub fn build_subst_map(ctx: &CodegenCtx, def_id: DefId, type_args: &[Ty]) -> HashMap<DefId, Ty> {
    let param_ids = get_type_param_def_ids(ctx, def_id);
    let mut subst = HashMap::new();
    for (param_def_id, arg_ty) in param_ids.iter().zip(type_args.iter()) {
        subst.insert(*param_def_id, arg_ty.clone());
    }
    subst
}

/// Convert an Axion Ty to an LLVM BasicTypeEnum.
pub fn ty_to_llvm<'ctx>(ctx: &CodegenCtx<'ctx>, ty: &Ty) -> BasicTypeEnum<'ctx> {
    match ty {
        Ty::Prim(prim) => prim_to_llvm(ctx.context, *prim),
        Ty::Unit => ctx.context.i8_type().into(),
        Ty::Struct { def_id, type_args } => struct_to_llvm(ctx, *def_id, type_args),
        Ty::Enum { def_id, type_args } => enum_to_llvm(ctx, *def_id, type_args),
        Ty::Tuple(elems) => {
            let field_types: Vec<BasicTypeEnum<'ctx>> =
                elems.iter().map(|t| ty_to_llvm(ctx, t)).collect();
            ctx.context.struct_type(&field_types, false).into()
        }
        Ty::Fn { .. } => {
            // Function pointer
            ctx.context
                .ptr_type(AddressSpace::default())
                .into()
        }
        Ty::Ref(_) => {
            ctx.context
                .ptr_type(AddressSpace::default())
                .into()
        }
        Ty::Slice(_) => {
            // Slice = fat pointer: { ptr, i64 len }
            ctx.context
                .struct_type(
                    &[
                        ctx.context.ptr_type(AddressSpace::default()).into(),
                        ctx.context.i64_type().into(),
                    ],
                    false,
                )
                .into()
        }
        Ty::Array { elem, len } => {
            let elem_llvm = ty_to_llvm(ctx, elem);
            elem_llvm.array_type(*len as u32).into()
        }
        Ty::Param(_) | Ty::Infer(_) | Ty::Error => {
            // Fallback: i64
            ctx.context.i64_type().into()
        }
    }
}

/// Convert a primitive type to LLVM type.
pub fn prim_to_llvm<'ctx>(context: &'ctx Context, prim: PrimTy) -> BasicTypeEnum<'ctx> {
    match prim {
        PrimTy::I8 | PrimTy::U8 | PrimTy::Bool => context.i8_type().into(),
        PrimTy::I16 | PrimTy::U16 => context.i16_type().into(),
        PrimTy::I32 | PrimTy::U32 | PrimTy::Char => context.i32_type().into(),
        PrimTy::I64 | PrimTy::U64 | PrimTy::Usize => context.i64_type().into(),
        PrimTy::I128 | PrimTy::U128 => context.i128_type().into(),
        PrimTy::F16 | PrimTy::Bf16 => context.f16_type().into(),
        PrimTy::F32 => context.f32_type().into(),
        PrimTy::F64 => context.f64_type().into(),
        PrimTy::Str => {
            // str = { ptr, i64 len }
            context
                .struct_type(
                    &[
                        context.ptr_type(AddressSpace::default()).into(),
                        context.i64_type().into(),
                    ],
                    false,
                )
                .into()
        }
        PrimTy::Never => context.i8_type().into(),
    }
}

/// Convert a struct type to LLVM struct type, substituting type parameters with concrete types.
fn struct_to_llvm<'ctx>(ctx: &CodegenCtx<'ctx>, def_id: DefId, type_args: &[Ty]) -> BasicTypeEnum<'ctx> {
    // String → { ptr, i64 len, i64 cap }
    let type_name = ctx.resolved.symbols.iter()
        .find(|s| s.def_id == def_id)
        .map(|s| s.name.as_str());
    if type_name == Some("String") || type_name == Some("Array") {
        return ctx.context.struct_type(&[
            ctx.context.ptr_type(AddressSpace::default()).into(),
            ctx.context.i64_type().into(),
            ctx.context.i64_type().into(),
        ], false).into();
    }
    if type_name == Some("HashMap") {
        return ctx.context.struct_type(&[
            ctx.context.ptr_type(AddressSpace::default()).into(), // keys
            ctx.context.ptr_type(AddressSpace::default()).into(), // values
            ctx.context.ptr_type(AddressSpace::default()).into(), // states
            ctx.context.i64_type().into(), // size
            ctx.context.i64_type().into(), // cap
        ], false).into();
    }

    if let Some(fields) = ctx.type_env.struct_fields.get(&def_id) {
        let subst = build_subst_map(ctx, def_id, type_args);
        let field_types: Vec<BasicTypeEnum<'ctx>> = fields
            .iter()
            .map(|(_, ty)| {
                let resolved_ty = if subst.is_empty() { ty.clone() } else { substitute(ty, &subst) };
                ty_to_llvm(ctx, &resolved_ty)
            })
            .collect();
        ctx.context.struct_type(&field_types, false).into()
    } else {
        // Fallback: empty struct
        ctx.context.struct_type(&[], false).into()
    }
}

/// Convert an Axion Ty to an LLVM metadata type (for function parameters).
pub fn ty_to_llvm_metadata<'ctx>(
    ctx: &CodegenCtx<'ctx>,
    ty: &Ty,
) -> BasicMetadataTypeEnum<'ctx> {
    ty_to_llvm(ctx, ty).into()
}

/// Check if a type is "void-like" (Unit).
pub fn is_void_ty(ty: &Ty) -> bool {
    matches!(ty, Ty::Unit)
}

/// Convert an enum type to LLVM struct type: { i8 tag, [N x i8] payload }.
/// N is the maximum payload size across all variants.
fn enum_to_llvm<'ctx>(ctx: &CodegenCtx<'ctx>, def_id: DefId, type_args: &[Ty]) -> BasicTypeEnum<'ctx> {
    let max_bytes = enum_max_payload_bytes(ctx, def_id, type_args);
    if max_bytes == 0 {
        // All variants are unit variants — just a tag byte.
        ctx.context
            .struct_type(&[ctx.context.i8_type().into()], false)
            .into()
    } else {
        ctx.context
            .struct_type(
                &[
                    ctx.context.i8_type().into(),
                    ctx.context.i8_type().array_type(max_bytes).into(),
                ],
                false,
            )
            .into()
    }
}

/// Compute the maximum payload size (in bytes) across all variants of an enum.
pub fn enum_max_payload_bytes<'ctx>(ctx: &CodegenCtx<'ctx>, def_id: DefId, type_args: &[Ty]) -> u32 {
    let variants = match ctx.type_env.enum_variants.get(&def_id) {
        Some(v) => v,
        None => return 0,
    };
    let subst = build_subst_map(ctx, def_id, type_args);
    variants
        .iter()
        .map(|(_, _, fields)| variant_payload_bytes(ctx, fields, &subst))
        .max()
        .unwrap_or(0)
}

/// Compute the payload size (in bytes) for a single variant's fields.
fn variant_payload_bytes<'ctx>(ctx: &CodegenCtx<'ctx>, fields: &[(String, Ty)], subst: &HashMap<DefId, Ty>) -> u32 {
    if fields.is_empty() {
        return 0;
    }
    let field_types: Vec<BasicTypeEnum<'ctx>> = fields
        .iter()
        .map(|(_, ty)| {
            let resolved_ty = if subst.is_empty() { ty.clone() } else { substitute(ty, subst) };
            ty_to_llvm(ctx, &resolved_ty)
        })
        .collect();
    field_types.iter().map(|t| estimate_type_bytes(*t)).sum()
}

/// Estimate the size in bytes of an LLVM type.
fn estimate_type_bytes(ty: BasicTypeEnum) -> u32 {
    match ty {
        BasicTypeEnum::IntType(i) => (i.get_bit_width() + 7) / 8,
        BasicTypeEnum::FloatType(_) => 8, // Assume f64 (worst case for f16/f32)
        BasicTypeEnum::PointerType(_) => 8,
        BasicTypeEnum::StructType(s) => {
            (0..s.count_fields())
                .map(|i| estimate_type_bytes(s.get_field_type_at_index(i).unwrap()))
                .sum()
        }
        BasicTypeEnum::ArrayType(a) => {
            estimate_type_bytes(a.get_element_type()) * a.len()
        }
        BasicTypeEnum::VectorType(_) => 16,
    }
}

/// Get the LLVM struct type representing a variant's fields, with type substitution.
pub fn variant_struct_type<'ctx>(
    ctx: &CodegenCtx<'ctx>,
    fields: &[(String, Ty)],
    subst: &HashMap<DefId, Ty>,
) -> inkwell::types::StructType<'ctx> {
    let field_types: Vec<BasicTypeEnum<'ctx>> = fields
        .iter()
        .map(|(_, ty)| {
            let resolved_ty = if subst.is_empty() { ty.clone() } else { substitute(ty, subst) };
            ty_to_llvm(ctx, &resolved_ty)
        })
        .collect();
    ctx.context.struct_type(&field_types, false)
}
