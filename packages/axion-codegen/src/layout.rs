use axion_resolve::def_id::DefId;
use axion_types::ty::{PrimTy, Ty};
use inkwell::context::Context;
use inkwell::types::{BasicMetadataTypeEnum, BasicTypeEnum};
use inkwell::AddressSpace;

use crate::context::CodegenCtx;

/// Convert an Axion Ty to an LLVM BasicTypeEnum.
pub fn ty_to_llvm<'ctx>(ctx: &CodegenCtx<'ctx>, ty: &Ty) -> BasicTypeEnum<'ctx> {
    match ty {
        Ty::Prim(prim) => prim_to_llvm(ctx.context, *prim),
        Ty::Unit => ctx.context.i8_type().into(),
        Ty::Struct { def_id, .. } => struct_to_llvm(ctx, *def_id),
        Ty::Enum { def_id, .. } => enum_to_llvm(ctx, *def_id),
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
        Ty::Ref(_) | Ty::Slice(_) => {
            // Pointer
            ctx.context
                .ptr_type(AddressSpace::default())
                .into()
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

/// Convert a struct type to LLVM struct type.
fn struct_to_llvm<'ctx>(ctx: &CodegenCtx<'ctx>, def_id: DefId) -> BasicTypeEnum<'ctx> {
    if let Some(fields) = ctx.type_env.struct_fields.get(&def_id) {
        let field_types: Vec<BasicTypeEnum<'ctx>> =
            fields.iter().map(|(_, ty)| ty_to_llvm(ctx, ty)).collect();
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
fn enum_to_llvm<'ctx>(ctx: &CodegenCtx<'ctx>, def_id: DefId) -> BasicTypeEnum<'ctx> {
    let max_bytes = enum_max_payload_bytes(ctx, def_id);
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
pub fn enum_max_payload_bytes<'ctx>(ctx: &CodegenCtx<'ctx>, def_id: DefId) -> u32 {
    let variants = match ctx.type_env.enum_variants.get(&def_id) {
        Some(v) => v,
        None => return 0,
    };
    variants
        .iter()
        .map(|(_, _, fields)| variant_payload_bytes(ctx, fields))
        .max()
        .unwrap_or(0)
}

/// Compute the payload size (in bytes) for a single variant's fields.
fn variant_payload_bytes<'ctx>(ctx: &CodegenCtx<'ctx>, fields: &[(String, Ty)]) -> u32 {
    if fields.is_empty() {
        return 0;
    }
    let field_types: Vec<BasicTypeEnum<'ctx>> =
        fields.iter().map(|(_, ty)| ty_to_llvm(ctx, ty)).collect();
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

/// Get the LLVM struct type representing a variant's fields.
pub fn variant_struct_type<'ctx>(
    ctx: &CodegenCtx<'ctx>,
    fields: &[(String, Ty)],
) -> inkwell::types::StructType<'ctx> {
    let field_types: Vec<BasicTypeEnum<'ctx>> =
        fields.iter().map(|(_, ty)| ty_to_llvm(ctx, ty)).collect();
    ctx.context.struct_type(&field_types, false)
}
