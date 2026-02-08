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
        Ty::Enum { .. } => {
            // Tagged union: { i8 tag, [max_variant_size x i8] }
            // For simplicity, use { i8, i64 } as a fixed layout.
            ctx.context
                .struct_type(
                    &[
                        ctx.context.i8_type().into(),
                        ctx.context.i64_type().into(),
                    ],
                    false,
                )
                .into()
        }
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
