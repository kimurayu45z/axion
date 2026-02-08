use inkwell::values::FunctionValue;
use inkwell::AddressSpace;

use crate::context::CodegenCtx;

/// Declare C library intrinsics used for println, print, etc.
pub fn declare_intrinsics<'ctx>(ctx: &mut CodegenCtx<'ctx>) {
    // int printf(const char *fmt, ...)
    let printf_ty = ctx.context.i32_type().fn_type(
        &[ctx.context.ptr_type(AddressSpace::default()).into()],
        true, // variadic
    );
    ctx.module.add_function("printf", printf_ty, None);

    // int puts(const char *s)
    let puts_ty = ctx.context.i32_type().fn_type(
        &[ctx.context.ptr_type(AddressSpace::default()).into()],
        false,
    );
    ctx.module.add_function("puts", puts_ty, None);

    // void exit(int status)
    let exit_ty = ctx
        .context
        .void_type()
        .fn_type(&[ctx.context.i32_type().into()], false);
    ctx.module.add_function("exit", exit_ty, None);
}

/// Get the printf function.
pub fn get_printf<'ctx>(ctx: &CodegenCtx<'ctx>) -> Option<FunctionValue<'ctx>> {
    ctx.module.get_function("printf")
}

/// Build a call to printf with a format string and arguments.
pub fn build_printf_call<'ctx>(
    ctx: &CodegenCtx<'ctx>,
    fmt: &str,
    args: &[inkwell::values::BasicMetadataValueEnum<'ctx>],
) {
    let printf = match get_printf(ctx) {
        Some(f) => f,
        None => return,
    };

    // Create global string constant for format.
    let fmt_str = ctx.builder.build_global_string_ptr(fmt, "fmt").unwrap();
    let mut call_args: Vec<inkwell::values::BasicMetadataValueEnum> =
        vec![fmt_str.as_pointer_value().into()];
    call_args.extend_from_slice(args);
    ctx.builder
        .build_call(printf, &call_args, "printf_ret")
        .unwrap();
}
