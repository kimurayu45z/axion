use std::ffi::CString;

use inkwell::values::AsValueRef;
use llvm_sys::core::LLVMSetValueName2;

use crate::context::CodegenCtx;

/// Create a C-compatible `main(argc, argv) -> i32` entry point
/// that calls the Axion `main()` function.
pub fn create_entry_point<'ctx>(ctx: &mut CodegenCtx<'ctx>) {
    let axion_main = ctx.module.get_function("main");

    if axion_main.is_some() {
        create_wrapper(ctx);
    }
}

fn create_wrapper<'ctx>(ctx: &mut CodegenCtx<'ctx>) {
    let axion_main = match ctx.module.get_function("main") {
        Some(f) => f,
        None => return,
    };

    // Check if the axion main already returns i32 — if so, no wrapping needed.
    let ret_type = axion_main.get_type().get_return_type();
    if ret_type.is_some() {
        // Has a return type — the function already returns a value.
        return;
    }

    // The axion main returns void. Rename it and create a C wrapper.
    let old_name = "axion_main_impl";
    let c_name = CString::new(old_name).unwrap();
    unsafe {
        LLVMSetValueName2(axion_main.as_value_ref(), c_name.as_ptr(), old_name.len());
    }

    let i32_type = ctx.context.i32_type();
    let main_ty = i32_type.fn_type(&[], false);
    let c_main = ctx.module.add_function("main", main_ty, None);

    let entry = ctx.context.append_basic_block(c_main, "entry");
    ctx.builder.position_at_end(entry);

    // Call axion_main_impl.
    ctx.builder
        .build_call(
            ctx.module.get_function(old_name).unwrap(),
            &[],
            "call_main",
        )
        .unwrap();

    // Return 0.
    ctx.builder
        .build_return(Some(&i32_type.const_int(0, false)))
        .unwrap();
}
