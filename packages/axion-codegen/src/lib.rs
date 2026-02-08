pub mod context;
pub mod layout;
pub mod intrinsics;
pub mod function;
pub mod expr;
pub mod stmt;
pub mod entry;

#[cfg(test)]
mod tests;

use axion_mono::output::MonoOutput;
use axion_resolve::ResolveOutput;
use axion_types::env::TypeEnv;
use axion_types::TypeCheckOutput;
use axion_syntax::SourceFile;
use inkwell::context::Context;
use inkwell::targets::{
    CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine,
};
use inkwell::OptimizationLevel;

use crate::context::CodegenCtx;
use crate::entry::create_entry_point;
use crate::function::{
    compile_functions, compile_specialized_functions, declare_functions,
    declare_specialized_functions,
};
use crate::intrinsics::declare_intrinsics;

/// Compile a source file to LLVM IR (as a string).
pub fn compile_to_ir(
    source_file: &SourceFile,
    resolved: &ResolveOutput,
    type_check: &TypeCheckOutput,
    type_env: &TypeEnv,
    module_name: &str,
    mono_output: Option<&MonoOutput>,
) -> String {
    let context = Context::create();
    let mut ctx = CodegenCtx::new(&context, module_name, resolved, type_check, type_env, mono_output);

    // Phase 1: Declare all functions.
    declare_functions(&mut ctx, source_file);
    declare_specialized_functions(&mut ctx);

    // Phase 2: Declare intrinsics.
    declare_intrinsics(&mut ctx);

    // Phase 3: Compile function bodies.
    compile_functions(&mut ctx, source_file);
    compile_specialized_functions(&mut ctx);

    // Phase 4: Create entry point wrapper.
    create_entry_point(&mut ctx);

    ctx.module.print_to_string().to_string()
}

/// Compile a source file to an object file, returning the bytes.
pub fn compile_to_object(
    source_file: &SourceFile,
    resolved: &ResolveOutput,
    type_check: &TypeCheckOutput,
    type_env: &TypeEnv,
    module_name: &str,
    mono_output: Option<&MonoOutput>,
) -> Result<Vec<u8>, String> {
    let context = Context::create();
    let mut ctx = CodegenCtx::new(&context, module_name, resolved, type_check, type_env, mono_output);

    declare_functions(&mut ctx, source_file);
    declare_specialized_functions(&mut ctx);
    declare_intrinsics(&mut ctx);
    compile_functions(&mut ctx, source_file);
    compile_specialized_functions(&mut ctx);
    create_entry_point(&mut ctx);

    // Verify the module.
    if let Err(msg) = ctx.module.verify() {
        return Err(format!("LLVM verification failed: {}", msg.to_string()));
    }

    // Initialize target.
    Target::initialize_all(&InitializationConfig::default());

    let triple = TargetMachine::get_default_triple();
    let target = Target::from_triple(&triple).map_err(|e| e.to_string())?;
    let machine = target
        .create_target_machine(
            &triple,
            "generic",
            "",
            OptimizationLevel::Default,
            RelocMode::Default,
            CodeModel::Default,
        )
        .ok_or_else(|| "Failed to create target machine".to_string())?;

    let buf = machine
        .write_to_memory_buffer(&ctx.module, FileType::Object)
        .map_err(|e| e.to_string())?;

    Ok(buf.as_slice().to_vec())
}

/// Compile a source file to an executable at the given output path.
pub fn compile_to_executable(
    source_file: &SourceFile,
    resolved: &ResolveOutput,
    type_check: &TypeCheckOutput,
    type_env: &TypeEnv,
    module_name: &str,
    output_path: &str,
    mono_output: Option<&MonoOutput>,
) -> Result<(), String> {
    let obj_bytes = compile_to_object(source_file, resolved, type_check, type_env, module_name, mono_output)?;

    // Write object file to a temp path.
    let obj_path = format!("{}.o", output_path);
    std::fs::write(&obj_path, &obj_bytes)
        .map_err(|e| format!("Failed to write object file: {}", e))?;

    // Link with system linker.
    let status = std::process::Command::new("cc")
        .arg(&obj_path)
        .arg("-o")
        .arg(output_path)
        .status()
        .map_err(|e| format!("Failed to run linker: {}", e))?;

    // Clean up object file.
    let _ = std::fs::remove_file(&obj_path);

    if status.success() {
        Ok(())
    } else {
        Err(format!(
            "Linker failed with exit code: {}",
            status.code().unwrap_or(-1)
        ))
    }
}
