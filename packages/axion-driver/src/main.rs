use axion_diagnostics::DiagnosticOutput;
use axion_parser::parse;
use std::path::Path;
use std::process;

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: axion-driver <command> [options] <file|dir>");
        eprintln!();
        eprintln!("Commands:");
        eprintln!("  check <file|dir>    Parse and check an Axion source file or project");
        eprintln!("  build <file|dir>    Compile an Axion source file or project to an executable");
        eprintln!();
        eprintln!("Options:");
        eprintln!("  --output-format json    Output diagnostics as JSON");
        eprintln!("  --emit-llvm-ir          Emit LLVM IR instead of an executable");
        eprintln!("  -o <name>               Output file name");
        process::exit(1);
    }

    match args[1].as_str() {
        "check" => cmd_check(&args[2..]),
        "build" => cmd_build(&args[2..]),
        other => {
            eprintln!("unknown command: {other}");
            process::exit(1);
        }
    }
}

fn cmd_check(args: &[String]) {
    let mut file_path: Option<&str> = None;
    let mut json_output = false;

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--output-format" => {
                i += 1;
                if i < args.len() && args[i] == "json" {
                    json_output = true;
                } else {
                    eprintln!("expected 'json' after --output-format");
                    process::exit(1);
                }
            }
            s if !s.starts_with('-') => {
                file_path = Some(s);
            }
            other => {
                eprintln!("unknown option: {other}");
                process::exit(1);
            }
        }
        i += 1;
    }

    let file_path = match file_path {
        Some(p) => p,
        None => {
            eprintln!("error: no input file specified");
            process::exit(1);
        }
    };

    let path = Path::new(file_path);
    if path.is_dir() {
        cmd_check_project(path, json_output);
    } else {
        cmd_check_single(file_path, json_output);
    }
}

fn cmd_check_single(file_path: &str, json_output: bool) {
    let source = match std::fs::read_to_string(file_path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: could not read file '{file_path}': {e}");
            process::exit(1);
        }
    };

    let (combined_source, prelude_lines) = axion_resolve::prelude::with_prelude(&source);

    let (ast, mut diagnostics) = parse(&combined_source, file_path);

    // Name resolution pass.
    let (resolved, resolve_diags) = axion_resolve::resolve_single(&ast, file_path, &combined_source);
    diagnostics.extend(resolve_diags);

    // Type checking pass.
    let (type_out, type_diags) = axion_types::type_check(&ast, &resolved, file_path, &combined_source);
    diagnostics.extend(type_diags);

    // Borrow checking pass.
    let mut unify_check = axion_types::unify::UnifyContext::new();
    let type_env_check = axion_types::env::TypeEnv::build(&ast, &resolved, &mut unify_check);
    let borrow_diags = axion_borrow::borrow_check(
        &ast, &resolved, &type_out, &type_env_check, file_path, &combined_source,
    );
    diagnostics.extend(borrow_diags);

    // Filter out diagnostics from the prelude and adjust line numbers.
    let prelude_lines_u32 = prelude_lines as u32;
    diagnostics.retain(|d| d.primary_span.line > prelude_lines_u32);
    for diag in &mut diagnostics {
        diag.primary_span.line -= prelude_lines_u32;
    }

    report_diagnostics(&diagnostics, file_path, json_output);
}

fn cmd_check_project(root: &Path, json_output: bool) {
    let output = axion_module::compile_project_with_prelude(root);
    let display = root.display().to_string();
    report_diagnostics(&output.diagnostics, &display, json_output);
}

fn cmd_build(args: &[String]) {
    let mut file_path: Option<&str> = None;
    let mut output_name: Option<String> = None;
    let mut emit_llvm_ir = false;
    let mut json_output = false;

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "-o" => {
                i += 1;
                if i < args.len() {
                    output_name = Some(args[i].clone());
                } else {
                    eprintln!("expected output name after -o");
                    process::exit(1);
                }
            }
            "--emit-llvm-ir" => {
                emit_llvm_ir = true;
            }
            "--output-format" => {
                i += 1;
                if i < args.len() && args[i] == "json" {
                    json_output = true;
                } else {
                    eprintln!("expected 'json' after --output-format");
                    process::exit(1);
                }
            }
            s if !s.starts_with('-') => {
                file_path = Some(s);
            }
            other => {
                eprintln!("unknown option: {other}");
                process::exit(1);
            }
        }
        i += 1;
    }

    let file_path = match file_path {
        Some(p) => p,
        None => {
            eprintln!("error: no input file specified");
            eprintln!("Usage: axion-driver build [options] <file|dir>");
            process::exit(1);
        }
    };

    let path = Path::new(file_path);
    if path.is_dir() {
        cmd_build_project(path, output_name, emit_llvm_ir, json_output);
    } else {
        cmd_build_single(file_path, output_name, emit_llvm_ir, json_output);
    }
}

fn cmd_build_single(file_path: &str, output_name: Option<String>, emit_llvm_ir: bool, json_output: bool) {
    let source = match std::fs::read_to_string(file_path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: could not read file '{file_path}': {e}");
            process::exit(1);
        }
    };

    let (combined_source, prelude_lines) = axion_resolve::prelude::with_prelude(&source);

    let (ast, mut diagnostics) = parse(&combined_source, file_path);
    let (resolved, resolve_diags) = axion_resolve::resolve_single(&ast, file_path, &combined_source);
    diagnostics.extend(resolve_diags);
    let (type_out, type_diags) = axion_types::type_check(&ast, &resolved, file_path, &combined_source);
    diagnostics.extend(type_diags);

    // Borrow checking pass (before codegen).
    let mut unify_borrow = axion_types::unify::UnifyContext::new();
    let type_env_borrow = axion_types::env::TypeEnv::build(&ast, &resolved, &mut unify_borrow);
    let borrow_diags = axion_borrow::borrow_check(
        &ast, &resolved, &type_out, &type_env_borrow, file_path, &combined_source,
    );
    diagnostics.extend(borrow_diags);

    // Filter out diagnostics from the prelude and adjust line numbers.
    let prelude_lines_u32 = prelude_lines as u32;
    diagnostics.retain(|d| d.primary_span.line > prelude_lines_u32);
    for diag in &mut diagnostics {
        diag.primary_span.line -= prelude_lines_u32;
    }

    let has_errors = diagnostics
        .iter()
        .any(|d| d.severity == axion_diagnostics::Severity::Error);

    if has_errors {
        if json_output {
            let diag_output = DiagnosticOutput::new(diagnostics);
            println!("{}", diag_output.to_json());
        } else {
            for diag in &diagnostics {
                eprintln!(
                    "{}: [{}] {}",
                    diag.severity.as_str(),
                    diag.code,
                    diag.message
                );
                eprintln!(
                    "  --> {}:{}:{}",
                    diag.primary_span.file,
                    diag.primary_span.line,
                    diag.primary_span.col
                );
            }
        }
        process::exit(1);
    }

    // Build the TypeEnv.
    let mut unify = axion_types::unify::UnifyContext::new();
    let type_env = axion_types::env::TypeEnv::build(&ast, &resolved, &mut unify);

    // Monomorphization pass.
    let mono_output = axion_mono::monomorphize(&ast, &resolved, &type_out, &type_env);

    let module_name = Path::new(file_path)
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("main");

    if emit_llvm_ir {
        let ir = axion_codegen::compile_to_ir(&ast, &resolved, &type_out, &type_env, module_name, Some(&mono_output));
        let ir_path = format!("{}.ll", module_name);
        match std::fs::write(&ir_path, &ir) {
            Ok(()) => println!("Wrote {ir_path}"),
            Err(e) => {
                eprintln!("error: could not write IR: {e}");
                process::exit(1);
            }
        }
        return;
    }

    let output_path = output_name.unwrap_or_else(|| module_name.to_string());

    match axion_codegen::compile_to_executable(
        &ast,
        &resolved,
        &type_out,
        &type_env,
        module_name,
        &output_path,
        Some(&mono_output),
    ) {
        Ok(()) => {
            println!("Built {output_path}");
        }
        Err(e) => {
            eprintln!("error: compilation failed: {e}");
            process::exit(1);
        }
    }
}

fn cmd_build_project(root: &Path, output_name: Option<String>, emit_llvm_ir: bool, json_output: bool) {
    let output = axion_module::compile_project_with_prelude(root);

    let has_errors = output
        .diagnostics
        .iter()
        .any(|d| d.severity == axion_diagnostics::Severity::Error);

    if has_errors {
        let display = root.display().to_string();
        report_diagnostics_and_exit(&output.diagnostics, &display, json_output);
    }

    // Per-module IR output mode: emit .ll files and return early.
    if emit_llvm_ir {
        for module in &output.modules {
            let resolved = match module.resolved.as_ref() {
                Some(r) => r,
                None => continue,
            };
            let type_out = match module.type_output.as_ref() {
                Some(t) => t,
                None => continue,
            };

            let mut unify = axion_types::unify::UnifyContext::new();
            let type_env = axion_types::env::TypeEnv::build(&module.ast, resolved, &mut unify);

            let borrow_diags = axion_borrow::borrow_check(
                &module.ast, resolved, type_out, &type_env, &module.file_path, &module.source,
            );
            let borrow_errors: Vec<_> = borrow_diags
                .iter()
                .filter(|d| d.severity == axion_diagnostics::Severity::Error)
                .collect();
            if !borrow_errors.is_empty() {
                for diag in &borrow_errors {
                    eprintln!(
                        "{}: [{}] {}",
                        diag.severity.as_str(),
                        diag.code,
                        diag.message
                    );
                    eprintln!(
                        "  --> {}:{}:{}",
                        diag.primary_span.file,
                        diag.primary_span.line,
                        diag.primary_span.col
                    );
                }
                process::exit(1);
            }

            let mono = axion_mono::monomorphize(&module.ast, resolved, type_out, &type_env);
            let mod_name = module.module_path.0.join("_");
            let ir = axion_codegen::compile_to_ir(
                &module.ast, resolved, type_out, &type_env, &mod_name, Some(&mono),
            );
            let ir_path = format!("{}.ll", mod_name);
            match std::fs::write(&ir_path, &ir) {
                Ok(()) => println!("Wrote {ir_path}"),
                Err(e) => {
                    eprintln!("error: could not write IR: {e}");
                    process::exit(1);
                }
            }
        }
        return;
    }

    // Per-module: borrow check, monomorphize, codegen to .o
    let mut obj_paths = Vec::new();
    for module in &output.modules {
        let resolved = match module.resolved.as_ref() {
            Some(r) => r,
            None => continue,
        };
        let type_out = match module.type_output.as_ref() {
            Some(t) => t,
            None => continue,
        };

        // Borrow check.
        let mut unify = axion_types::unify::UnifyContext::new();
        let type_env = axion_types::env::TypeEnv::build(&module.ast, resolved, &mut unify);
        let borrow_diags = axion_borrow::borrow_check(
            &module.ast, resolved, type_out, &type_env, &module.file_path, &module.source,
        );

        let borrow_errors: Vec<_> = borrow_diags
            .iter()
            .filter(|d| d.severity == axion_diagnostics::Severity::Error)
            .collect();
        if !borrow_errors.is_empty() {
            for diag in &borrow_errors {
                eprintln!(
                    "{}: [{}] {}",
                    diag.severity.as_str(),
                    diag.code,
                    diag.message
                );
                eprintln!(
                    "  --> {}:{}:{}",
                    diag.primary_span.file,
                    diag.primary_span.line,
                    diag.primary_span.col
                );
            }
            process::exit(1);
        }

        // Monomorphize.
        let mono = axion_mono::monomorphize(&module.ast, resolved, type_out, &type_env);

        // Codegen to object.
        let mod_name = module.module_path.0.join("_");
        let obj_bytes = match axion_codegen::compile_to_object(
            &module.ast, resolved, type_out, &type_env, &mod_name, Some(&mono),
        ) {
            Ok(bytes) => bytes,
            Err(e) => {
                eprintln!("error: codegen failed for module '{}': {e}", mod_name);
                process::exit(1);
            }
        };

        let obj_path = format!("{}.o", mod_name);
        if let Err(e) = std::fs::write(&obj_path, &obj_bytes) {
            eprintln!("error: could not write object file '{obj_path}': {e}");
            process::exit(1);
        }
        obj_paths.push(obj_path);
    }

    // Link all .o files.
    let output_path = output_name.unwrap_or_else(|| "a.out".to_string());
    let status = match std::process::Command::new("cc")
        .args(&obj_paths)
        .arg("-o")
        .arg(&output_path)
        .status()
    {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: failed to run linker: {e}");
            // Clean up .o files.
            for p in &obj_paths {
                let _ = std::fs::remove_file(p);
            }
            process::exit(1);
        }
    };

    // Clean up .o files.
    for p in &obj_paths {
        let _ = std::fs::remove_file(p);
    }

    if status.success() {
        println!("Built {output_path}");
    } else {
        eprintln!(
            "error: linker failed with exit code: {}",
            status.code().unwrap_or(-1)
        );
        process::exit(1);
    }
}

fn report_diagnostics(diagnostics: &[axion_diagnostics::Diagnostic], label: &str, json_output: bool) {
    if json_output {
        let output = DiagnosticOutput::new(diagnostics.to_vec());
        println!("{}", output.to_json());
    } else {
        let has_errors = diagnostics
            .iter()
            .any(|d| d.severity == axion_diagnostics::Severity::Error);
        if diagnostics.is_empty() {
            println!("OK: {label}");
        } else {
            for diag in diagnostics {
                eprintln!(
                    "{}: [{}] {}",
                    diag.severity.as_str(),
                    diag.code,
                    diag.message
                );
                eprintln!(
                    "  --> {}:{}:{}",
                    diag.primary_span.file,
                    diag.primary_span.line,
                    diag.primary_span.col
                );
            }
            if has_errors {
                process::exit(1);
            }
        }
    }
}

fn report_diagnostics_and_exit(diagnostics: &[axion_diagnostics::Diagnostic], label: &str, json_output: bool) -> ! {
    report_diagnostics(diagnostics, label, json_output);
    process::exit(1);
}

/// Extension to get string representation of severity.
trait SeverityExt {
    fn as_str(&self) -> &'static str;
}

impl SeverityExt for axion_diagnostics::Severity {
    fn as_str(&self) -> &'static str {
        match self {
            axion_diagnostics::Severity::Error => "error",
            axion_diagnostics::Severity::Warning => "warning",
        }
    }
}
