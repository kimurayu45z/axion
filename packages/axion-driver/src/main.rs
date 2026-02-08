use axion_diagnostics::DiagnosticOutput;
use axion_parser::parse;
use std::path::Path;
use std::process;

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: axion-driver <command> [options] <file>");
        eprintln!();
        eprintln!("Commands:");
        eprintln!("  check <file>    Parse and check an Axion source file");
        eprintln!("  build <file>    Compile an Axion source file to an executable");
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

    let source = match std::fs::read_to_string(file_path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: could not read file '{file_path}': {e}");
            process::exit(1);
        }
    };

    let (ast, mut diagnostics) = parse(&source, file_path);

    // Name resolution pass.
    let (resolved, resolve_diags) = axion_resolve::resolve_single(&ast, file_path, &source);
    diagnostics.extend(resolve_diags);

    // Type checking pass.
    let (type_out, type_diags) = axion_types::type_check(&ast, &resolved, file_path, &source);
    diagnostics.extend(type_diags);

    // Borrow checking pass.
    let mut unify_check = axion_types::unify::UnifyContext::new();
    let type_env_check = axion_types::env::TypeEnv::build(&ast, &resolved, &mut unify_check);
    let borrow_diags = axion_borrow::borrow_check(
        &ast, &resolved, &type_out, &type_env_check, file_path, &source,
    );
    diagnostics.extend(borrow_diags);

    if json_output {
        let output = DiagnosticOutput::new(diagnostics);
        println!("{}", output.to_json());
    } else {
        if diagnostics.is_empty() {
            println!("OK: {file_path}");
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
            process::exit(1);
        }
    }
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
            eprintln!("Usage: axion-driver build [options] <file>");
            process::exit(1);
        }
    };

    let source = match std::fs::read_to_string(file_path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: could not read file '{file_path}': {e}");
            process::exit(1);
        }
    };

    let (ast, mut diagnostics) = parse(&source, file_path);
    let (resolved, resolve_diags) = axion_resolve::resolve_single(&ast, file_path, &source);
    diagnostics.extend(resolve_diags);
    let (type_out, type_diags) = axion_types::type_check(&ast, &resolved, file_path, &source);
    diagnostics.extend(type_diags);

    // Borrow checking pass (before codegen).
    let mut unify_borrow = axion_types::unify::UnifyContext::new();
    let type_env_borrow = axion_types::env::TypeEnv::build(&ast, &resolved, &mut unify_borrow);
    let borrow_diags = axion_borrow::borrow_check(
        &ast, &resolved, &type_out, &type_env_borrow, file_path, &source,
    );
    diagnostics.extend(borrow_diags);

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
