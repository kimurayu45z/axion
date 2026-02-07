use axion_diagnostics::DiagnosticOutput;
use axion_parser::parse;
use std::process;

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: axion-driver <command> [options] [file]");
        eprintln!();
        eprintln!("Commands:");
        eprintln!("  check <file>    Parse and check an Axion source file");
        eprintln!();
        eprintln!("Options:");
        eprintln!("  --output-format json    Output diagnostics as JSON");
        process::exit(1);
    }

    match args[1].as_str() {
        "check" => cmd_check(&args[2..]),
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

    let (_ast, diagnostics) = parse(&source, file_path);

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
