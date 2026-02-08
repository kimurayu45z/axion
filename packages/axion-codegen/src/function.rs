use axion_resolve::def_id::SymbolKind;
use axion_syntax::*;
use axion_types::ty::Ty;
use inkwell::types::BasicType;

use crate::context::CodegenCtx;
use crate::expr::compile_expr;
use crate::layout::{is_void_ty, ty_to_llvm, ty_to_llvm_metadata};
use crate::stmt::compile_stmt;

/// Emit cleanup code: free all heap-allocated pointers in reverse order.
pub fn emit_cleanup<'ctx>(ctx: &CodegenCtx<'ctx>) {
    let free_fn = match ctx.module.get_function("free") {
        Some(f) => f,
        None => return,
    };
    for ptr in ctx.heap_allocs.iter().rev() {
        ctx.builder
            .build_call(free_fn, &[(*ptr).into()], "")
            .unwrap();
    }
}

/// Phase 1: Declare all functions (create LLVM function declarations).
pub fn declare_functions<'ctx>(ctx: &mut CodegenCtx<'ctx>, source_file: &SourceFile) {
    for item in &source_file.items {
        if let ItemKind::Function(f) = &item.kind {
            declare_fn(ctx, f, item.span);
        }
    }
}

fn declare_fn<'ctx>(ctx: &mut CodegenCtx<'ctx>, f: &FnDef, item_span: Span) {
    // Find the DefId for this function.
    let def_id = ctx
        .resolved
        .symbols
        .iter()
        .find(|s| s.span == item_span && s.kind == SymbolKind::Function)
        .map(|s| s.def_id);
    let Some(def_id) = def_id else { return };

    // Get the function type from TypeEnv.
    let fn_ty = ctx.type_env.defs.get(&def_id).map(|info| &info.ty);
    let Some(Ty::Fn { params, ret }) = fn_ty else {
        return;
    };

    // Build LLVM function type.
    let param_types: Vec<inkwell::types::BasicMetadataTypeEnum> = params
        .iter()
        .map(|t| ty_to_llvm_metadata(ctx, t))
        .collect();

    let fn_type = if is_void_ty(ret) {
        ctx.context.void_type().fn_type(&param_types, false)
    } else {
        ty_to_llvm(ctx, ret).fn_type(&param_types, false)
    };

    let fn_value = ctx.module.add_function(&f.name, fn_type, None);
    ctx.functions.insert(def_id, fn_value);
}

/// Phase 3: Compile function bodies.
pub fn compile_functions<'ctx>(ctx: &mut CodegenCtx<'ctx>, source_file: &SourceFile) {
    for item in &source_file.items {
        if let ItemKind::Function(f) = &item.kind {
            compile_fn_body(ctx, f, item.span);
        }
    }
}

fn compile_fn_body<'ctx>(ctx: &mut CodegenCtx<'ctx>, f: &FnDef, item_span: Span) {
    // Find the DefId and LLVM function.
    let def_id = ctx
        .resolved
        .symbols
        .iter()
        .find(|s| s.span == item_span && s.kind == SymbolKind::Function)
        .map(|s| s.def_id);
    let Some(def_id) = def_id else { return };
    let Some(&fn_value) = ctx.functions.get(&def_id) else {
        return;
    };

    // Get the return type.
    let fn_ty = ctx.type_env.defs.get(&def_id).map(|info| &info.ty);
    let ret_ty = match fn_ty {
        Some(Ty::Fn { ret, .. }) => (**ret).clone(),
        _ => Ty::Unit,
    };

    // Create entry basic block.
    let entry_bb = ctx.context.append_basic_block(fn_value, "entry");
    ctx.builder.position_at_end(entry_bb);

    // Clear locals and heap allocations for this function.
    ctx.locals.clear();
    ctx.local_types.clear();
    ctx.heap_allocs.clear();

    // Alloca params as local variables.
    for (i, param) in f.params.iter().enumerate() {
        let param_sym = ctx
            .resolved
            .symbols
            .iter()
            .find(|s| s.kind == SymbolKind::Param && s.span == param.span);

        if let Some(sym) = param_sym {
            let param_ty = fn_value.get_nth_param(i as u32);
            if let Some(param_val) = param_ty {
                let val_ty = param_val.get_type();
                let alloca = ctx
                    .builder
                    .build_alloca(val_ty, &param.name)
                    .unwrap();
                ctx.builder.build_store(alloca, param_val).unwrap();
                ctx.locals.insert(sym.def_id, alloca);
                ctx.local_types.insert(sym.def_id, val_ty);
            }
        }
    }

    // Compile body statements.
    let mut last_val = None;
    for (i, stmt) in f.body.iter().enumerate() {
        let is_last = i == f.body.len() - 1;
        if is_last {
            // The last statement might be an expression whose value we return.
            if let StmtKind::Expr(expr) = &stmt.kind {
                last_val = compile_expr(ctx, expr);
            } else {
                compile_stmt(ctx, stmt);
            }
        } else {
            compile_stmt(ctx, stmt);
        }

        // Check if the current block is already terminated.
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

    // Insert return if not already terminated.
    if ctx
        .builder
        .get_insert_block()
        .unwrap()
        .get_terminator()
        .is_none()
    {
        emit_cleanup(ctx);
        if is_void_ty(&ret_ty) {
            ctx.builder.build_return(None).unwrap();
        } else if let Some(val) = last_val {
            ctx.builder.build_return(Some(&val)).unwrap();
        } else {
            // Return default value.
            let ret_llvm_ty = ty_to_llvm(ctx, &ret_ty);
            let zero = ret_llvm_ty.const_zero();
            ctx.builder.build_return(Some(&zero)).unwrap();
        }
    }
}

/// Declare all specialized (monomorphized) functions.
pub fn declare_specialized_functions<'ctx>(ctx: &mut CodegenCtx<'ctx>) {
    let mono = match ctx.mono_output {
        Some(m) => m,
        None => return,
    };

    // Clone specialized_fns to avoid borrow issues.
    let specs: Vec<_> = mono.specialized_fns.iter().map(|s| {
        (s.mangled_name.clone(), s.fn_ty.clone())
    }).collect();

    for (mangled_name, fn_ty) in &specs {
        let Ty::Fn { params, ret } = fn_ty else { continue };

        let param_types: Vec<inkwell::types::BasicMetadataTypeEnum> = params
            .iter()
            .map(|t| ty_to_llvm_metadata(ctx, t))
            .collect();

        let fn_type = if is_void_ty(ret) {
            ctx.context.void_type().fn_type(&param_types, false)
        } else {
            ty_to_llvm(ctx, ret).fn_type(&param_types, false)
        };

        let fn_value = ctx.module.add_function(mangled_name, fn_type, None);
        ctx.mono_fn_values.insert(mangled_name.clone(), fn_value);
    }
}

/// Compile bodies of all specialized (monomorphized) functions.
pub fn compile_specialized_functions<'ctx>(ctx: &mut CodegenCtx<'ctx>) {
    let mono = match ctx.mono_output {
        Some(m) => m,
        None => return,
    };

    // Clone the data we need to avoid borrow conflicts.
    let specs: Vec<_> = mono.specialized_fns.iter().map(|s| {
        (
            s.mangled_name.clone(),
            s.fn_ty.clone(),
            s.body.clone(),
            s.params.clone(),
            s.subst.clone(),
        )
    }).collect();

    for (mangled_name, fn_ty, body, params, subst) in &specs {
        let Some(&fn_value) = ctx.mono_fn_values.get(mangled_name.as_str()) else {
            continue;
        };

        let ret_ty = match fn_ty {
            Ty::Fn { ret, .. } => (**ret).clone(),
            _ => Ty::Unit,
        };

        // Set current substitution so get_expr_ty applies it.
        ctx.current_subst = subst.clone();

        // Create entry basic block.
        let entry_bb = ctx.context.append_basic_block(fn_value, "entry");
        ctx.builder.position_at_end(entry_bb);

        // Clear locals and heap allocations for this function.
        ctx.locals.clear();
        ctx.local_types.clear();
        ctx.heap_allocs.clear();

        // Alloca params as local variables.
        for (i, param) in params.iter().enumerate() {
            let param_sym = ctx
                .resolved
                .symbols
                .iter()
                .find(|s| s.kind == SymbolKind::Param && s.span == param.span);

            if let Some(sym) = param_sym {
                let param_val = fn_value.get_nth_param(i as u32);
                if let Some(param_val) = param_val {
                    let val_ty = param_val.get_type();
                    let alloca = ctx
                        .builder
                        .build_alloca(val_ty, &param.name)
                        .unwrap();
                    ctx.builder.build_store(alloca, param_val).unwrap();
                    ctx.locals.insert(sym.def_id, alloca);
                    ctx.local_types.insert(sym.def_id, val_ty);
                }
            }
        }

        // Compile body statements.
        let mut last_val = None;
        for (i, stmt) in body.iter().enumerate() {
            let is_last = i == body.len() - 1;
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

        // Insert return if not already terminated.
        if ctx
            .builder
            .get_insert_block()
            .unwrap()
            .get_terminator()
            .is_none()
        {
            emit_cleanup(ctx);
            if is_void_ty(&ret_ty) {
                ctx.builder.build_return(None).unwrap();
            } else if let Some(val) = last_val {
                ctx.builder.build_return(Some(&val)).unwrap();
            } else {
                let ret_llvm_ty = ty_to_llvm(ctx, &ret_ty);
                let zero = ret_llvm_ty.const_zero();
                ctx.builder.build_return(Some(&zero)).unwrap();
            }
        }

        // Clear substitution.
        ctx.current_subst.clear();
    }
}
