use axion_resolve::def_id::SymbolKind;
use axion_syntax::*;
use axion_types::ty::Ty;
use inkwell::types::BasicType;
use inkwell::AddressSpace;

use crate::context::CodegenCtx;
use crate::expr::compile_expr;
use crate::layout::{is_void_ty, ty_to_llvm, ty_to_llvm_metadata};
use crate::stmt::compile_stmt;

/// Emit cleanup code: call drop methods on droppable locals, then free heap-allocated pointers.
pub fn emit_cleanup<'ctx>(ctx: &CodegenCtx<'ctx>) {
    // Call drop methods in reverse order (LIFO).
    for (alloca, llvm_ty, drop_fn) in ctx.drop_locals.iter().rev() {
        // Check if the drop method expects a pointer (pass-by-reference) or a value.
        let first_param_is_ptr = drop_fn
            .get_type()
            .get_param_types()
            .first()
            .map(|t| t.is_pointer_type())
            .unwrap_or(false);
        if first_param_is_ptr {
            // Pass the alloca pointer directly.
            ctx.builder
                .build_call(*drop_fn, &[(*alloca).into()], "")
                .unwrap();
        } else {
            let val = ctx
                .builder
                .build_load(*llvm_ty, *alloca, "drop_val")
                .unwrap();
            ctx.builder
                .build_call(*drop_fn, &[val.into()], "")
                .unwrap();
        }
    }

    // Free heap allocations.
    if let Some(free_fn) = ctx.module.get_function("free") {
        for ptr in ctx.heap_allocs.iter().rev() {
            ctx.builder
                .build_call(free_fn, &[(*ptr).into()], "")
                .unwrap();
        }
    }
}

/// Phase 1: Declare all functions and methods (create LLVM function declarations).
pub fn declare_functions<'ctx>(ctx: &mut CodegenCtx<'ctx>, source_file: &SourceFile) {
    for item in &source_file.items {
        match &item.kind {
            ItemKind::Function(f) => declare_fn(ctx, f, item.span),
            ItemKind::Method(m) => declare_method(ctx, m, item.span),
            _ => {}
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

/// Phase 3: Compile function and method bodies.
pub fn compile_functions<'ctx>(ctx: &mut CodegenCtx<'ctx>, source_file: &SourceFile) {
    for item in &source_file.items {
        match &item.kind {
            ItemKind::Function(f) => compile_fn_body(ctx, f, item.span),
            ItemKind::Method(m) => compile_method_body(ctx, m, item.span),
            _ => {}
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
    ctx.drop_locals.clear();

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

fn declare_method<'ctx>(ctx: &mut CodegenCtx<'ctx>, m: &MethodDef, item_span: Span) {
    let def_id = ctx
        .resolved
        .symbols
        .iter()
        .find(|s| s.span == item_span && s.kind == SymbolKind::Method)
        .map(|s| s.def_id);
    let Some(def_id) = def_id else { return };

    let fn_ty = ctx.type_env.defs.get(&def_id).map(|info| &info.ty);
    let Some(Ty::Fn { params, ret }) = fn_ty else {
        return;
    };

    let param_types: Vec<inkwell::types::BasicMetadataTypeEnum> = params
        .iter()
        .enumerate()
        .map(|(i, t)| {
            if i == 0 && matches!(m.receiver_modifier, ReceiverModifier::Mut | ReceiverModifier::Borrow) {
                ctx.context.ptr_type(AddressSpace::default()).into()
            } else {
                ty_to_llvm_metadata(ctx, t)
            }
        })
        .collect();

    let fn_type = if is_void_ty(ret) {
        ctx.context.void_type().fn_type(&param_types, false)
    } else {
        ty_to_llvm(ctx, ret).fn_type(&param_types, false)
    };

    // Method name is "ReceiverType.methodName".
    let receiver_name = type_expr_name(&m.receiver_type);
    let fn_name = format!("{}.{}", receiver_name, m.name);
    let fn_value = ctx.module.add_function(&fn_name, fn_type, None);
    ctx.functions.insert(def_id, fn_value);
}

fn compile_method_body<'ctx>(ctx: &mut CodegenCtx<'ctx>, m: &MethodDef, item_span: Span) {
    let def_id = ctx
        .resolved
        .symbols
        .iter()
        .find(|s| s.span == item_span && s.kind == SymbolKind::Method)
        .map(|s| s.def_id);
    let Some(def_id) = def_id else { return };
    let Some(&fn_value) = ctx.functions.get(&def_id) else {
        return;
    };

    let fn_ty = ctx.type_env.defs.get(&def_id).map(|info| &info.ty);
    let ret_ty = match fn_ty {
        Some(Ty::Fn { ret, .. }) => (**ret).clone(),
        _ => Ty::Unit,
    };

    let entry_bb = ctx.context.append_basic_block(fn_value, "entry");
    ctx.builder.position_at_end(entry_bb);

    ctx.locals.clear();
    ctx.local_types.clear();
    ctx.heap_allocs.clear();
    ctx.drop_locals.clear();

    // First parameter is the implicit `self` (receiver).
    // The resolver registers `self` as a Param with Span::dummy(), so we find it
    // by checking which `self` DefId is referenced in resolutions within this method.
    if let Some(self_val) = fn_value.get_nth_param(0) {
        // Collect all `self` param DefIds.
        let self_def_ids: Vec<_> = ctx
            .resolved
            .symbols
            .iter()
            .filter(|s| s.kind == SymbolKind::Param && s.name == "self")
            .map(|s| s.def_id)
            .collect();
        // Find which one is referenced within this method's span.
        let self_def_id = ctx
            .resolved
            .resolutions
            .iter()
            .filter(|&(&offset, _)| offset >= item_span.start && offset < item_span.end)
            .find(|(_, def_id)| self_def_ids.contains(def_id))
            .map(|(_, &def_id)| def_id);
        let self_sym = self_def_id.and_then(|did| {
            ctx.resolved.symbols.iter().find(|s| s.def_id == did)
        });
        if let Some(sym) = self_sym {
            if matches!(m.receiver_modifier, ReceiverModifier::Mut | ReceiverModifier::Borrow) {
                // self_val is already a pointer to caller's struct — use directly.
                let ptr = self_val.into_pointer_value();
                let fn_ty = ctx.type_env.defs.get(&def_id).map(|info| &info.ty);
                let pointee_ty = match fn_ty {
                    Some(Ty::Fn { params, .. }) if !params.is_empty() => ty_to_llvm(ctx, &params[0]),
                    _ => ctx.context.i64_type().into(),
                };
                ctx.locals.insert(sym.def_id, ptr);
                ctx.local_types.insert(sym.def_id, pointee_ty);
            } else {
                // Move: pass by value (current behavior).
                let val_ty = self_val.get_type();
                let alloca = ctx.builder.build_alloca(val_ty, "self").unwrap();
                ctx.builder.build_store(alloca, self_val).unwrap();
                ctx.locals.insert(sym.def_id, alloca);
                ctx.local_types.insert(sym.def_id, val_ty);
            }
        }
    }

    // Remaining parameters (offset by 1 because of self).
    for (i, param) in m.params.iter().enumerate() {
        let param_sym = ctx
            .resolved
            .symbols
            .iter()
            .find(|s| s.kind == SymbolKind::Param && s.span == param.span);

        if let Some(sym) = param_sym {
            let param_val = fn_value.get_nth_param((i + 1) as u32);
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
    for (i, stmt) in m.body.iter().enumerate() {
        let is_last = i == m.body.len() - 1;
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
}

/// Helper: extract the name from a TypeExpr.
fn type_expr_name(te: &TypeExpr) -> String {
    match te {
        TypeExpr::Named { name, .. } => name.clone(),
        _ => "Unknown".to_string(),
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
        (s.mangled_name.clone(), s.fn_ty.clone(), s.is_method, s.receiver_modifier.clone())
    }).collect();

    for (mangled_name, fn_ty, is_method, receiver_modifier) in &specs {
        let Ty::Fn { params, ret } = fn_ty else { continue };

        let param_types: Vec<inkwell::types::BasicMetadataTypeEnum> = params
            .iter()
            .enumerate()
            .map(|(i, t)| {
                if i == 0 && *is_method {
                    if matches!(receiver_modifier, Some(ReceiverModifier::Mut) | Some(ReceiverModifier::Borrow)) {
                        return ctx.context.ptr_type(AddressSpace::default()).into();
                    }
                }
                ty_to_llvm_metadata(ctx, t)
            })
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
            s.is_method,
            s.receiver_modifier.clone(),
            s.original_def_id,
        )
    }).collect();

    for (mangled_name, fn_ty, body, params, subst, is_method, receiver_modifier, original_def_id) in &specs {
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

        // Handle self parameter for methods.
        let param_offset = if *is_method {
            // Find the `self` DefId for this method.
            let method_sym = ctx.resolved.symbols.iter().find(|s| s.def_id == *original_def_id);
            let item_span = method_sym.map(|s| s.span).unwrap_or(Span::dummy());

            if let Some(self_val) = fn_value.get_nth_param(0) {
                let self_def_ids: Vec<_> = ctx.resolved.symbols.iter()
                    .filter(|s| s.kind == SymbolKind::Param && s.name == "self")
                    .map(|s| s.def_id)
                    .collect();
                let self_def_id = ctx.resolved.resolutions.iter()
                    .filter(|&(&offset, _)| offset >= item_span.start && offset < item_span.end)
                    .find(|(_, def_id)| self_def_ids.contains(def_id))
                    .map(|(_, &def_id)| def_id);
                let self_sym = self_def_id.and_then(|did| {
                    ctx.resolved.symbols.iter().find(|s| s.def_id == did)
                });
                if let Some(sym) = self_sym {
                    let pass_by_ref = matches!(receiver_modifier, Some(ReceiverModifier::Mut) | Some(ReceiverModifier::Borrow));
                    if pass_by_ref {
                        let ptr = self_val.into_pointer_value();
                        let Ty::Fn { params: fn_params, .. } = fn_ty else { unreachable!() };
                        let pointee_ty = if !fn_params.is_empty() {
                            ty_to_llvm(ctx, &fn_params[0])
                        } else {
                            ctx.context.i64_type().into()
                        };
                        ctx.locals.insert(sym.def_id, ptr);
                        ctx.local_types.insert(sym.def_id, pointee_ty);
                    } else {
                        let val_ty = self_val.get_type();
                        let alloca = ctx.builder.build_alloca(val_ty, "self").unwrap();
                        ctx.builder.build_store(alloca, self_val).unwrap();
                        ctx.locals.insert(sym.def_id, alloca);
                        ctx.local_types.insert(sym.def_id, val_ty);
                    }
                }
            }
            1u32
        } else {
            0u32
        };

        // Alloca params as local variables.
        for (i, param) in params.iter().enumerate() {
            let param_sym = ctx
                .resolved
                .symbols
                .iter()
                .find(|s| s.kind == SymbolKind::Param && s.span == param.span);

            if let Some(sym) = param_sym {
                let param_val = fn_value.get_nth_param((i as u32) + param_offset);
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
