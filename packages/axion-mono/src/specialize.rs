use std::collections::HashMap;

use axion_resolve::def_id::DefId;
use axion_resolve::ResolveOutput;
use axion_syntax::*;
use axion_types::env::TypeEnv;
use axion_types::ty::Ty;

use crate::collect::Instantiation;
use crate::output::{MonoOutput, SpecKey, SpecializedFn};

/// Create specialized function copies for each instantiation.
pub fn specialize(
    source_file: &SourceFile,
    resolved: &ResolveOutput,
    type_env: &TypeEnv,
    instantiations: &[Instantiation],
) -> MonoOutput {
    let mut output = MonoOutput::new();

    for inst in instantiations {
        let fn_sym = resolved
            .symbols
            .iter()
            .find(|s| s.def_id == inst.fn_def_id);
        let Some(fn_sym) = fn_sym else { continue };

        // Find the function's or method's AST node.
        enum FnOrMethod<'a> {
            Fn(&'a FnDef),
            Method(&'a MethodDef),
        }
        let fn_or_method = source_file.items.iter().find_map(|item| {
            if item.span == fn_sym.span {
                match &item.kind {
                    ItemKind::Function(f) => Some(FnOrMethod::Fn(f)),
                    ItemKind::Method(m) => Some(FnOrMethod::Method(m)),
                    _ => None,
                }
            } else {
                None
            }
        });
        let Some(fn_or_method) = fn_or_method else { continue };

        // Find the function's type parameter DefIds by collecting Ty::Param
        // from the function's registered type. This handles impl-level type params
        // whose source spans are outside the method's span.
        let type_param_defs: Vec<DefId> = if let Some(info) = type_env.defs.get(&inst.fn_def_id) {
            let mut params = Vec::new();
            collect_param_def_ids(&info.ty, &mut params);
            // Deduplicate while preserving order.
            let mut seen_set = std::collections::HashSet::new();
            params.retain(|d| seen_set.insert(*d));
            params
        } else {
            Vec::new()
        };

        if type_param_defs.len() != inst.type_args.len() {
            continue;
        }

        // Build substitution map.
        let mut subst: HashMap<DefId, Ty> = HashMap::new();
        for (param_def_id, arg_ty) in type_param_defs.iter().zip(inst.type_args.iter()) {
            subst.insert(*param_def_id, arg_ty.clone());
        }

        // Build the specialized function type.
        let fn_ty_info = type_env.defs.get(&inst.fn_def_id);
        let specialized_ty = if let Some(info) = fn_ty_info {
            substitute(&info.ty, &subst)
        } else {
            continue;
        };

        // Generate mangled name and build SpecializedFn.
        let (mangled_name, body, params, return_type, is_method, receiver_modifier) = match &fn_or_method {
            FnOrMethod::Fn(f) => {
                let name = mangle_name(&f.name, &inst.type_args);
                (name, f.body.clone(), f.params.clone(), f.return_type.clone(), false, None)
            }
            FnOrMethod::Method(m) => {
                let receiver_name = match &m.receiver_type {
                    TypeExpr::Named { name, .. } => name.clone(),
                    _ => "Unknown".to_string(),
                };
                let base_name = format!("{}.{}", receiver_name, m.name);
                let name = mangle_name(&base_name, &inst.type_args);
                (name, m.body.clone(), m.params.clone(), m.return_type.clone(), true, Some(m.receiver_modifier.clone()))
            }
        };

        let key = SpecKey {
            fn_def_id: inst.fn_def_id,
            type_args: inst.type_args.clone(),
        };

        output.specializations.insert(key, mangled_name.clone());
        output.specialized_fns.push(SpecializedFn {
            original_def_id: inst.fn_def_id,
            type_args: inst.type_args.clone(),
            mangled_name,
            fn_ty: specialized_ty,
            body,
            params,
            return_type,
            subst,
            is_method,
            receiver_modifier,
        });
    }

    output
}

/// Apply type substitution.
pub fn substitute(ty: &Ty, subst: &HashMap<DefId, Ty>) -> Ty {
    match ty {
        Ty::Param(def_id) => subst.get(def_id).cloned().unwrap_or_else(|| ty.clone()),
        Ty::Struct { def_id, type_args } => Ty::Struct {
            def_id: *def_id,
            type_args: type_args.iter().map(|t| substitute(t, subst)).collect(),
        },
        Ty::Enum { def_id, type_args } => Ty::Enum {
            def_id: *def_id,
            type_args: type_args.iter().map(|t| substitute(t, subst)).collect(),
        },
        Ty::Tuple(elems) => Ty::Tuple(elems.iter().map(|t| substitute(t, subst)).collect()),
        Ty::Fn { params, ret } => Ty::Fn {
            params: params.iter().map(|t| substitute(t, subst)).collect(),
            ret: Box::new(substitute(ret, subst)),
        },
        Ty::Ref(inner) => Ty::Ref(Box::new(substitute(inner, subst))),
        Ty::Slice(inner) => Ty::Slice(Box::new(substitute(inner, subst))),
        Ty::Array { elem, len } => Ty::Array {
            elem: Box::new(substitute(elem, subst)),
            len: *len,
        },
        _ => ty.clone(),
    }
}

/// Collect all Ty::Param DefIds from a type.
fn collect_param_def_ids(ty: &Ty, out: &mut Vec<DefId>) {
    match ty {
        Ty::Param(def_id) => {
            if !out.contains(def_id) {
                out.push(*def_id);
            }
        }
        Ty::Struct { type_args, .. } | Ty::Enum { type_args, .. } => {
            for t in type_args {
                collect_param_def_ids(t, out);
            }
        }
        Ty::Tuple(elems) => {
            for t in elems {
                collect_param_def_ids(t, out);
            }
        }
        Ty::Fn { params, ret } => {
            for t in params {
                collect_param_def_ids(t, out);
            }
            collect_param_def_ids(ret, out);
        }
        Ty::Ref(inner) | Ty::Slice(inner) => {
            collect_param_def_ids(inner, out);
        }
        Ty::Array { elem, .. } => {
            collect_param_def_ids(elem, out);
        }
        _ => {}
    }
}

/// Generate a mangled name for a specialization.
fn mangle_name(base_name: &str, type_args: &[Ty]) -> String {
    let mut name = base_name.to_string();
    for arg in type_args {
        name.push_str("__");
        name.push_str(&ty_to_suffix(arg));
    }
    name
}

/// Convert a type to a suffix string for mangling.
fn ty_to_suffix(ty: &Ty) -> String {
    match ty {
        Ty::Prim(p) => format!("{}", p),
        Ty::Unit => "unit".to_string(),
        Ty::Struct { def_id, .. } => format!("s{}", def_id.0),
        Ty::Enum { def_id, .. } => format!("e{}", def_id.0),
        Ty::Tuple(elems) => {
            let parts: Vec<String> = elems.iter().map(ty_to_suffix).collect();
            format!("t_{}", parts.join("_"))
        }
        Ty::Fn { params, ret } => {
            let p: Vec<String> = params.iter().map(ty_to_suffix).collect();
            format!("fn_{}_r_{}", p.join("_"), ty_to_suffix(ret))
        }
        Ty::Ref(inner) => format!("ref_{}", ty_to_suffix(inner)),
        Ty::Array { elem, len } => format!("arr_{}_{}", len, ty_to_suffix(elem)),
        Ty::Param(def_id) => format!("p{}", def_id.0),
        _ => "unknown".to_string(),
    }
}
