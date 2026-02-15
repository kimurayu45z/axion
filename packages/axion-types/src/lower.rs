use axion_resolve::def_id::DefId;
use axion_resolve::symbol::Symbol;
use axion_syntax::TypeExpr;
use std::collections::HashMap;

use crate::ty::{PrimTy, Ty};

/// Lower a TypeExpr to a Ty.
pub(crate) fn lower_type_expr(
    te: &TypeExpr,
    symbols: &[Symbol],
    resolutions: &HashMap<u32, DefId>,
) -> Ty {
    match te {
        TypeExpr::Named { name, args, span } => {
            // Built-in parameterized type: Ptr[T]
            if name == "Ptr" {
                let inner = args
                    .first()
                    .map(|a| lower_type_expr(a, symbols, resolutions))
                    .unwrap_or(Ty::Unit);
                return Ty::Ptr(Box::new(inner));
            }

            // Check if it's a primitive type.
            if let Some(prim) = PrimTy::from_name(name) {
                return Ty::Prim(prim);
            }

            // Look up the resolution for this type name.
            if let Some(&def_id) = resolutions.get(&span.start) {
                let lowered_args: Vec<Ty> = args
                    .iter()
                    .map(|a| lower_type_expr(a, symbols, resolutions))
                    .collect();

                // Determine if this is a struct, enum, type param, or type alias.
                if let Some(sym) = symbols.iter().find(|s| s.def_id == def_id) {
                    use axion_resolve::def_id::SymbolKind;
                    match sym.kind {
                        SymbolKind::Struct => Ty::Struct {
                            def_id,
                            type_args: lowered_args,
                        },
                        SymbolKind::Enum => Ty::Enum {
                            def_id,
                            type_args: lowered_args,
                        },
                        SymbolKind::TypeParam => {
                            // If this TypeParam has a parent (e.g., `Self` → struct),
                            // resolve to the parent type.
                            if let Some(parent_id) = sym.parent {
                                let parent_sym =
                                    symbols.iter().find(|s| s.def_id == parent_id);
                                if let Some(parent) = parent_sym {
                                    match parent.kind {
                                        SymbolKind::Struct => {
                                            return Ty::Struct {
                                                def_id: parent_id,
                                                type_args: lowered_args,
                                            };
                                        }
                                        SymbolKind::Enum => {
                                            return Ty::Enum {
                                                def_id: parent_id,
                                                type_args: lowered_args,
                                            };
                                        }
                                        _ => {}
                                    }
                                }
                            }
                            Ty::Param(def_id)
                        }
                        SymbolKind::TypeAlias => {
                            // For built-in primitive types registered as TypeAlias
                            if let Some(prim) = PrimTy::from_name(&sym.name) {
                                Ty::Prim(prim)
                            } else {
                                // User-defined type alias — for now, treat as Error
                                Ty::Error
                            }
                        }
                        SymbolKind::Interface => {
                            // Interfaces used as types (e.g. dyn Interface) — defer
                            Ty::Error
                        }
                        _ => Ty::Error,
                    }
                } else {
                    Ty::Error
                }
            } else {
                // Unresolved type — return Error to prevent cascading
                Ty::Error
            }
        }

        TypeExpr::Tuple { elements, .. } => {
            if elements.is_empty() {
                Ty::Unit
            } else {
                let elems = elements
                    .iter()
                    .map(|e| lower_type_expr(e, symbols, resolutions))
                    .collect();
                Ty::Tuple(elems)
            }
        }

        TypeExpr::Fn { params, ret, .. } => {
            let param_tys = params
                .iter()
                .map(|p| lower_type_expr(p, symbols, resolutions))
                .collect();
            let ret_ty = lower_type_expr(ret, symbols, resolutions);
            Ty::Fn {
                params: param_tys,
                ret: Box::new(ret_ty),
            }
        }

        TypeExpr::Ref { inner, .. } => {
            let inner_ty = lower_type_expr(inner, symbols, resolutions);
            Ty::Ref(Box::new(inner_ty))
        }

        TypeExpr::Slice { inner, .. } => {
            let inner_ty = lower_type_expr(inner, symbols, resolutions);
            Ty::Slice(Box::new(inner_ty))
        }

        TypeExpr::Array { inner, size, .. } => {
            let elem_ty = lower_type_expr(inner, symbols, resolutions);
            Ty::Array { elem: Box::new(elem_ty), len: *size }
        }

        TypeExpr::Dyn { .. } => {
            // Dynamic dispatch — defer
            Ty::Error
        }

        TypeExpr::Active { .. } => {
            // Active types — defer
            Ty::Error
        }

        TypeExpr::DimApply { .. } => {
            // Dimension types — defer
            Ty::Error
        }
    }
}
