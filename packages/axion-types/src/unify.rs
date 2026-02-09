use crate::ty::{InferVar, Ty};

/// The unification context manages inference variables and their substitutions.
pub struct UnifyContext {
    /// Substitution table: InferVar index → resolved Ty (or None if still unknown).
    substitutions: Vec<Option<Ty>>,
}

impl UnifyContext {
    pub fn new() -> Self {
        Self {
            substitutions: Vec::new(),
        }
    }

    /// Allocate a fresh inference variable.
    pub fn fresh_var(&mut self) -> InferVar {
        let id = self.substitutions.len() as u32;
        self.substitutions.push(None);
        InferVar(id)
    }

    /// Unify two types, updating substitutions as needed.
    /// Returns Ok(()) on success, Err((a, b)) on failure with the conflicting types.
    pub fn unify(&mut self, a: &Ty, b: &Ty) -> Result<(), (Ty, Ty)> {
        let a = self.shallow_resolve(a);
        let b = self.shallow_resolve(b);

        match (&a, &b) {
            // Error is poison — always unifies
            (Ty::Error, _) | (_, Ty::Error) => Ok(()),

            // Same inference variable
            (Ty::Infer(v1), Ty::Infer(v2)) if v1 == v2 => Ok(()),

            // Inference variable on the left
            (Ty::Infer(v), _) => {
                if self.occurs_in(v, &b) {
                    Err((a, b))
                } else {
                    self.substitutions[v.0 as usize] = Some(b);
                    Ok(())
                }
            }

            // Inference variable on the right
            (_, Ty::Infer(v)) => {
                if self.occurs_in(v, &a) {
                    Err((a, b))
                } else {
                    self.substitutions[v.0 as usize] = Some(a);
                    Ok(())
                }
            }

            // Primitives
            (Ty::Prim(p1), Ty::Prim(p2)) => {
                if p1 == p2 {
                    Ok(())
                } else {
                    Err((a, b))
                }
            }

            // Unit
            (Ty::Unit, Ty::Unit) => Ok(()),

            // Struct
            (
                Ty::Struct {
                    def_id: d1,
                    type_args: args1,
                },
                Ty::Struct {
                    def_id: d2,
                    type_args: args2,
                },
            ) => {
                if d1 != d2 {
                    Err((a, b))
                } else if args1.len() == args2.len() {
                    for (a1, b1) in args1.iter().zip(args2.iter()) {
                        self.unify(a1, b1)?;
                    }
                    Ok(())
                } else if args1.is_empty() || args2.is_empty() {
                    // One side has no type_args (e.g. from older code paths) — allow
                    Ok(())
                } else {
                    Err((a, b))
                }
            }

            // Enum
            (
                Ty::Enum {
                    def_id: d1,
                    type_args: args1,
                },
                Ty::Enum {
                    def_id: d2,
                    type_args: args2,
                },
            ) => {
                if d1 != d2 || args1.len() != args2.len() {
                    Err((a, b))
                } else {
                    for (a1, b1) in args1.iter().zip(args2.iter()) {
                        self.unify(a1, b1)?;
                    }
                    Ok(())
                }
            }

            // Tuple
            (Ty::Tuple(elems1), Ty::Tuple(elems2)) => {
                if elems1.len() != elems2.len() {
                    Err((a, b))
                } else {
                    for (e1, e2) in elems1.iter().zip(elems2.iter()) {
                        self.unify(e1, e2)?;
                    }
                    Ok(())
                }
            }

            // Function
            (
                Ty::Fn {
                    params: p1,
                    ret: r1,
                },
                Ty::Fn {
                    params: p2,
                    ret: r2,
                },
            ) => {
                if p1.len() != p2.len() {
                    Err((a, b))
                } else {
                    for (pa, pb) in p1.iter().zip(p2.iter()) {
                        self.unify(pa, pb)?;
                    }
                    self.unify(r1, r2)
                }
            }

            // Reference
            (Ty::Ref(inner1), Ty::Ref(inner2)) => self.unify(inner1, inner2),

            // Slice
            (Ty::Slice(inner1), Ty::Slice(inner2)) => self.unify(inner1, inner2),

            // Type parameter: same DefId
            (Ty::Param(d1), Ty::Param(d2)) => {
                if d1 == d2 {
                    Ok(())
                } else {
                    Err((a, b))
                }
            }

            // Everything else fails
            _ => Err((a, b)),
        }
    }

    /// Resolve a type, substituting all known inference variables recursively.
    pub fn resolve(&self, ty: &Ty) -> Ty {
        match ty {
            Ty::Infer(v) => {
                if let Some(resolved) = &self.substitutions[v.0 as usize] {
                    self.resolve(resolved)
                } else {
                    ty.clone()
                }
            }
            Ty::Struct { def_id, type_args } => Ty::Struct {
                def_id: *def_id,
                type_args: type_args.iter().map(|t| self.resolve(t)).collect(),
            },
            Ty::Enum { def_id, type_args } => Ty::Enum {
                def_id: *def_id,
                type_args: type_args.iter().map(|t| self.resolve(t)).collect(),
            },
            Ty::Tuple(elems) => Ty::Tuple(elems.iter().map(|t| self.resolve(t)).collect()),
            Ty::Fn { params, ret } => Ty::Fn {
                params: params.iter().map(|t| self.resolve(t)).collect(),
                ret: Box::new(self.resolve(ret)),
            },
            Ty::Ref(inner) => Ty::Ref(Box::new(self.resolve(inner))),
            Ty::Slice(inner) => Ty::Slice(Box::new(self.resolve(inner))),
            _ => ty.clone(),
        }
    }

    /// Shallow resolve: follow inference variable chain but don't recurse into structure.
    fn shallow_resolve(&self, ty: &Ty) -> Ty {
        match ty {
            Ty::Infer(v) => {
                if let Some(resolved) = &self.substitutions[v.0 as usize] {
                    self.shallow_resolve(resolved)
                } else {
                    ty.clone()
                }
            }
            _ => ty.clone(),
        }
    }

    /// Occurs check: does the inference variable appear anywhere in the type?
    fn occurs_in(&self, v: &InferVar, ty: &Ty) -> bool {
        match ty {
            Ty::Infer(v2) => {
                if v == v2 {
                    return true;
                }
                if let Some(resolved) = &self.substitutions[v2.0 as usize] {
                    self.occurs_in(v, resolved)
                } else {
                    false
                }
            }
            Ty::Struct { type_args, .. } | Ty::Enum { type_args, .. } => {
                type_args.iter().any(|t| self.occurs_in(v, t))
            }
            Ty::Tuple(elems) => elems.iter().any(|t| self.occurs_in(v, t)),
            Ty::Fn { params, ret } => {
                params.iter().any(|t| self.occurs_in(v, t)) || self.occurs_in(v, ret)
            }
            Ty::Ref(inner) | Ty::Slice(inner) => self.occurs_in(v, inner),
            _ => false,
        }
    }
}
