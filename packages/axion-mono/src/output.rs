use std::collections::HashMap;

use axion_resolve::def_id::DefId;
use axion_syntax::*;
use axion_syntax::ReceiverModifier;
use axion_types::ty::Ty;

/// A unique specialization key: (original fn DefId, concrete type args).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SpecKey {
    pub fn_def_id: DefId,
    pub type_args: Vec<Ty>,
}

/// A specialized function ready for codegen.
#[derive(Debug, Clone)]
pub struct SpecializedFn {
    /// The original function DefId.
    pub original_def_id: DefId,
    /// The concrete type arguments.
    pub type_args: Vec<Ty>,
    /// The mangled name for the specialization (e.g., `id__i64`).
    pub mangled_name: String,
    /// The specialized function type (all type params replaced).
    pub fn_ty: Ty,
    /// The original function's AST body (cloned from the source).
    pub body: Vec<Stmt>,
    /// The original function's params (cloned).
    pub params: Vec<Param>,
    /// The original function's return type (cloned).
    pub return_type: Option<TypeExpr>,
    /// Substitution map: TypeParam DefId → concrete Ty.
    pub subst: HashMap<DefId, Ty>,
    /// Whether this is a method (has self receiver).
    pub is_method: bool,
    /// Receiver modifier for methods.
    pub receiver_modifier: Option<ReceiverModifier>,
}

/// Output of the monomorphization pass.
#[derive(Debug, Clone)]
pub struct MonoOutput {
    /// Mapping from (original DefId, type args) → mangled name.
    pub specializations: HashMap<SpecKey, String>,
    /// List of specialized function definitions.
    pub specialized_fns: Vec<SpecializedFn>,
}

impl MonoOutput {
    pub fn new() -> Self {
        Self {
            specializations: HashMap::new(),
            specialized_fns: Vec::new(),
        }
    }

    /// Look up the mangled name for a generic call site.
    pub fn lookup(&self, fn_def_id: DefId, type_args: &[Ty]) -> Option<&str> {
        let key = SpecKey {
            fn_def_id,
            type_args: type_args.to_vec(),
        };
        self.specializations.get(&key).map(|s| s.as_str())
    }
}
