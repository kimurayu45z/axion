use axion_syntax::{Span, Visibility};

use crate::def_id::SymbolKind;
use crate::scope::ScopeId;
use crate::ResolveContext;

/// Primitive type names built into the language.
const PRIMITIVE_TYPES: &[&str] = &[
    "i8", "i16", "i32", "i64", "i128",
    "u8", "u16", "u32", "u64", "u128", "usize", "isize",
    "f16", "f32", "f64", "bf16",
    "bool", "char", "str", "never",
];

/// Register all built-in primitive types into the module (root) scope.
pub(crate) fn register_builtins(ctx: &mut ResolveContext, root: ScopeId) {
    for &name in PRIMITIVE_TYPES {
        let def_id = ctx.alloc_symbol(
            name.to_string(),
            SymbolKind::TypeAlias,
            Visibility::Pub,
            Span::dummy(),
            None,
        );
        ctx.scope_tree.insert_type(root, name.to_string(), def_id);
    }

    // `Self` is not registered globally — it is injected per method/constructor scope.
    // `Fn` is a keyword-level type expression handled by the parser, not a named type.

    // Register common prelude values: `print`, `println` as built-in functions.
    for &name in &["print", "println"] {
        let def_id = ctx.alloc_symbol(
            name.to_string(),
            SymbolKind::Function,
            Visibility::Pub,
            Span::dummy(),
            None,
        );
        ctx.scope_tree.insert_value(root, name.to_string(), def_id);
    }
}

/// Return the list of built-in primitive type names (for testing).
pub fn primitive_type_names() -> &'static [&'static str] {
    PRIMITIVE_TYPES
}
