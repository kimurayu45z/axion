use std::collections::HashMap;

use axion_resolve::def_id::{DefId, SymbolKind};
use axion_resolve::symbol::Symbol;
use axion_resolve::ResolveOutput;
use axion_syntax::*;

use crate::lower::lower_type_expr;
use crate::ty::Ty;
use crate::unify::UnifyContext;

/// Type information for a single definition.
#[derive(Debug, Clone)]
pub struct TypeInfo {
    pub ty: Ty,
}

/// The type environment built from the AST and resolution output.
pub struct TypeEnv {
    /// DefId → TypeInfo for all definitions.
    pub defs: HashMap<DefId, TypeInfo>,
    /// Struct DefId → list of (field_name, Ty).
    pub struct_fields: HashMap<DefId, Vec<(String, Ty)>>,
    /// Enum DefId → list of (variant_name, variant_DefId, fields: Vec<(field_name, Ty)>).
    pub enum_variants: HashMap<DefId, Vec<(String, DefId, Vec<(String, Ty)>)>>,
    /// Interface DefId → list of (method_name, Fn type).
    pub interface_methods: HashMap<DefId, Vec<(String, Ty)>>,
    /// TypeParam DefId → list of interface DefId bounds.
    pub type_param_bounds: HashMap<DefId, Vec<DefId>>,
    /// (TypeParam DefId, Interface DefId) → list of bound type args (e.g. Iterator[i64] → [i64]).
    pub interface_bound_type_args: HashMap<(DefId, DefId), Vec<Ty>>,
    /// Function/Method DefId → list of ParamModifiers for each param.
    pub param_modifiers: HashMap<DefId, Vec<ParamModifier>>,
    /// Method DefId → ReceiverModifier.
    pub receiver_modifiers: HashMap<DefId, ReceiverModifier>,
    /// Function/Method DefId → list of effect names.
    pub fn_effects: HashMap<DefId, Vec<String>>,
    /// Interface DefId → list of concrete types that implement it.
    pub interface_impls: HashMap<DefId, Vec<Ty>>,
}

impl TypeEnv {
    /// Inject external definitions (e.g. from imported modules) into this environment.
    pub fn inject_external(
        &mut self,
        defs: &std::collections::HashMap<DefId, TypeInfo>,
        struct_fields: &std::collections::HashMap<DefId, Vec<(String, crate::ty::Ty)>>,
        enum_variants: &std::collections::HashMap<DefId, Vec<(String, DefId, Vec<(String, crate::ty::Ty)>)>>,
    ) {
        for (id, info) in defs {
            if !self.defs.contains_key(id) {
                self.defs.insert(*id, info.clone());
            }
        }
        for (id, fields) in struct_fields {
            if !self.struct_fields.contains_key(id) {
                self.struct_fields.insert(*id, fields.clone());
            }
        }
        for (id, variants) in enum_variants {
            if !self.enum_variants.contains_key(id) {
                self.enum_variants.insert(*id, variants.clone());
            }
        }
    }

    /// Register built-in interface implementations for marker interfaces.
    /// Maps primitive types to their marker interfaces (SInt, UInt, Int, SNumber, Float, Number).
    pub fn register_builtin_impls(&mut self, symbols: &[Symbol]) {
        use crate::ty::PrimTy;

        let signed = [PrimTy::I8, PrimTy::I16, PrimTy::I32, PrimTy::I64, PrimTy::I128, PrimTy::Isize];
        let unsigned = [PrimTy::U8, PrimTy::U16, PrimTy::U32, PrimTy::U64, PrimTy::U128, PrimTy::Usize];
        let floats = [PrimTy::F16, PrimTy::F32, PrimTy::F64, PrimTy::Bf16];

        for (iface_name, prims) in [
            ("SInt", signed.as_slice()),
            ("UInt", unsigned.as_slice()),
            ("Float", floats.as_slice()),
        ] {
            if let Some(iface_sym) = symbols.iter().find(|s| s.name == iface_name && s.kind == SymbolKind::Interface) {
                let tys: Vec<Ty> = prims.iter().map(|p| Ty::Prim(*p)).collect();
                self.interface_impls.insert(iface_sym.def_id, tys);
            }
        }

        // Int = SInt ∪ UInt
        if let Some(int_sym) = symbols.iter().find(|s| s.name == "Int" && s.kind == SymbolKind::Interface) {
            let all_int: Vec<Ty> = signed.iter().chain(unsigned.iter())
                .map(|p| Ty::Prim(*p)).collect();
            self.interface_impls.insert(int_sym.def_id, all_int);
        }

        // SNumber = SInt ∪ Float
        if let Some(snumber_sym) = symbols.iter().find(|s| s.name == "SNumber" && s.kind == SymbolKind::Interface) {
            let all_signed_numeric: Vec<Ty> = signed.iter().chain(floats.iter())
                .map(|p| Ty::Prim(*p)).collect();
            self.interface_impls.insert(snumber_sym.def_id, all_signed_numeric);
        }

        // Number = Int ∪ Float = SInt ∪ UInt ∪ Float
        if let Some(number_sym) = symbols.iter().find(|s| s.name == "Number" && s.kind == SymbolKind::Interface) {
            let all_numeric: Vec<Ty> = signed.iter().chain(unsigned.iter()).chain(floats.iter())
                .map(|p| Ty::Prim(*p)).collect();
            self.interface_impls.insert(number_sym.def_id, all_numeric);
        }

        // Ord = all numerics + str + String + bool
        if let Some(ord_sym) = symbols.iter().find(|s| s.name == "Ord" && s.kind == SymbolKind::Interface) {
            let mut ord_tys: Vec<Ty> = signed.iter()
                .chain(unsigned.iter())
                .chain(floats.iter())
                .map(|p| Ty::Prim(*p))
                .collect();
            ord_tys.push(Ty::Prim(PrimTy::Str));
            ord_tys.push(Ty::Prim(PrimTy::Bool));
            if let Some(string_sym) = symbols.iter().find(|s| s.name == "String" && s.kind == SymbolKind::Struct) {
                ord_tys.push(Ty::Struct { def_id: string_sym.def_id, type_args: vec![] });
            }
            self.interface_impls.insert(ord_sym.def_id, ord_tys);
        }
    }

    /// Build the type environment from AST + resolve output.
    pub fn build(
        source_file: &SourceFile,
        resolved: &ResolveOutput,
        unify: &mut UnifyContext,
    ) -> Self {
        let mut env = TypeEnv {
            defs: HashMap::new(),
            struct_fields: HashMap::new(),
            enum_variants: HashMap::new(),
            interface_methods: HashMap::new(),
            type_param_bounds: HashMap::new(),
            interface_bound_type_args: HashMap::new(),
            param_modifiers: HashMap::new(),
            receiver_modifiers: HashMap::new(),
            fn_effects: HashMap::new(),
            interface_impls: HashMap::new(),
        };

        let symbols = &resolved.symbols;
        let resolutions = &resolved.resolutions;

        // Register built-in functions (print, println) with a generic Fn signature.
        for sym in symbols {
            if sym.kind == SymbolKind::Function && sym.span == Span::dummy() {
                // Built-in functions: accept any args, return Unit.
                let ty = Ty::Fn {
                    params: vec![Ty::Error], // variadic — accept anything
                    ret: Box::new(Ty::Unit),
                };
                env.defs.insert(sym.def_id, TypeInfo { ty });
            }
        }

        for item in &source_file.items {
            env.register_item(item, symbols, resolutions, unify);
        }

        env
    }

    fn register_item(
        &mut self,
        item: &Item,
        symbols: &[axion_resolve::symbol::Symbol],
        resolutions: &HashMap<u32, DefId>,
        unify: &mut UnifyContext,
    ) {
        match &item.kind {
            ItemKind::Function(f) => {
                self.register_fn_def(f, item, symbols, resolutions, unify);
            }
            ItemKind::Method(m) => {
                self.register_method_def(m, item, symbols, resolutions, unify);
            }
            ItemKind::Constructor(c) => {
                self.register_constructor_def(c, item, symbols, resolutions, unify);
            }
            ItemKind::Struct(s) => {
                self.register_struct_def(s, item, symbols, resolutions);
            }
            ItemKind::Enum(e) => {
                self.register_enum_def(e, item, symbols, resolutions);
            }
            ItemKind::TypeAlias(ta) => {
                self.register_type_alias(ta, item, symbols, resolutions);
            }
            ItemKind::Extern(ext) => {
                self.register_extern_block(ext, symbols, resolutions, unify);
            }
            ItemKind::Interface(iface) => {
                self.register_interface_def(iface, item, symbols, resolutions);
            }
            ItemKind::Import(_) | ItemKind::Export(_) | ItemKind::Test(_) => {
                // Import/export decls and tests don't need type env entries.
            }
            ItemKind::ImplFor(_) => {
                // Checked in type_check phase, not env building.
            }
        }
    }

    fn register_fn_def(
        &mut self,
        f: &FnDef,
        item: &Item,
        symbols: &[axion_resolve::symbol::Symbol],
        resolutions: &HashMap<u32, DefId>,
        unify: &mut UnifyContext,
    ) {
        // Find the DefId for this function.
        let def_id = self.find_def_id_for_item(item, symbols);
        let Some(def_id) = def_id else { return };

        // Register type params.
        self.register_type_params(&f.type_params, symbols, resolutions);

        // Build parameter types.
        let param_tys: Vec<Ty> = f
            .params
            .iter()
            .map(|p| lower_type_expr(&p.ty, symbols, resolutions))
            .collect();

        // Build return type.
        let ret_ty = match &f.return_type {
            Some(te) => lower_type_expr(te, symbols, resolutions),
            None => Ty::Unit,
        };

        let fn_ty = Ty::Fn {
            params: param_tys,
            ret: Box::new(ret_ty),
        };
        self.defs.insert(def_id, TypeInfo { ty: fn_ty });

        // Register parameter modifiers.
        let modifiers: Vec<ParamModifier> = f.params.iter().map(|p| p.modifier.clone()).collect();
        self.param_modifiers.insert(def_id, modifiers);

        // Register effects.
        if !f.effects.is_empty() {
            let effects: Vec<String> = f.effects.iter().map(|e| e.name.clone()).collect();
            self.fn_effects.insert(def_id, effects);
        }

        // Register parameters as local defs.
        self.register_params(&f.params, symbols, resolutions, unify);
    }

    fn register_method_def(
        &mut self,
        m: &MethodDef,
        item: &Item,
        symbols: &[axion_resolve::symbol::Symbol],
        resolutions: &HashMap<u32, DefId>,
        unify: &mut UnifyContext,
    ) {
        let def_id = self.find_def_id_for_item(item, symbols);
        let Some(def_id) = def_id else { return };

        // Register type params.
        self.register_type_params(&m.type_params, symbols, resolutions);

        // Receiver type.
        let receiver_ty = lower_type_expr(&m.receiver_type, symbols, resolutions);

        // Build parameter types (receiver is implicit `self`).
        let mut param_tys: Vec<Ty> = vec![receiver_ty];
        for p in &m.params {
            param_tys.push(lower_type_expr(&p.ty, symbols, resolutions));
        }

        // Return type.
        let ret_ty = match &m.return_type {
            Some(te) => lower_type_expr(te, symbols, resolutions),
            None => Ty::Unit,
        };

        let fn_ty = Ty::Fn {
            params: param_tys,
            ret: Box::new(ret_ty),
        };
        self.defs.insert(def_id, TypeInfo { ty: fn_ty });

        // Register parameter modifiers.
        let modifiers: Vec<ParamModifier> = m.params.iter().map(|p| p.modifier.clone()).collect();
        self.param_modifiers.insert(def_id, modifiers);

        // Register receiver modifier.
        self.receiver_modifiers.insert(def_id, m.receiver_modifier.clone());

        // Register effects.
        if !m.effects.is_empty() {
            let effects: Vec<String> = m.effects.iter().map(|e| e.name.clone()).collect();
            self.fn_effects.insert(def_id, effects);
        }

        // Register parameters.
        self.register_params(&m.params, symbols, resolutions, unify);
    }

    fn register_constructor_def(
        &mut self,
        c: &ConstructorDef,
        item: &Item,
        symbols: &[axion_resolve::symbol::Symbol],
        resolutions: &HashMap<u32, DefId>,
        unify: &mut UnifyContext,
    ) {
        let def_id = self.find_def_id_for_item(item, symbols);
        let Some(def_id) = def_id else { return };

        // Register type params.
        self.register_type_params(&c.type_params, symbols, resolutions);

        // Build parameter types.
        let param_tys: Vec<Ty> = c
            .params
            .iter()
            .map(|p| lower_type_expr(&p.ty, symbols, resolutions))
            .collect();

        // Return type: if explicit, use it. Otherwise, look up the struct type.
        let ret_ty = if let Some(te) = &c.return_type {
            lower_type_expr(te, symbols, resolutions)
        } else {
            // Find the struct def_id for the type_name.
            let struct_def = symbols
                .iter()
                .find(|s| s.name == c.type_name && s.kind == SymbolKind::Struct);
            if let Some(s) = struct_def {
                Ty::Struct {
                    def_id: s.def_id,
                    type_args: vec![],
                }
            } else {
                Ty::Error
            }
        };

        let fn_ty = Ty::Fn {
            params: param_tys,
            ret: Box::new(ret_ty),
        };
        self.defs.insert(def_id, TypeInfo { ty: fn_ty });

        // Register parameter modifiers.
        let modifiers: Vec<ParamModifier> = c.params.iter().map(|p| p.modifier.clone()).collect();
        self.param_modifiers.insert(def_id, modifiers);

        // Register parameters.
        self.register_params(&c.params, symbols, resolutions, unify);
    }

    fn register_struct_def(
        &mut self,
        s: &StructDef,
        item: &Item,
        symbols: &[axion_resolve::symbol::Symbol],
        resolutions: &HashMap<u32, DefId>,
    ) {
        let def_id = self.find_def_id_for_item(item, symbols);
        let Some(def_id) = def_id else { return };

        // Register type params.
        self.register_type_params(&s.type_params, symbols, resolutions);

        // Register struct fields.
        let fields: Vec<(String, Ty)> = s
            .fields
            .iter()
            .map(|f| {
                let ty = lower_type_expr(&f.ty, symbols, resolutions);
                (f.name.clone(), ty)
            })
            .collect();
        self.struct_fields.insert(def_id, fields);

        // Register the struct type itself.
        let ty = Ty::Struct {
            def_id,
            type_args: vec![],
        };
        self.defs.insert(def_id, TypeInfo { ty });
    }

    fn register_enum_def(
        &mut self,
        e: &EnumDef,
        item: &Item,
        symbols: &[axion_resolve::symbol::Symbol],
        resolutions: &HashMap<u32, DefId>,
    ) {
        let def_id = self.find_def_id_for_item(item, symbols);
        let Some(def_id) = def_id else { return };

        // Register type params.
        self.register_type_params(&e.type_params, symbols, resolutions);

        // Register variants.
        let mut variants = Vec::new();
        for variant in &e.variants {
            // Find the variant's DefId.
            let variant_def = symbols.iter().find(|s| {
                s.name == variant.name
                    && s.kind == SymbolKind::EnumVariant
                    && s.parent == Some(def_id)
            });
            let variant_def_id = variant_def.map(|s| s.def_id).unwrap_or(DefId(u32::MAX));

            let fields: Vec<(String, Ty)> = variant
                .fields
                .iter()
                .map(|f| {
                    let ty = lower_type_expr(&f.ty, symbols, resolutions);
                    (f.name.clone(), ty)
                })
                .collect();
            variants.push((variant.name.clone(), variant_def_id, fields));
        }
        self.enum_variants.insert(def_id, variants);

        // Register the enum type itself.
        let ty = Ty::Enum {
            def_id,
            type_args: vec![],
        };
        self.defs.insert(def_id, TypeInfo { ty });
    }

    fn register_type_alias(
        &mut self,
        ta: &TypeAlias,
        item: &Item,
        symbols: &[axion_resolve::symbol::Symbol],
        resolutions: &HashMap<u32, DefId>,
    ) {
        let def_id = self.find_def_id_for_item(item, symbols);
        let Some(def_id) = def_id else { return };

        let ty = lower_type_expr(&ta.ty, symbols, resolutions);
        self.defs.insert(def_id, TypeInfo { ty });
    }

    fn register_extern_block(
        &mut self,
        ext: &ExternBlock,
        symbols: &[axion_resolve::symbol::Symbol],
        resolutions: &HashMap<u32, DefId>,
        unify: &mut UnifyContext,
    ) {
        for decl in &ext.decls {
            // Find the DefId for this extern fn.
            let def_id = symbols
                .iter()
                .find(|s| s.name == decl.name && s.kind == SymbolKind::ExternFn)
                .map(|s| s.def_id);
            let Some(def_id) = def_id else { continue };

            let param_tys: Vec<Ty> = decl
                .params
                .iter()
                .map(|p| lower_type_expr(&p.ty, symbols, resolutions))
                .collect();

            let ret_ty = match &decl.return_type {
                Some(te) => lower_type_expr(te, symbols, resolutions),
                None => Ty::Unit,
            };

            let fn_ty = Ty::Fn {
                params: param_tys,
                ret: Box::new(ret_ty),
            };
            self.defs.insert(def_id, TypeInfo { ty: fn_ty });

            // Register effects for extern fn.
            if !decl.effects.is_empty() {
                let effects: Vec<String> =
                    decl.effects.iter().map(|e| e.name.clone()).collect();
                self.fn_effects.insert(def_id, effects);
            }

            // Register parameters.
            self.register_params(&decl.params, symbols, resolutions, unify);
        }
    }

    fn register_type_params(
        &mut self,
        type_params: &[TypeParam],
        symbols: &[axion_resolve::symbol::Symbol],
        resolutions: &HashMap<u32, DefId>,
    ) {
        for tp in type_params {
            match tp {
                TypeParam::Type { span, bounds, .. } => {
                    // The resolver doesn't record a resolution for type params;
                    // find the symbol by span match instead.
                    let tp_sym = symbols.iter().find(|s| {
                        s.kind == SymbolKind::TypeParam && s.name != "Self" && s.span == *span
                    });
                    if let Some(tp_sym) = tp_sym {
                        let def_id = tp_sym.def_id;
                        self.defs.insert(def_id, TypeInfo { ty: Ty::Param(def_id) });
                        // Register bounds for this type parameter.
                        if !bounds.is_empty() {
                            let mut bound_def_ids = Vec::new();
                            for bound in bounds {
                                let iface_def_id = if let Some(&id) = resolutions.get(&bound.span.start) {
                                    Some(id)
                                } else {
                                    // Fall back to finding the interface by name.
                                    symbols.iter().find(|s| {
                                        s.name == bound.name && s.kind == SymbolKind::Interface
                                    }).map(|s| s.def_id)
                                };
                                if let Some(iface_def_id) = iface_def_id {
                                    bound_def_ids.push(iface_def_id);
                                    // Store bound type args (e.g. Iterator[i64] → [i64]).
                                    if !bound.args.is_empty() {
                                        let bound_args: Vec<Ty> = bound.args.iter()
                                            .map(|a| lower_type_expr(a, symbols, resolutions))
                                            .collect();
                                        self.interface_bound_type_args.insert((def_id, iface_def_id), bound_args);
                                    }
                                }
                            }
                            if !bound_def_ids.is_empty() {
                                self.type_param_bounds.insert(def_id, bound_def_ids);
                            }
                        }
                    } else if let Some(&def_id) = resolutions.get(&span.start) {
                        // Fallback: try resolution map
                        self.defs.insert(def_id, TypeInfo { ty: Ty::Param(def_id) });
                    }
                }
                TypeParam::Const { span, ty, .. } => {
                    if let Some(&def_id) = resolutions.get(&span.start) {
                        let ty = lower_type_expr(ty, symbols, resolutions);
                        self.defs.insert(def_id, TypeInfo { ty });
                    }
                }
                TypeParam::Dim { span, .. } => {
                    if let Some(&def_id) = resolutions.get(&span.start) {
                        self.defs.insert(def_id, TypeInfo { ty: Ty::Error });
                    }
                }
            }
        }
    }

    fn register_interface_def(
        &mut self,
        iface: &InterfaceDef,
        item: &Item,
        symbols: &[axion_resolve::symbol::Symbol],
        resolutions: &HashMap<u32, DefId>,
    ) {
        // Find the interface symbol by name and kind, since the item span may not match
        // the symbol span exactly for interface definitions.
        let def_id = self.find_def_id_for_item(item, symbols).or_else(|| {
            symbols.iter().find(|s| {
                s.name == iface.name && s.kind == SymbolKind::Interface
            }).map(|s| s.def_id)
        });
        let Some(def_id) = def_id else { return };

        // Register type params.
        self.register_type_params(&iface.type_params, symbols, resolutions);

        // Find the interface's implicit Self type parameter.
        let iface_sym = symbols.iter().find(|s| s.def_id == def_id);
        let self_ty = iface_sym.and_then(|is| {
            symbols.iter().find(|s| {
                s.kind == SymbolKind::TypeParam
                    && s.name == "Self"
                    && s.span.start >= is.span.start
                    && s.span.end <= is.span.end
            })
        }).map(|s| Ty::Param(s.def_id));

        // Lower each InterfaceMethod to a (name, Fn type) entry.
        let mut methods = Vec::new();
        for method in &iface.methods {
            let explicit_params: Vec<Ty> = method
                .params
                .iter()
                .map(|p| lower_type_expr(&p.ty, symbols, resolutions))
                .collect();
            // If the method has a receiver (self), prepend Self as the first parameter.
            let param_tys = if method.receiver_modifier.is_some() {
                let mut all = Vec::new();
                if let Some(ref st) = self_ty {
                    all.push(st.clone());
                }
                all.extend(explicit_params);
                all
            } else {
                explicit_params
            };
            let ret_ty = match &method.return_type {
                Some(te) => lower_type_expr(te, symbols, resolutions),
                None => Ty::Unit,
            };
            let fn_ty = Ty::Fn {
                params: param_tys,
                ret: Box::new(ret_ty),
            };
            methods.push((method.name.clone(), fn_ty));
        }
        self.interface_methods.insert(def_id, methods);
    }

    fn register_params(
        &mut self,
        params: &[Param],
        symbols: &[axion_resolve::symbol::Symbol],
        resolutions: &HashMap<u32, DefId>,
        _unify: &mut UnifyContext,
    ) {
        for param in params {
            // Find the DefId for this parameter via its span.
            if let Some(&def_id) = resolutions.get(&param.span.start) {
                let ty = lower_type_expr(&param.ty, symbols, resolutions);
                self.defs.insert(def_id, TypeInfo { ty });
            } else {
                // Try finding the param symbol by name among Param-kind symbols.
                let param_sym = symbols.iter().find(|s| {
                    s.name == param.name && s.kind == SymbolKind::Param && s.span == param.span
                });
                if let Some(sym) = param_sym {
                    let ty = lower_type_expr(&param.ty, symbols, resolutions);
                    self.defs.insert(sym.def_id, TypeInfo { ty });
                }
            }
        }
    }

    /// Find the DefId for a top-level item by matching its span against symbols.
    fn find_def_id_for_item(
        &self,
        item: &Item,
        symbols: &[axion_resolve::symbol::Symbol],
    ) -> Option<DefId> {
        symbols
            .iter()
            .find(|s| s.span == item.span)
            .map(|s| s.def_id)
    }
}
