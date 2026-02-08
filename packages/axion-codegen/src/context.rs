use std::collections::HashMap;

use axion_resolve::def_id::DefId;
use axion_resolve::ResolveOutput;
use axion_types::env::TypeEnv;
use axion_types::TypeCheckOutput;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::types::BasicTypeEnum;
use inkwell::values::{FunctionValue, PointerValue};

/// Codegen context holding LLVM state and mappings.
pub struct CodegenCtx<'ctx> {
    pub context: &'ctx Context,
    pub module: Module<'ctx>,
    pub builder: Builder<'ctx>,
    pub resolved: &'ctx ResolveOutput,
    pub type_check: &'ctx TypeCheckOutput,
    pub type_env: &'ctx TypeEnv,
    /// DefId → LLVM FunctionValue
    pub functions: HashMap<DefId, FunctionValue<'ctx>>,
    /// DefId → LLVM PointerValue (local variables / params)
    pub locals: HashMap<DefId, PointerValue<'ctx>>,
    /// DefId → LLVM type of the stored value (to avoid span-based type lookup issues)
    pub local_types: HashMap<DefId, BasicTypeEnum<'ctx>>,
    /// String literal cache: content → global pointer
    pub string_literals: HashMap<String, PointerValue<'ctx>>,
    /// Loop context for break/continue
    pub loop_exit_block: Option<inkwell::basic_block::BasicBlock<'ctx>>,
    pub loop_header_block: Option<inkwell::basic_block::BasicBlock<'ctx>>,
}

impl<'ctx> CodegenCtx<'ctx> {
    pub fn new(
        context: &'ctx Context,
        module_name: &str,
        resolved: &'ctx ResolveOutput,
        type_check: &'ctx TypeCheckOutput,
        type_env: &'ctx TypeEnv,
    ) -> Self {
        let module = context.create_module(module_name);
        let builder = context.create_builder();

        Self {
            context,
            module,
            builder,
            resolved,
            type_check,
            type_env,
            functions: HashMap::new(),
            locals: HashMap::new(),
            local_types: HashMap::new(),
            string_literals: HashMap::new(),
            loop_exit_block: None,
            loop_header_block: None,
        }
    }
}
