use std::collections::HashMap;

use axion_mono::output::MonoOutput;
use axion_resolve::def_id::DefId;
use axion_resolve::ResolveOutput;
use axion_types::env::TypeEnv;
use axion_types::ty::Ty;
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
    /// Counter for generating unique closure names
    pub closure_counter: u32,
    /// Monomorphization output (specialized functions).
    pub mono_output: Option<&'ctx MonoOutput>,
    /// Mangled name → LLVM FunctionValue for specialized functions.
    pub mono_fn_values: HashMap<String, FunctionValue<'ctx>>,
    /// Current type substitution (active when compiling a specialized function body).
    pub current_subst: HashMap<DefId, Ty>,
    /// Heap-allocated pointers in the current function (for cleanup before return).
    pub heap_allocs: Vec<PointerValue<'ctx>>,
    /// Locals that need drop calls at cleanup: (alloca pointer, LLVM type, drop FunctionValue).
    pub drop_locals: Vec<(PointerValue<'ctx>, BasicTypeEnum<'ctx>, FunctionValue<'ctx>)>,
}

impl<'ctx> CodegenCtx<'ctx> {
    pub fn new(
        context: &'ctx Context,
        module_name: &str,
        resolved: &'ctx ResolveOutput,
        type_check: &'ctx TypeCheckOutput,
        type_env: &'ctx TypeEnv,
        mono_output: Option<&'ctx MonoOutput>,
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
            closure_counter: 0,
            mono_output,
            mono_fn_values: HashMap::new(),
            current_subst: HashMap::new(),
            heap_allocs: Vec::new(),
            drop_locals: Vec::new(),
        }
    }
}
