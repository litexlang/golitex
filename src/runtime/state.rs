//! Run-wide runtime state and execution-frame lifecycle.

use crate::prelude::*;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

pub struct Runtime {
    /// The module world for this top-level run. Imported modules execute in
    /// this Runtime and are selected by `execution_stack` frames.
    pub module_manager: Box<ModuleManager>,
    pub execution_stack: Vec<ExecutionFrame>,
    /// Monotone runtime-wide allocator. Local environments may disappear, but
    /// a fact ID is never reused during the run.
    pub next_fact_id: u64,
    pub symbol_id_allocator: Rc<SymbolIdAllocator>,
    pub template_instance_interner: RefCell<HashMap<String, SymbolBinding>>,
    /// Direct struct carriers learned only when a typed binding executes.
    /// This keeps exact transient binder identities usable after their local
    /// environment has ended, for example when a stored theorem is instantiated.
    pub(crate) executed_direct_struct_carriers: HashMap<SymbolId, StructObj>,
    pub run_options: RunOptions,
}

impl Runtime {
    pub fn new(run_options: RunOptions) -> Self {
        Runtime {
            module_manager: Box::new(ModuleManager::new()),
            execution_stack: vec![],
            next_fact_id: 1,
            symbol_id_allocator: Rc::new(SymbolIdAllocator::new()),
            template_instance_interner: RefCell::new(HashMap::new()),
            executed_direct_struct_carriers: HashMap::new(),
            run_options,
        }
    }
}

impl Default for Runtime {
    fn default() -> Self {
        Self::new(RunOptions::default())
    }
}

impl Runtime {
    pub fn allocate_fact_id(&mut self) -> Result<FactId, RuntimeError> {
        let value = self.next_fact_id;
        self.next_fact_id = value.checked_add(1).ok_or_else(|| {
            RuntimeError::from(UnknownRuntimeError(RuntimeErrorStruct::new_with_just_msg(
                "fact ID space exhausted".to_string(),
            )))
        })?;
        Ok(FactId::new(value))
    }

    pub fn set_output_detail(&mut self, output_detail: OutputDetail) {
        self.run_options = self.run_options.with_output_detail(output_detail);
    }

    pub fn effective_output_detail(&self) -> OutputDetail {
        self.run_options.output_detail()
    }

    #[deprecated(note = "use `set_output_detail`")]
    pub fn set_output_style(&mut self, output_detail: OutputDetail) {
        self.set_output_detail(output_detail);
    }

    #[deprecated(note = "use `effective_output_detail`")]
    pub fn effective_output_style(&self) -> OutputDetail {
        self.effective_output_detail()
    }

    pub fn is_compact_output(&self) -> bool {
        self.effective_output_detail() == OutputDetail::Compact
    }

    pub fn is_normal_output(&self) -> bool {
        self.effective_output_detail() == OutputDetail::Normal
    }

    pub fn is_detailed_output(&self) -> bool {
        self.effective_output_detail() == OutputDetail::Detailed
    }

    pub fn current_file_path_rc(&self) -> Rc<str> {
        self.execution_stack
            .last()
            .map(|frame| frame.module_file_info.source_path.clone())
            .unwrap_or_else(|| Rc::from(""))
    }

    pub fn ensure_execution_frame_for_parse(&mut self) {
        if !self.execution_stack.is_empty() {
            return;
        }
        let source_path = self
            .module_manager
            .module(ModuleId::ROOT)
            .map(|module| module.main_file_path.clone())
            .unwrap_or_default();
        let module_file_info = match self.module_manager.module(ModuleId::ROOT) {
            Some(_) => {
                let existing_file_id = self
                    .module_manager
                    .module(ModuleId::ROOT)
                    .and_then(|module| module.module_source_file);
                match existing_file_id {
                    Some(file_id) => self
                        .module_manager
                        .execution_module_file_info(ModuleId::ROOT, file_id)
                        .expect("root source file should exist"),
                    None => self
                        .module_manager
                        .create_execution_file(ModuleId::ROOT, source_path.as_str())
                        .expect("root execution file should be registered"),
                }
            }
            None => self
                .module_manager
                .create_root_module(source_path.as_str(), true),
        };
        self.execution_stack
            .push(ExecutionFrame::new(module_file_info));
    }

    pub fn current_parse_context(&self) -> &ParseContext {
        &self
            .execution_stack
            .last()
            .expect("an execution frame should exist while parsing")
            .parse_context
    }

    pub fn current_parse_context_mut(&mut self) -> &mut ParseContext {
        &mut self
            .execution_stack
            .last_mut()
            .expect("an execution frame should exist while parsing")
            .parse_context
    }

    pub fn current_module_id(&self) -> ModuleId {
        self.execution_stack
            .last()
            .map(|frame| frame.module_file_info.module_id)
            .expect("current execution frame should exist")
    }

    pub fn current_module(&self) -> &ModuleRunner {
        self.module_manager
            .module(self.current_module_id())
            .expect("current module should exist")
    }

    pub fn current_module_mut(&mut self) -> &mut ModuleRunner {
        let module_id = self.current_module_id();
        self.module_manager
            .module_mut(module_id)
            .expect("current module should exist")
    }

    pub fn push_file_execution_frame(&mut self, module_id: ModuleId, file_id: FileId) {
        self.push_file_execution_frame_with_mode(
            module_id,
            file_id,
            ExecutionMode::RequireVerification,
        );
    }

    pub fn push_file_execution_frame_with_mode(
        &mut self,
        module_id: ModuleId,
        file_id: FileId,
        execution_mode: ExecutionMode,
    ) {
        let module_file_info = self
            .module_manager
            .execution_module_file_info(module_id, file_id)
            .expect("execution frame must point to a registered module file");
        self.execution_stack.push(ExecutionFrame::new_with_mode(
            module_file_info,
            execution_mode,
        ));
    }

    pub fn canonical_module_name_for_parse(&self, name: &str) -> String {
        let Some(frame) = self.execution_stack.last() else {
            return name.to_string();
        };
        self.module_manager
            .canonical_name_for_reference(frame.module_file_info.module_id, name)
            .unwrap_or_else(|| name.to_string())
    }

    pub fn pop_execution_frame(&mut self) {
        self.execution_stack
            .pop()
            .expect("an execution frame should exist before it is popped");
    }

    pub fn strict_mode_applies_to_current_module(&self) -> bool {
        if !self.run_options.is_strict() {
            return false;
        }
        let Some(frame) = self.execution_stack.last() else {
            return false;
        };
        !self
            .module_manager
            .module(frame.module_file_info.module_id)
            .is_some_and(|module| module.is_standard_library)
    }

    pub fn has_active_execution_frame(&self) -> bool {
        !self.execution_stack.is_empty()
    }

    pub fn current_execution_mode(&self) -> ExecutionMode {
        self.execution_stack
            .last()
            .map(|frame| frame.execution_mode)
            .unwrap_or(ExecutionMode::RequireVerification)
    }

    pub fn current_execution_is_trusted_file(&self) -> bool {
        self.current_execution_mode() == ExecutionMode::Trusted
    }

    pub fn record_unverified_import(&mut self, kind: &str, name: String, line_file: LineFile) {
        if self
            .module_manager
            .unverified_imports
            .iter()
            .any(|entry| entry.kind == kind && entry.name == name && entry.line_file == line_file)
        {
            return;
        }
        self.module_manager
            .unverified_imports
            .push(UnverifiedImport {
                kind: kind.to_string(),
                name,
                line_file,
            });
    }

    pub fn unverified_imports(&self) -> &[UnverifiedImport] {
        &self.module_manager.unverified_imports
    }

    pub fn replace_current_execution_mode(
        &mut self,
        execution_mode: ExecutionMode,
    ) -> ExecutionMode {
        let frame = self
            .execution_stack
            .last_mut()
            .expect("an execution frame should exist while running a statement");
        let previous = frame.execution_mode;
        frame.execution_mode = execution_mode;
        previous
    }
}

impl Runtime {
    pub fn validate_name(
        &mut self,
        name: &str,
        _current_line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        if let Err(invalid_name_message) = is_valid_litex_name(name) {
            return Err(ParseRuntimeError(RuntimeErrorStruct::new_with_just_msg(
                invalid_name_message,
            ))
            .into());
        }

        Ok(())
    }

    pub fn validate_user_fn_param_names_for_parse(
        &mut self,
        names: &[String],
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        for name in names {
            if let Err(e) = is_valid_litex_name(name) {
                return Err(
                    ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
                        e,
                        line_file.clone(),
                    ))
                    .into(),
                );
            }
        }
        Ok(())
    }

    pub fn validate_names_and_insert_into_top_parsing_time_name_scope(
        &mut self,
        names: &Vec<String>,
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        for name in names {
            self.validate_name_and_insert_into_top_parsing_time_name_scope(
                name,
                line_file.clone(),
            )?;
        }
        Ok(())
    }

    /// Validates identifier syntax only; does not record bindings (see `run_in_local_parsing_time_name_scope`).
    pub fn validate_name_and_insert_into_top_parsing_time_name_scope(
        &mut self,
        name: &str,
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        self.validate_name(name, line_file)
    }
}

impl Runtime {
    /// Start a standalone source run with its own root module and execution frame.
    pub fn start_isolated_source(&mut self, source_path: &str) {
        self.start_isolated_source_with_kind(source_path, true);
    }

    /// Start a standalone physical file run with its own root module and frame.
    pub fn start_isolated_file(&mut self, source_path: &str) {
        self.start_isolated_source_with_kind(source_path, false);
    }

    fn start_isolated_source_with_kind(&mut self, source_path: &str, is_virtual_source: bool) {
        let module_file_info = self
            .module_manager
            .create_root_module(source_path, is_virtual_source);
        self.execution_stack
            .push(ExecutionFrame::new(module_file_info));
    }

    /// Start a repository run with its root module. File frames are pushed only
    /// while registered Litex files execute.
    pub fn start_repository_run(
        &mut self,
        repository_root: String,
        main_file_path: String,
    ) -> Result<ModuleId, String> {
        let module_id = self
            .module_manager
            .create_repository_root_module(repository_root, main_file_path.clone())?;
        Ok(module_id)
    }

    /// After `start_isolated_source`, point the current user source at another
    /// path without pushing more layers.
    pub fn set_current_user_lit_file_path(&mut self, path: &str) {
        let path_rc: Rc<str> = Rc::from(path);
        let (module_id, file_id) = self
            .execution_stack
            .last()
            .map(|frame| {
                (
                    frame.module_file_info.module_id,
                    frame.module_file_info.file_id,
                )
            })
            .expect("a user source frame should exist before changing its path");
        self.module_manager
            .module_mut(module_id)
            .and_then(|module| module.file_mut(file_id))
            .expect("current user source file should be registered")
            .source_path = path.to_string();
        self.execution_stack
            .last_mut()
            .expect("current user source frame should exist")
            .module_file_info
            .source_path = path_rc.clone();
        if module_id == ModuleId::ROOT {
            self.module_manager
                .module_mut(module_id)
                .expect("root module should exist")
                .main_file_path = path.to_string();
        }
    }

    /// Make the discovered repository's root module the persistent environment for
    /// interactive input. This method does not itself execute the ordered `[export]` plan.
    pub fn prepare_current_repository_for_repl(
        &mut self,
        source_path: &str,
    ) -> Result<(), RuntimeError> {
        let module_id = self
            .module_manager
            .module(ModuleId::ROOT)
            .map(|module| module.id)
            .expect("repository root module should exist");
        let module_file_info = self
            .module_manager
            .create_execution_file(module_id, source_path)
            .expect("repository REPL source should be registered");
        self.execution_stack
            .push(ExecutionFrame::new(module_file_info));
        Ok(())
    }
}

#[cfg(test)]
#[path = "../../tests/unit/runtime/state/test_support.rs"]
mod test_support;
