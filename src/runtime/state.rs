//! Run-wide Runtime state and execution-frame lifecycle.

use crate::prelude::*;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OutputStyle {
    Compact,
    Normal,
    Detailed,
}

impl OutputStyle {
    pub fn is_detailed(self) -> bool {
        self == OutputStyle::Detailed
    }
}

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
    /// Statement-local proof reuse and recursion guards. These scopes mirror
    /// temporary runtime environments, but are not part of the persistent
    /// mathematical environment and are never merged or snapshotted.
    pub statement_proof_state: StatementProofStateStack,
    pub output_style: OutputStyle,
    pub strict_mode: bool,
    pub output_language: OutputLanguage,
}

impl Runtime {
    pub fn new(
        output_style: OutputStyle,
        strict_mode: bool,
        output_language: OutputLanguage,
    ) -> Self {
        Runtime {
            module_manager: Box::new(ModuleManager::new()),
            execution_stack: vec![],
            next_fact_id: 1,
            symbol_id_allocator: Rc::new(SymbolIdAllocator::new()),
            template_instance_interner: RefCell::new(HashMap::new()),
            statement_proof_state: StatementProofStateStack::new(),
            output_style,
            strict_mode,
            output_language,
        }
    }
}

impl Default for Runtime {
    fn default() -> Self {
        Self::new(OutputStyle::Normal, false, OutputLanguage::English)
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

    pub fn set_output_style(&mut self, output_style: OutputStyle) {
        self.output_style = output_style;
    }

    pub fn effective_output_style(&self) -> OutputStyle {
        self.output_style
    }

    pub fn is_compact_output(&self) -> bool {
        self.effective_output_style() == OutputStyle::Compact
    }

    pub fn is_normal_output(&self) -> bool {
        self.effective_output_style() == OutputStyle::Normal
    }

    pub fn is_detailed_output(&self) -> bool {
        self.effective_output_style() == OutputStyle::Detailed
    }

    pub fn current_file_path_rc(&self) -> Rc<str> {
        self.execution_stack
            .last()
            .map(|frame| frame.source_path.clone())
            .unwrap_or_else(|| Rc::from(""))
    }

    pub fn ensure_execution_frame_for_parse(&mut self) {
        if !self.execution_stack.is_empty() {
            return;
        }
        let source_path = self.module_manager.entry_path_rc.to_string();
        let module_id = match self.module_manager.entry_module_id {
            Some(module_id) => module_id,
            None => self
                .module_manager
                .create_entry_module(source_path.as_str()),
        };
        self.execution_stack.push(ExecutionFrame::new(
            module_id,
            ExecutionLayer::Main,
            source_path.as_str(),
        ));
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
            .map(|frame| frame.module_id)
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

    pub fn push_module_execution_frame(&mut self, module_id: ModuleId, source_path: &str) {
        self.push_module_execution_frame_with_mode(module_id, source_path, ExecutionMode::Verified);
    }

    pub fn push_module_execution_frame_with_mode(
        &mut self,
        module_id: ModuleId,
        source_path: &str,
        execution_mode: ExecutionMode,
    ) {
        self.execution_stack.push(ExecutionFrame::new_with_mode(
            module_id,
            ExecutionLayer::Main,
            source_path,
            execution_mode,
        ));
    }

    pub fn push_file_execution_frame(
        &mut self,
        module_id: ModuleId,
        file_id: FileId,
        source_path: &str,
    ) {
        self.push_file_execution_frame_with_mode(
            module_id,
            file_id,
            source_path,
            ExecutionMode::Verified,
        );
    }

    pub fn push_file_execution_frame_with_mode(
        &mut self,
        module_id: ModuleId,
        file_id: FileId,
        source_path: &str,
        execution_mode: ExecutionMode,
    ) {
        self.execution_stack.push(ExecutionFrame::new_with_mode(
            module_id,
            ExecutionLayer::File(file_id),
            source_path,
            execution_mode,
        ));
    }

    pub fn canonical_module_name_for_parse(&self, name: &str) -> String {
        let Some(frame) = self.execution_stack.last() else {
            return name.to_string();
        };
        self.module_manager
            .canonical_name_for_reference(frame.module_id, name)
            .unwrap_or_else(|| name.to_string())
    }

    pub fn pop_execution_frame(&mut self) {
        if self.execution_stack.len() <= 1 {
            unreachable!("cannot pop the root user execution frame")
        }
        self.execution_stack.pop();
    }

    pub fn strict_mode_applies_to_current_module(&self) -> bool {
        if !self.strict_mode {
            return false;
        }
        let Some(frame) = self.execution_stack.last() else {
            return false;
        };
        !self
            .module_manager
            .module(frame.module_id)
            .is_some_and(|module| module.is_standard_library)
    }

    pub fn has_active_execution_frame(&self) -> bool {
        !self.execution_stack.is_empty()
    }

    pub fn current_execution_mode(&self) -> ExecutionMode {
        self.execution_stack
            .last()
            .map(|frame| frame.execution_mode)
            .unwrap_or(ExecutionMode::Verified)
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
    /// Start a standalone source run with its own entry module and root execution frame.
    pub fn start_isolated_source(&mut self, source_path: &str) {
        let module_id = self.module_manager.create_entry_module(source_path);
        self.execution_stack.push(ExecutionFrame::new(
            module_id,
            ExecutionLayer::Main,
            source_path,
        ));
    }

    /// Start a repository run with its root module and root execution frame.
    pub fn start_repository_run(
        &mut self,
        repository_root: String,
        main_file_path: String,
    ) -> Result<ModuleId, String> {
        let module_id = self
            .module_manager
            .create_repository_entry_module(repository_root, main_file_path.clone())?;
        self.execution_stack.push(ExecutionFrame::new(
            module_id,
            ExecutionLayer::Main,
            main_file_path.as_str(),
        ));
        Ok(module_id)
    }

    /// After `start_isolated_source`, point the current user source at another
    /// path without pushing more layers.
    pub fn set_current_user_lit_file_path(&mut self, path: &str) {
        let path_rc: Rc<str> = Rc::from(path);
        self.module_manager.entry_path_rc = path_rc.clone();
        if let Some(frame) = self.execution_stack.last_mut() {
            frame.source_path = path_rc;
        }
        if let Some(entry_id) = self.module_manager.entry_module_id {
            if let Some(module) = self.module_manager.module_mut(entry_id) {
                module.main_file_path = path.to_string();
            }
        }
    }

    /// Make the discovered repository's root module the persistent environment for
    /// interactive input. This method does not itself execute the ordered `[export]` plan.
    pub fn prepare_current_repository_for_repl(
        &mut self,
        source_path: &str,
    ) -> Result<(), RuntimeError> {
        let module_id = self.current_module_id();
        self.module_manager
            .module_mut(module_id)
            .expect("repository entry module should exist");
        self.execution_stack
            .last_mut()
            .expect("repository REPL should have an execution frame")
            .source_path = Rc::from(source_path);
        self.refresh_current_bare_symbol_index()
    }
}

#[cfg(test)]
#[path = "../../tests/unit/runtime/state/test_support.rs"]
mod test_support;
