//! Run-wide runtime state and current-source lifecycle.

use crate::prelude::*;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

pub struct Runtime {
    /// The module world for this top-level run.
    pub module_manager: Box<ModuleManager>,
    /// Module owning `current_source_id`. Source ids are module-local because
    /// import targets already carry their owner module id.
    pub current_module_id: Option<ModuleId>,
    /// The one source currently being parsed or executed.
    pub current_source_id: Option<SourceId>,
    /// Mode for the current operation; this is transient runtime state, not
    /// source metadata.
    pub active_mode: ExecutionMode,
    /// Temporary environments nested inside the current source.
    pub local_scopes: Vec<Box<Environment>>,
    /// Transient binder and scope state shared by one nested parser traversal.
    /// Changing the current source neither consumes nor resets it.
    pub(crate) parse_context: ParseContext,
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SourceActivation {
    /// Module that owns the checkpointed source id.
    pub module_id: Option<ModuleId>,
    /// Source that was active before a projection temporarily switched source.
    pub source_id: Option<SourceId>,
    /// Active verification mode restored with the source.
    pub mode: ExecutionMode,
}

impl Runtime {
    pub fn new(run_options: RunOptions) -> Self {
        Runtime {
            module_manager: Box::new(ModuleManager::new()),
            current_module_id: None,
            current_source_id: None,
            active_mode: ExecutionMode::RequireVerification,
            local_scopes: vec![],
            parse_context: ParseContext::new(),
            next_fact_id: 1,
            symbol_id_allocator: Rc::new(SymbolIdAllocator::new()),
            template_instance_interner: RefCell::new(HashMap::new()),
            executed_direct_struct_carriers: HashMap::new(),
            run_options,
        }
    }
}

fn virtual_source_from_legacy_label(label: &str) -> VirtualSource {
    match label.to_ascii_lowercase().as_str() {
        "eval" => VirtualSource::Eval,
        "repl" => VirtualSource::Repl,
        "session" => VirtualSource::Session,
        "to-lean" | "to_lean" => VirtualSource::ToLean,
        "to-latex" | "to_latex" => VirtualSource::ToLatex,
        _ => VirtualSource::Named(label.to_string()),
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
        let options = self.run_options;
        self.run_options = RunOptions::new(
            options.run(),
            output_detail,
            options.output_language(),
            options.summary(),
        );
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
        self.current_source()
            .map(|source| Rc::from(source.display_label()))
            .unwrap_or_else(|| Rc::from(""))
    }

    pub fn current_source(&self) -> Option<&Source> {
        let module_id = self.current_module_id?;
        let source_id = self.current_source_id?;
        self.module_manager.module(module_id)?.source(source_id)
    }

    fn activate_source(&mut self, module_id: ModuleId, source_id: SourceId, mode: ExecutionMode) {
        assert!(
            self.local_scopes.is_empty(),
            "a source cannot be selected with an active local environment"
        );
        self.current_module_id = Some(module_id);
        self.current_source_id = Some(source_id);
        self.active_mode = mode;
    }

    fn reset_current_source_state(&mut self) {
        self.current_module_id = None;
        self.current_source_id = None;
        self.active_mode = ExecutionMode::RequireVerification;
        self.local_scopes.clear();
    }

    pub fn source_activation(&self) -> SourceActivation {
        SourceActivation {
            module_id: self.current_module_id,
            source_id: self.current_source_id,
            mode: self.active_mode,
        }
    }

    pub fn restore_source_activation(&mut self, activation: SourceActivation) {
        match (activation.module_id, activation.source_id) {
            (Some(module_id), Some(source_id)) => {
                self.activate_source(module_id, source_id, activation.mode)
            }
            _ => self.reset_current_source_state(),
        }
    }

    pub fn ensure_current_source_for_parse(&mut self) {
        if self.current_source_id.is_some() {
            return;
        }
        debug_assert!(
            self.parse_context.is_at_root_scope(),
            "a current source cannot be selected inside an active parser scope"
        );
        let source_id = match self.module_manager.module(ModuleId::ROOT) {
            Some(_) => {
                let existing_source_id = self
                    .module_manager
                    .module(ModuleId::ROOT)
                    .and_then(|module| module.module_source_id);
                match existing_source_id {
                    Some(source_id) => source_id,
                    None => self
                        .module_manager
                        .create_virtual_source(ModuleId::ROOT, VirtualSource::Eval)
                        .expect("root execution source should be registered"),
                }
            }
            None => self
                .module_manager
                .create_virtual_root_module(VirtualSource::Eval),
        };
        self.activate_source(
            ModuleId::ROOT,
            source_id,
            ExecutionMode::RequireVerification,
        );
    }

    pub fn current_parse_context(&self) -> &ParseContext {
        &self.parse_context
    }

    pub fn current_parse_context_mut(&mut self) -> &mut ParseContext {
        &mut self.parse_context
    }

    pub fn current_module_id(&self) -> ModuleId {
        self.current_module_id
            .expect("a current source should exist")
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

    pub fn activate_source_for_execution(&mut self, module_id: ModuleId, source_id: SourceId) {
        self.activate_source_with_mode(module_id, source_id, ExecutionMode::RequireVerification);
    }

    pub fn activate_source_with_mode(
        &mut self,
        module_id: ModuleId,
        source_id: SourceId,
        execution_mode: ExecutionMode,
    ) {
        debug_assert!(
            self.parse_context.is_at_root_scope(),
            "a source cannot be selected inside an active parser scope"
        );
        self.activate_source(module_id, source_id, execution_mode);
    }

    pub fn canonical_module_name_for_parse(&self, name: &str) -> String {
        let Some(module_id) = self.current_module_id else {
            return name.to_string();
        };
        self.module_manager
            .canonical_name_for_reference(module_id, name)
            .unwrap_or_else(|| name.to_string())
    }

    pub fn clear_current_source(&mut self) {
        debug_assert!(
            self.parse_context.is_at_root_scope(),
            "the current source cannot be cleared inside an active parser scope"
        );
        self.reset_current_source_state();
    }

    pub fn strict_mode_applies_to_current_module(&self) -> bool {
        if !self.run_options.is_strict() {
            return false;
        }
        let Some(module_id) = self.current_module_id else {
            return false;
        };
        !self
            .module_manager
            .module(module_id)
            .is_some_and(|module| module.is_standard_library)
    }

    pub fn has_current_source(&self) -> bool {
        self.current_source_id.is_some()
    }

    pub fn current_execution_mode(&self) -> ExecutionMode {
        self.active_mode
    }

    pub fn current_execution_is_trusted_source(&self) -> bool {
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
        let previous = self.active_mode;
        self.active_mode = execution_mode;
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
    pub fn start_virtual_source(&mut self, kind: VirtualSource) {
        debug_assert!(self.parse_context.is_at_root_scope());
        let source_id = self.module_manager.create_virtual_root_module(kind);
        self.activate_source(
            ModuleId::ROOT,
            source_id,
            ExecutionMode::RequireVerification,
        );
    }

    pub fn start_real_file(&mut self, path: &str) {
        self.start_real_file_path(RealFilePath::new(path));
    }

    pub fn start_real_file_path(&mut self, path: RealFilePath) {
        debug_assert!(self.parse_context.is_at_root_scope());
        let source_id = self.module_manager.create_file_root_module(path);
        self.activate_source(
            ModuleId::ROOT,
            source_id,
            ExecutionMode::RequireVerification,
        );
    }

    /// Start a standalone virtual source with its own root module.
    #[deprecated(note = "use start_virtual_source with a VirtualSource variant")]
    pub fn start_isolated_source(&mut self, legacy_label: &str) {
        self.start_virtual_source(virtual_source_from_legacy_label(legacy_label));
    }

    /// Start a standalone physical file run with its own root module and source.
    #[deprecated(note = "use start_real_file")]
    pub fn start_isolated_file(&mut self, source_path: &str) {
        self.start_real_file(source_path);
    }

    /// Start a repository run with its root module. Registered sources are
    /// activated by the repository execution pipeline as they execute.
    pub fn start_repository_run(
        &mut self,
        repository_root: String,
        main_file_path: String,
    ) -> Result<ModuleId, String> {
        self.start_repository_run_typed(
            RealDirectoryPath::new(repository_root),
            RealFilePath::new(main_file_path),
        )
    }

    pub fn start_repository_run_typed(
        &mut self,
        repository_root: RealDirectoryPath,
        main_file_path: RealFilePath,
    ) -> Result<ModuleId, String> {
        let module_id = self
            .module_manager
            .create_repository_root_module(repository_root, main_file_path)?;
        Ok(module_id)
    }

    /// After a standalone source has been created, point that current source at
    /// a physical file path without creating another source.
    pub fn set_current_user_lit_file_path(&mut self, path: &str) {
        let (module_id, source_id) = self
            .current_module_id
            .zip(self.current_source_id)
            .expect("a user source should exist before changing its path");
        self.module_manager
            .module_mut(module_id)
            .and_then(|module| module.source_mut(source_id))
            .expect("current user source should be registered")
            .origin = SourcePath::RealFilePath(RealFilePath::new(path));
        if module_id == ModuleId::ROOT {
            self.module_manager
                .module_mut(module_id)
                .expect("root module should exist")
                .location = ModuleLocation::SingleFile;
        }
    }

    /// Make the discovered repository's root module the persistent environment for
    /// interactive input. This method does not itself execute the ordered `[export]` plan.
    #[deprecated(note = "use prepare_current_module_for_virtual_source")]
    pub fn prepare_current_repository_for_repl(
        &mut self,
        source_path: &str,
    ) -> Result<(), RuntimeError> {
        self.prepare_current_module_for_virtual_source(virtual_source_from_legacy_label(
            source_path,
        ))
    }

    pub fn prepare_current_module_for_virtual_source(
        &mut self,
        kind: VirtualSource,
    ) -> Result<(), RuntimeError> {
        debug_assert!(
            self.parse_context.is_at_root_scope(),
            "a repository REPL cannot start inside an active parser scope"
        );
        let inherited_environment = self
            .current_source()
            .map(|source| source.environment.clone());
        let module_id = self
            .module_manager
            .module(ModuleId::ROOT)
            .map(|module| module.id)
            .expect("repository root module should exist");
        let source_id = self
            .module_manager
            .create_virtual_source(module_id, kind)
            .expect("repository REPL source should be registered");
        if let Some(environment) = inherited_environment {
            self.module_manager
                .module_mut(module_id)
                .and_then(|module| module.source_mut(source_id))
                .expect("interactive source should be registered")
                .environment = environment;
        }
        self.activate_source(
            ModuleId::ROOT,
            source_id,
            ExecutionMode::RequireVerification,
        );
        Ok(())
    }
}

#[cfg(test)]
#[path = "../../tests/unit/runtime/state/test_support.rs"]
mod test_support;
