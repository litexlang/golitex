use crate::prelude::*;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RunMode {
    File,
    Repository,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OutputStyle {
    Compact,
    Normal,
    Detailed,
}

#[derive(Clone, Debug)]
pub struct UnverifiedImport {
    pub kind: String,
    pub name: String,
    pub line_file: LineFile,
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
    pub run_mode: RunMode,
    /// Parameters that the active recursive fact matcher may instantiate.
    /// Captured parameters of the same object kind must remain rigid.
    pub(crate) active_arg_match_bindings: Vec<(ParamObjType, String)>,
    /// Atomic facts currently being expanded by the recursive inference cascade.
    pub(crate) active_atomic_fact_inferences: HashSet<FactString>,
    /// Objects currently being checked for well-definedness.
    pub(crate) active_well_defined_objects: HashSet<ObjString>,
    pub(crate) symbol_id_allocator: Rc<SymbolIdAllocator>,
    pub(crate) template_instance_interner: RefCell<HashMap<String, SymbolBinding>>,
    /// Parser-only notation metadata. A source binder written as `a &Struct`
    /// records the struct view used to lower later `a.field` expressions.
    pub(crate) default_struct_views: HashMap<SymbolId, StructObj>,
    /// Struct declarations retained by parse-only consumers such as LaTeX output.
    /// These declarations never enter the verified environment.
    pub(crate) parsed_struct_definitions: HashMap<String, DefStructStmt>,
    pub detail_output: bool,
    pub output_style: OutputStyle,
    pub strict_mode: bool,
    pub isolated: bool,
    pub output_language: OutputLanguage,
    pub unverified_imports: Vec<UnverifiedImport>,
    pub(crate) trusted_prefix_policy: Option<TrustedPrefixPolicy>,
    pub(crate) trusted_prefix_statement_context: Option<TrustedPrefixStatementContext>,
    pub trusted_prefix_report: Option<TrustedPrefixReport>,
    pub trusted_prefix_setup_error: Option<String>,
}

impl Runtime {
    pub fn new() -> Self {
        Runtime {
            module_manager: Box::new(ModuleManager::new()),
            execution_stack: vec![],
            run_mode: RunMode::File,
            active_arg_match_bindings: vec![],
            active_atomic_fact_inferences: HashSet::new(),
            active_well_defined_objects: HashSet::new(),
            symbol_id_allocator: Rc::new(SymbolIdAllocator::new()),
            template_instance_interner: RefCell::new(HashMap::new()),
            default_struct_views: HashMap::new(),
            parsed_struct_definitions: HashMap::new(),
            detail_output: false,
            output_style: OutputStyle::Normal,
            strict_mode: false,
            isolated: false,
            output_language: OutputLanguage::English,
            unverified_imports: vec![],
            trusted_prefix_policy: None,
            trusted_prefix_statement_context: None,
            trusted_prefix_report: None,
            trusted_prefix_setup_error: None,
        }
    }
}

impl Runtime {
    pub fn set_output_style(&mut self, output_style: OutputStyle) {
        self.output_style = output_style;
        self.detail_output = output_style == OutputStyle::Detailed;
    }

    pub fn effective_output_style(&self) -> OutputStyle {
        if self.detail_output {
            OutputStyle::Detailed
        } else {
            self.output_style
        }
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

    pub(crate) fn ensure_execution_frame_for_parse(&mut self) {
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

    pub(crate) fn current_parse_context(&self) -> &ParseContext {
        &self
            .execution_stack
            .last()
            .expect("an execution frame should exist while parsing")
            .parse_context
    }

    pub(crate) fn current_parse_context_mut(&mut self) -> &mut ParseContext {
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

    pub(crate) fn has_active_execution_frame(&self) -> bool {
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
            .unverified_imports
            .iter()
            .any(|entry| entry.kind == kind && entry.name == name && entry.line_file == line_file)
        {
            return;
        }
        self.unverified_imports.push(UnverifiedImport {
            kind: kind.to_string(),
            name,
            line_file,
        });
    }

    fn current_execution_target(&self) -> (ModuleId, ExecutionLayer) {
        let frame = self
            .execution_stack
            .last()
            .expect("an execution frame should always exist");
        (frame.module_id, frame.layer)
    }

    pub(crate) fn configure_trusted_prefix(
        &mut self,
        module_id: ModuleId,
        layer: ExecutionLayer,
        before_line: usize,
    ) {
        self.trusted_prefix_policy = Some(TrustedPrefixPolicy::new(module_id, layer, before_line));
        self.trusted_prefix_statement_context = None;
    }

    pub(crate) fn clear_trusted_prefix_execution_policy(&mut self) {
        self.trusted_prefix_policy = None;
        self.trusted_prefix_statement_context = None;
    }

    pub(crate) fn trusted_prefix_before_line_for_current_target(&self) -> Option<usize> {
        let (module_id, layer) = self.current_execution_target();
        self.trusted_prefix_policy
            .as_ref()
            .filter(|policy| policy.matches(module_id, layer))
            .map(|policy| policy.before_line)
    }

    pub(crate) fn begin_trusted_prefix_statement(&mut self, is_trusted: bool) {
        let (module_id, layer) = self.current_execution_target();
        self.trusted_prefix_statement_context = Some(TrustedPrefixStatementContext::new(
            module_id, layer, is_trusted,
        ));
    }

    pub(crate) fn end_trusted_prefix_statement(&mut self) {
        self.trusted_prefix_statement_context = None;
    }

    pub(crate) fn current_statement_is_in_trusted_prefix_run(&self) -> bool {
        let (module_id, layer) = self.current_execution_target();
        self.trusted_prefix_statement_context
            .as_ref()
            .is_some_and(|context| context.matches(module_id, layer))
    }

    pub(crate) fn current_statement_is_cli_trusted_prefix(&self) -> bool {
        let (module_id, layer) = self.current_execution_target();
        self.trusted_prefix_statement_context
            .as_ref()
            .filter(|context| context.matches(module_id, layer))
            .is_some_and(|context| context.is_trusted)
    }

    pub(crate) fn replace_current_execution_mode(
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
    pub fn new_file_path_new_env_new_name_scope(&mut self, path: &str) {
        self.run_mode = RunMode::File;
        let module_id = self.module_manager.create_entry_module(path);
        self.execution_stack
            .push(ExecutionFrame::new(module_id, ExecutionLayer::Main, path));
    }

    pub fn new_repository_path_new_env_new_name_scope(
        &mut self,
        repository_root: String,
        main_file_path: String,
    ) -> Result<ModuleId, String> {
        self.run_mode = RunMode::Repository;
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

    /// After `new_file_path_new_env_new_name_scope`, point the current user source label at
    /// another path without pushing more layers (pair with `clear_current_env_and_parse_name_scope`).
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
    pub fn prepare_current_repository_for_repl(&mut self, source_label: &str) {
        let module_id = self.current_module_id();
        self.module_manager
            .module_mut(module_id)
            .expect("repository entry module should exist");
        self.execution_stack
            .last_mut()
            .expect("repository REPL should have an execution frame")
            .source_path = Rc::from(source_label);
    }

    /// Rebuild the module registry between independent runner items.
    #[cfg(test)]
    pub(crate) fn reset_for_isolated_runner_item(&mut self) {
        let path = self.current_file_path_rc().to_string();
        self.module_manager = Box::new(ModuleManager::new());
        self.execution_stack.clear();
        self.unverified_imports.clear();
        self.parsed_struct_definitions.clear();
        self.active_atomic_fact_inferences.clear();
        self.active_well_defined_objects.clear();
        self.trusted_prefix_policy = None;
        self.trusted_prefix_statement_context = None;
        self.trusted_prefix_report = None;
        self.trusted_prefix_setup_error = None;
        self.new_file_path_new_env_new_name_scope(path.as_str());
    }
}

impl Runtime {
    pub fn top_level_env(&mut self) -> &mut Environment {
        if self
            .execution_stack
            .last()
            .is_some_and(|frame| !frame.local_environment_stack.is_empty())
        {
            return self
                .execution_stack
                .last_mut()
                .and_then(|frame| frame.local_environment_stack.last_mut())
                .map(|environment| environment.as_mut())
                .expect("local environment should exist");
        }

        let (module_id, layer) = self.current_execution_target();
        match layer {
            ExecutionLayer::Main => self
                .module_manager
                .module_mut(module_id)
                .map(|module| module.main_environment.as_mut())
                .expect("current module should exist"),
            ExecutionLayer::File(file_id) => self
                .module_manager
                .module_mut(module_id)
                .and_then(|module| module.file_mut(file_id))
                .map(|file| file.environment.as_mut())
                .expect("current file environment should exist"),
        }
    }
}

impl Runtime {
    fn push_env(&mut self) {
        let frame = self
            .execution_stack
            .last_mut()
            .expect("an execution frame should always exist");
        frame
            .local_environment_stack
            .push(Box::new(Environment::new_empty_env()));
    }

    fn pop_env(&mut self) {
        let frame = self
            .execution_stack
            .last_mut()
            .expect("an execution frame should always exist");
        frame
            .local_environment_stack
            .pop()
            .expect("no local environment to pop");
    }

    /// Replace the top user environment with an empty one and clear parse-time free-param scopes.
    pub fn clear_current_env_and_parse_name_scope(&mut self) {
        if self
            .execution_stack
            .last()
            .is_some_and(|frame| !frame.local_environment_stack.is_empty())
        {
            if let Some(environment) = self
                .execution_stack
                .last_mut()
                .and_then(|frame| frame.local_environment_stack.last_mut())
            {
                **environment = Environment::new_empty_env();
            }
        } else {
            let (module_id, layer) = self.current_execution_target();
            if let Some(module) = self.module_manager.module_mut(module_id) {
                match layer {
                    ExecutionLayer::Main => {
                        module.main_environment = Box::new(Environment::new_empty_env());
                    }
                    ExecutionLayer::File(file_id) => {
                        if let Some(file) = module.file_mut(file_id) {
                            file.environment = Box::new(Environment::new_empty_env());
                        }
                    }
                }
            }
        }
        self.current_parse_context_mut().clear();
        self.parsed_struct_definitions.clear();
    }

    /// Runs a closure in a temporary child environment and pops it on normal return.
    /// This matches manual `push_env`/`pop_env`; a panic will not restore the stack.
    pub fn run_in_local_env<T, E, F>(&mut self, f: F) -> Result<T, E>
    where
        F: FnOnce(&mut Self) -> Result<T, E>,
    {
        self.push_env();
        let result = f(self);
        self.pop_env();
        result
    }

    /// Runs a closure in a temporary child environment. On success, commits the child environment
    /// into the parent with environment merge semantics; on failure, discards it. The closure must
    /// not mutate module discovery or loading state.
    pub fn run_in_local_env_and_commit<T, F>(&mut self, f: F) -> Result<T, RuntimeError>
    where
        F: FnOnce(&mut Self) -> Result<T, RuntimeError>,
    {
        let parse_context_before = self.current_parse_context().clone();

        self.push_env();
        let result = f(self);
        let child = self
            .execution_stack
            .last_mut()
            .and_then(|frame| frame.local_environment_stack.pop())
            .expect("local environment should exist after push_env");

        *self.current_parse_context_mut() = parse_context_before;

        let value = result?;
        self.top_level_env().merge_committed_child(*child)?;
        Ok(value)
    }

    /// Restores the current frame's [`ParseContext`] after `f` so parse-time bindings (e.g.
    /// `have x …` without `=`) do not leak across sibling `?` goal blocks or out of nested parses
    /// that use this wrapper (`forall`, `exist`, goal blocks, `prop` bodies, etc.).
    pub fn run_in_local_parsing_time_name_scope<T, E, F>(&mut self, f: F) -> Result<T, E>
    where
        F: FnOnce(&mut Self) -> Result<T, E>,
    {
        let saved_parse_context = self.current_parse_context().clone();
        let result = f(self);
        *self.current_parse_context_mut() = saved_parse_context;
        result
    }

    /// Keeps object names introduced by `have` or `obtain` local to one parsed proof body.
    pub fn run_in_local_proof_parsing_scope<T, E, F>(&mut self, f: F) -> Result<T, E>
    where
        F: FnOnce(&mut Self) -> Result<T, E>,
    {
        self.current_parse_context_mut().local_binding_scope_depth += 1;
        let result = self.run_in_local_parsing_time_name_scope(f);
        self.current_parse_context_mut().local_binding_scope_depth -= 1;
        result
    }

    pub fn register_local_identifier_bindings_for_parse(
        &mut self,
        names: &[String],
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        if self.current_parse_context().local_binding_scope_depth == 0 || names.is_empty() {
            return Ok(());
        }
        self.begin_parsing_scope(ParamObjType::Identifier, names, line_file)
            .map(|_| ())
    }

    pub fn register_local_existing_identifier_bindings_for_parse(
        &mut self,
        bindings: &[SymbolBinding],
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        if self.current_parse_context().local_binding_scope_depth == 0 || bindings.is_empty() {
            return Ok(());
        }
        for binding in bindings {
            let name = binding.name();
            if self.current_parse_context().active_binding(name).is_some()
                || self.visible_symbol_definition(name).is_some()
                || is_keyword(name)
                || is_builtin_identifier_name(name)
                || is_builtin_predicate(name)
            {
                return Err(crate::runtime::runtime_symbol::active_parse_name_error(
                    name, &line_file,
                ));
            }
        }
        self.current_parse_context_mut().free_params.begin_scope(
            ParamObjType::Identifier,
            bindings,
            line_file,
        )?;
        self.current_parse_context_mut()
            .push_scope_frame(bindings.to_vec());
        Ok(())
    }

    /// `begin_scope` → `f` → `end_scope`; runs `end_scope` on both `Ok` and `Err` (not on `begin_scope` failure).
    pub fn parse_in_local_free_param_scope<T, F>(
        &mut self,
        kind: ParamObjType,
        names: &[String],
        line_file: LineFile,
        f: F,
    ) -> Result<T, RuntimeError>
    where
        F: FnOnce(&mut Self) -> Result<T, RuntimeError>,
    {
        self.begin_parsing_scope(kind, names, line_file)?;
        let result = f(self);
        self.end_parsing_scope(kind, names);
        result
    }

    pub fn parse_in_local_free_param_scope_with_bindings<T, F>(
        &mut self,
        kind: ParamObjType,
        names: &[String],
        line_file: LineFile,
        f: F,
    ) -> Result<(T, Vec<SymbolBinding>), RuntimeError>
    where
        F: FnOnce(&mut Self) -> Result<T, RuntimeError>,
    {
        let bindings = self.begin_parsing_scope(kind, names, line_file)?;
        let result = f(self);
        self.end_parsing_scope(kind, names);
        result.map(|value| (value, bindings))
    }

    pub fn parse_in_existing_free_param_scope<T, F>(
        &mut self,
        kind: ParamObjType,
        bindings: &[SymbolBinding],
        line_file: LineFile,
        parse_body: F,
    ) -> Result<T, RuntimeError>
    where
        F: FnOnce(&mut Self) -> Result<T, RuntimeError>,
    {
        if bindings.is_empty() {
            return parse_body(self);
        }
        let names = bindings
            .iter()
            .map(|binding| binding.name().to_string())
            .collect::<Vec<_>>();
        for binding in bindings {
            if let Some(active) = self.current_parse_context().active_binding(binding.name()) {
                if active.id() != binding.id() {
                    return Err(crate::runtime::runtime_symbol::active_parse_name_error(
                        binding.name(),
                        &line_file,
                    ));
                }
            }
            if let Some(visible) = self.visible_symbol_definition(binding.name()) {
                if visible.binding().id() != binding.id() {
                    return Err(crate::runtime::runtime_symbol::active_parse_name_error(
                        binding.name(),
                        &line_file,
                    ));
                }
            }
        }
        self.current_parse_context_mut()
            .free_params
            .begin_scope(kind, bindings, line_file)?;
        self.current_parse_context_mut()
            .push_scope_frame(bindings.to_vec());
        let result = parse_body(self);
        self.end_parsing_scope(kind, &names);
        result
    }

    pub fn parse_stmts_with_existing_free_param_bindings<F>(
        &mut self,
        kind: ParamObjType,
        bindings: &[SymbolBinding],
        line_file: LineFile,
        parse_body: F,
    ) -> Result<Vec<Stmt>, RuntimeError>
    where
        F: FnOnce(&mut Self) -> Result<Vec<Stmt>, RuntimeError>,
    {
        self.run_in_local_proof_parsing_scope(|this| {
            this.parse_in_existing_free_param_scope(kind, bindings, line_file, parse_body)
        })
    }

    pub fn parse_stmts_with_free_param_scope_and_bindings<F>(
        &mut self,
        kind: ParamObjType,
        names: &[String],
        line_file: LineFile,
        parse_body: F,
    ) -> Result<(Vec<Stmt>, Vec<SymbolBinding>), RuntimeError>
    where
        F: FnOnce(&mut Self) -> Result<Vec<Stmt>, RuntimeError>,
    {
        self.run_in_local_proof_parsing_scope(|this| {
            this.parse_in_local_free_param_scope_with_bindings(kind, names, line_file, parse_body)
        })
    }
}

impl Runtime {
    pub fn is_name_used_for_identifier(&self, name: &str) -> bool {
        if is_builtin_identifier_name(name) {
            return true;
        }

        for env in self.iter_environments_from_top() {
            if env.defined_identifiers.contains_key(name) {
                return true;
            }
        }

        false
    }

    pub fn is_name_used_for_prop(&self, name: &str) -> bool {
        return self.get_prop_definition_by_name(name).is_some();
    }

    pub fn is_name_used_for_abstract_prop(&self, name: &str) -> bool {
        if is_builtin_predicate(name) {
            return true;
        }

        return self.get_abstract_prop_definition_by_name(name).is_some();
    }

    pub fn is_name_used_for_algo(&self, name: &str) -> bool {
        return self.get_algo_definition_by_name(name).is_some();
    }
}

impl Runtime {
    pub fn store_tuple_obj_and_cart(
        &mut self,
        name: &str,
        tuple: Option<Tuple>,
        cart: Option<Cart>,
        line_file: LineFile,
    ) {
        let known_tuple_objs = &mut self.top_level_env().known_objs_equal_to_tuple;
        let old_tuple_and_cart = known_tuple_objs.get(name).cloned();

        let merged_tuple = match (tuple, old_tuple_and_cart.as_ref()) {
            (Some(new_tuple), _) => Some(new_tuple),
            (None, Some((old_tuple, _, _))) => old_tuple.clone(),
            (None, None) => None,
        };
        let merged_cart = match (cart, old_tuple_and_cart.as_ref()) {
            (Some(new_cart), _) => Some(new_cart),
            (None, Some((_, old_cart, _))) => old_cart.clone(),
            (None, None) => None,
        };
        let merged_line_file = line_file;

        known_tuple_objs.insert(
            name.to_string(),
            (merged_tuple, merged_cart, merged_line_file),
        );
    }

    pub fn store_known_cart_obj(&mut self, name: &str, cart: Cart, line_file: LineFile) {
        self.top_level_env()
            .known_objs_equal_to_cart
            .insert(name.to_string(), (cart, line_file));
    }

    pub fn store_known_set_builder_obj(
        &mut self,
        name: &str,
        set_builder: SetBuilder,
        line_file: LineFile,
    ) {
        self.top_level_env()
            .known_objs_equal_to_set_builder
            .insert(name.to_string(), (set_builder, line_file));
    }

    pub fn store_known_finite_seq_list_obj(
        &mut self,
        name: &str,
        list: FiniteSeqListObj,
        member_of_finite_seq_set: Option<FiniteSeqSet>,
        line_file: LineFile,
    ) {
        let map = &mut self.top_level_env().known_objs_equal_to_finite_seq_list;
        let old = map.get(name).cloned();
        let merged_member = match (member_of_finite_seq_set, old.as_ref()) {
            (Some(new_s), _) => Some(new_s),
            (None, Some((_, Some(old_s), _))) => Some(old_s.clone()),
            (None, _) => None,
        };
        map.insert(name.to_string(), (list, merged_member, line_file));
    }

    pub fn store_known_matrix_list_obj(
        &mut self,
        name: &str,
        matrix: MatrixListObj,
        member_of_matrix_set: Option<MatrixSet>,
        line_file: LineFile,
    ) {
        let map = &mut self.top_level_env().known_objs_equal_to_matrix_list;
        let old = map.get(name).cloned();
        let merged_member = match (member_of_matrix_set, old.as_ref()) {
            (Some(new_s), _) => Some(new_s),
            (None, Some((_, Some(old_s), _))) => Some(old_s.clone()),
            (None, _) => None,
        };
        map.insert(name.to_string(), (matrix, merged_member, line_file));
    }

    pub fn store_obj_in_matrix_set(
        &mut self,
        obj: &Obj,
        matrix_set: MatrixSet,
        line_file: LineFile,
    ) {
        self.top_level_env()
            .known_objs_in_matrix_sets
            .insert(obj.to_string(), (matrix_set, line_file));
    }

    pub fn matrix_set_to_fn_set(&self, ms: &MatrixSet, line_file: LineFile) -> FnSet {
        let pair = self.generate_random_unused_names(2);
        let p1 = self
            .fresh_param_group_with_set(vec![pair[0].clone()], StandardSet::NPos.into())
            .expect("internal binder identity counter exhausted");
        let p2 = self
            .fresh_param_group_with_set(vec![pair[1].clone()], StandardSet::NPos.into())
            .expect("internal binder identity counter exhausted");
        FnSet::new(
            vec![p1.clone(), p2.clone()],
            vec![
                AtomicFact::from(LessEqualFact::new(
                    obj_for_bound_param_in_scope(&p1.params[0], ParamObjType::FnSet),
                    (*ms.row_len).clone(),
                    line_file.clone(),
                ))
                .into(),
                AtomicFact::from(LessEqualFact::new(
                    obj_for_bound_param_in_scope(&p2.params[0], ParamObjType::FnSet),
                    (*ms.col_len).clone(),
                    line_file.clone(),
                ))
                .into(),
            ],
            (*ms.set).clone(),
        )
        .expect("generated matrix fn set uses fresh parameters")
    }

    pub fn finite_seq_set_to_fn_set(&self, fs: &FiniteSeqSet, line_file: LineFile) -> FnSet {
        let param = self.generate_random_unused_name();
        let param_group = self
            .fresh_param_group_with_set(vec![param], StandardSet::NPos.into())
            .expect("internal binder identity counter exhausted");
        FnSet::new(
            vec![param_group.clone()],
            vec![AtomicFact::from(LessEqualFact::new(
                obj_for_bound_param_in_scope(&param_group.params[0], ParamObjType::FnSet),
                (*fs.n).clone(),
                line_file,
            ))
            .into()],
            (*fs.set).clone(),
        )
        .expect("generated finite sequence fn set uses a fresh parameter")
    }

    pub fn seq_set_to_fn_set(&self, ss: &SeqSet, _line_file: LineFile) -> FnSet {
        let param = self.generate_random_unused_name();
        FnSet::new(
            vec![self
                .fresh_param_group_with_set(vec![param], StandardSet::NPos.into())
                .expect("internal binder identity counter exhausted")],
            vec![],
            (*ss.set).clone(),
        )
        .expect("generated sequence fn set uses a fresh parameter")
    }

    pub fn finite_seq_set_to_fn_set_from_surface_dom_param(
        &self,
        fs: &FiniteSeqSet,
        line_file: LineFile,
        surface_dom_param: &str,
    ) -> Result<FnSet, RuntimeError> {
        let params = vec![self.fresh_param_group_with_set(
            vec![surface_dom_param.to_string()],
            StandardSet::NPos.into(),
        )?];
        let dom_facts: Vec<OrAndChainAtomicFact> = vec![OrAndChainAtomicFact::AtomicFact(
            LessEqualFact::new(
                obj_for_bound_param_in_scope(&params[0].params[0], ParamObjType::FnSet),
                (*fs.n).clone(),
                line_file,
            )
            .into(),
        )];
        self.new_fn_set(params, dom_facts, (*fs.set).clone())
    }

    pub fn store_well_defined_obj_cache(&mut self, obj: &Obj) {
        self.top_level_env()
            .cache_well_defined_obj
            .insert(obj.to_string(), ());
    }
}

impl Runtime {
    pub fn new_fn_set(
        &self,
        params_and_their_sets: impl Into<ParamDefWithSet>,
        dom_facts: Vec<OrAndChainAtomicFact>,
        ret_set: Obj,
    ) -> Result<FnSet, RuntimeError> {
        let empty: HashMap<String, Obj> = HashMap::new();
        let mut dom_stored = Vec::with_capacity(dom_facts.len());
        for d in &dom_facts {
            dom_stored.push(self.inst_or_and_chain_atomic_fact(
                d,
                &empty,
                ParamObjType::FnSet,
                None,
            )?);
        }
        let ret_stored = self.inst_obj(&ret_set, &empty, ParamObjType::FnSet)?;
        Ok(FnSet::new(params_and_their_sets, dom_stored, ret_stored)?)
    }

    pub fn new_anonymous_fn(
        &self,
        params_and_their_sets: impl Into<ParamDefWithSet>,
        dom_facts: Vec<OrAndChainAtomicFact>,
        ret_set: Obj,
        equal_to: Obj,
    ) -> Result<AnonymousFn, RuntimeError> {
        let empty: HashMap<String, Obj> = HashMap::new();
        let mut dom_stored = Vec::with_capacity(dom_facts.len());
        for d in &dom_facts {
            dom_stored.push(self.inst_or_and_chain_atomic_fact(
                d,
                &empty,
                ParamObjType::FnSet,
                None,
            )?);
        }
        let ret_stored = self.inst_obj(&ret_set, &empty, ParamObjType::FnSet)?;
        let eq_stored = self.inst_obj(&equal_to, &empty, ParamObjType::FnSet)?;
        Ok(AnonymousFn::new(
            params_and_their_sets,
            dom_stored,
            ret_stored,
            eq_stored,
        )?)
    }

    pub fn fn_set_from_fn_set_clause(&self, clause: &FnSetClause) -> Result<FnSet, RuntimeError> {
        self.new_fn_set(
            clause.params_def_with_set.clone(),
            clause.dom_facts.clone(),
            clause.ret_set.clone(),
        )
    }
}

impl Runtime {
    pub fn params_to_arg_map(
        &self,
        param_defs: &ParamDefWithType,
        args: &[Obj],
    ) -> Result<HashMap<String, Obj>, RuntimeError> {
        let param_bindings = param_defs.collect_param_bindings();
        if param_bindings.len() != args.len() {
            return Err(
                InstantiateRuntimeError(RuntimeErrorStruct::new_with_just_msg(format!(
                    "params_to_arg_map: expected {} argument(s), got {}",
                    param_bindings.len(),
                    args.len()
                )))
                .into(),
            );
        }

        let mut result: HashMap<String, Obj> = HashMap::new();
        for (binding, arg) in param_bindings.iter().zip(args.iter()) {
            insert_symbol_substitution(&mut result, binding, arg.clone());
        }
        Ok(result)
    }
}
