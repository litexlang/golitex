use crate::prelude::*;
use std::collections::HashMap;
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
    pub parsing_free_param_collection: FreeParamCollection,
    pub parsing_local_binding_scope_depth: usize,
    pub detail_output: bool,
    pub output_style: OutputStyle,
    pub strict_mode: bool,
    pub output_language: OutputLanguage,
    pub loading_builtin_code: bool,
    pub trusted_import_summary: ProofTrustSummary,
}

impl Runtime {
    pub fn new() -> Self {
        Runtime {
            module_manager: Box::new(ModuleManager::new(BUILTIN_CODE_PATH)),
            execution_stack: vec![ExecutionFrame::new_builtin()],
            run_mode: RunMode::File,
            parsing_free_param_collection: FreeParamCollection::new(),
            parsing_local_binding_scope_depth: 0,
            detail_output: false,
            output_style: OutputStyle::Normal,
            strict_mode: false,
            output_language: OutputLanguage::English,
            loading_builtin_code: false,
            trusted_import_summary: ProofTrustSummary::new(),
        }
    }

    // Same empty runtime as `new`, then runs builtin definitions; panics if that fails.
    pub fn new_with_builtin_code() -> Self {
        let mut runtime = Self::new();
        runtime.loading_builtin_code = true;
        let (stmt_results, runtime_error) =
            crate::pipeline::run_source_code(builtin_code().as_str(), &mut runtime);
        if runtime_error.is_some() {
            let (_, msg) = crate::pipeline::render_run_source_code_output(
                &runtime,
                &stmt_results,
                &runtime_error,
                true,
            );
            panic!("builtin code execution failed: {}", msg);
        }
        runtime.loading_builtin_code = false;
        runtime
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
            .unwrap_or_else(|| Rc::from(BUILTIN_CODE_PATH))
    }

    pub fn current_module_id(&self) -> ModuleId {
        self.execution_stack
            .last()
            .and_then(|frame| frame.module_id)
            .expect("current execution frame is not a module frame")
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

    pub fn activate_local_import(&mut self, name: String, target: ImportTarget) {
        self.execution_stack
            .last_mut()
            .expect("an execution frame should always exist")
            .active_local_imports
            .insert(name, target);
    }

    pub fn active_local_import(&self, name: &str) -> Option<ImportTarget> {
        self.execution_stack
            .last()
            .and_then(|frame| frame.active_local_imports.get(name))
            .copied()
    }

    pub fn canonical_module_name_for_parse(&self, name: &str) -> String {
        let target = self
            .active_local_import(name)
            .or_else(|| self.module_manager.import_target_by_canonical_name(name));
        target
            .and_then(|target| self.module_manager.canonical_name_for_target(target))
            .unwrap_or(name)
            .to_string()
    }

    pub fn unique_active_local_import_member_namespace(&self, name: &str) -> Option<String> {
        let current_has_name = self.iter_environments_from_top().any(|environment| {
            environment.defined_identifiers.contains_key(name)
                || environment.defined_def_props.contains_key(name)
                || environment.defined_abstract_props.contains_key(name)
                || environment.defined_algorithms.contains_key(name)
                || environment.defined_structs.contains_key(name)
                || environment.defined_templates.contains_key(name)
                || environment.defined_thm_stmts.contains_key(name)
                || environment.defined_strategy_stmts.contains_key(name)
        });
        if current_has_name {
            return None;
        }

        let import_names = self
            .execution_stack
            .last()
            .map(|frame| {
                frame
                    .active_local_imports
                    .keys()
                    .cloned()
                    .collect::<Vec<String>>()
            })
            .unwrap_or_default();
        let mut matching_namespaces = vec![];
        for import_name in import_names {
            let imported_has_name = self
                .imported_module_environments(import_name.as_str())
                .iter()
                .any(|environment| {
                    environment.defined_identifiers.contains_key(name)
                        || environment.defined_def_props.contains_key(name)
                        || environment.defined_abstract_props.contains_key(name)
                        || environment.defined_algorithms.contains_key(name)
                        || environment.defined_structs.contains_key(name)
                        || environment.defined_templates.contains_key(name)
                        || environment.defined_thm_stmts.contains_key(name)
                        || environment.defined_strategy_stmts.contains_key(name)
                });
            if !imported_has_name {
                continue;
            }
            let namespace = self.canonical_module_name_for_parse(import_name.as_str());
            if !matching_namespaces.contains(&namespace) {
                matching_namespaces.push(namespace);
            }
        }

        if matching_namespaces.len() == 1 {
            matching_namespaces.pop()
        } else {
            None
        }
    }

    pub fn pop_execution_frame(&mut self) {
        if self.execution_stack.len() <= 1 {
            unreachable!("cannot pop the builtin execution frame")
        }
        self.execution_stack.pop();
    }

    pub fn strict_mode_applies_to_current_module(&self) -> bool {
        self.strict_mode
            && self
                .execution_stack
                .last()
                .and_then(|frame| frame.module_id)
                == self.module_manager.entry_module_id
    }

    pub fn current_layer(&self) -> ExecutionLayer {
        self.execution_stack
            .last()
            .map(|frame| frame.layer)
            .expect("an execution frame should always exist")
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

    pub fn record_trusted_import(&mut self, kind: &str, name: String, line_file: LineFile) {
        self.trusted_import_summary
            .add_dependency(kind, Some(name), line_file);
    }

    fn current_execution_target(&self) -> (Option<ModuleId>, ExecutionLayer) {
        let frame = self
            .execution_stack
            .last()
            .expect("an execution frame should always exist");
        (frame.module_id, frame.layer)
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

    /// Make the discovered repository's root module the persistent environment for an
    /// interactive REPL without executing its `[run]` plan.
    pub fn prepare_current_repository_for_repl(&mut self, source_label: &str) {
        let root_exports = self.module_manager.root_exports.clone();
        let module_id = self.current_module_id();
        let module = self
            .module_manager
            .module_mut(module_id)
            .expect("repository entry module should exist");
        module.main_local_imports = root_exports;
        self.execution_stack
            .last_mut()
            .expect("repository REPL should have an execution frame")
            .source_path = Rc::from(source_label);
    }

    /// Rebuild the module registry between independent runner items while reusing builtins.
    #[cfg(test)]
    pub(crate) fn reset_for_isolated_runner_item(&mut self) {
        let path = self.current_file_path_rc().to_string();
        let mut module_manager = Box::new(ModuleManager::new(path.as_str()));
        std::mem::swap(
            &mut module_manager.builtin_environment,
            &mut self.module_manager.builtin_environment,
        );
        self.module_manager = module_manager;
        self.execution_stack = vec![ExecutionFrame::new_builtin()];
        self.parsing_free_param_collection.clear();
        self.trusted_import_summary = ProofTrustSummary::new();
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
            ExecutionLayer::Builtin => self.module_manager.builtin_environment.as_mut(),
            ExecutionLayer::Main => self
                .module_manager
                .module_mut(module_id.expect("main execution requires a module"))
                .map(|module| module.main_environment.as_mut())
                .expect("current module should exist"),
            ExecutionLayer::File(file_id) => self
                .module_manager
                .module_mut(module_id.expect("file execution requires a module"))
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
    /// The builtin layer at index 0 is left unchanged.
    pub fn clear_current_env_and_parse_name_scope(&mut self) {
        if self.has_user_env() {
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
                let module_id = module_id.expect("user execution requires a module");
                if let Some(module) = self.module_manager.module_mut(module_id) {
                    match layer {
                        ExecutionLayer::Builtin => {}
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
        }
        self.parsing_free_param_collection.clear();
    }

    pub fn has_user_env(&self) -> bool {
        self.execution_stack
            .last()
            .is_some_and(|frame| frame.layer != ExecutionLayer::Builtin)
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
    /// into the parent with environment merge semantics; on failure, discards it.
    pub fn run_in_local_env_and_commit<T, F>(&mut self, f: F) -> Result<T, RuntimeError>
    where
        F: FnOnce(&mut Self) -> Result<T, RuntimeError>,
    {
        let module_manager_before = self.module_manager.clone();
        let parsing_free_params_before = self.parsing_free_param_collection.clone();

        self.push_env();
        let result = f(self);
        let child = self
            .execution_stack
            .last_mut()
            .and_then(|frame| frame.local_environment_stack.pop())
            .expect("local environment should exist after push_env");

        self.parsing_free_param_collection = parsing_free_params_before;
        self.module_manager = module_manager_before;

        let value = result?;
        self.top_level_env().merge_committed_child(*child)?;
        Ok(value)
    }

    /// Restores [`Runtime::parsing_free_param_collection`] after `f` so parse-time bindings (e.g.
    /// `have x …` without `=`) do not leak across sibling `?` goal blocks or out of nested parses
    /// that use this wrapper (`forall`, `exist`, goal blocks, `prop` bodies, etc.).
    pub fn run_in_local_parsing_time_name_scope<T, E, F>(&mut self, f: F) -> Result<T, E>
    where
        F: FnOnce(&mut Self) -> Result<T, E>,
    {
        let saved_free_params = self.parsing_free_param_collection.clone();
        let result = f(self);
        self.parsing_free_param_collection = saved_free_params;
        result
    }

    /// Keeps object names introduced by `have` or `obtain` local to one parsed proof body.
    pub fn run_in_local_proof_parsing_scope<T, E, F>(&mut self, f: F) -> Result<T, E>
    where
        F: FnOnce(&mut Self) -> Result<T, E>,
    {
        self.parsing_local_binding_scope_depth += 1;
        let result = self.run_in_local_parsing_time_name_scope(f);
        self.parsing_local_binding_scope_depth -= 1;
        result
    }

    pub fn register_local_identifier_bindings_for_parse(
        &mut self,
        names: &[String],
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        if self.parsing_local_binding_scope_depth == 0 || names.is_empty() {
            return Ok(());
        }
        self.parsing_free_param_collection
            .begin_scope(ParamObjType::Identifier, names, line_file)
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
        self.parsing_free_param_collection
            .begin_scope(kind, names, line_file)?;
        let result = f(self);
        self.parsing_free_param_collection.end_scope(kind, names);
        result
    }

    /// If `names` is empty, runs `f` with no extra scope; otherwise wraps it in `parse_in_local_free_param_scope`.
    pub fn with_optional_free_param_scope<T, F>(
        &mut self,
        kind: ParamObjType,
        names: &[String],
        line_file: LineFile,
        f: F,
    ) -> Result<T, RuntimeError>
    where
        F: FnOnce(&mut Self) -> Result<T, RuntimeError>,
    {
        if names.is_empty() {
            f(self)
        } else {
            self.parse_in_local_free_param_scope(kind, names, line_file, f)
        }
    }

    pub fn parse_stmts_with_optional_free_param_scope<F>(
        &mut self,
        kind: ParamObjType,
        names: &[String],
        line_file: LineFile,
        parse_body: F,
    ) -> Result<Vec<Stmt>, RuntimeError>
    where
        F: FnOnce(&mut Self) -> Result<Vec<Stmt>, RuntimeError>,
    {
        self.run_in_local_proof_parsing_scope(|this| {
            this.with_optional_free_param_scope(kind, names, line_file, parse_body)
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

    pub fn matrix_set_to_fn_set(&self, ms: &MatrixSet, line_file: LineFile) -> FnSet {
        let pair = self.generate_random_unused_names(2);
        let p1 = pair[0].clone();
        let p2 = pair[1].clone();
        FnSet::new(
            vec![
                ParamGroupWithSet::new(vec![p1.clone()], StandardSet::NPos.into()),
                ParamGroupWithSet::new(vec![p2.clone()], StandardSet::NPos.into()),
            ],
            vec![
                AtomicFact::from(LessEqualFact::new(
                    obj_for_bound_param_in_scope(p1, ParamObjType::FnSet),
                    (*ms.row_len).clone(),
                    line_file.clone(),
                ))
                .into(),
                AtomicFact::from(LessEqualFact::new(
                    obj_for_bound_param_in_scope(p2, ParamObjType::FnSet),
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
        FnSet::new(
            vec![ParamGroupWithSet::new(
                vec![param.clone()],
                StandardSet::NPos.into(),
            )],
            vec![AtomicFact::from(LessEqualFact::new(
                obj_for_bound_param_in_scope(param, ParamObjType::FnSet),
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
            vec![ParamGroupWithSet::new(
                vec![param.clone()],
                StandardSet::NPos.into(),
            )],
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
        let params = vec![ParamGroupWithSet::new(
            vec![surface_dom_param.to_string()],
            StandardSet::NPos.into(),
        )];
        let dom_facts: Vec<OrAndChainAtomicFact> = vec![OrAndChainAtomicFact::AtomicFact(
            LessEqualFact::new(
                Identifier::new(surface_dom_param.to_string()).into(),
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
        let param_names = param_defs.collect_param_names();
        if param_names.len() != args.len() {
            return Err(
                InstantiateRuntimeError(RuntimeErrorStruct::new_with_just_msg(format!(
                    "params_to_arg_map: expected {} argument(s), got {}",
                    param_names.len(),
                    args.len()
                )))
                .into(),
            );
        }

        let mut result: HashMap<String, Obj> = HashMap::new();
        for (param_name, arg) in param_names.iter().zip(args.iter()) {
            result.insert(param_name.clone(), arg.clone());
        }
        Ok(result)
    }
}
