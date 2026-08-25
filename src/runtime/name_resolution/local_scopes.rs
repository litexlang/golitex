//! Temporary parser and proof scopes owned by the active execution frame.

use crate::prelude::*;

impl Runtime {
    fn current_execution_target(&self) -> (ModuleId, ExecutionLayer) {
        let frame = self
            .execution_stack
            .last()
            .expect("an execution frame should always exist");
        (frame.module_id, frame.layer)
    }

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
        self.statement_proof_state.push_scope();
    }

    /// Runs a closure in a temporary child environment and pops it on normal return.
    /// This matches manual `push_env`/`pop_env`; a panic will not restore the stack.
    pub fn run_in_local_env<T, E, F>(&mut self, f: F) -> Result<T, E>
    where
        F: FnOnce(&mut Self) -> Result<T, E>,
    {
        self.push_env();
        let result = f(self);
        let _child = self
            .execution_stack
            .last_mut()
            .and_then(|frame| frame.local_environment_stack.pop())
            .expect("local environment should exist after push_env");
        self.statement_proof_state.pop_scope();
        result
    }

    /// Runs a closure in an isolated child environment and returns that child
    /// on success instead of committing or discarding it.
    pub fn run_in_local_env_and_take<T, E, F>(&mut self, f: F) -> Result<(T, Environment), E>
    where
        F: FnOnce(&mut Self) -> Result<T, E>,
    {
        self.push_env();
        let result = f(self);
        let child = self
            .execution_stack
            .last_mut()
            .and_then(|frame| frame.local_environment_stack.pop())
            .expect("local environment should exist after push_env");
        self.statement_proof_state.pop_scope();
        result.map(|value| (value, *child))
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
        self.statement_proof_state.pop_scope();

        if result.is_ok() {
            self.current_parse_context_mut()
                .restore_scoped_state(parse_context_before);
        } else {
            *self.current_parse_context_mut() = parse_context_before;
        }

        let value = result?;
        self.top_level_env().merge_committed_child(*child)?;
        Ok(value)
    }

    /// Restores the current frame's scoped parsing state after `f` so parse-time bindings (e.g.
    /// `have x …` without `=`) do not leak across sibling `?` goal blocks or out of nested parses
    /// that use this wrapper (`forall`, `exist`, goal blocks, `prop` bodies, etc.). Successful
    /// parses retain SymbolId-indexed notation metadata owned by the source frame.
    pub fn run_in_local_parsing_time_name_scope<T, E, F>(&mut self, f: F) -> Result<T, E>
    where
        F: FnOnce(&mut Self) -> Result<T, E>,
    {
        let saved_parse_context = self.current_parse_context().clone();
        let result = f(self);
        if result.is_ok() {
            self.current_parse_context_mut()
                .restore_scoped_state(saved_parse_context);
        } else {
            *self.current_parse_context_mut() = saved_parse_context;
        }
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
        self.begin_parsing_scope(BindingScope::DefinitionBinding, names, line_file)
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
                return Err(super::symbols::active_parse_name_error(name, &line_file));
            }
            if let Some(external) = self.bare_symbol(name) {
                return Err(super::symbols::bare_symbol_name_reserved_error(
                    name,
                    external,
                    Some(line_file.clone()),
                ));
            }
        }
        self.current_parse_context_mut().free_params.begin_scope(
            BindingScope::DefinitionBinding,
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
        scope: BindingScope,
        names: &[String],
        line_file: LineFile,
        f: F,
    ) -> Result<T, RuntimeError>
    where
        F: FnOnce(&mut Self) -> Result<T, RuntimeError>,
    {
        self.begin_parsing_scope(scope, names, line_file)?;
        let result = f(self);
        self.end_parsing_scope(names);
        result
    }

    pub fn parse_in_local_free_param_scope_with_bindings<T, F>(
        &mut self,
        scope: BindingScope,
        names: &[String],
        line_file: LineFile,
        f: F,
    ) -> Result<(T, Vec<SymbolBinding>), RuntimeError>
    where
        F: FnOnce(&mut Self) -> Result<T, RuntimeError>,
    {
        let bindings = self.begin_parsing_scope(scope, names, line_file)?;
        let result = f(self);
        self.end_parsing_scope(names);
        result.map(|value| (value, bindings))
    }

    pub fn parse_in_existing_free_param_scope<T, F>(
        &mut self,
        scope: BindingScope,
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
            if scope.respects_bare_symbols(binding.name()) {
                if let Some(external) = self.bare_symbol(binding.name()) {
                    return Err(super::symbols::bare_symbol_name_reserved_error(
                        binding.name(),
                        external,
                        Some(line_file.clone()),
                    ));
                }
            }
            if let Some(active) = self.current_parse_context().active_binding(binding.name()) {
                if active.id() != binding.id() {
                    return Err(super::symbols::active_parse_name_error(
                        binding.name(),
                        &line_file,
                    ));
                }
            }
            if let Some(visible) = self.visible_symbol_definition(binding.name()) {
                if visible.binding().id() != binding.id() {
                    return Err(super::symbols::active_parse_name_error(
                        binding.name(),
                        &line_file,
                    ));
                }
            }
        }
        self.current_parse_context_mut()
            .free_params
            .begin_scope(scope, bindings, line_file)?;
        self.current_parse_context_mut()
            .push_scope_frame(bindings.to_vec());
        let result = parse_body(self);
        self.end_parsing_scope(&names);
        result
    }

    pub fn parse_stmts_with_existing_free_param_bindings<F>(
        &mut self,
        scope: BindingScope,
        bindings: &[SymbolBinding],
        line_file: LineFile,
        parse_body: F,
    ) -> Result<Vec<Stmt>, RuntimeError>
    where
        F: FnOnce(&mut Self) -> Result<Vec<Stmt>, RuntimeError>,
    {
        self.run_in_local_proof_parsing_scope(|this| {
            this.parse_in_existing_free_param_scope(scope, bindings, line_file, parse_body)
        })
    }

    pub fn parse_stmts_with_free_param_scope_and_bindings<F>(
        &mut self,
        scope: BindingScope,
        names: &[String],
        line_file: LineFile,
        parse_body: F,
    ) -> Result<(Vec<Stmt>, Vec<SymbolBinding>), RuntimeError>
    where
        F: FnOnce(&mut Self) -> Result<Vec<Stmt>, RuntimeError>,
    {
        self.run_in_local_proof_parsing_scope(|this| {
            this.parse_in_local_free_param_scope_with_bindings(scope, names, line_file, parse_body)
        })
    }
}
