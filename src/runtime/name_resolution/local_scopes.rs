//! Runtime-owned parser scopes and current-source local environments.

use crate::prelude::*;

impl Runtime {
    fn current_source_target(&self) -> (ModuleId, SourceId) {
        (
            self.current_module_id
                .expect("a current source should always exist"),
            self.current_source_id
                .expect("a current source should always exist"),
        )
    }

    pub fn top_level_env(&mut self) -> &mut Environment {
        if !self.local_scopes.is_empty() {
            return self
                .local_scopes
                .last_mut()
                .map(|environment| environment.as_mut())
                .expect("local environment should exist");
        }

        let (module_id, source_id) = self.current_source_target();
        self.module_manager
            .module_mut(module_id)
            .and_then(|module| module.source_mut(source_id))
            .map(|source| source.environment.as_mut())
            .expect("current source environment should exist")
    }
}

impl Runtime {
    fn push_env(&mut self) {
        self.local_scopes
            .push(Box::new(Environment::new_empty_env()));
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
            .local_scopes
            .pop()
            .expect("local environment should exist after push_env");
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
            .local_scopes
            .pop()
            .expect("local environment should exist after push_env");
        result.map(|value| (value, *child))
    }

    /// Runs a closure in a temporary child environment. On success, commits the child environment
    /// into the parent with environment merge semantics; on failure, discards it. The closure must
    /// not mutate module discovery or loading state.
    pub fn run_in_local_env_and_commit<T, F>(&mut self, f: F) -> Result<T, RuntimeError>
    where
        F: FnOnce(&mut Self) -> Result<T, RuntimeError>,
    {
        self.push_env();
        let result = f(self);
        let child = self
            .local_scopes
            .pop()
            .expect("local environment should exist after push_env");

        let value = result?;
        self.top_level_env().merge_committed_child(*child)?;
        Ok(value)
    }

    /// Restores the current frame's scoped parsing state after `f` so parse-time bindings (e.g.
    /// `have x …` without `=`) do not leak across sibling `?` goal blocks or out of nested parses
    /// that use this wrapper (`forall`, `exist`, goal blocks, `prop` bodies, etc.). Successful
    /// parses retain only non-scoped parser metadata owned by the current source.
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
