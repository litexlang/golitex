use crate::prelude::*;

impl Runtime {
    pub fn store_def_prop(&mut self, def_prop_stmt: &DefPropStmt) -> Result<(), RuntimeError> {
        let name = def_prop_stmt.name.clone();
        let env = self.top_level_env();
        if env.defined_def_props.contains_key(&name) {
            return Err(name_already_used_error(&name, "prop"));
        }
        if env.defined_abstract_props.contains_key(&name) {
            return Err(name_already_used_error(&name, "abstract_prop"));
        }
        self.register_declared_symbol(&name, SymbolRole::Predicate)?;
        let env = self.top_level_env();
        env.defined_def_props.insert(name, def_prop_stmt.clone());
        Ok(())
    }

    pub fn store_def_abstract_prop(
        &mut self,
        def_abstract_prop_stmt: &DefAbstractPropStmt,
    ) -> Result<(), RuntimeError> {
        let name = def_abstract_prop_stmt.name.clone();
        let env = self.top_level_env();
        if env.defined_abstract_props.contains_key(&name) {
            return Err(name_already_used_error(&name, "abstract_prop"));
        }
        if env.defined_def_props.contains_key(&name) {
            return Err(name_already_used_error(&name, "prop"));
        }
        self.register_declared_symbol(&name, SymbolRole::AbstractPredicate)?;
        let env = self.top_level_env();
        env.defined_abstract_props
            .insert(name, def_abstract_prop_stmt.clone());
        Ok(())
    }

    pub fn store_def_algo(&mut self, def_algo_stmt: &DefAlgoStmt) -> Result<(), RuntimeError> {
        let name = def_algo_stmt.name.clone();
        let env = self.top_level_env();
        if env.defined_algorithms.contains_key(&name) {
            return Err(name_already_used_error(&name, "algorithm implementation"));
        }
        env.defined_algorithms.insert(name, def_algo_stmt.clone());
        Ok(())
    }

    pub fn store_def_struct(
        &mut self,
        def_struct_stmt: &DefStructStmt,
    ) -> Result<(), RuntimeError> {
        let name = def_struct_stmt.name.clone();
        let env = self.top_level_env();
        if env.defined_structs.contains_key(&name) {
            return Err(name_already_used_error(&name, "struct"));
        }
        self.register_declared_symbol(&name, SymbolRole::Structure)?;
        let env = self.top_level_env();
        env.defined_structs.insert(name, def_struct_stmt.clone());
        Ok(())
    }

    pub fn store_def_template(
        &mut self,
        def_template_stmt: &DefTemplateStmt,
    ) -> Result<(), RuntimeError> {
        let name = def_template_stmt.template_name.clone();
        let env = self.top_level_env();
        if env.defined_templates.contains_key(&name) {
            return Err(name_already_used_error(&name, "template"));
        }
        self.register_declared_symbol(&name, SymbolRole::Template)?;
        let env = self.top_level_env();
        env.defined_templates
            .insert(name, def_template_stmt.clone());
        Ok(())
    }

    pub fn store_def_thm(&mut self, def_thm_stmt: &DefThmStmt) -> Result<(), RuntimeError> {
        self.store_def_thm_with_trust(def_thm_stmt, &ProofTrustSummary::new())
    }

    pub fn store_def_thm_with_trust(
        &mut self,
        def_thm_stmt: &DefThmStmt,
        trust_summary: &ProofTrustSummary,
    ) -> Result<(), RuntimeError> {
        let mut trust_summary = trust_summary.clone();
        trust_summary.merge(&self.current_trusted_prefix_statement_trust());
        if self
            .top_level_env()
            .defined_thm_stmts
            .contains_key(&def_thm_stmt.name)
        {
            return Err(name_already_used_error(&def_thm_stmt.name, "thm"));
        }
        let role = match def_thm_stmt.kind {
            DefThmKind::Theorem => SymbolRole::Theorem,
            DefThmKind::Axiom => SymbolRole::Axiom,
        };
        self.register_declared_symbol(&def_thm_stmt.name, role)?;
        let env = self.top_level_env();
        env.defined_thm_stmts
            .insert(def_thm_stmt.name.clone(), def_thm_stmt.clone());
        if !trust_summary.is_empty() {
            env.defined_thm_trust_summaries
                .insert(def_thm_stmt.name.clone(), trust_summary);
        }
        Ok(())
    }

    pub fn store_def_strategy(
        &mut self,
        def_strategy_stmt: &DefStrategyStmt,
    ) -> Result<(), RuntimeError> {
        if self
            .top_level_env()
            .defined_strategy_stmts
            .contains_key(&def_strategy_stmt.name)
        {
            return Err(name_already_used_error(&def_strategy_stmt.name, "strategy"));
        }
        self.register_declared_symbol(&def_strategy_stmt.name, SymbolRole::Strategy)?;
        let env = self.top_level_env();
        env.defined_strategy_stmts
            .insert(def_strategy_stmt.name.clone(), def_strategy_stmt.clone());
        Ok(())
    }

    pub fn store_free_param_or_identifier_name(
        &mut self,
        name: &str,
        kind: ParamObjType,
    ) -> Result<(), RuntimeError> {
        if let Some(existing_kind) = self.top_level_env().defined_identifiers.get(name) {
            return Err(NameAlreadyUsedRuntimeError(RuntimeErrorStruct::new_with_just_msg(format!(
                    "identifier `{}` is already bound in this scope as {:?} (cannot re-bind as {:?})",
                    name, existing_kind, kind
                )))
            .into());
        }
        if kind == ParamObjType::Identifier {
            self.register_declared_symbol(name, SymbolRole::Object)?;
        }
        let env = self.top_level_env();
        env.defined_identifiers.insert(name.to_string(), kind);
        Ok(())
    }

    pub fn store_parameter_binding(
        &mut self,
        binding: &SymbolBinding,
        kind: ParamObjType,
    ) -> Result<(), RuntimeError> {
        let name = binding.name();
        if let Some(existing_kind) = self.top_level_env().defined_identifiers.get(name) {
            return Err(
                NameAlreadyUsedRuntimeError(RuntimeErrorStruct::new_with_just_msg(format!(
                "identifier `{}` is already bound in this scope as {:?} (cannot re-bind as {:?})",
                name, existing_kind, kind
            )))
                .into(),
            );
        }
        let role = if kind == ParamObjType::Identifier {
            SymbolRole::Object
        } else {
            SymbolRole::Binder
        };
        self.register_existing_symbol_binding(binding.clone(), role)?;
        self.top_level_env()
            .defined_identifiers
            .insert(name.to_string(), kind);
        Ok(())
    }
}

fn name_already_used_error(name: &str, existing_namespace: &str) -> RuntimeError {
    NameAlreadyUsedRuntimeError(RuntimeErrorStruct::new_with_just_msg(format!(
        "name `{}` is already used in this scope as {}",
        name, existing_namespace
    )))
    .into()
}
