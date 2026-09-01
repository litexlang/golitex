use crate::prelude::*;

impl Runtime {
    pub fn store_def_setting(
        &mut self,
        def_setting_stmt: &DefSettingStmt,
    ) -> Result<(), RuntimeError> {
        let name = def_setting_stmt.name.clone();
        if self
            .top_level_env()
            .definitions
            .setting_definitions
            .contains_key(&name)
        {
            return Err(name_already_used_error(&name, "setting"));
        }
        self.register_definition_symbol(&name, SymbolRole::Setting)?;
        self.top_level_env()
            .definitions
            .setting_definitions
            .insert(name, def_setting_stmt.clone());
        Ok(())
    }

    pub fn store_def_prop(&mut self, def_prop_stmt: &DefPropStmt) -> Result<(), RuntimeError> {
        let name = def_prop_stmt.name.clone();
        let env = self.top_level_env();
        if env.definitions.predicate_definitions.contains_key(&name) {
            return Err(name_already_used_error(&name, "prop"));
        }
        if env
            .definitions
            .abstract_predicate_definitions
            .contains_key(&name)
        {
            return Err(name_already_used_error(&name, "abstract_prop"));
        }
        self.register_definition_symbol(&name, SymbolRole::Predicate)?;
        let env = self.top_level_env();
        env.definitions
            .predicate_definitions
            .insert(name, def_prop_stmt.clone());
        Ok(())
    }

    pub fn store_def_abstract_prop(
        &mut self,
        def_abstract_prop_stmt: &DefAbstractPropStmt,
    ) -> Result<(), RuntimeError> {
        let name = def_abstract_prop_stmt.name.clone();
        let env = self.top_level_env();
        if env
            .definitions
            .abstract_predicate_definitions
            .contains_key(&name)
        {
            return Err(name_already_used_error(&name, "abstract_prop"));
        }
        if env.definitions.predicate_definitions.contains_key(&name) {
            return Err(name_already_used_error(&name, "prop"));
        }
        self.register_definition_symbol(&name, SymbolRole::AbstractPredicate)?;
        let env = self.top_level_env();
        env.definitions
            .abstract_predicate_definitions
            .insert(name, def_abstract_prop_stmt.clone());
        Ok(())
    }

    pub fn store_def_algo(&mut self, def_algo_stmt: &DefAlgoStmt) -> Result<(), RuntimeError> {
        let name = def_algo_stmt.name.clone();
        let env = self.top_level_env();
        if env.definitions.algorithm_definitions.contains_key(&name) {
            return Err(name_already_used_error(&name, "algorithm implementation"));
        }
        env.definitions
            .algorithm_definitions
            .insert(name, def_algo_stmt.clone());
        Ok(())
    }

    pub fn store_def_struct(
        &mut self,
        def_struct_stmt: &DefStructStmt,
    ) -> Result<(), RuntimeError> {
        let name = def_struct_stmt.name.clone();
        let env = self.top_level_env();
        if env.definitions.structure_definitions.contains_key(&name) {
            return Err(name_already_used_error(&name, "struct"));
        }
        self.register_definition_symbol(&name, SymbolRole::Structure)?;
        let env = self.top_level_env();
        env.definitions
            .structure_definitions
            .insert(name, def_struct_stmt.clone());
        Ok(())
    }

    pub fn store_def_template(
        &mut self,
        def_template_stmt: &DefTemplateStmt,
    ) -> Result<(), RuntimeError> {
        let name = def_template_stmt.template_name.clone();
        let env = self.top_level_env();
        if env.definitions.template_definitions.contains_key(&name) {
            return Err(name_already_used_error(&name, "template"));
        }
        self.register_definition_symbol(&name, SymbolRole::Template)?;
        let env = self.top_level_env();
        env.definitions
            .template_definitions
            .insert(name, def_template_stmt.clone());
        Ok(())
    }

    pub fn store_def_thm(&mut self, def_thm_stmt: &DefThmStmt) -> Result<(), RuntimeError> {
        if self
            .top_level_env()
            .definitions
            .theorem_definitions
            .contains_key(&def_thm_stmt.name)
        {
            return Err(name_already_used_error(&def_thm_stmt.name, "thm"));
        }
        self.register_definition_symbol(&def_thm_stmt.name, SymbolRole::Theorem)?;
        let env = self.top_level_env();
        env.definitions
            .theorem_definitions
            .insert(def_thm_stmt.name.clone(), def_thm_stmt.clone());
        Ok(())
    }

    pub fn store_axiom(&mut self, axiom_stmt: &AxiomStmt) -> Result<(), RuntimeError> {
        if self
            .top_level_env()
            .definitions
            .axiom_definitions
            .contains_key(&axiom_stmt.name)
        {
            return Err(name_already_used_error(&axiom_stmt.name, "axiom"));
        }
        self.register_definition_symbol(&axiom_stmt.name, SymbolRole::Axiom)?;
        let env = self.top_level_env();
        env.definitions
            .axiom_definitions
            .insert(axiom_stmt.name.clone(), axiom_stmt.clone());
        Ok(())
    }

    pub fn store_def_strategy(
        &mut self,
        def_strategy_stmt: &DefStrategyStmt,
    ) -> Result<(), RuntimeError> {
        if self
            .top_level_env()
            .definitions
            .strategy_definitions
            .contains_key(&def_strategy_stmt.name)
        {
            return Err(name_already_used_error(&def_strategy_stmt.name, "strategy"));
        }
        self.register_definition_symbol(&def_strategy_stmt.name, SymbolRole::Strategy)?;
        let env = self.top_level_env();
        env.definitions
            .strategy_definitions
            .insert(def_strategy_stmt.name.clone(), def_strategy_stmt.clone());
        Ok(())
    }

    pub fn store_parameter_binding(
        &mut self,
        binding: &SymbolBinding,
        scope: BindingScope,
    ) -> Result<(), RuntimeError> {
        let role = match scope {
            BindingScope::DefinitionBinding => SymbolRole::Object,
            BindingScope::StructureField => SymbolRole::StructureField,
            BindingScope::LocalBinder | BindingScope::ReuseActiveBinder => SymbolRole::Binder,
        };
        self.register_existing_symbol_binding(binding.clone(), role)?;
        Ok(())
    }

    pub fn store_typed_parameter_binding(
        &mut self,
        binding: &SymbolBinding,
        scope: BindingScope,
        param_type: &ParamType,
    ) -> Result<(), RuntimeError> {
        self.store_parameter_binding(binding, scope)?;
        if let ParamType::Obj(Obj::StructObj(struct_obj)) = param_type {
            self.remember_direct_struct_carrier_for_binding(binding, struct_obj);
        }
        Ok(())
    }

    pub fn store_set_bound_parameter_binding(
        &mut self,
        binding: &SymbolBinding,
        scope: BindingScope,
        param_set: &Obj,
    ) -> Result<(), RuntimeError> {
        self.store_parameter_binding(binding, scope)?;
        if let Obj::StructObj(struct_obj) = param_set {
            self.remember_direct_struct_carrier_for_binding(binding, struct_obj);
        }
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
