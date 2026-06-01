use crate::prelude::*;

impl Runtime {
    pub fn get_prop_definition_by_name(&self, predicate_name: &str) -> Option<DefPropStmt> {
        if let Some((module_name, local_name)) = split_module_qualified_name(predicate_name) {
            if self.is_current_parse_module(module_name) {
                return self
                    .get_prop_definition_by_name_in_current_envs(local_name)
                    .cloned();
            }
            return self
                .imported_module_environment(module_name)
                .and_then(|environment| {
                    get_prop_definition_by_name_in_env(environment.as_ref(), local_name.to_string())
                        .cloned()
                });
        }

        self.get_prop_definition_by_name_in_current_envs(predicate_name)
            .cloned()
    }

    pub fn get_active_prop_definition_by_name(&self, predicate_name: &str) -> Option<DefPropStmt> {
        if let Some((module_name, local_name)) = split_module_qualified_name(predicate_name) {
            if self.is_current_parse_module(module_name) {
                return self
                    .get_prop_definition_by_name_in_current_envs(local_name)
                    .cloned();
            }
            return self
                .active_imported_module_environment(module_name)
                .and_then(|environment| {
                    get_prop_definition_by_name_in_env(environment.as_ref(), local_name.to_string())
                        .cloned()
                });
        }

        self.get_prop_definition_by_name_in_current_envs(predicate_name)
            .cloned()
    }

    fn get_prop_definition_by_name_in_current_envs(
        &self,
        predicate_name: &str,
    ) -> Option<&DefPropStmt> {
        for environment in self.iter_environments_from_top() {
            match get_prop_definition_by_name_in_env(environment, predicate_name.to_string()) {
                Some(definition) => return Some(definition),
                None if environment
                    .defined_abstract_props
                    .contains_key(predicate_name) =>
                {
                    return None
                }
                None => {}
            }
        }

        None
    }

    /// Look up abstract prop (`abstract_prop` keyword) definition by name from current env or builtin.
    pub fn get_abstract_prop_definition_by_name(
        &self,
        predicate_name: &str,
    ) -> Option<DefAbstractPropStmt> {
        if let Some((module_name, local_name)) = split_module_qualified_name(predicate_name) {
            if self.is_current_parse_module(module_name) {
                return self
                    .get_abstract_prop_definition_by_name_in_current_envs(local_name)
                    .cloned();
            }
            return self
                .imported_module_environment(module_name)
                .and_then(|environment| {
                    get_abstract_prop_definition_by_name_in_env(
                        environment.as_ref(),
                        local_name.to_string(),
                    )
                    .cloned()
                });
        }

        self.get_abstract_prop_definition_by_name_in_current_envs(predicate_name)
            .cloned()
    }

    fn get_abstract_prop_definition_by_name_in_current_envs(
        &self,
        predicate_name: &str,
    ) -> Option<&DefAbstractPropStmt> {
        for environment in self.iter_environments_from_top() {
            match get_abstract_prop_definition_by_name_in_env(
                environment,
                predicate_name.to_string(),
            ) {
                Some(definition) => return Some(definition),
                None if environment.defined_def_props.contains_key(predicate_name) => return None,
                None => {}
            }
        }

        None
    }

    pub fn get_algo_definition_by_name(&self, algo_name: &str) -> Option<DefAlgoStmt> {
        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment.defined_algorithms.get(algo_name) {
                return Some(definition.clone());
            }
        }
        None
    }

    pub fn get_struct_definition_by_name(&self, struct_name: &str) -> Option<DefStructStmt> {
        if let Some((module_name, local_name)) = split_module_qualified_name(struct_name) {
            if self.is_current_parse_module(module_name) {
                return self
                    .get_struct_definition_by_name_in_current_envs(local_name)
                    .cloned();
            }
            return self
                .imported_module_environment(module_name)
                .and_then(|environment| environment.defined_structs.get(local_name).cloned());
        }

        self.get_struct_definition_by_name_in_current_envs(struct_name)
            .cloned()
    }

    fn get_struct_definition_by_name_in_current_envs(
        &self,
        struct_name: &str,
    ) -> Option<&DefStructStmt> {
        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment.defined_structs.get(struct_name) {
                return Some(definition);
            }
        }

        None
    }

    pub fn get_template_definition_by_name(&self, template_name: &str) -> Option<DefTemplateStmt> {
        if let Some((module_name, local_name)) = split_module_qualified_name(template_name) {
            if self.is_current_parse_module(module_name) {
                return self
                    .get_template_definition_by_name_in_current_envs(local_name)
                    .cloned();
            }
            return self
                .imported_module_environment(module_name)
                .and_then(|environment| environment.defined_templates.get(local_name).cloned());
        }

        self.get_template_definition_by_name_in_current_envs(template_name)
            .cloned()
    }

    fn get_template_definition_by_name_in_current_envs(
        &self,
        template_name: &str,
    ) -> Option<&DefTemplateStmt> {
        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment.defined_templates.get(template_name) {
                return Some(definition);
            }
        }

        None
    }

    pub fn get_thm_definition_by_name(&self, thm_name: &str) -> Option<DefThmStmt> {
        if let Some((module_name, local_name)) = split_module_qualified_name(thm_name) {
            if self.is_current_parse_module(module_name) {
                return self
                    .get_thm_definition_by_name_in_current_envs(local_name)
                    .cloned();
            }
            return self
                .imported_module_environment(module_name)
                .and_then(|environment| environment.defined_thm_stmts.get(local_name).cloned());
        }

        self.get_thm_definition_by_name_in_current_envs(thm_name)
            .cloned()
    }

    fn get_thm_definition_by_name_in_current_envs(&self, thm_name: &str) -> Option<&DefThmStmt> {
        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment.defined_thm_stmts.get(thm_name) {
                return Some(definition);
            }
        }

        None
    }

    pub fn get_strategy_definition_by_name(&self, strategy_name: &str) -> Option<DefStrategyStmt> {
        if let Some((module_name, local_name)) = split_module_qualified_name(strategy_name) {
            if self.is_current_parse_module(module_name) {
                return self
                    .get_strategy_definition_by_name_in_current_envs(local_name)
                    .cloned();
            }
            return self
                .imported_module_environment(module_name)
                .and_then(|environment| {
                    environment.defined_strategy_stmts.get(local_name).cloned()
                });
        }

        self.get_strategy_definition_by_name_in_current_envs(strategy_name)
            .cloned()
    }

    fn get_strategy_definition_by_name_in_current_envs(
        &self,
        strategy_name: &str,
    ) -> Option<&DefStrategyStmt> {
        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment.defined_strategy_stmts.get(strategy_name) {
                return Some(definition);
            }
        }

        None
    }
}

fn split_module_qualified_name(name: &str) -> Option<(&str, &str)> {
    let parts = name.split(MOD_SIGN).collect::<Vec<&str>>();
    if parts.len() == 2 && !parts[0].is_empty() && !parts[1].is_empty() {
        Some((parts[0], parts[1]))
    } else {
        None
    }
}

fn get_prop_definition_by_name_in_env(
    environment: &Environment,
    predicate_name: String,
) -> Option<&DefPropStmt> {
    if let Some(definition) = environment.defined_def_props.get(predicate_name.as_str()) {
        return Some(definition);
    }
    if environment
        .defined_abstract_props
        .contains_key(predicate_name.as_str())
    {
        return None;
    }
    None
}

fn get_abstract_prop_definition_by_name_in_env(
    environment: &Environment,
    predicate_name: String,
) -> Option<&DefAbstractPropStmt> {
    if let Some(definition) = environment
        .defined_abstract_props
        .get(predicate_name.as_str())
    {
        return Some(definition);
    }
    if environment
        .defined_def_props
        .contains_key(predicate_name.as_str())
    {
        return None;
    }
    None
}
