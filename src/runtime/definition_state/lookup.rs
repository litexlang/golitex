//! Definition lookup across the active module environment.

use crate::prelude::*;

impl Runtime {
    pub fn get_setting_definition_by_name(&self, setting_name: &str) -> Option<DefSettingStmt> {
        if let Some((module_name, local_name)) = split_module_qualified_name(setting_name) {
            if self.is_current_parse_module(module_name) {
                return self
                    .get_setting_definition_by_name_in_current_envs(local_name)
                    .cloned();
            }
            return self
                .imported_module_environments(module_name)
                .into_iter()
                .find_map(|environment| {
                    environment
                        .definitions
                        .setting_definitions
                        .get(local_name)
                        .cloned()
                });
        }

        self.get_setting_definition_by_name_in_current_envs(setting_name)
            .cloned()
    }

    fn get_setting_definition_by_name_in_current_envs(
        &self,
        setting_name: &str,
    ) -> Option<&DefSettingStmt> {
        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment
                .definitions
                .setting_definitions
                .get(setting_name)
            {
                return Some(definition);
            }
        }
        None
    }

    pub fn get_prop_definition_by_name(&self, predicate_name: &str) -> Option<DefPropStmt> {
        if let Some((module_name, local_name)) = split_module_qualified_name(predicate_name) {
            if self.is_current_parse_module(module_name) {
                return self
                    .get_prop_definition_by_name_in_current_envs(local_name)
                    .cloned();
            }
            return get_prop_definition_from_environments(
                self.imported_module_environments(module_name),
                local_name,
            );
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
            return get_prop_definition_from_environments(
                self.imported_module_environments(module_name),
                local_name,
            );
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
                    .definitions
                    .abstract_predicate_definitions
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
            return get_abstract_prop_definition_from_environments(
                self.imported_module_environments(module_name),
                local_name,
            );
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
                None if environment
                    .definitions
                    .predicate_definitions
                    .contains_key(predicate_name) =>
                {
                    return None
                }
                None => {}
            }
        }

        None
    }

    pub fn get_algo_definition_by_name(&self, algo_name: &str) -> Option<DefAlgoStmt> {
        if let Some((module_name, local_name)) = split_module_qualified_name(algo_name) {
            if self.is_current_parse_module(module_name) {
                return self
                    .get_algo_definition_by_name_in_current_envs(local_name)
                    .cloned();
            }
            return self
                .imported_module_environments(module_name)
                .into_iter()
                .find_map(|environment| {
                    environment
                        .definitions
                        .algorithm_definitions
                        .get(local_name)
                        .cloned()
                });
        }

        self.get_algo_definition_by_name_in_current_envs(algo_name)
            .cloned()
    }

    fn get_algo_definition_by_name_in_current_envs(&self, algo_name: &str) -> Option<&DefAlgoStmt> {
        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment.definitions.algorithm_definitions.get(algo_name) {
                return Some(definition);
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
                .imported_module_environments(module_name)
                .into_iter()
                .find_map(|environment| {
                    environment
                        .definitions
                        .structure_definitions
                        .get(local_name)
                        .cloned()
                });
        }

        self.get_struct_definition_by_name_in_current_envs(struct_name)
            .cloned()
    }

    fn get_struct_definition_by_name_in_current_envs(
        &self,
        struct_name: &str,
    ) -> Option<&DefStructStmt> {
        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment
                .definitions
                .structure_definitions
                .get(struct_name)
            {
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
                .imported_module_environments(module_name)
                .into_iter()
                .find_map(|environment| {
                    environment
                        .definitions
                        .template_definitions
                        .get(local_name)
                        .cloned()
                });
        }

        self.get_template_definition_by_name_in_current_envs(template_name)
            .cloned()
    }

    fn get_template_definition_by_name_in_current_envs(
        &self,
        template_name: &str,
    ) -> Option<&DefTemplateStmt> {
        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment
                .definitions
                .template_definitions
                .get(template_name)
            {
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
                .imported_module_environments(module_name)
                .into_iter()
                .find_map(|environment| {
                    environment
                        .definitions
                        .theorem_definitions
                        .get(local_name)
                        .cloned()
                });
        }

        self.get_thm_definition_by_name_in_current_envs(thm_name)
            .cloned()
    }

    fn get_thm_definition_by_name_in_current_envs(&self, thm_name: &str) -> Option<&DefThmStmt> {
        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment.definitions.theorem_definitions.get(thm_name) {
                return Some(definition);
            }
        }

        None
    }

    pub fn get_axiom_definition_by_name(&self, axiom_name: &str) -> Option<AxiomStmt> {
        if let Some((module_name, local_name)) = split_module_qualified_name(axiom_name) {
            if self.is_current_parse_module(module_name) {
                return self
                    .get_axiom_definition_by_name_in_current_envs(local_name)
                    .cloned();
            }
            return self
                .imported_module_environments(module_name)
                .into_iter()
                .find_map(|environment| {
                    environment
                        .definitions
                        .axiom_definitions
                        .get(local_name)
                        .cloned()
                });
        }

        self.get_axiom_definition_by_name_in_current_envs(axiom_name)
            .cloned()
    }

    fn get_axiom_definition_by_name_in_current_envs(&self, axiom_name: &str) -> Option<&AxiomStmt> {
        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment.definitions.axiom_definitions.get(axiom_name) {
                return Some(definition);
            }
        }

        None
    }

    pub fn get_thm_or_axiom_fact_by_name(&self, name: &str) -> Option<Fact> {
        if let Some(theorem) = self.get_thm_definition_by_name(name) {
            return Some(theorem.fact);
        }
        self.get_axiom_definition_by_name(name)
            .map(|axiom| axiom.forall_fact.into())
    }

    pub fn get_strategy_definition_by_name(&self, strategy_name: &str) -> Option<DefStrategyStmt> {
        if let Some((module_name, local_name)) = split_module_qualified_name(strategy_name) {
            if self.is_current_parse_module(module_name) {
                return self
                    .get_strategy_definition_by_name_in_current_envs(local_name)
                    .cloned();
            }
            return self
                .imported_module_environments(module_name)
                .into_iter()
                .find_map(|environment| {
                    environment
                        .definitions
                        .strategy_definitions
                        .get(local_name)
                        .cloned()
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
            if let Some(definition) = environment
                .definitions
                .strategy_definitions
                .get(strategy_name)
            {
                return Some(definition);
            }
        }

        None
    }
}

fn split_module_qualified_name(name: &str) -> Option<(&str, &str)> {
    name.rsplit_once(MOD_SIGN)
        .filter(|(module_name, local_name)| !module_name.is_empty() && !local_name.is_empty())
}

fn get_prop_definition_by_name_in_env(
    environment: &Environment,
    predicate_name: String,
) -> Option<&DefPropStmt> {
    if let Some(definition) = environment
        .definitions
        .predicate_definitions
        .get(predicate_name.as_str())
    {
        return Some(definition);
    }
    if environment
        .definitions
        .abstract_predicate_definitions
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
        .definitions
        .abstract_predicate_definitions
        .get(predicate_name.as_str())
    {
        return Some(definition);
    }
    if environment
        .definitions
        .predicate_definitions
        .contains_key(predicate_name.as_str())
    {
        return None;
    }
    None
}

fn get_prop_definition_from_environments(
    environments: Vec<&Environment>,
    predicate_name: &str,
) -> Option<DefPropStmt> {
    for environment in environments {
        if let Some(definition) = environment
            .definitions
            .predicate_definitions
            .get(predicate_name)
        {
            return Some(definition.clone());
        }
        if environment
            .definitions
            .abstract_predicate_definitions
            .contains_key(predicate_name)
        {
            return None;
        }
    }

    None
}

fn get_abstract_prop_definition_from_environments(
    environments: Vec<&Environment>,
    predicate_name: &str,
) -> Option<DefAbstractPropStmt> {
    for environment in environments {
        if let Some(definition) = environment
            .definitions
            .abstract_predicate_definitions
            .get(predicate_name)
        {
            return Some(definition.clone());
        }
        if environment
            .definitions
            .predicate_definitions
            .contains_key(predicate_name)
        {
            return None;
        }
    }

    None
}
