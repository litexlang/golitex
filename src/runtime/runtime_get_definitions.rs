use crate::prelude::*;

impl Runtime {
    pub fn get_prop_definition_by_name(&self, predicate_name: &str) -> Option<&DefPropStmt> {
        let parts = predicate_name.split(MOD_SIGN).collect::<Vec<&str>>();
        if parts.len() != 1 {
            unimplemented!();
        }

        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment.defined_def_props.get(predicate_name) {
                return Some(definition);
            }
        }

        None
    }

    /// Look up abstract prop (`abstract_prop` keyword) definition by name from current env or builtin.
    pub fn get_abstract_prop_definition_by_name(
        &self,
        predicate_name: &str,
    ) -> Option<&DefAbstractPropStmt> {
        let parts = predicate_name.split(MOD_SIGN).collect::<Vec<&str>>();
        if parts.len() != 1 {
            unimplemented!();
        }

        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment.defined_abstract_props.get(predicate_name) {
                return Some(definition);
            }
        }

        None
    }

    pub fn get_algo_definition_by_name(&self, algo_name: &str) -> Option<&DefAlgoStmt> {
        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment.defined_algorithms.get(algo_name) {
                return Some(definition);
            }
        }
        None
    }

    pub fn get_struct_definition_by_name(&self, struct_name: &str) -> Option<&DefStructStmt> {
        let parts = struct_name.split(MOD_SIGN).collect::<Vec<&str>>();
        if parts.len() != 1 {
            unimplemented!();
        }

        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment.defined_structs.get(struct_name) {
                return Some(definition);
            }
        }

        None
    }

    pub fn get_template_definition_by_name(&self, template_name: &str) -> Option<&DefTemplateStmt> {
        let parts = template_name.split(MOD_SIGN).collect::<Vec<&str>>();
        if parts.len() != 1 {
            unimplemented!();
        }

        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment.defined_templates.get(template_name) {
                return Some(definition);
            }
        }

        None
    }
}
