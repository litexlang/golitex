use crate::prelude::*;

impl Runtime {
    pub fn get_predicate_with_meaning_definition_by_name(
        &self,
        predicate_name: &str,
    ) -> Option<&DefPropWithMeaningStmt> {
        let parts = predicate_name.split(MOD_SIGN).collect::<Vec<&str>>();
        if parts.len() != 1 {
            unimplemented!();
        }

        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment.defined_props_with_meaning.get(predicate_name) {
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
            if let Some(definition) = environment
                .defined_abstract_props
                .get(predicate_name)
            {
                return Some(definition);
            }
        }

        None
    }

    pub fn get_cloned_param_type_struct_definition_by_name(
        &self,
        param_type_struct_name: &str,
    ) -> Option<DefParamTypeStructStmt> {
        let parts = param_type_struct_name.split(MOD_SIGN).collect::<Vec<&str>>();
        if parts.len() != 1 {
            unimplemented!();
        }

        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment
                .defined_structs
                .get(param_type_struct_name)
            {
                return Some(definition.clone());
            }
        }

        None
    }

    pub fn get_obj_in_struct(
        &self,
        struct_name: &str,
    ) -> Option<&StructParamType> {
        let parts = struct_name.split(MOD_SIGN).collect::<Vec<&str>>();
        if parts.len() != 1 {
            unimplemented!();
        }

        for environment in self.iter_environments_from_top() {
            if let Some(t) = environment.defined_field_access_name.get(struct_name) {
                return Some(&t);
            }
        }

        None
    }
    
    pub fn get_param_type_struct_definition_by_name(
        &self,
        param_type_struct_name: &str,
    ) -> Option<&DefParamTypeStructStmt> {
        let parts = param_type_struct_name.split(MOD_SIGN).collect::<Vec<&str>>();
        if parts.len() != 1 {
            unimplemented!();
        }

        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment
                .defined_structs
                .get(param_type_struct_name)
            {
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

    pub fn get_family_definition_by_name(
        &self,
        family_name: &str,
    ) -> Option<&DefFamilyStmt> {
        let parts = family_name.split(MOD_SIGN).collect::<Vec<&str>>();
        if parts.len() != 1 {
            unimplemented!();
        }

        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment.defined_families.get(family_name) {
                return Some(definition);
            }
        }

        None
    }

    pub fn get_cloned_family_definition_by_name(
        &self,
        family_name: &str,
    ) -> Option<DefFamilyStmt> {
        let parts = family_name.split(MOD_SIGN).collect::<Vec<&str>>();
        if parts.len() != 1 {
            unimplemented!();
        }

        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment.defined_families.get(family_name) {
                return Some(definition.clone());
            }
        }

        None
    }
}
