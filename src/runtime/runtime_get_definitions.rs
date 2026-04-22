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

    pub fn get_family_definition_by_name(&self, family_name: &str) -> Option<&DefFamilyStmt> {
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

    pub fn get_cloned_family_definition_by_name(&self, family_name: &str) -> Option<DefFamilyStmt> {
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

    pub fn get_definition_of_struct_where_object_satisfies(
        &self,
        obj: &AtomicName,
    ) -> Option<&DefStructStmt> {
        let Some(struct_object_satisfies) = self.get_object_satisfy_struct(obj) else {
            return None;
        };

        let Some(def) =
            self.get_definition_of_struct_by_name(&struct_object_satisfies.name.to_string())
        else {
            return None;
        };

        Some(def)
    }

    pub fn get_definition_of_struct_by_name(&self, struct_name: &str) -> Option<&DefStructStmt> {
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

    pub fn get_cloned_definition_of_struct(&self, struct_name: &str) -> Option<DefStructStmt> {
        let parts = struct_name.split(MOD_SIGN).collect::<Vec<&str>>();
        if parts.len() != 1 {
            unimplemented!();
        }

        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment.defined_structs.get(struct_name) {
                return Some(definition.clone());
            }
        }

        None
    }
}
