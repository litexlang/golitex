use crate::prelude::*;

impl Runtime {
    pub fn store_def_prop_with_meaning(
        &mut self,
        def_prop_with_meaning_stmt: &DefPropWithMeaningStmt,
    ) -> Result<(), RuntimeErrorStruct> {
        let name = def_prop_with_meaning_stmt.name.clone();
        self.top_level_env()
            .defined_props_with_meaning
            .insert(name, def_prop_with_meaning_stmt.clone());
        Ok(())
    }

    pub fn store_def_abstract_prop(
        &mut self,
        def_abstract_prop_stmt: &DefAbstractPropStmt,
    ) -> Result<(), RuntimeErrorStruct> {
        let name = def_abstract_prop_stmt.name.clone();
        self.top_level_env()
            .defined_abstract_props
            .insert(name, def_abstract_prop_stmt.clone());
        Ok(())
    }

    pub fn store_def_algo(&mut self, def_algo_stmt: &DefAlgoStmt) -> Result<(), RuntimeErrorStruct> {
        let name = def_algo_stmt.name.clone();
        self.top_level_env()
            .defined_algorithms
            .insert(name, def_algo_stmt.clone());
        Ok(())
    }

    pub fn store_identifier_obj(&mut self, name: &str) -> Result<(), RuntimeErrorStruct> {
        self.top_level_env()
            .defined_identifiers
            .insert(name.to_string(), ());
        Ok(())
    }

    pub fn store_struct_def(
        &mut self,
        def_param_type_struct_stmt: &DefParamTypeStructStmt,
    ) -> Result<(), RuntimeErrorStruct> {
        let name = def_param_type_struct_stmt.name.clone();

        self.top_level_env()
            .defined_structs
            .insert(name, def_param_type_struct_stmt.clone());
        Ok(())
    }

    pub fn store_def_family(
        &mut self,
        def_family_stmt: &DefFamilyStmt,
    ) -> Result<(), RuntimeErrorStruct> {
        let name = def_family_stmt.name.clone();
        self.top_level_env()
            .defined_families
            .insert(name, def_family_stmt.clone());
        Ok(())
    }
}
