use crate::prelude::*;

impl Runtime {
    pub fn store_def_prop_with_meaning(
        &mut self,
        def_prop_with_meaning_stmt: &DefPropWithMeaningStmt,
    ) -> Result<(), ExecStmtError> {
        let name = def_prop_with_meaning_stmt.name.clone();
        self.top_level_env()
            .defined_props_with_meaning
            .insert(name, def_prop_with_meaning_stmt.clone());
        Ok(())
    }

    pub fn store_def_prop_without_meaning(
        &mut self,
        def_prop_without_meaning_stmt: &DefPropWithoutMeaningStmt,
    ) -> Result<(), ExecStmtError> {
        let name = def_prop_without_meaning_stmt.name.clone();
        self.top_level_env()
            .defined_props_without_meaning
            .insert(name, def_prop_without_meaning_stmt.clone());
        Ok(())
    }

    pub fn store_def_algo(&mut self, def_algo_stmt: &DefAlgoStmt) -> Result<(), ExecStmtError> {
        let name = def_algo_stmt.name.clone();
        self.top_level_env()
            .defined_algorithms
            .insert(name, def_algo_stmt.clone());
        Ok(())
    }

    pub fn store_identifier_obj(&mut self, name: &str) -> Result<(), ExecStmtError> {
        self.top_level_env()
            .defined_identifier_and_field_access
            .insert(name.to_string(), ());
        Ok(())
    }

    pub fn store_def_struct_with_fields(
        &mut self,
        def_struct_with_fields_stmt: &DefStructWithFieldsStmt,
    ) -> Result<(), ExecStmtError> {
        let name = def_struct_with_fields_stmt.name.clone();
        self.top_level_env()
            .defined_structs_with_fields
            .insert(name, def_struct_with_fields_stmt.clone());
        Ok(())
    }

    pub fn store_def_struct_with_no_field(
        &mut self,
        def_struct_with_no_field_stmt: &DefStructWithNoFieldStmt,
    ) -> Result<(), ExecStmtError> {
        let name = def_struct_with_no_field_stmt.name.clone();
        self.top_level_env()
            .defined_structs_with_no_field
            .insert(name, def_struct_with_no_field_stmt.clone());
        Ok(())
    }
}
