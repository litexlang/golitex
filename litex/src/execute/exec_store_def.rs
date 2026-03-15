use crate::error::{ExecError, WellDefinedError};
use crate::stmt::definition_stmt::{DefPropStmt, DefPropWithoutMeaningStmt, DefStructWithFieldsStmt, DefStructWithNoFieldStmt};
use crate::stmt::define_algorithm_stmt::DefAlgoStmt;
use crate::common::keywords::{PROP, STRUCT, ALGO};
use super::Executor;
use crate::common::is_valid_litex_name::is_valid_litex_name;

impl<'a> Executor<'a> {
    pub fn validate_name_and_store_def_prop(&mut self, def_prop_stmt: &DefPropStmt) -> Result<(), ExecError> {
        if let Err(e) = self.validate_name(&def_prop_stmt.name) {
            return Err(ExecError::new(format!("invalid {} name", PROP), vec![e.into()], def_prop_stmt.line_file_index));
        }
        let name = def_prop_stmt.name.clone();
        self.runtime_context.defined_props.insert(name.clone(), def_prop_stmt.clone());
        self.runtime_context.top_level_env().defined_props.insert(name, def_prop_stmt.clone());
        Ok(())
    }

    pub fn validate_name_and_store_def_prop_without_meaning(&mut self, def_prop_without_meaning_stmt: &DefPropWithoutMeaningStmt) -> Result<(), ExecError> {
        if let Err(e) = self.validate_name(&def_prop_without_meaning_stmt.name) {
            return Err(ExecError::new(format!("invalid {} name", PROP), vec![e.into()], def_prop_without_meaning_stmt.line_file_index));
        }
        let name = def_prop_without_meaning_stmt.name.clone();
        self.runtime_context.defined_props_without_meaning.insert(name.clone(), def_prop_without_meaning_stmt.clone());
        self.runtime_context.top_level_env().defined_props_without_meaning.insert(name, def_prop_without_meaning_stmt.clone());
        Ok(())
    }

    pub fn validate_name_and_store_def_algo(&mut self, def_algo_stmt: &DefAlgoStmt) -> Result<(), ExecError> {
        if let Err(e) = self.validate_name(&def_algo_stmt.name) {
            return Err(ExecError::new(format!("invalid {} name", ALGO), vec![e.into()], def_algo_stmt.line_file_index));
        }
        let name = def_algo_stmt.name.clone();
        self.runtime_context.defined_algorithms.insert(name.clone(), def_algo_stmt.clone());
        self.runtime_context.top_level_env().defined_algorithms.insert(name, def_algo_stmt.clone());
        Ok(())
    }

    pub fn validate_name_and_store_identifier_obj(&mut self, name: &str) -> Result<(), ExecError> {
        if let Err(e) = self.validate_name(name) {
            return Err(ExecError::new(format!("invalid identifier name {}", name), vec![e.into()], None));
        }
        self.runtime_context.defined_identifier_objs.insert(name.to_string(), ());
        self.runtime_context.top_level_env().defined_identifier_objs.insert(name.to_string(), ());
        Ok(())
    }
    
    pub fn validate_name_and_store_def_struct_with_fields(&mut self, def_struct_with_fields_stmt: &DefStructWithFieldsStmt) -> Result<(), ExecError> {
        let name = def_struct_with_fields_stmt.name.clone();
        if let Err(e) = self.validate_name(&name) {
            return Err(ExecError::new(format!("invalid {} name", STRUCT), vec![e.into()], def_struct_with_fields_stmt.line_file_index));
        }
        self.runtime_context.defined_structs_with_fields.insert(name.clone(), def_struct_with_fields_stmt.clone());
        self.runtime_context.top_level_env().defined_structs_with_fields.insert(name, def_struct_with_fields_stmt.clone());
        Ok(())
    }

    pub fn validate_name_and_store_def_struct_with_no_field(&mut self, def_struct_with_no_field_stmt: &DefStructWithNoFieldStmt) -> Result<(), ExecError> {
        let name = def_struct_with_no_field_stmt.name.clone();
        if let Err(e) = self.validate_name(&name) {
            return Err(ExecError::new(format!("invalid {} name", STRUCT), vec![e.into()], def_struct_with_no_field_stmt.line_file_index));
        }
        self.runtime_context.defined_structs_with_no_field.insert(name.clone(), def_struct_with_no_field_stmt.clone());
        self.runtime_context.top_level_env().defined_structs_with_no_field.insert(name, def_struct_with_no_field_stmt.clone());
        Ok(())
    }

    pub fn validate_name(&self, name: &str) -> Result<(), WellDefinedError> {
        if let Err(e) = is_valid_litex_name(name) {
            return Err(WellDefinedError::new(e.clone(), vec![], None));
        }

        if self.runtime_context.is_name_used(name) {
            return Err(WellDefinedError::new(format!("name {} is already used", name), vec![], None));
        }
        
        Ok(())
    }
}
