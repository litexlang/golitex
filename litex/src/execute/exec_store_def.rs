use crate::error::{ExecError, WellDefinedError};
use crate::stmt::definition_stmt::{DefPropStmt, DefStructStmt};
use crate::stmt::define_algorithm_stmt::DefAlgoStmt;
use crate::common::keywords::{PROP, STRUCT, ALGO};
use super::Executor;
use crate::common::is_valid_litex_name::is_valid_litex_name;

impl<'a> Executor<'a> {
    pub fn validate_name_and_store_def_prop(&mut self, def_prop_stmt: &DefPropStmt) -> Result<(), ExecError> {
        if let Err(e) = self.validate_name(&def_prop_stmt.name) {
            return Err(ExecError::new(format!("invalid {} name", PROP).as_str(), vec![e.into()], def_prop_stmt.line_file_index));
        }
        let name = def_prop_stmt.name.clone();
        self.runtime_context.defined_props.insert(name.clone(), def_prop_stmt.clone());
        self.runtime_context.top_level_env().defined_props.insert(name, def_prop_stmt.clone());
        Ok(())
    }

    pub fn validate_name_and_store_def_algo(&mut self, def_algo_stmt: &DefAlgoStmt) -> Result<(), ExecError> {
        if let Err(e) = self.validate_name(&def_algo_stmt.name) {
            return Err(ExecError::new(format!("invalid {} name", ALGO).as_str(), vec![e.into()], def_algo_stmt.line_file_index));
        }
        let name = def_algo_stmt.name.clone();
        self.runtime_context.defined_algorithms.insert(name.clone(), def_algo_stmt.clone());
        self.runtime_context.top_level_env().defined_algorithms.insert(name, def_algo_stmt.clone());
        Ok(())
    }

    pub fn validate_name_and_store_identifier_obj(&mut self, name: &str) -> Result<(), ExecError> {
        if let Err(e) = self.validate_name(name) {
            return Err(ExecError::new(format!("invalid identifier name {}", name).as_str(), vec![e.into()], None));
        }
        self.runtime_context.defined_identifier_objs.insert(name.to_string(), ());
        self.runtime_context.top_level_env().defined_identifier_objs.insert(name.to_string(), ());
        Ok(())
    }
    
    pub fn validate_name_and_store_def_struct(&mut self, def_struct_stmt: &DefStructStmt) -> Result<(), ExecError> {
        let name = def_struct_stmt.name().to_string();
        if let Err(e) = self.validate_name(&name) {
            return Err(ExecError::new(format!("invalid {} name", STRUCT).as_str(), vec![e.into()], None)); }
            let name = def_struct_stmt.name().to_string();
        self.runtime_context.defined_structs.insert(name.clone(), def_struct_stmt.clone());
        self.runtime_context.top_level_env().defined_structs.insert(name, def_struct_stmt.clone());
        Ok(())
    }

    pub fn validate_name(&self, name: &str) -> Result<(), WellDefinedError> {
        if let Err(e) = is_valid_litex_name(name) {
            return Err(WellDefinedError::new(e.as_str(), vec![], None));
        }

        if self.runtime_context.is_name_used(name) {
            return Err(WellDefinedError::new(format!("name {} is already used", name).as_str(), vec![], None));
        }
        
        Ok(())
    }
}
