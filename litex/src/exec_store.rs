use crate::errors::ExecError;
use crate::executor::Executor;
use crate::definition_stmt::{DefPropStmt, DefStructStmt};
use crate::define_algorithm_stmt::DefAlgoStmt;
use crate::keywords::{PROP, STRUCT, ALGO};

impl<'a> Executor<'a> {
    pub fn validate_name_and_store_def_prop(&mut self, def_prop_stmt: DefPropStmt) -> Result<(), ExecError> {
        if !self.validate_name(&def_prop_stmt.name) {
            return Err(ExecError::new(format!("invalid {} name", PROP).as_str()));
        }
        let name = def_prop_stmt.name.clone();
        self.runtime_context.defined_props.insert(name.clone(), def_prop_stmt.clone());
        self.runtime_context.top_level_env().defined_props.insert(name, def_prop_stmt);
        Ok(())
    }

    pub fn validate_name_and_store_def_algo(&mut self, def_algo_stmt: DefAlgoStmt) -> Result<(), ExecError> {
        if !self.validate_name(&def_algo_stmt.name) {
            return Err(ExecError::new(format!("invalid {} name", ALGO).as_str()));
        }
        let name = def_algo_stmt.name.clone();
        self.runtime_context.defined_algorithms.insert(name.clone(), def_algo_stmt.clone());
        self.runtime_context.top_level_env().defined_algorithms.insert(name, def_algo_stmt);
        Ok(())
    }

    pub fn validate_name_and_store_atom_name(&mut self, atom_name: String) -> Result<(), ExecError> {
        if !self.validate_name(&atom_name) {
            return Err(ExecError::new("invalid atom name"));
        }
        self.runtime_context.defined_atom_names.insert(atom_name.clone(), ());
        self.runtime_context.top_level_env().defined_atom_names.insert(atom_name, ());
        Ok(())
    }

    pub fn validate_name_and_store_def_struct(&mut self, def_struct_stmt: DefStructStmt) -> Result<(), ExecError> {
        let name = def_struct_stmt.name().to_string();
        if !self.validate_name(&name) {
            return Err(ExecError::new(format!("invalid {} name", STRUCT).as_str()));
        }
        self.runtime_context.defined_structs.insert(name.clone(), def_struct_stmt.clone());
        self.runtime_context.top_level_env().defined_structs.insert(name, def_struct_stmt);
        Ok(())
    }

    pub fn validate_name(&self, _name: &str) -> bool {
        true
    }
}