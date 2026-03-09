use crate::errors::{ExecError, StmtError};
use crate::fact::Fact;
use crate::stmt::parameter_type_and_property::ParamDefWithParamType;
use crate::stmt::definition_stmt::{DefPropStmt, DefStructStmt};
use crate::stmt::define_algorithm_stmt::DefAlgoStmt;
use crate::keywords::{PROP, STRUCT, ALGO};
use super::Executor;

impl<'a> Executor<'a> {
    pub fn validate_name_and_store_def_prop(&mut self, def_prop_stmt: &DefPropStmt) -> Result<(), ExecError> {
        if !self.validate_name(&def_prop_stmt.name) {
            return Err(ExecError::new(format!("invalid {} name", PROP).as_str(), vec![], def_prop_stmt.line_file_index));
        }
        let name = def_prop_stmt.name.clone();
        self.runtime_context.defined_props.insert(name.clone(), def_prop_stmt.clone());
        self.runtime_context.top_level_env().defined_props.insert(name, def_prop_stmt.clone());
        Ok(())
    }

    pub fn validate_name_and_store_def_algo(&mut self, def_algo_stmt: &DefAlgoStmt) -> Result<(), ExecError> {
        if !self.validate_name(&def_algo_stmt.name) {
            return Err(ExecError::new(format!("invalid {} name", ALGO).as_str(), vec![], def_algo_stmt.line_file_index));
        }
        let name = def_algo_stmt.name.clone();
        self.runtime_context.defined_algorithms.insert(name.clone(), def_algo_stmt.clone());
        self.runtime_context.top_level_env().defined_algorithms.insert(name, def_algo_stmt.clone());
        Ok(())
    }

    pub fn validate_name_and_store_atom_name(&mut self, arg_def: &Vec<ParamDefWithParamType>, line_file_index: Option<(usize, usize)>) -> Result<(), ExecError> {
        for param_def in arg_def.iter() {
            for name in param_def.0.iter() {
                if !self.validate_name(&name) {
                    if !self.validate_name(&name) {
                        return Err(ExecError::new("invalid atom name", vec![], line_file_index));
                    }
                    self.runtime_context.defined_atom_names.insert(name.clone(), ());
                    self.runtime_context.top_level_env().defined_atom_names.insert(name.clone(), ());
                }
            }
        }
        Ok(())
    }

    pub fn validate_name_and_store_def_struct(&mut self, def_struct_stmt: &DefStructStmt) -> Result<(), ExecError> {
        let name = def_struct_stmt.name().to_string();
        if !self.validate_name(&name) {
            return Err(ExecError::new(format!("invalid {} name", STRUCT).as_str(), vec![], def_struct_stmt.line_file_index())); }
        self.runtime_context.defined_structs.insert(name.clone(), def_struct_stmt.clone());
        self.runtime_context.top_level_env().defined_structs.insert(name, def_struct_stmt.clone());
        Ok(())
    }

    pub fn validate_name(&self, _name: &str) -> bool {
        true
    }
}

impl<'a> Executor<'a> {
    pub fn validate_and_store_fact(&mut self, fact: &Fact) -> Result<(), ExecError> {
        let result = self.runtime_context.environments.last_mut().unwrap().store_fact(fact.clone());
        if let Err(store_err) = result {
            return Err(ExecError::new(
                format!("store fact error: {}", store_err).as_str(),
                vec![StmtError::StoreFactError(store_err)],
                fact.line_file(),
            ));
        }
        Ok(())
    }
}
