use super::error::{RuntimeError, RuntimeResult};
use super::real_or_virtual_path::RealOrVirtualPath;
use super::runtime_ids::{FactId, IdentifierId, PropAlgebraicPropertyId, WellDefinednessId};
use crate::new_pipeline::exec_env::exec_env::ExecEnv;
use crate::new_pipeline::module_manager::{
    ExportFileAndItsExecEnv, ModuleHierarchy, ModuleManager,
};
use std::collections::HashMap;

pub struct Runtime {
    pub is_current_file_trusted: bool,
    pub module_manager: ModuleManager,
    pub execution_environments_stack: Vec<Box<ExecEnv>>,
    pub parse_scope_stack: Vec<Box<ParseScope>>,
    pub current_file: RealOrVirtualPath,
    pub ids: Ids,
}

// Name occupied in a parse scope. Plain `x` and `mod::x` are distinct.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum OccupiedName {
    Plain(String),
    WithMod { mod_name: String, name: String },
}

// One parse layer's occupied names. Inner scopes must not reuse a visible outer name.
pub struct ParseScope {
    pub occupied: HashMap<OccupiedName, IdentifierId>,
}

pub struct Ids {
    next_fact_id: FactId,
    next_well_definedness_id: WellDefinednessId,
    next_identifier_id: IdentifierId,
    next_prop_algebraic_property_id: PropAlgebraicPropertyId,
}

impl Runtime {
    pub fn new() -> Self {
        Self {
            is_current_file_trusted: false,
            module_manager: ModuleManager::new(ModuleHierarchy::Module),
            execution_environments_stack: Vec::new(),
            parse_scope_stack: Vec::new(),
            current_file: RealOrVirtualPath::Eval,
            ids: Ids::new(),
        }
    }

    pub fn begin_file(&mut self, file: RealOrVirtualPath, trusted: bool) {
        self.current_file = file;
        self.is_current_file_trusted = trusted;
        self.execution_environments_stack
            .push(Box::new(ExecEnv::new()));
        self.push_parse_scope();
    }

    pub fn finish_file(&mut self) -> (RealOrVirtualPath, Box<ExecEnv>) {
        let file = self.current_file.clone();
        let exec_env = self
            .execution_environments_stack
            .pop()
            .expect("no file ExecEnv");
        self.parse_scope_stack.clear();
        self.is_current_file_trusted = false;
        (file, exec_env)
    }

    pub fn abort_file(&mut self) {
        self.execution_environments_stack.clear();
        self.parse_scope_stack.clear();
        self.is_current_file_trusted = false;
    }

    pub fn publish_completed_export_file(
        &mut self,
        file: RealOrVirtualPath,
        exec_env: Box<ExecEnv>,
    ) {
        let name = file.name();
        let path = file.display_path();
        self.module_manager
            .record_export_file(ExportFileAndItsExecEnv::new(name, path, exec_env));
    }

    pub fn push_parse_scope(&mut self) {
        self.parse_scope_stack.push(Box::new(ParseScope::new()));
    }

    pub fn pop_parse_scope(&mut self) {
        self.parse_scope_stack
            .pop()
            .expect("parse scope stack empty");
    }

    pub fn occupied_name_is_visible(&self, key: &OccupiedName) -> bool {
        for scope in &self.parse_scope_stack {
            if scope.occupied.contains_key(key) {
                return true;
            }
        }
        false
    }

    pub fn lookup_identifier_id(&self, key: &OccupiedName) -> Option<IdentifierId> {
        for scope in self.parse_scope_stack.iter().rev() {
            if let Some(identifier_id) = scope.occupied.get(key) {
                return Some(*identifier_id);
            }
        }
        None
    }

    // Allocate a new global IdentifierId and occupy `key` in the current scope.
    pub fn define_atom(&mut self, key: OccupiedName) -> RuntimeResult<IdentifierId> {
        if self.occupied_name_is_visible(&key) {
            return Err(RuntimeError::Invariant(format!(
                "name `{key}` is already bound in an enclosing parse scope"
            )));
        }
        let identifier_id = self.ids.allocate_identifier_id();
        let scope = self
            .parse_scope_stack
            .last_mut()
            .ok_or_else(|| RuntimeError::Invariant("no parse scope".to_string()))?;
        scope.occupied.insert(key, identifier_id);
        Ok(identifier_id)
    }

    // Put an already-allocated IdentifierId into the current scope without allocating.
    pub fn occupy_atom(
        &mut self,
        key: OccupiedName,
        identifier_id: IdentifierId,
    ) -> RuntimeResult<()> {
        if self.occupied_name_is_visible(&key) {
            return Err(RuntimeError::Invariant(format!(
                "name `{key}` is already bound in an enclosing parse scope"
            )));
        }
        let scope = self
            .parse_scope_stack
            .last_mut()
            .ok_or_else(|| RuntimeError::Invariant("no parse scope".to_string()))?;
        scope.occupied.insert(key, identifier_id);
        Ok(())
    }

    pub fn define_plain_atom(&mut self, name: String) -> RuntimeResult<IdentifierId> {
        self.define_atom(OccupiedName::Plain(name))
    }

    pub fn occupy_plain_atom(
        &mut self,
        name: String,
        identifier_id: IdentifierId,
    ) -> RuntimeResult<()> {
        self.occupy_atom(OccupiedName::Plain(name), identifier_id)
    }

    pub fn lookup_plain_identifier_id(&self, name: &str) -> Option<IdentifierId> {
        self.lookup_identifier_id(&OccupiedName::Plain(name.to_string()))
    }

    pub fn top_exec_env(&self) -> &ExecEnv {
        self.execution_environments_stack
            .last()
            .expect("no ExecEnv")
    }

    pub fn top_exec_env_mut(&mut self) -> &mut ExecEnv {
        self.execution_environments_stack
            .last_mut()
            .expect("no ExecEnv")
    }

    // Child ExecEnv for a statement-local binder / WD scope. Uses the existing stack.
    pub fn push_local_exec_env(&mut self) {
        self.execution_environments_stack
            .push(Box::new(ExecEnv::new()));
    }

    pub fn pop_local_exec_env(&mut self) -> Box<ExecEnv> {
        if self.execution_environments_stack.len() <= 1 {
            panic!("pop_local_exec_env: refusing to pop the file ExecEnv");
        }
        self.execution_environments_stack
            .pop()
            .expect("no local ExecEnv")
    }

    // Run `f` in a fresh local ExecEnv; on success return (value, closed local env).
    // On error the local env is discarded.
    pub fn run_in_local_env_and_take<T, F>(&mut self, f: F) -> RuntimeResult<(T, Box<ExecEnv>)>
    where
        F: FnOnce(&mut Self) -> RuntimeResult<T>,
    {
        self.push_local_exec_env();
        match f(self) {
            Ok(value) => {
                let local_env = self.pop_local_exec_env();
                Ok((value, local_env))
            }
            Err(err) => {
                let _ = self.pop_local_exec_env();
                Err(err)
            }
        }
    }
}

impl ParseScope {
    pub fn new() -> Self {
        Self {
            occupied: HashMap::new(),
        }
    }
}

impl Ids {
    pub fn new() -> Self {
        Self {
            next_fact_id: FactId::new(1),
            next_well_definedness_id: WellDefinednessId::new(1),
            next_identifier_id: IdentifierId::new(1),
            next_prop_algebraic_property_id: PropAlgebraicPropertyId::new(1),
        }
    }

    pub fn allocate_fact_id(&mut self) -> FactId {
        let current = self.next_fact_id;
        self.next_fact_id = FactId::new(bump(current.value(), "fact"));
        current
    }

    pub fn allocate_well_definedness_id(&mut self) -> WellDefinednessId {
        let current = self.next_well_definedness_id;
        self.next_well_definedness_id =
            WellDefinednessId::new(bump(current.value(), "well-definedness"));
        current
    }

    pub fn allocate_identifier_id(&mut self) -> IdentifierId {
        let current = self.next_identifier_id;
        self.next_identifier_id = IdentifierId::new(bump(current.value(), "identifier"));
        current
    }

    pub fn allocate_prop_algebraic_property_id(&mut self) -> PropAlgebraicPropertyId {
        let current = self.next_prop_algebraic_property_id;
        self.next_prop_algebraic_property_id =
            PropAlgebraicPropertyId::new(bump(current.value(), "prop algebraic property"));
        current
    }
}

impl std::fmt::Display for OccupiedName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OccupiedName::Plain(name) => write!(f, "{name}"),
            OccupiedName::WithMod { mod_name, name } => write!(f, "{mod_name}::{name}"),
        }
    }
}

fn bump(value: u64, label: &str) -> u64 {
    value
        .checked_add(1)
        .unwrap_or_else(|| panic!("{label} ID space exhausted"))
}
