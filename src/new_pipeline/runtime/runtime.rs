use super::error::{RuntimeError, RuntimeResult};
use super::real_or_virtual_path::RealOrVirtualPath;
use super::runtime_ids::{FactId, PropAlgebraicPropertyId, WellDefinednessId};
use crate::new_pipeline::exec_env::exec_env::ExecEnv;
use crate::new_pipeline::module_manager::{
    ExportFileAndItsExecEnv, ModuleHierarchy, ModuleManager,
};
use std::collections::HashSet;

// -----------------------------------------------------------------------------
// Core data model
// -----------------------------------------------------------------------------

/// Process-wide owner of new_pipeline execution and parse state.
///
/// Like `ExecEnv`, this is core data model: it owns the live stacks, current
/// file, global id counters, and module manager.  A single `Runtime` drives
/// one interpreter session; `ExecEnv` instances on
/// `execution_environments_stack` are the per-scope stores it pushes and pops.
pub struct Runtime {
    pub is_current_file_trusted: bool,
    pub module_manager: ModuleManager,
    pub execution_environments_stack: Vec<Box<ExecEnv>>,
    pub parse_scope_stack: Vec<Box<ParseScope>>,
    pub current_file: RealOrVirtualPath,
    pub ids: Ids,
}

/// Name occupied in a parse scope. Plain `x` and `mod::x` are distinct.
///
/// Under the locked name-is-identity premise (`identifier_identity.md`), this
/// name *is* the symbol identity.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum OccupiedName {
    Plain(String),
    WithMod { mod_name: String, name: String },
}

/// One parse layer's occupied names. Inner scopes must not reuse a visible outer name.
pub struct ParseScope {
    pub occupied: HashSet<OccupiedName>,
}

/// Global monotonic id counters owned by `Runtime` (facts / WD / prop properties).
pub struct Ids {
    next_fact_id: FactId,
    next_well_definedness_id: WellDefinednessId,
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
            if scope.occupied.contains(key) {
                return true;
            }
        }
        false
    }

    // Occupy `key` in the current scope (name is identity; no per-occurrence id).
    pub fn define_atom(&mut self, key: OccupiedName) -> RuntimeResult<()> {
        if let OccupiedName::Plain(name) = &key {
            if crate::new_pipeline::ast::obj::is_binder_slot_name(name) {
                return Err(RuntimeError::Invariant(format!(
                    "binder-slot name `{name}` cannot be occupied as a free atom"
                )));
            }
        }
        if self.occupied_name_is_visible(&key) {
            return Err(RuntimeError::Invariant(format!(
                "name `{key}` is already bound in an enclosing parse scope"
            )));
        }
        let scope = self
            .parse_scope_stack
            .last_mut()
            .ok_or_else(|| RuntimeError::Invariant("no parse scope".to_string()))?;
        scope.occupied.insert(key);
        Ok(())
    }

    // Occupy an already-known name in the current scope (e.g. re-open forall binders).
    pub fn occupy_atom(&mut self, key: OccupiedName) -> RuntimeResult<()> {
        if let OccupiedName::Plain(name) = &key {
            if crate::new_pipeline::ast::obj::is_binder_slot_name(name) {
                return Err(RuntimeError::Invariant(format!(
                    "binder-slot name `{name}` cannot be occupied as a free atom"
                )));
            }
        }
        if self.occupied_name_is_visible(&key) {
            return Err(RuntimeError::Invariant(format!(
                "name `{key}` is already bound in an enclosing parse scope"
            )));
        }
        let scope = self
            .parse_scope_stack
            .last_mut()
            .ok_or_else(|| RuntimeError::Invariant("no parse scope".to_string()))?;
        scope.occupied.insert(key);
        Ok(())
    }

    pub fn define_plain_atom(&mut self, name: String) -> RuntimeResult<()> {
        self.define_atom(OccupiedName::Plain(name))
    }

    pub fn occupy_plain_atom(&mut self, name: String) -> RuntimeResult<()> {
        self.occupy_atom(OccupiedName::Plain(name))
    }

    pub fn plain_atom_is_visible(&self, name: &str) -> bool {
        self.occupied_name_is_visible(&OccupiedName::Plain(name.to_string()))
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
            occupied: HashSet::new(),
        }
    }
}

impl Ids {
    pub fn new() -> Self {
        Self {
            next_fact_id: FactId::new(1),
            next_well_definedness_id: WellDefinednessId::new(1),
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
