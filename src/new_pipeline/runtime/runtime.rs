use super::error::{RuntimeError, RuntimeResult};
use super::real_or_virtual_path::RealOrVirtualPath;
use super::runtime_ids::{FactId, PropAlgebraicPropertyId, WellDefinednessId};
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::exec_env::exec_env::ExecEnv;
use crate::new_pipeline::module_manager::{ExportFileAndItsExecEnv, GlobalModuleManager};
use std::collections::HashSet;

// -----------------------------------------------------------------------------
// Core data model
// -----------------------------------------------------------------------------

/// Process-wide owner of new_pipeline execution and parse state.
///
/// Like `ExecEnv`, this is core data model: it owns the live stacks, current
/// file, global id counters, and global module manager.  A single `Runtime` drives
/// one interpreter session; `ExecEnv` instances on
/// `execution_environments_stack` are the per-scope stores it pushes and pops.
pub struct Runtime {
    pub global_module_manager: GlobalModuleManager,
    /// Module owning the `.lit` currently parsed/run: `None` = root, `Some(i)` = `imports[i]`.
    pub current_mod_id: Option<usize>,
    pub execution_environments_stack: Vec<Box<ExecEnv>>,
    pub parse_scope_stack: Vec<Box<ParseScope>>,
    pub current_file: RealOrVirtualPath,
    pub ids: Ids,
}

/// One parse layer's occupied names. Inner scopes must not reuse a visible outer name.
///
/// Keys are `AtomicName` (plain / `file_id` / `mod_id`+`file_id`). Under the
/// locked identity premise, qualified atoms use indices from
/// `GlobalModuleManager`, not surface import aliases.
pub struct ParseScope {
    pub occupied: HashSet<AtomicName>,
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
            global_module_manager: GlobalModuleManager::new(),
            current_mod_id: None,
            execution_environments_stack: Vec::new(),
            parse_scope_stack: Vec::new(),
            current_file: RealOrVirtualPath::Eval,
            ids: Ids::new(),
        }
    }

    pub fn begin_file(&mut self, file: RealOrVirtualPath) {
        self.current_file = file;
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
        (file, exec_env)
    }

    pub fn abort_file(&mut self) {
        self.execution_environments_stack.clear();
        self.parse_scope_stack.clear();
    }

    pub fn publish_completed_export_file(
        &mut self,
        file: RealOrVirtualPath,
        exec_env: Box<ExecEnv>,
    ) {
        let name = file.name();
        let path = file.display_path();
        self.global_module_manager
            .record_root_export(ExportFileAndItsExecEnv::new(name, path, exec_env));
    }

    pub fn push_parse_scope(&mut self) {
        self.parse_scope_stack.push(Box::new(ParseScope::new()));
    }

    pub fn pop_parse_scope(&mut self) {
        self.parse_scope_stack
            .pop()
            .expect("parse scope stack empty");
    }

    pub fn occupied_name_is_visible(&self, key: &AtomicName) -> bool {
        for scope in &self.parse_scope_stack {
            if scope.occupied.contains(key) {
                return true;
            }
        }
        false
    }

    // Occupy `key` in the current scope (name is identity; no per-occurrence id).
    pub fn define_atom(&mut self, key: AtomicName) -> RuntimeResult<()> {
        if let AtomicName::Plain { name } = &key {
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
    pub fn occupy_atom(&mut self, key: AtomicName) -> RuntimeResult<()> {
        if let AtomicName::Plain { name } = &key {
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
        self.define_atom(AtomicName::plain(name))
    }

    pub fn occupy_plain_atom(&mut self, name: String) -> RuntimeResult<()> {
        self.occupy_atom(AtomicName::plain(name))
    }

    pub fn plain_atom_is_visible(&self, name: &str) -> bool {
        self.occupied_name_is_visible(&AtomicName::plain(name.to_string()))
    }

    /// Elaborate surface `::` segments using `global_module_manager` + `current_mod_id`.
    pub fn elaborate_name_parts(&self, parts: &[String]) -> RuntimeResult<AtomicName> {
        self.global_module_manager
            .elaborate_name_parts(self.current_mod_id, parts)
            .map_err(RuntimeError::Invariant)
    }

    /// Elaborate `a:::b` flatten sugar.
    pub fn elaborate_flat_import(&self, alias: &str, name: String) -> RuntimeResult<AtomicName> {
        self.global_module_manager
            .elaborate_flat_import(self.current_mod_id, alias, name)
            .map_err(RuntimeError::Invariant)
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
    pub fn run_in_local_env_and_take_env<T, F>(&mut self, f: F) -> RuntimeResult<(T, Box<ExecEnv>)>
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

fn bump(value: u64, label: &str) -> u64 {
    value
        .checked_add(1)
        .unwrap_or_else(|| panic!("{label} ID space exhausted"))
}
