use super::error::{RuntimeError, RuntimeResult};
use super::real_or_virtual_path::RealOrVirtualPath;
use super::runtime_ids::{FactId, PropAlgebraicPropertyId, SymbolId, WellDefinednessId};
use crate::new_pipeline::execution_environment::exec_env::ExecEnv;
use crate::new_pipeline::module_manager::{
    ExportFileAndItsExecEnv, ModuleHierarchy, ModuleManager,
};
use std::collections::HashSet;

// One parse layer's occupied names. Inner scopes must not reuse a visible outer name.
pub struct ParseScope {
    pub occupied: HashSet<String>,
}

pub struct Ids {
    next_fact_id: FactId,
    next_well_definedness_id: WellDefinednessId,
    next_symbol_id: SymbolId,
    next_prop_algebraic_property_id: PropAlgebraicPropertyId,
}

pub struct Runtime {
    pub is_current_file_trusted: bool,
    pub module_manager: ModuleManager,
    pub execution_environments_stack: Vec<Box<ExecEnv>>,
    pub parse_scope_stack: Vec<Box<ParseScope>>,
    pub current_file: RealOrVirtualPath,
    pub ids: Ids,
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
        self.parse_scope_stack
            .push(Box::new(ParseScope::new()));
    }

    pub fn pop_parse_scope(&mut self) {
        self.parse_scope_stack
            .pop()
            .expect("parse scope stack empty");
    }

    pub fn name_is_visible(&self, name: &str) -> bool {
        for scope in &self.parse_scope_stack {
            if scope.occupied.contains(name) {
                return true;
            }
        }
        false
    }

    // Reject if name is already visible in any outer or current scope (no shadowing).
    pub fn occupy_name(&mut self, name: String) -> RuntimeResult<()> {
        if self.name_is_visible(&name) {
            return Err(RuntimeError::Invariant(format!(
                "name `{name}` is already bound in an enclosing parse scope"
            )));
        }
        let scope = self
            .parse_scope_stack
            .last_mut()
            .ok_or_else(|| RuntimeError::Invariant("no parse scope".to_string()))?;
        scope.occupied.insert(name);
        Ok(())
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
            next_symbol_id: SymbolId::new(1),
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

    pub fn allocate_symbol_id(&mut self) -> SymbolId {
        let current = self.next_symbol_id;
        self.next_symbol_id = SymbolId::new(bump(current.value(), "symbol"));
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
