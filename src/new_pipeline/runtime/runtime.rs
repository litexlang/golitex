use super::runtime_ids::{AtomId, FactId, Id, PropAlgebraicPropertyId2, WellDefinednessId2};
use crate::new_pipeline::execution_environment::exec_env::ExecEnv;
use crate::new_pipeline::module_manager::{
    ExportFileAndItsExecEnv, ModuleHierarchy, ModuleManager,
};
use std::collections::HashMap;
use std::path::{Path, PathBuf};

pub struct ParseScope {
    pub symbol_to_atom_id: HashMap<String, AtomId>,
    pub atom_id_to_atom: HashMap<AtomId, String>,
}

impl ParseScope {
    pub fn new() -> Self {
        Self {
            symbol_to_atom_id: HashMap::new(),
            atom_id_to_atom: HashMap::new(),
        }
    }
}

pub struct Runtime {
    pub is_current_file_trusted: bool,
    pub module_manager: ModuleManager,
    pub execution_environments_stack: Vec<Box<ExecEnv>>,
    pub parse_scope_stack: Vec<Box<ParseScope>>,
    pub current_file_path: Option<PathBuf>,
    next_fact_id: Id,
    next_well_definedness_id: Id,
    next_atom_id: Id,
    next_symbol_id: Id,
    next_prop_algebraic_property_id: PropAlgebraicPropertyId2,
}

impl Runtime {
    pub fn new() -> Self {
        Self {
            is_current_file_trusted: false,
            module_manager: ModuleManager::new(ModuleHierarchy::Module),
            execution_environments_stack: Vec::new(),
            parse_scope_stack: Vec::new(),
            current_file_path: None,
            next_fact_id: 1,
            next_well_definedness_id: 1,
            next_atom_id: 1,
            next_symbol_id: 1,
            next_prop_algebraic_property_id: 1,
        }
    }

    pub fn begin_file(&mut self, path: impl Into<PathBuf>, trusted: bool) {
        self.current_file_path = Some(path.into());
        self.is_current_file_trusted = trusted;
        self.execution_environments_stack
            .push(Box::new(ExecEnv::new()));
    }

    pub fn finish_file(&mut self) -> (PathBuf, Box<ExecEnv>) {
        let path = self.current_file_path.take().expect("no active file");
        let exec_env = self
            .execution_environments_stack
            .pop()
            .expect("no file ExecEnv");
        self.is_current_file_trusted = false;
        (path, exec_env)
    }

    pub fn abort_file(&mut self) {
        self.execution_environments_stack.clear();
        self.parse_scope_stack.clear();
        self.current_file_path = None;
        self.is_current_file_trusted = false;
    }

    pub fn publish_completed_export_file(&mut self, path: PathBuf, exec_env: Box<ExecEnv>) {
        let name = path
            .file_name()
            .and_then(|name| name.to_str())
            .map(str::to_owned)
            .unwrap_or_else(|| path.to_string_lossy().into_owned());
        self.module_manager
            .record_export_file(ExportFileAndItsExecEnv::new(name, path, exec_env));
    }

    pub fn current_file_path(&self) -> Option<&Path> {
        self.current_file_path.as_deref()
    }

    pub fn allocate_fact_id(&mut self) -> FactId {
        FactId::new(Self::next_id(&mut self.next_fact_id, "fact"))
    }

    pub fn allocate_well_definedness_id(&mut self) -> WellDefinednessId2 {
        WellDefinednessId2::new(Self::next_id(
            &mut self.next_well_definedness_id,
            "well-definedness",
        ))
    }

    pub fn allocate_atom_id(&mut self) -> AtomId {
        AtomId::new(Self::next_id(&mut self.next_atom_id, "atom"))
    }

    pub fn allocate_symbol_id(&mut self) -> Id {
        Self::next_id(&mut self.next_symbol_id, "symbol")
    }

    pub fn allocate_prop_algebraic_property_id(&mut self) -> PropAlgebraicPropertyId2 {
        let current = self.next_prop_algebraic_property_id;
        self.next_prop_algebraic_property_id = current
            .checked_add(1)
            .unwrap_or_else(|| panic!("predicate algebraic-property ID space exhausted"));
        current
    }

    fn next_id(counter: &mut Id, label: &str) -> Id {
        let current = *counter;
        *counter = current
            .checked_add(1)
            .unwrap_or_else(|| panic!("{label} ID space exhausted"));
        current
    }
}
