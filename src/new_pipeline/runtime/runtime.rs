use super::error::{RuntimeError, RuntimeResult};
use super::real_or_virtual_path::RealOrVirtualPath;
use super::runtime_ids::{FactId, IdentifierId, PropRewritePropertyId, WellDefinednessId};
use crate::new_pipeline::ast::names::{AtomicName, BoundName, PlainName};
use crate::new_pipeline::ast::obj::IdentifierObj;
use crate::new_pipeline::exec_env::exec_env::ExecEnv;
use crate::new_pipeline::launch_command::LaunchCommand;
use crate::new_pipeline::module_manager::{ExportFileAndItsExecEnv, GlobalModuleManager};
use std::collections::HashMap;

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
    pub execution_environments_stack: Vec<Box<ExecEnv>>,
    pub parse_scope_stack: Vec<Box<ParseScope>>,
    pub current_file: RealOrVirtualPath,
    pub global_ids: GlobalIds,
    /// How this Runtime session was launched (`-strict` / `-session` live here).
    pub launch_command: LaunchCommand,
    /// Export-file index of the `.lit` currently being parsed/run in the
    /// *current* module's `LitexConfig.exports` (0 for bare `-e` / `-f` / REPL).
    pub current_export_file_id: usize,
}

/// One parse layer's plain names → [`IdentifierId`].
/// Inner scopes must not reuse a visible outer plain name.
pub struct ParseScope {
    pub plain: HashMap<String, IdentifierId>,
}

/// Global monotonic id counters owned by `Runtime`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GlobalIds {
    next_fact_id: FactId,
    next_well_definedness_id: WellDefinednessId,
    next_prop_rewrite_property_id: PropRewritePropertyId,
    next_identifier_id: IdentifierId,
}

impl Runtime {
    /// Create a session from its launch contract and open the matching file env.
    pub fn new(command: LaunchCommand) -> Self {
        let file = match &command {
            LaunchCommand::Repl { .. } => RealOrVirtualPath::Repl,
            LaunchCommand::Eval { .. } => RealOrVirtualPath::Eval,
            LaunchCommand::File { path, .. } | LaunchCommand::Repository { path, .. } => {
                RealOrVirtualPath::Real(path.clone())
            }
            LaunchCommand::Help | LaunchCommand::Version => {
                panic!("Runtime::new does not accept Help/Version LaunchCommand")
            }
        };
        let mut runtime = Self {
            global_module_manager: GlobalModuleManager::new(),
            execution_environments_stack: Vec::new(),
            parse_scope_stack: Vec::new(),
            current_file: file.clone(),
            global_ids: GlobalIds::new(),
            launch_command: command,
            current_export_file_id: 0,
        };
        runtime.begin_file(file);
        runtime
    }

    pub fn begin_file(&mut self, file: RealOrVirtualPath) {
        self.current_file = file;
        self.execution_environments_stack
            .push(Box::new(ExecEnv::new(self.global_ids.clone())));
        self.push_parse_scope();
    }

    /// Set which export slot of the current module is being parsed/run.
    pub fn set_current_export_file_id(&mut self, export_file_id: usize) {
        self.current_export_file_id = export_file_id;
    }

    pub fn finish_file(&mut self) -> (RealOrVirtualPath, Box<ExecEnv>) {
        let file = self.current_file.clone();
        let mut exec_env = self
            .execution_environments_stack
            .pop()
            .expect("no file ExecEnv");
        exec_env.global_ids_at_leave = Some(self.global_ids.clone());
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

    pub fn plain_atom_is_visible(&self, name: &str) -> bool {
        for scope in &self.parse_scope_stack {
            if scope.plain.contains_key(name) {
                return true;
            }
        }
        false
    }

    pub fn resolve_plain_atom(&self, name: &str) -> RuntimeResult<IdentifierId> {
        Ok(self.resolve_plain_atom_with_scope_index(name)?.0)
    }

    /// Resolve a plain name and report which parse-scope index holds it.
    /// Index `0` is the file-root scope pushed by `begin_file`.
    pub fn resolve_plain_atom_with_scope_index(
        &self,
        name: &str,
    ) -> RuntimeResult<(IdentifierId, usize)> {
        for (scope_index, scope) in self.parse_scope_stack.iter().enumerate().rev() {
            if let Some(id) = scope.plain.get(name) {
                return Ok((*id, scope_index));
            }
        }
        Err(RuntimeError::InternalBug(format!(
            "undefined name `{name}`"
        )))
    }

    /// True when `name` is bound in the file-root parse scope (scope 0).
    pub fn is_bound_in_file_root_parse_scope(&self, name: &str) -> bool {
        self.parse_scope_stack
            .first()
            .is_some_and(|scope| scope.plain.contains_key(name))
    }

    /// Global reference form for a file-root symbol (no IdentifierId).
    ///
    /// - root module: `WithExportFileId { current_export_file_id, name }`
    /// - inside imported mod: `WithModAndExportFileId { current_mod_id, … }`
    pub fn atomic_name_for_file_root_symbol(&self, name: PlainName) -> AtomicName {
        match self.global_module_manager.current_mod_id() {
            None => AtomicName::WithExportFileId {
                export_file_id: self.current_export_file_id,
                name,
            },
            Some(global_mod_id) => AtomicName::WithModAndExportFileId {
                global_mod_id,
                export_file_id: self.current_export_file_id,
                name,
            },
        }
    }

    pub fn identifier_obj_for_file_root_symbol(&self, name: PlainName) -> IdentifierObj {
        match self.atomic_name_for_file_root_symbol(name) {
            AtomicName::WithExportFileId {
                export_file_id,
                name,
            } => IdentifierObj::with_export_file_id(export_file_id, name),
            AtomicName::WithModAndExportFileId {
                global_mod_id,
                export_file_id,
                name,
            } => IdentifierObj::with_mod_and_export_file_id(global_mod_id, export_file_id, name),
            AtomicName::Plain { name } => {
                panic!("file-root symbol must not stay Plain: `{name}`")
            }
        }
    }

    /// Free reference: file-root binding → qualified; inner binding → Plain+id.
    pub fn identifier_obj_for_plain_free_ref(
        &self,
        name: String,
    ) -> RuntimeResult<IdentifierObj> {
        let (id, scope_index) = self.resolve_plain_atom_with_scope_index(&name)?;
        if scope_index == 0 {
            Ok(self.identifier_obj_for_file_root_symbol(name))
        } else {
            Ok(IdentifierObj::plain(id, name))
        }
    }

    /// Exec/store mention of a defined symbol: qualify iff it is a file-root name.
    pub fn identifier_obj_for_stored_mention(&self, bound: &BoundName) -> IdentifierObj {
        if self.is_bound_in_file_root_parse_scope(&bound.name) {
            self.identifier_obj_for_file_root_symbol(bound.name.clone())
        } else {
            IdentifierObj::from_bound_name(bound)
        }
    }

    /// Prop/atomic name free ref: file-root prop → qualified; else stay Plain.
    pub fn atomic_name_for_plain_prop_ref(&self, name: String) -> AtomicName {
        if self.is_bound_in_file_root_parse_scope(&name) {
            self.atomic_name_for_file_root_symbol(name)
        } else {
            AtomicName::Plain { name }
        }
    }

    // Allocate a new IdentifierId and occupy `name` in the current scope.
    pub fn define_plain_atom(&mut self, name: String) -> RuntimeResult<BoundName> {
        if self.plain_atom_is_visible(&name) {
            return Err(RuntimeError::InternalBug(format!(
                "name `{name}` is already bound in an enclosing parse scope"
            )));
        }
        let id = self.global_ids.allocate_identifier_id();
        let scope = self
            .parse_scope_stack
            .last_mut()
            .ok_or_else(|| RuntimeError::InternalBug("no parse scope".to_string()))?;
        scope.plain.insert(name.clone(), id);
        Ok(BoundName::new(id, name))
    }

    // Re-occupy an existing BoundName (e.g. re-open forall binders) without reallocating.
    pub fn occupy_bound_name(&mut self, bound: &BoundName) -> RuntimeResult<()> {
        if self.plain_atom_is_visible(&bound.name) {
            return Err(RuntimeError::InternalBug(format!(
                "name `{}` is already bound in an enclosing parse scope",
                bound.name
            )));
        }
        let scope = self
            .parse_scope_stack
            .last_mut()
            .ok_or_else(|| RuntimeError::InternalBug("no parse scope".to_string()))?;
        scope.plain.insert(bound.name.clone(), bound.id);
        Ok(())
    }

    /// Elaborate surface `::` segments using `global_module_manager.current_mod_id`.
    pub fn elaborate_name_parts(&self, parts: &[String]) -> RuntimeResult<AtomicName> {
        self.global_module_manager
            .elaborate_name_parts(parts)
            .map_err(RuntimeError::InternalBug)
    }

    /// Elaborate `a:::b` flatten sugar.
    pub fn elaborate_flat_import(&self, alias: &str, name: String) -> RuntimeResult<AtomicName> {
        self.global_module_manager
            .elaborate_flat_import(alias, name)
            .map_err(RuntimeError::InternalBug)
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
            .push(Box::new(ExecEnv::new(self.global_ids.clone())));
    }

    pub fn pop_local_exec_env(&mut self) -> Box<ExecEnv> {
        if self.execution_environments_stack.len() <= 1 {
            panic!("pop_local_exec_env: refusing to pop the file ExecEnv");
        }
        let mut exec_env = self
            .execution_environments_stack
            .pop()
            .expect("no local ExecEnv");
        exec_env.global_ids_at_leave = Some(self.global_ids.clone());
        exec_env
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
            plain: HashMap::new(),
        }
    }
}

impl GlobalIds {
    pub fn new() -> Self {
        Self {
            next_fact_id: FactId::new(1),
            next_well_definedness_id: WellDefinednessId::new(1),
            next_prop_rewrite_property_id: PropRewritePropertyId::new(1),
            next_identifier_id: IdentifierId::new(1),
        }
    }

    pub fn allocate_fact_id(&mut self) -> FactId {
        let current = self.next_fact_id;
        self.next_fact_id = current.add_one();
        current
    }

    pub fn allocate_well_definedness_id(&mut self) -> WellDefinednessId {
        let current = self.next_well_definedness_id;
        self.next_well_definedness_id = current.add_one();
        current
    }

    pub fn allocate_prop_rewrite_property_id(&mut self) -> PropRewritePropertyId {
        let current = self.next_prop_rewrite_property_id;
        self.next_prop_rewrite_property_id = current.add_one();
        current
    }

    pub fn allocate_identifier_id(&mut self) -> IdentifierId {
        let current = self.next_identifier_id;
        self.next_identifier_id = current.add_one();
        current
    }
}
