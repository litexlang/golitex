use super::code_source::CodeSource;
use super::error::{RuntimeError, RuntimeResult};
use super::real_or_virtual_path::RealOrVirtualPath;
use super::runtime_ids::{FactId, IdentifierId, PropRewritePropertyId, WellDefinednessId};
use crate::ast::names::{AtomicName, BoundName, PlainName};
use crate::ast::obj::IdentifierObj;
use crate::exec_env::exec_env::ExecEnv;
use crate::exec_env::session_view::ExecEnvSessionView;
use crate::launch_command::LaunchCommand;
use crate::module_manager::{ExportFileAndItsExecEnv, GlobalModuleManager};
use std::collections::HashMap;

// -----------------------------------------------------------------------------
// Core data model
// -----------------------------------------------------------------------------

/// Process-wide owner of execution and parse state.
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
    /// Where the currently running code came from (drives outermost symbol qualify).
    pub code_source: CodeSource,
}

/// One parse layer's plain names → [`IdentifierId`].
/// Inner scopes must not reuse a visible outer plain name.
pub struct ParseScope {
    pub plain: HashMap<String, IdentifierId>
}

/// Global monotonic id counters owned by `Runtime`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GlobalIds {
    next_fact_id: FactId,
    next_well_definedness_id: WellDefinednessId,
    next_prop_rewrite_property_id: PropRewritePropertyId,
    next_identifier_id: IdentifierId
}

impl Runtime {
    /// Create a session from its launch contract and open the matching file env.
    pub fn new(command: LaunchCommand) -> Self {
        let code_source = match &command {
            LaunchCommand::Eval { .. } => CodeSource::Eval,
            LaunchCommand::Repl { .. } => CodeSource::Repl,
            LaunchCommand::File { .. }
            | LaunchCommand::Repository { .. }
            | LaunchCommand::ExtractExecutableCode {
                input: crate::launch_command::ExtractInput::File(_)
                    | crate::launch_command::ExtractInput::Repository(_),
                ..
            }
            | LaunchCommand::CompileToLatex {
                input: crate::launch_command::LatexInput::File(_)
                    | crate::launch_command::LatexInput::Repository(_),
                ..
            } => CodeSource::StandaloneFile,
            LaunchCommand::ExtractExecutableCode {
                input: crate::launch_command::ExtractInput::Code(_),
                ..
            }
            | LaunchCommand::CompileToLatex {
                input: crate::launch_command::LatexInput::Code(_), ..
            } => CodeSource::Eval,
            LaunchCommand::Help { .. } | LaunchCommand::Version { .. } => {
                panic!("Runtime::new does not accept Help/Version LaunchCommand")
            }
        };
        let file = match &command {
            LaunchCommand::Repl { .. } => RealOrVirtualPath::Repl,
            LaunchCommand::Eval { .. }
            | LaunchCommand::ExtractExecutableCode {
                input: crate::launch_command::ExtractInput::Code(_),
                ..
            }
            | LaunchCommand::CompileToLatex {
                input: crate::launch_command::LatexInput::Code(_), ..
            } => RealOrVirtualPath::Eval,
            LaunchCommand::File { path, .. }
            | LaunchCommand::Repository { path, .. }
            | LaunchCommand::ExtractExecutableCode {
                input:
                    crate::launch_command::ExtractInput::File(path)
                    | crate::launch_command::ExtractInput::Repository(path),
                ..
            }
            | LaunchCommand::CompileToLatex {
                input: crate::launch_command::LatexInput::File(path)
                    | crate::launch_command::LatexInput::Repository(path),
                ..
            } => RealOrVirtualPath::Real(path.clone()),
            LaunchCommand::Help { .. } | LaunchCommand::Version { .. } => {
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
            code_source,
        };
        runtime.begin_file(file);
        runtime
    }

    pub fn begin_file(&mut self, file: RealOrVirtualPath) {
        self.current_file = file;
        let session_view =
            ExecEnvSessionView::new(self.global_ids.clone(), self.code_source.clone());
        self.execution_environments_stack
            .push(Box::new(ExecEnv::new(Some(session_view))));
        self.push_parse_scope();
    }

    pub fn set_code_source(&mut self, code_source: CodeSource) {
        self.code_source = code_source;
    }

    pub fn finish_file(&mut self) -> (RealOrVirtualPath, Box<ExecEnv>) {
        let file = self.current_file.clone();
        let mut exec_env = self
            .execution_environments_stack
            .pop()
            .expect("no file ExecEnv");
        if let Some(view) = exec_env.session_view.as_mut() {
            view.stamp_leave(self.global_ids.clone());
        }
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

    /// Outermost-scope symbol name form from live `code_source`.
    ///
    /// - `Eval` / `Repl` / `StandaloneFile` → `Plain` (no publication stamp)
    /// - `RootExport` → `WithExportFileId`
    /// - `ImportedExport` → `WithModAndExportFileId`
    pub fn atomic_name_for_file_root_symbol(&self, name: PlainName) -> AtomicName {
        match &self.code_source {
            CodeSource::Eval | CodeSource::Repl | CodeSource::StandaloneFile => {
                AtomicName::Plain { name }
            }
            CodeSource::RootExport { export_file_id } => AtomicName::WithExportFileId {
                export_file_id: *export_file_id,
                name
            },
            CodeSource::ImportedExport {
                global_mod_id,
                export_file_id
            } => AtomicName::WithModAndExportFileId {
                global_mod_id: *global_mod_id,
                export_file_id: *export_file_id,
                name
            }
        }
    }

    pub fn identifier_obj_for_file_root_symbol(&self, name: PlainName) -> IdentifierObj {
        match self.atomic_name_for_file_root_symbol(name.clone()) {
            AtomicName::Plain { name } => {
                let id = self
                    .resolve_plain_atom(&name)
                    .expect("file-root Plain symbol must be bound in parse scope");
                IdentifierObj::plain(id, name)
            }
            AtomicName::WithExportFileId {
                export_file_id,
                name
            } => IdentifierObj::with_export_file_id(export_file_id, name),
            AtomicName::WithModAndExportFileId {
                global_mod_id,
                export_file_id,
                name
            } => IdentifierObj::with_mod_and_export_file_id(global_mod_id, export_file_id, name)
        }
    }

    /// Free reference: outermost + promoting `code_source` → qualified;
    /// otherwise Plain+id (inner binders, or Eval/Repl/StandaloneFile outermost).
    pub fn identifier_obj_for_plain_free_ref(
        &self,
        name: String,
    ) -> RuntimeResult<IdentifierObj> {
        let (id, scope_index) = self.resolve_plain_atom_with_scope_index(&name)?;
        if scope_index == 0 && self.code_source.promotes_outermost_symbols() {
            Ok(self.identifier_obj_for_file_root_symbol(name))
        } else {
            Ok(IdentifierObj::plain(id, name))
        }
    }

    /// Qualify only the same file-root binding, never a local binding whose
    /// surface name happens to match a later file-root declaration.
    pub fn identifier_obj_for_stored_mention(&self, bound: &BoundName) -> IdentifierObj {
        if self
            .parse_scope_stack
            .first()
            .and_then(|scope| scope.plain.get(&bound.name))
            == Some(&bound.id)
            && self.code_source.promotes_outermost_symbols()
        {
            self.identifier_obj_for_file_root_symbol(bound.name.clone())
        } else {
            IdentifierObj::from_bound_name(bound)
        }
    }

    /// Prop/atomic name free ref: promote only when outermost and promoting.
    pub fn atomic_name_for_plain_prop_ref(&self, name: String) -> AtomicName {
        if self.is_bound_in_file_root_parse_scope(&name)
            && self.code_source.promotes_outermost_symbols()
        {
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
            .push(Box::new(ExecEnv::new(None)));
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
            plain: HashMap::new()
        }
    }
}

impl GlobalIds {
    pub fn new() -> Self {
        Self {
            next_fact_id: FactId::new(1),
            next_well_definedness_id: WellDefinednessId::new(1),
            next_prop_rewrite_property_id: PropRewritePropertyId::new(1),
            next_identifier_id: IdentifierId::new(1)
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

    /// KB / cache watermarks without exposing typed id fields.
    pub fn to_u64s(&self) -> (u64, u64, u64, u64) {
        (
            self.next_fact_id.value(),
            self.next_well_definedness_id.value(),
            self.next_prop_rewrite_property_id.value(),
            self.next_identifier_id.value(),
        )
    }

    pub fn from_u64s(
        next_fact_id: u64,
        next_well_definedness_id: u64,
        next_prop_rewrite_property_id: u64,
        next_identifier_id: u64,
    ) -> Self {
        Self {
            next_fact_id: FactId::new(next_fact_id),
            next_well_definedness_id: WellDefinednessId::new(next_well_definedness_id),
            next_prop_rewrite_property_id: PropRewritePropertyId::new(
                next_prop_rewrite_property_id,
            ),
            next_identifier_id: IdentifierId::new(next_identifier_id)
        }
    }
}
