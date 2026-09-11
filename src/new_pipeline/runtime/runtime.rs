//! Runtime state for the new execution pipeline.
//!
//! This module is intentionally independent from the legacy runtime.  The
//! runner owns the `tokenize -> parse -> execute` stages; this file owns the
//! state and lifecycle those stages share.

use super::runtime_ids::{AtomId, FactId, Id, PropAlgebraicPropertyId2, WellDefinednessId2};
use crate::new_pipeline::execution_environment::exec_env::ExecEnv;
use crate::new_pipeline::module_manager::module_manager::{
    ExportFileAndItsExecEnv, ModuleHierarchy, ModuleManager,
};
use std::collections::HashMap;
use std::path::{Path, PathBuf};

// -----------------------------------------------------------------------------
// Public configuration and error types
// -----------------------------------------------------------------------------

/// The two deliberately separate execution pipelines.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RunMode {
    /// Proof-bearing execution.  This is the first implemented path.
    Verified,
    /// Future fast path.  It must never be an implicit fallback from Verified.
    Unverified,
}

/// The source target supported by the new runner.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RunTarget {
    /// `litex -e <code>`.
    Eval(String),
    /// `litex -f <file>`.
    File(PathBuf),
    /// `litex -r <module>`; kept as a boundary for the later implementation.
    Repository(PathBuf),
}

/// Options produced by the command-line `run` entry point.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RunOptions {
    pub target: RunTarget,
    pub mode: RunMode,
}

impl RunOptions {
    pub fn eval(code: impl Into<String>) -> Self {
        Self {
            target: RunTarget::Eval(code.into()),
            mode: RunMode::Verified,
        }
    }

    pub fn verified_file(path: impl Into<PathBuf>) -> Self {
        Self {
            target: RunTarget::File(path.into()),
            mode: RunMode::Verified,
        }
    }

    pub fn unverified_file(path: impl Into<PathBuf>) -> Self {
        Self {
            target: RunTarget::File(path.into()),
            mode: RunMode::Unverified,
        }
    }

    pub fn repository(path: impl Into<PathBuf>) -> Self {
        Self {
            target: RunTarget::Repository(path.into()),
            mode: RunMode::Verified,
        }
    }
}

/// Runtime-wide options.  More output settings can be added here when the
/// new result renderer is designed; they do not belong to the file lifecycle.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RuntimeOptions {
    pub mode: RunMode,
}

impl Default for RuntimeOptions {
    fn default() -> Self {
        Self {
            mode: RunMode::Verified,
        }
    }
}

/// Errors used by the new pipeline scaffold.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PipelineError {
    InvalidArguments(String),
    Io { path: PathBuf, message: String },
    Unsupported(String),
    Invariant(String),
}

pub type PipelineResult<T> = Result<T, PipelineError>;

// -----------------------------------------------------------------------------
// Parse and file handoff types
// -----------------------------------------------------------------------------

/// Parse-only atom placeholder.  It is deliberately not an execution object.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Atom {
    pub spelling: String,
}

/// Scope used by the parser for binders such as `fn`, `forall`, and `exist`.
#[derive(Clone, Debug, Default)]
pub struct ParseScope {
    pub symbol_to_atom_id: HashMap<String, AtomId>,
    pub atom_id_to_atom: HashMap<AtomId, Atom>,
}

/// Metadata for the file currently being processed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CurrentFile {
    pub name: String,
    pub path: PathBuf,
}

impl CurrentFile {
    pub fn new(path: impl Into<PathBuf>) -> Self {
        let path = path.into();
        let name = path
            .file_name()
            .and_then(|name| name.to_str())
            .map(str::to_owned)
            .unwrap_or_else(|| path.to_string_lossy().into_owned());
        Self { name, path }
    }
}

/// The successful handoff from the runtime stack to `ModuleManager`.
///
/// This is never optional.  It can only be constructed after a file has one
/// top-level environment left on the stack.
pub struct CompletedFile {
    pub name: String,
    pub path: PathBuf,
    pub exec_env: Box<ExecEnv>,
}

// -----------------------------------------------------------------------------
// Runtime state
// -----------------------------------------------------------------------------

/// Mutable state shared by one new-pipeline invocation.
pub struct Runtime {
    pub runtime_options: RuntimeOptions,

    /// Recursive config/module tree.  Completed file environments are owned
    /// by this tree, not copied into a global environment.
    pub module_manager: ModuleManager,

    /// Transient trust state for the active file.
    pub is_current_file_trusted: bool,

    /// Empty between files.  Element zero is the file environment; additional
    /// elements are dynamic child scopes.
    pub execution_environments_stack: Vec<Box<ExecEnv>>,

    /// Independent parser scopes; these never create `ExecEnv`s.
    pub parse_scope_stack: Vec<Box<ParseScope>>,

    pub current_file: Option<CurrentFile>,

    /// Runtime-owned monotone ID counters.
    next_fact_id: Id,
    next_well_definedness_id: Id,
    next_atom_id: Id,
    next_symbol_id: Id,
    next_prop_algebraic_property_id: PropAlgebraicPropertyId2,
}

// -----------------------------------------------------------------------------
// Construction and identity allocation
// -----------------------------------------------------------------------------

impl Runtime {
    /// Create a runtime with no active file and no root `ExecEnv`.
    pub fn new(runtime_options: RuntimeOptions) -> Self {
        Self {
            runtime_options,
            module_manager: ModuleManager::new(ModuleHierarchy::Module),
            is_current_file_trusted: false,
            execution_environments_stack: Vec::new(),
            parse_scope_stack: Vec::new(),
            current_file: None,
            next_fact_id: 1,
            next_well_definedness_id: 1,
            next_atom_id: 1,
            next_symbol_id: 1,
            next_prop_algebraic_property_id: 1,
        }
    }

    pub fn from_run_options(options: &RunOptions) -> Self {
        Self::new(RuntimeOptions { mode: options.mode })
    }

    fn next_id(counter: &mut Id, label: &str) -> Id {
        let current = *counter;
        *counter = current
            .checked_add(1)
            .unwrap_or_else(|| panic!("{label} ID space exhausted"));
        current
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
}

// -----------------------------------------------------------------------------
// File and scope lifecycle
// -----------------------------------------------------------------------------

impl Runtime {
    /// Start one source.  Every source gets a fresh top-level `ExecEnv`.
    pub fn begin_file(&mut self, path: impl Into<PathBuf>, trusted: bool) {
        assert!(
            self.execution_environments_stack.is_empty(),
            "the execution stack must be empty before a file starts"
        );
        assert!(
            self.parse_scope_stack.is_empty(),
            "all parse scopes must be closed before a file starts"
        );
        self.current_file = Some(CurrentFile::new(path));
        self.is_current_file_trusted = trusted;
        self.execution_environments_stack.push(Box::new(ExecEnv::new()));
    }

    /// Finish one source and detach its top-level environment.
    pub fn finish_file(&mut self) -> CompletedFile {
        assert!(
            self.current_file.is_some(),
            "a file must be active before it can finish"
        );
        assert!(
            self.parse_scope_stack.is_empty(),
            "all parse scopes must be closed before a file finishes"
        );
        assert_eq!(
            self.execution_environments_stack.len(),
            1,
            "a file must finish with exactly one top-level execution environment"
        );

        let exec_env = self
            .execution_environments_stack
            .pop()
            .expect("the top-level file environment must exist");
        let file = self
            .current_file
            .take()
            .expect("the current file metadata must exist");
        self.is_current_file_trusted = false;
        CompletedFile {
            name: file.name,
            path: file.path,
            exec_env,
        }
    }

    /// Abort a failed source.  Its partial environment is never published.
    pub fn abort_file(&mut self) {
        self.execution_environments_stack.clear();
        self.parse_scope_stack.clear();
        self.current_file = None;
        self.is_current_file_trusted = false;
    }

    /// Publish a completed file.  The main `-f` file uses this same path.
    pub fn publish_completed_export_file(&mut self, completed: CompletedFile) {
        self.module_manager
            .record_export_file(ExportFileAndItsExecEnv::new(
                completed.name,
                completed.path,
                completed.exec_env,
            ));
    }

    /// Enter a dynamic child execution scope.
    pub fn push_execution_scope(&mut self) {
        assert!(
            !self.execution_environments_stack.is_empty(),
            "a child execution scope requires an active file"
        );
        self.execution_environments_stack.push(Box::new(ExecEnv::new()));
    }

    /// Leave a child scope.  The file's top-level environment is owned by
    /// `finish_file` and cannot be popped here.
    pub fn pop_execution_scope(&mut self) -> Box<ExecEnv> {
        assert!(
            self.execution_environments_stack.len() > 1,
            "the top-level file environment is not a child scope"
        );
        self.execution_environments_stack
            .pop()
            .expect("the child execution environment must exist")
    }

    pub fn current_execution_env(&self) -> &ExecEnv {
        self.execution_environments_stack
            .last()
            .map(Box::as_ref)
            .expect("an active execution environment is required")
    }

    pub fn current_execution_env_mut(&mut self) -> &mut ExecEnv {
        self.execution_environments_stack
            .last_mut()
            .map(Box::as_mut)
            .expect("an active execution environment is required")
    }

    /// Newest execution scope first, then its parents.  Module environments
    /// are not flattened into this iterator.
    pub fn visible_execution_environments(&self) -> impl Iterator<Item = &ExecEnv> {
        self.execution_environments_stack
            .iter()
            .rev()
            .map(Box::as_ref)
    }

    pub fn push_parse_scope(&mut self) {
        self.parse_scope_stack.push(Box::new(ParseScope::default()));
    }

    pub fn pop_parse_scope(&mut self) -> Box<ParseScope> {
        self.parse_scope_stack
            .pop()
            .expect("a parse scope must be active before it can be popped")
    }

    pub fn current_parse_scope(&self) -> &ParseScope {
        self.parse_scope_stack
            .last()
            .map(Box::as_ref)
            .expect("an active parse scope is required")
    }

    pub fn current_parse_scope_mut(&mut self) -> &mut ParseScope {
        self.parse_scope_stack
            .last_mut()
            .map(Box::as_mut)
            .expect("an active parse scope is required")
    }

    pub fn current_file_path(&self) -> Option<&Path> {
        self.current_file.as_ref().map(|file| file.path.as_path())
    }
}
