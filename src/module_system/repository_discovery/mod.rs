use crate::prelude::*;
use std::collections::{HashMap, HashSet};
use std::env;
use std::fs;
use std::path::{Component, Path, PathBuf};
use std::rc::Rc;

const LITEX_CONFIG: &str = "litex.config";
const LITEX_TODO: &str = "todo.lit";
const LOCAL_DRAFTS: &str = ".drafts";
const LAKE_BUILD_DIRECTORY: &str = ".lake";

mod config_exports;
mod config_imports;
mod filesystem_paths;
mod import_cycles;
mod model;
mod module_config;
mod project_authorization;
mod project_config_files;
mod requested_target;
mod standard_library;
mod terminal_imports;

use config_exports::*;
use config_imports::*;
use filesystem_paths::*;
use import_cycles::*;
pub use model::RepositoryFileTarget;
use module_config::*;
use project_authorization::*;
use project_config_files::*;
pub use requested_target::{discover_repository, discover_repository_for_file};
use standard_library::discover_config_std_import;
pub use standard_library::{discover_terminal_std_import, resolve_std_root};
pub use terminal_imports::discover_terminal_module_import;
