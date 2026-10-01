//! Detailed JSON projection: field-isomorphic Exec/Verify IR (no `local_env`).

mod builtin_atomic_gen;
mod entry;
mod equality_builtin_gen;
mod exist_builtin_gen;
mod or_builtin_gen;
mod searched;
mod known_special_property;
mod stmt;
mod store;
mod strategy_gen;
mod verify;
mod wd;
mod wd_by_def;

pub use entry::{project_run_detailed, project_stmt_detailed};
