use crate::error::RuntimeError;
use crate::result::StmtResult;
use crate::runtime::Runtime;
use std::path::Path;
use std::sync::{Mutex, OnceLock};

/// Test-only shorthand for the production `Runtime::execute_source` entry point.
pub fn execute_source(
    source_code: &str,
    runtime: &mut Runtime,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    runtime.execute_source(source_code).into_parts()
}

pub fn with_standard_library_root(std_root: &Path, test: impl FnOnce()) {
    let lock = standard_library_root_env_lock()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let _restore = StandardLibraryRootEnvGuard::new();
    std::env::set_var("LITEX_STD_PATH", std_root);
    test();
    drop(lock);
}

fn standard_library_root_env_lock() -> &'static Mutex<()> {
    static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    LOCK.get_or_init(|| Mutex::new(()))
}

struct StandardLibraryRootEnvGuard {
    previous: Option<std::ffi::OsString>,
}

impl StandardLibraryRootEnvGuard {
    fn new() -> Self {
        Self {
            previous: std::env::var_os("LITEX_STD_PATH"),
        }
    }
}

impl Drop for StandardLibraryRootEnvGuard {
    fn drop(&mut self) {
        if let Some(previous) = self.previous.as_ref() {
            std::env::set_var("LITEX_STD_PATH", previous);
        } else {
            std::env::remove_var("LITEX_STD_PATH");
        }
    }
}
