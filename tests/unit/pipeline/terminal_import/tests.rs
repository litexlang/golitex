use super::run_terminal_import;
use crate::prelude::{OutputDetail, OutputLanguage};
use crate::runtime::{Runtime, RuntimeOptions, SummaryOption};
use crate::test_support::{execute_source, with_standard_library_root};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

struct Fixture {
    root: PathBuf,
}

impl Fixture {
    fn new(name: &str) -> Self {
        static NEXT_ID: AtomicUsize = AtomicUsize::new(0);
        let id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
        let root = std::env::temp_dir().join(format!(
            "litex-terminal-import-{name}-{}-{id}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).expect("create terminal import fixture");
        Self { root }
    }

    fn path(&self, name: &str) -> PathBuf {
        self.root.join(name)
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

fn write_file(path: &Path, source: &str) {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).expect("create fixture directory");
    }
    fs::write(path, source).expect("write fixture file");
}

fn module_config(export_name: &str, source_name: &str) -> String {
    format!("[hierarchy]\nmodule\n\n[export]\n{export_name} = \"./{source_name}\"\n")
}

#[test]
fn failed_terminal_import_rolls_back_before_the_same_alias_is_retried() {
    let fixture = Fixture::new("rollback");
    let broken = fixture.path("broken");
    write_file(
        &broken.join("litex.config"),
        module_config("main", "main.lit").as_str(),
    );
    write_file(&broken.join("main.lit"), "have broken R =\n");
    let valid = fixture.path("valid");
    write_file(
        &valid.join("litex.config"),
        module_config("main", "main.lit").as_str(),
    );
    write_file(&valid.join("main.lit"), "have value R = 7\n");

    let mut runtime = Runtime::default();
    runtime.start_isolated_source("repl");
    let (failed_ok, failed) = run_terminal_import(
        format!("import \"{}\" as Retry", broken.to_string_lossy()).as_str(),
        &mut runtime,
    );
    assert!(!failed_ok);
    assert!(failed.contains("error"), "{failed}");
    assert!(runtime.module_manager.module_id_by_name("Retry").is_none());
    assert!(runtime.unverified_imports().is_empty());

    let (retried_ok, retried) = run_terminal_import(
        format!("import \"{}\" as Retry", valid.to_string_lossy()).as_str(),
        &mut runtime,
    );
    assert!(retried_ok);
    assert!(retried.contains("\"execution\": \"executed\""), "{retried}");
    let (_, use_error) = execute_source("Retry::main::value = 7", &mut runtime);
    assert!(use_error.is_none(), "{use_error:?}");
}

#[test]
fn standard_terminal_import_records_execution_then_reuse() {
    let fixture = Fixture::new("standard-reuse");
    let std_root = fixture.path("std");
    write_file(
        &std_root.join("basics/litex.config"),
        "[hierarchy]\nmodule\n\n[module]\nflatten = true\n\n[export]\nmain = \"./main.lit\"\n",
    );
    write_file(&std_root.join("basics/main.lit"), "have std_value R = 1\n");

    let mut runtime = Runtime::default();
    runtime.start_isolated_source("repl");

    with_standard_library_root(&std_root, || {
        let (first_ok, first) = run_terminal_import("import std basics", &mut runtime);
        assert!(first_ok);
        assert!(first.contains("\"execution\": \"executed\""), "{first}");

        let (second_ok, second) = run_terminal_import("import std basics", &mut runtime);
        assert!(second_ok);
        assert!(second.contains("\"execution\": \"reused\""), "{second}");
    });
}

#[test]
fn strict_terminal_import_verifies_and_rolls_back_a_failing_module() {
    let fixture = Fixture::new("strict");
    let dependency = fixture.path("dependency");
    write_file(
        &dependency.join("litex.config"),
        module_config("assumption", "assumption.lit").as_str(),
    );
    write_file(&dependency.join("assumption.lit"), "1 = 0\n");

    let mut runtime = Runtime::new(RuntimeOptions::strict(
        OutputDetail::Normal,
        OutputLanguage::English,
        SummaryOption::None,
    ));
    runtime.start_isolated_source("repl");
    let (ok, output) = run_terminal_import(
        format!(
            "import \"{}\" as StrictDependency",
            dependency.to_string_lossy()
        )
        .as_str(),
        &mut runtime,
    );
    assert!(!ok);
    assert!(output.contains("1 = 0"), "{output}");
    assert!(runtime
        .module_manager
        .module_id_by_name("StrictDependency")
        .is_none());
    assert!(runtime.unverified_imports().is_empty());
}
