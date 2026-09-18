//! Unit tests for config-driven `-r` / `-f`.

use crate::new_pipeline::launch_command::LaunchCommand;
use crate::new_pipeline::run::run_command_outcome::RunSessionError;
use crate::new_pipeline::run_module::{run_file_with_config, run_project};
use std::fs;
use std::path::PathBuf;
use std::time::{SystemTime, UNIX_EPOCH};

fn temp_dir(label: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("time")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("litex_run_module_{label}_{nanos}"));
    fs::create_dir_all(&dir).expect("mkdir");
    dir
}

fn write(path: &std::path::Path, body: &str) {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).expect("mkdir parent");
    }
    fs::write(path, body).expect("write");
}

#[test]
fn run_project_runs_import_then_root_export() {
    let root = temp_dir("ok");
    write(
        &root.join("lib/litex.config"),
        "[export]\nbase = \"./base.lit\"\n",
    );
    write(&root.join("lib/base.lit"), "let x = 1\n");
    write(
        &root.join("litex.config"),
        "[import]\nLib = \"./lib\"\n\n[export]\nmain = \"./main.lit\"\n",
    );
    write(&root.join("main.lit"), "1 = 1\n");

    let result = run_project(LaunchCommand::Repository {
        path: root.clone(),
        session: false,
        strict: false,
    })
    .expect("run_project");

    assert!(result.run.success);
    assert!(result.run.session_error.is_none());
    assert_eq!(result.files.len(), 2);
    assert!(result.files.iter().all(|file| file.run.success));

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn run_project_soft_fail_becomes_fail_to_import() {
    let root = temp_dir("soft");
    write(
        &root.join("litex.config"),
        "[export]\nmain = \"./main.lit\"\n",
    );
    write(&root.join("main.lit"), "1 = 2\n");

    let result = run_project(LaunchCommand::Repository {
        path: root.clone(),
        session: false,
        strict: false,
    })
    .expect("run_project");

    assert!(!result.run.success);
    assert!(matches!(
        result.run.session_error,
        Some(RunSessionError::FailToImport)
    ));
    assert_eq!(result.files.len(), 1);
    assert!(!result.files[0].run.success);

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn run_project_missing_import_dir_is_fail_to_import() {
    let root = temp_dir("missing");
    write(
        &root.join("litex.config"),
        "[import]\nMissing = \"./no_such_mod\"\n\n[export]\nmain = \"./main.lit\"\n",
    );
    write(&root.join("main.lit"), "1 = 1\n");

    let result = run_project(LaunchCommand::Repository {
        path: root.clone(),
        session: false,
        strict: false,
    })
    .expect("run_project");

    assert!(!result.run.success);
    assert!(matches!(
        result.run.session_error,
        Some(RunSessionError::FailToImport)
    ));
    assert!(result.files.is_empty());

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn run_file_isolated_without_config() {
    let root = temp_dir("f_iso");
    let path = root.join("alone.lit");
    write(&path, "1 = 1\n");

    let result = run_file_with_config(LaunchCommand::File {
        path: path.clone(),
        session: false,
        strict: false,
    })
    .expect("run_file");

    assert!(result.run.success);
    assert!(result.run.session_error.is_none());

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn run_file_stops_at_listed_export() {
    let root = temp_dir("f_listed");
    write(
        &root.join("litex.config"),
        "[export]\na = \"./a.lit\"\nb = \"./b.lit\"\n",
    );
    write(&root.join("a.lit"), "1 = 1\n");
    // If b ran, this soft fail would become FailToImport.
    write(&root.join("b.lit"), "1 = 2\n");

    let result = run_file_with_config(LaunchCommand::File {
        path: root.join("a.lit"),
        session: false,
        strict: false,
    })
    .expect("run_file");

    assert!(result.run.success);
    assert!(result.run.session_error.is_none());

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn run_file_unlisted_runs_all_exports_then_target() {
    let root = temp_dir("f_extra");
    write(
        &root.join("litex.config"),
        "[export]\na = \"./a.lit\"\n",
    );
    write(&root.join("a.lit"), "1 = 1\n");
    write(&root.join("scratch.lit"), "2 = 2\n");

    let result = run_file_with_config(LaunchCommand::File {
        path: root.join("scratch.lit"),
        session: false,
        strict: false,
    })
    .expect("run_file");

    assert!(result.run.success);
    assert!(result.run.session_error.is_none());

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn run_file_mount_soft_fail_is_fail_to_import() {
    let root = temp_dir("f_mount_fail");
    write(
        &root.join("litex.config"),
        "[export]\nbad = \"./bad.lit\"\n",
    );
    write(&root.join("bad.lit"), "1 = 2\n");
    write(&root.join("scratch.lit"), "1 = 1\n");

    let result = run_file_with_config(LaunchCommand::File {
        path: root.join("scratch.lit"),
        session: false,
        strict: false,
    })
    .expect("run_file");

    assert!(!result.run.success);
    assert!(matches!(
        result.run.session_error,
        Some(RunSessionError::FailToImport)
    ));

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn run_file_target_soft_fail_is_normal_failure() {
    let root = temp_dir("f_target_fail");
    write(
        &root.join("litex.config"),
        "[export]\nok = \"./ok.lit\"\n",
    );
    write(&root.join("ok.lit"), "1 = 1\n");
    write(&root.join("scratch.lit"), "1 = 2\n");

    let result = run_file_with_config(LaunchCommand::File {
        path: root.join("scratch.lit"),
        session: false,
        strict: false,
    })
    .expect("run_file");

    assert!(!result.run.success);
    assert!(result.run.session_error.is_none());

    let _ = fs::remove_dir_all(&root);
}
