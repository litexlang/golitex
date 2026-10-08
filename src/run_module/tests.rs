//! Unit tests for config-driven `-r` / `-f`.

use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::run::run_command_outcome::RunSessionError;
use crate::run_module::{
    mount_cwd_config, run_file_with_config, run_project, MountCwdConfigOutcome,
};
use std::fs;
use std::path::PathBuf;
use std::time::{SystemTime, UNIX_EPOCH};

#[path = "cross_file_identity_tests.rs"]
mod cross_file_identity_tests;

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
        language: OutputLanguage::English,
    })
    .expect("run_project");

    assert!(result.run.success);
    assert!(result.run.session_error.is_none());
    assert_eq!(result.files.len(), 2);
    assert!(result.files.iter().all(|file| file.run.success));

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn run_project_cross_mod_release_thm_and_by_def() {
    let root = temp_dir("cross_def");
    write(
        &root.join("lib/litex.config"),
        "[export]\nbase = \"./base.lit\"\n",
    );
    write(
        &root.join("lib/base.lit"),
        "prop above_zero(x R):\n    x > 0\n\n\
         thm add_zero_right:\n    ? forall x R:\n        x + 0 = x\n    x + 0 = x\n",
    );
    write(
        &root.join("litex.config"),
        "[import]\nLib = \"./lib\"\n\n[export]\nmain = \"./main.lit\"\n",
    );
    write(
        &root.join("main.lit"),
        "by def $Lib::base::above_zero(1)\n\n\
         release thm Lib::base::add_zero_right(2)\n\
         2 + 0 = 2\n\n\
         by thm Lib:::add_zero_right(3) => 3 + 0 = 3\n",
    );

    let result = run_project(LaunchCommand::Repository {
        path: root.clone(),
        session: false,
        strict: false,
        language: OutputLanguage::English,
    })
    .expect("run_project");

    assert!(result.run.success, "{:?}", result.run.session_error);
    assert!(result.files.iter().all(|file| file.run.success));

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn run_project_kb_cache_write_then_hit_cross_mod() {
    let root = temp_dir("kb_cache");
    write(
        &root.join("lib/litex.config"),
        "[export]\nbase = \"./base.lit\"\n",
    );
    write(
        &root.join("lib/base.lit"),
        "prop above_zero(x R):\n    x > 0\n\n\
         thm add_zero_right:\n    ? forall x R:\n        x + 0 = x\n    x + 0 = x\n\n\
         have fn id(x R) R = x\n\
         let c = 1\n",
    );
    write(
        &root.join("litex.config"),
        "[import]\nLib = \"./lib\"\n\n[export]\nmain = \"./main.lit\"\n",
    );
    write(
        &root.join("main.lit"),
        "by def $Lib::base::above_zero(1)\n\n\
         release thm Lib::base::add_zero_right(2)\n\
         2 + 0 = 2\n\n\
         by thm Lib:::add_zero_right(3) => 3 + 0 = 3\n\n\
         release obj def Lib::base::c\n\
         Lib::base::c = 1\n\n\
         release obj def Lib::base::id\n\
         Lib::base::id(1) = 1\n",
    );

    let first = run_project(LaunchCommand::Repository {
        path: root.clone(),
        session: false,
        strict: false,
        language: OutputLanguage::English,
    })
    .expect("first run_project");
    assert!(first.run.success, "{:?}", first.run.session_error);
    assert!(
        root.join("lib/__litex_knowledge_base__/manifest.json")
            .is_file(),
        "expected kb write after cold import"
    );

    let second = run_project(LaunchCommand::Repository {
        path: root.clone(),
        session: false,
        strict: false,
        language: OutputLanguage::English,
    })
    .expect("second run_project");
    assert!(second.run.success, "{:?}", second.run.session_error);
    // Root export still runs; imported lib should be served from kb (no lib file result).
    assert_eq!(
        second.files.len(),
        1,
        "kb hit should skip re-exec of lib export"
    );

    // Old decimal/aggregate and empty-domain function-graph products must be
    // rebuilt even when their module source bytes have not changed.
    let manifest = root.join("lib/__litex_knowledge_base__/manifest.json");
    let current_manifest = fs::read_to_string(&manifest).unwrap();
    for old_abi in ["2", "5", "6"] {
        let old_manifest = current_manifest.replace(
            &format!("\"abi\": \"{}\"", crate::knowledge_base::KB_ABI),
            &format!("\"abi\": \"{old_abi}\""),
        );
        assert_ne!(old_manifest, current_manifest);
        fs::write(&manifest, old_manifest).unwrap();
        let rebuilt = run_project(LaunchCommand::Repository {
            path: root.clone(),
            session: false,
            strict: false,
            language: OutputLanguage::English,
        })
        .expect("old ABI falls back to source");
        assert!(rebuilt.run.success, "{:?}", rebuilt.run.session_error);
        assert_eq!(
            rebuilt.files.len(),
            2,
            "old cached library must execute again"
        );
        assert_eq!(fs::read_to_string(&manifest).unwrap(), current_manifest);
        let warm_again = run_project(LaunchCommand::Repository {
            path: root.clone(),
            session: false,
            strict: false,
            language: OutputLanguage::English,
        })
        .expect("rebuilt cache can be reused");
        assert!(warm_again.run.success);
        assert_eq!(warm_again.files.len(), 1);
    }

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
        language: OutputLanguage::English,
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
        language: OutputLanguage::English,
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
        language: OutputLanguage::English,
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
        language: OutputLanguage::English,
    })
    .expect("run_file");

    assert!(result.run.success);
    assert!(result.run.session_error.is_none());

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn run_file_unlisted_runs_all_exports_then_target() {
    let root = temp_dir("f_extra");
    write(&root.join("litex.config"), "[export]\na = \"./a.lit\"\n");
    write(&root.join("a.lit"), "1 = 1\n");
    write(&root.join("scratch.lit"), "2 = 2\n");

    let result = run_file_with_config(LaunchCommand::File {
        path: root.join("scratch.lit"),
        session: false,
        strict: false,
        language: OutputLanguage::English,
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
        language: OutputLanguage::English,
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
    write(&root.join("litex.config"), "[export]\nok = \"./ok.lit\"\n");
    write(&root.join("ok.lit"), "1 = 1\n");
    write(&root.join("scratch.lit"), "1 = 2\n");

    let result = run_file_with_config(LaunchCommand::File {
        path: root.join("scratch.lit"),
        session: false,
        strict: false,
        language: OutputLanguage::English,
    })
    .expect("run_file");

    assert!(!result.run.success);
    assert!(result.run.session_error.is_none());

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn mount_cwd_config_empty_when_missing() {
    let root = temp_dir("cwd_empty");
    let previous = std::env::current_dir().expect("cwd");
    std::env::set_current_dir(&root).expect("chdir");

    let mut runtime = crate::runtime::Runtime::new(LaunchCommand::Eval {
        code: "1 = 1".to_string(),
        session: false,
        strict: false,
        language: OutputLanguage::English,
    });
    runtime.abort_file();
    let outcome = mount_cwd_config(&mut runtime).expect("mount");
    assert!(matches!(outcome, MountCwdConfigOutcome::Done));

    std::env::set_current_dir(previous).expect("restore cwd");
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn mount_cwd_config_runs_exports() {
    let root = temp_dir("cwd_mount");
    write(
        &root.join("litex.config"),
        "[export]\nmain = \"./main.lit\"\n",
    );
    write(&root.join("main.lit"), "1 = 1\n");

    let previous = std::env::current_dir().expect("cwd");
    std::env::set_current_dir(&root).expect("chdir");

    let mut runtime = crate::runtime::Runtime::new(LaunchCommand::Eval {
        code: "1 = 1".to_string(),
        session: false,
        strict: false,
        language: OutputLanguage::English,
    });
    runtime.abort_file();
    let outcome = mount_cwd_config(&mut runtime).expect("mount");
    assert!(matches!(outcome, MountCwdConfigOutcome::Done));
    assert_eq!(runtime.global_module_manager.root_exports().len(), 1);

    std::env::set_current_dir(previous).expect("restore cwd");
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn mount_cwd_config_soft_fail_is_fail_to_import() {
    let root = temp_dir("cwd_fail");
    write(
        &root.join("litex.config"),
        "[export]\nbad = \"./bad.lit\"\n",
    );
    write(&root.join("bad.lit"), "1 = 2\n");

    let previous = std::env::current_dir().expect("cwd");
    std::env::set_current_dir(&root).expect("chdir");

    let mut runtime = crate::runtime::Runtime::new(LaunchCommand::Eval {
        code: "1 = 1".to_string(),
        session: false,
        strict: false,
        language: OutputLanguage::English,
    });
    runtime.abort_file();
    let outcome = mount_cwd_config(&mut runtime).expect("mount");
    assert!(matches!(
        outcome,
        MountCwdConfigOutcome::SessionError(RunSessionError::FailToImport)
    ));

    std::env::set_current_dir(previous).expect("restore cwd");
    let _ = fs::remove_dir_all(&root);
}
