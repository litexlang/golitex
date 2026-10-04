use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::run::RunSessionError;
use crate::run_module::{run_file_with_config, run_project};
use crate::runtime::RuntimeError;
use std::fs;
use std::time::{SystemTime, UNIX_EPOCH};

#[test]
fn mounted_export_errors_keep_their_runtime_classification() {
    let unique = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
    let root = std::env::temp_dir().join(format!("litex-error-forwarding-{}-{unique}", std::process::id()));
    fs::create_dir_all(root.join("dep")).unwrap();
    fs::write(root.join("main.lit"), "1 = 1\n").unwrap();
    fs::write(root.join("bad.lit"), "trust 1 = 1\n").unwrap();
    fs::write(root.join("litex.config"), "[export]\nbad = \"./bad.lit\"\nmain = \"./main.lit\"\n").unwrap();
    let command = LaunchCommand::Repository { path: root.clone(), session: false,
        strict: true, language: OutputLanguage::English };
    let run = run_project(command.clone()).unwrap();
    assert!(matches!(run.run.session_error, Some(RunSessionError::Runtime(RuntimeError::InvalidArguments(_)))));
    assert_eq!(run.files.len(), 1, "later exports must not execute");
    let file = run_file_with_config(LaunchCommand::File { path: root.join("main.lit"),
        session: false, strict: true, language: OutputLanguage::English }).unwrap();
    assert!(matches!(file.run.session_error, Some(RunSessionError::Runtime(RuntimeError::InvalidArguments(_)))));
    fs::write(root.join("litex.config"), "[import]\nDep = \"./dep\"\n[export]\nmain = \"./main.lit\"\n").unwrap();
    fs::write(root.join("dep/litex.config"), "[export]\nmain = \"./main.lit\"\n").unwrap();
    fs::write(root.join("dep/main.lit"), "trust 1 = 1\n").unwrap();
    let imported = run_project(command.clone()).unwrap();
    assert!(matches!(imported.run.session_error, Some(RunSessionError::Runtime(RuntimeError::InvalidArguments(_)))));
    fs::write(root.join("dep/main.lit"), "1 = 2\n").unwrap();
    let soft = run_project(command).unwrap();
    assert!(matches!(soft.run.session_error, Some(RunSessionError::FailToImport)));
    fs::remove_dir_all(root).unwrap();
}
