use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::run_module::run_project;
use std::fs;
use std::time::{SystemTime, UNIX_EPOCH};

#[test]
fn strict_import_cannot_replay_a_non_strict_trusted_theorem() {
    let unique = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
    let root = std::env::temp_dir().join(format!("litex-strict-cache-{}-{unique}", std::process::id()));
    fs::create_dir_all(root.join("dep")).unwrap();
    fs::write(root.join("litex.config"), "[import]\nDep = \"./dep\"\n[export]\nmain = \"./main.lit\"\n").unwrap();
    fs::write(root.join("dep/litex.config"), "[export]\nmain = \"./main.lit\"\n").unwrap();
    fs::write(root.join("dep/main.lit"), "thm false_theorem:\n    ? 0 = 1\n    trust 0 = 1\n").unwrap();
    fs::write(root.join("main.lit"), "release thm Dep::main::false_theorem\n0 = 1\n").unwrap();
    let command = |strict| LaunchCommand::Repository { path: root.clone(), session: false,
        strict, language: OutputLanguage::English };
    assert!(!run_project(command(true)).unwrap().run.success, "cold strict rejects trust");
    assert!(run_project(command(false)).unwrap().run.success, "deliberate non-strict trust fixture");
    assert!(root.join("dep/__litex_knowledge_base__/manifest.json").is_file());
    let warm = run_project(command(true)).unwrap();
    fs::remove_dir_all(root).unwrap();
    assert!(!warm.run.success, "strict must not accept the cached proof of 0 = 1");
    assert!(warm.run.session_error.is_some());
}
