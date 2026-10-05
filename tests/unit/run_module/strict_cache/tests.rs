use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::run_module::run_project;
use std::fs;
use std::time::{SystemTime, UNIX_EPOCH};

fn fresh_root(case: &str) -> std::path::PathBuf {
    let unique = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
    std::env::temp_dir().join(format!("litex-strict-cache-{case}-{}-{unique}", std::process::id()))
}

#[test]
fn strict_import_rechecks_user_axioms_in_a_cached_transitive_dependency() {
    let root = fresh_root("axiom-transitive");
    fs::create_dir_all(root.join("dep/leaf")).unwrap();
    fs::write(root.join("litex.config"), "[import]\nDep = \"./dep\"\n[export]\nmain = \"./main.lit\"\n").unwrap();
    fs::write(root.join("dep/litex.config"), "[import]\nLeaf = \"./leaf\"\n[export]\nmain = \"./main.lit\"\n").unwrap();
    fs::write(root.join("dep/leaf/litex.config"), "[export]\nmain = \"./main.lit\"\n").unwrap();
    fs::write(root.join("dep/leaf/main.lit"), "axiom false_axiom:\n    ? forall x R:\n        0 = 1\n").unwrap();
    fs::write(root.join("dep/main.lit"), "thm forwarded:\n    ? 0 = 1\n    release thm Leaf::main::false_axiom(0)\n").unwrap();
    fs::write(root.join("main.lit"), "release thm Dep::main::forwarded\n0 = 1\n").unwrap();
    let command = |strict| LaunchCommand::Repository { path: root.clone(), session: false,
        strict, language: OutputLanguage::English };
    let cold = run_project(command(true)).unwrap();
    assert!(!cold.run.success);
    assert!(format!("{:?}", cold.run.session_error).contains("`axiom` is forbidden"));
    assert!(run_project(command(false)).unwrap().run.success, "deliberate ordinary-mode axiom fixture");
    for dep in ["dep", "dep/leaf"] {
        assert!(root.join(dep).join("__litex_knowledge_base__/manifest.json").is_file());
    }
    let cached = run_project(command(false)).unwrap();
    assert!(cached.run.success);
    assert_eq!(cached.files.len(), 1, "ordinary mode actually replays the cache");
    let warm = run_project(command(true)).unwrap();
    fs::remove_dir_all(root).unwrap();
    assert!(!warm.run.success, "strict must recheck transitive source axioms");
    assert!(format!("{:?}", warm.run.session_error).contains("`axiom` is forbidden"));
}

#[test]
fn strict_import_cannot_replay_a_non_strict_trusted_theorem() {
    let root = fresh_root("direct");
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

#[test]
fn strict_import_rechecks_trust_in_a_transitive_dependency() {
    let root = fresh_root("transitive");
    fs::create_dir_all(root.join("dep/leaf")).unwrap();
    fs::write(root.join("litex.config"), "[import]\nDep = \"./dep\"\n[export]\nmain = \"./main.lit\"\n").unwrap();
    fs::write(root.join("dep/litex.config"), "[import]\nLeaf = \"./leaf\"\n[export]\nmain = \"./main.lit\"\n").unwrap();
    fs::write(root.join("dep/leaf/litex.config"), "[export]\nmain = \"./main.lit\"\n").unwrap();
    fs::write(root.join("dep/leaf/main.lit"), "thm false_theorem:\n    ? 0 = 1\n    trust 0 = 1\n").unwrap();
    fs::write(root.join("dep/main.lit"), "thm forwarded:\n    ? 0 = 1\n    release thm Leaf::main::false_theorem\n").unwrap();
    fs::write(root.join("main.lit"), "release thm Dep::main::forwarded\n0 = 1\n").unwrap();
    let command = |strict| LaunchCommand::Repository { path: root.clone(), session: false,
        strict, language: OutputLanguage::English };
    assert!(!run_project(command(true)).unwrap().run.success);
    assert!(run_project(command(false)).unwrap().run.success);
    for dep in ["dep", "dep/leaf"] {
        assert!(root.join(dep).join("__litex_knowledge_base__/manifest.json").is_file());
    }
    let warm = run_project(command(true)).unwrap();
    fs::remove_dir_all(root).unwrap();
    assert!(!warm.run.success, "strict must recheck transitive source trust");
    assert!(warm.run.session_error.is_some());
}

#[test]
fn strict_valid_imports_pass_cold_verification_after_non_strict_cache_warmup() {
    let root = fresh_root("valid");
    fs::create_dir_all(root.join("dep")).unwrap();
    fs::write(root.join("litex.config"), "[import]\nDep = \"./dep\"\n[export]\nmain = \"./main.lit\"\n").unwrap();
    fs::write(root.join("dep/litex.config"), "[export]\nmain = \"./main.lit\"\n").unwrap();
    fs::write(root.join("dep/main.lit"), "have fn identity(x R) R = x\n").unwrap();
    fs::write(root.join("main.lit"), "release obj def Dep::main::identity\nDep::main::identity(2) = 2\n").unwrap();
    let command = |strict| LaunchCommand::Repository { path: root.clone(), session: false,
        strict, language: OutputLanguage::English };
    assert!(run_project(command(false)).unwrap().run.success);
    let cached = run_project(command(false)).unwrap();
    assert!(cached.run.success);
    assert_eq!(cached.files.len(), 1, "ordinary mode retains actual cache replay");
    let strict = run_project(command(true)).unwrap();
    fs::remove_dir_all(root).unwrap();
    assert!(strict.run.success, "{:?}", strict.run.session_error);
    assert_eq!(strict.files.len(), 2, "strict rechecks the valid dependency source");
}
