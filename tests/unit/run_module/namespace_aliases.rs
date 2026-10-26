use crate::prelude::*;
use crate::run_module::{run_file_with_config, run_project};
use std::fs;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root = std::env::temp_dir().join(format!(
            "litex-namespace-aliases-{}-{nonce}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        for (name, text) in [
            (
                "litex.config",
                include_str!("../../../examples/module_manager/namespace_aliases/litex.config"),
            ),
            (
                "main.lit",
                include_str!("../../../examples/module_manager/namespace_aliases/main.lit"),
            ),
            (
                "library/litex.config",
                include_str!(
                    "../../../examples/module_manager/namespace_aliases/library/litex.config"
                ),
            ),
            (
                "library/defs.lit",
                include_str!("../../../examples/module_manager/namespace_aliases/library/defs.lit"),
            ),
            (
                "library/other.lit",
                include_str!(
                    "../../../examples/module_manager/namespace_aliases/library/other.lit"
                ),
            ),
        ] {
            let path = root.join(name);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(path, text).unwrap();
        }
        Self(root)
    }

    fn run(&self, code: &str) -> crate::run::RunFileResult {
        fs::write(self.0.join("main.lit"), code).unwrap();
        run_file_with_config(LaunchCommand::File {
            path: self.0.join("main.lit"),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        })
        .unwrap()
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn namespace_aliases_run_real_project_and_all_name_contexts() {
    let f = Fixture::new();
    let result = run_project(LaunchCommand::Repository {
        path: f.0.clone(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
    .unwrap();
    assert!(result.run.success, "{:?}", result.run.session_error);
    assert_eq!(result.files.len(), 3);
    let main = fs::read_to_string(f.0.join("main.lit")).unwrap();
    assert!(f.run(&main).run.success);
}

#[test]
fn namespace_aliases_reject_removed_triple_colon_in_each_name_context() {
    let f = Fixture::new();
    for code in [
        "Library:::value = 2",
        "by def $Library:::positive(1)",
        "$Library:::positive(1)",
        "by thm Library:::add_zero(2) => 2 + 0 = 2",
        "release thm Library:::add_zero(2)",
        "release obj def Library:::value",
        "\\Library:::copied<R> = R",
        "have pair &Library:::Pair = (1,2)",
    ] {
        let result = f.run(code);
        assert!(!result.run.success, "{code}");
        let json = result.run.normal_json.as_ref().unwrap();
        assert!(
            json.contains("has been removed") && json.contains("[alias]"),
            "{code}: {json}"
        );
        assert!(!json.contains("internal_bug"), "{code}: {json}");
    }
    assert!(f.run("C::value = Library::defs::value").run.success);
}

#[test]
fn namespace_aliases_do_not_create_symbols_exports_or_plain_names() {
    let f = Fixture::new();
    for code in [
        "C::ghost = C::ghost",
        "C = 2",
        "C::defs::value = 2",
        "Library::C::value = 2",
        "release obj def C::value\nC::value = 3",
        "have bad &C::Ghost = (1,2)",
        "\\C::ghost<R> = R",
    ] {
        assert!(!f.run(code).run.success, "{code}");
    }
}

#[test]
fn namespace_aliases_reject_unused_unknown_targets_before_file_or_project_execution() {
    let f = Fixture::new();
    let config = fs::read_to_string(f.0.join("litex.config"))
        .unwrap()
        .replace("D = Library::other", "D = Library::ghost");
    fs::write(f.0.join("litex.config"), config).unwrap();
    fs::write(f.0.join("main.lit"), "1 = 1\n").unwrap();
    let error = run_file_with_config(LaunchCommand::File {
        path: f.0.join("main.lit"),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
    .err()
    .unwrap();
    assert!(format!("{error:?}").contains("ghost"));
    let error = run_project(LaunchCommand::Repository {
        path: f.0.clone(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
    .err()
    .unwrap();
    assert!(format!("{error:?}").contains("ghost"));
}

#[test]
fn namespace_aliases_survive_real_cache_hits_and_target_changes_in_imported_packages() {
    let f = Fixture::new();
    // Use codec-supported object definitions so a warm run must really hit.
    fs::write(f.0.join("library/defs.lit"), "let value = 2\n").unwrap();
    fs::create_dir_all(f.0.join("consumer")).unwrap();
    fs::write(
        f.0.join("consumer/litex.config"),
        "[import]\nLib = \"../library\"\n[alias]\nC = Lib::defs\n[export]\nmain = \"main.lit\"\n",
    )
    .unwrap();
    fs::write(f.0.join("consumer/main.lit"), "let copied = C::value\n").unwrap();
    fs::write(
        f.0.join("litex.config"),
        "[import]\nUse = \"consumer\"\n[export]\nmain = \"main.lit\"\n",
    )
    .unwrap();
    fs::write(f.0.join("main.lit"), "release obj def Use::main::copied\nrelease obj def Lib::defs::value\nUse::main::copied = 2\n").unwrap();
    // The caller must declare its own imports; aliases from Use do not leak.
    let root = "[import]\nLib = \"library\"\nUse = \"consumer\"\n[alias]\nC = Lib::defs\n[export]\nmain = \"main.lit\"\n";
    fs::write(f.0.join("litex.config"), root).unwrap();
    let command = || LaunchCommand::Repository {
        path: f.0.clone(),
        session: false,
        strict: false,
        language: OutputLanguage::English,
    };
    let cold = run_project(command()).unwrap();
    assert!(cold.run.success, "{:?}", cold.run.session_error);
    let warm = run_project(command()).unwrap();
    assert!(warm.run.success, "{:?}", warm.run.session_error);
    assert_eq!(warm.files.len(), 1, "must actually skip cached imports");
    let use_config = fs::read_to_string(f.0.join("consumer/litex.config")).unwrap();
    fs::write(
        f.0.join("consumer/litex.config"),
        use_config.replace("C = Lib::defs", "C = Lib::other"),
    )
    .unwrap();
    fs::write(f.0.join("main.lit"), "release obj def Use::main::copied\nrelease obj def Lib::other::value\nUse::main::copied = 3\n").unwrap();
    let changed = run_project(command()).unwrap();
    assert!(changed.run.success, "{:?}", changed.run.session_error);
    assert_eq!(
        changed.files.len(),
        2,
        "alias config change must rebuild consumer only"
    );
    let cfg = fs::read_to_string(f.0.join("consumer/litex.config")).unwrap();
    fs::write(
        f.0.join("consumer/litex.config"),
        cfg.replace("C = Lib::other", "C = Lib::ghost"),
    )
    .unwrap();
    let invalid = run_project(command()).unwrap();
    assert!(
        !invalid.run.success,
        "invalid alias must fail before restoring cached consumer"
    );
}
