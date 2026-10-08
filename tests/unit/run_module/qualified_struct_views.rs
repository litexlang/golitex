use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::run_module::{run_file_with_config, run_project};
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

const MAIN: &str = include_str!("../../../examples/module_manager/qualified_struct_views/main.lit");

fn fixture(label: &str) -> PathBuf {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "litex-qualified-struct-{label}-{}-{nonce}",
        std::process::id()
    ));
    for (path, code) in [
        (
            "litex.config",
            include_str!("../../../examples/module_manager/qualified_struct_views/litex.config"),
        ),
        (
            "local.lit",
            include_str!("../../../examples/module_manager/qualified_struct_views/local.lit"),
        ),
        (
            "library/litex.config",
            include_str!(
                "../../../examples/module_manager/qualified_struct_views/library/litex.config"
            ),
        ),
        (
            "library/facts.lit",
            include_str!(
                "../../../examples/module_manager/qualified_struct_views/library/facts.lit"
            ),
        ),
        (
            "other/litex.config",
            include_str!(
                "../../../examples/module_manager/qualified_struct_views/other/litex.config"
            ),
        ),
        (
            "other/facts.lit",
            include_str!("../../../examples/module_manager/qualified_struct_views/other/facts.lit"),
        ),
        ("main.lit", MAIN),
    ] {
        let target = root.join(path);
        fs::create_dir_all(target.parent().unwrap()).unwrap();
        fs::write(target, code).unwrap();
    }
    root
}

fn checked_file(root: &Path, code: &str, expected: bool) {
    fs::write(root.join("main.lit"), code).unwrap();
    let result = run_file_with_config(LaunchCommand::File {
        path: root.join("main.lit"),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
    .expect("ordinary success/rejection must not escape as a runtime error");
    assert_eq!(
        result.run.success, expected,
        "{code}\n{:?}",
        result.run.session_error
    );
    assert!(!format!("{:?}", result.run.session_error).contains("InternalBug"));
    if !expected && result.run.session_error.is_none() && code.starts_with(MAIN) {
        // Each caller appends exactly one outer statement. Every earlier
        // result must succeed, so the expected rejection cannot hide a
        // broken field or owner in MAIN.
        let (tail, prefix) = result.run.statement_results.split_last().unwrap();
        assert!(prefix.len() >= 12 && tail.is_failed());
        assert!(
            prefix.iter().all(|stmt| !stmt.is_failed()),
            "a failure in the shared prefix must not masquerade as the expected negative tail"
        );
    }
    if expected {
        assert!(result.run.session_error.is_none());
        assert!(
            result.run.statement_results.len() >= 12,
            "fixture must actually execute"
        );
    }
}

#[test]
fn qualified_struct_views_keep_import_export_generic_and_nested_owners() {
    let root = fixture("positive");
    checked_file(&root, MAIN, true);
    let project = run_project(LaunchCommand::Repository {
        path: root.clone(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
    .unwrap();
    assert!(project.run.success && project.run.session_error.is_none());
    assert_eq!(project.files.len(), 4);
    assert!(project.files.iter().all(|file| file.run.success));
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn qualified_struct_views_reject_wrong_owner_carrier_field_and_arguments() {
    let root = fixture("negative");
    for tail in [
        "have fractional &Other::facts::Pair = (1/2,3/2)\n",
        "have fractional &local::Pair = (1/2,3/2)\n",
        "item.first = 3/2\n",
        "item(1) = 3/2\n",
        "item(3) = 0\n",
        "item.third = 0\n",
        "have bad &Lib::facts::Tagged<{}> = (0,0)\n",
        "have bad &Lib::facts::Pair<R> = (1,2)\n",
    ] {
        checked_file(&root, &format!("{MAIN}\n{tail}"), false);
    }
    checked_file(&root, MAIN, true);
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn qualified_struct_views_reject_unknown_or_malformed_paths_without_internal_bug() {
    let root = fixture("paths");
    for tail in [
        "have bad &Missing::facts::Pair = (1,2)\n",
        "have bad &Lib::missing::Pair = (1,2)\n",
        "have bad &Lib::facts::Missing = (1,2)\n",
        "have bad &Lib::facts:: = (1,2)\n",
        "have bad &Lib::::Pair = (1,2)\n",
    ] {
        checked_file(&root, &format!("{MAIN}\n{tail}"), false);
    }
    checked_file(&root, MAIN, true);
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn flattened_struct_view_still_requires_exactly_one_import_export() {
    let root = fixture("flat");
    fs::write(
        root.join("library/litex.config"),
        "[export]\nfacts = \"./facts.lit\"\nextra = \"./extra.lit\"\n",
    )
    .unwrap();
    fs::write(root.join("library/extra.lit"), "0=0\n").unwrap();
    let full_path = MAIN.replace("Lib:::Tagged", "Lib::facts::Tagged");
    checked_file(&root, &full_path, true);
    checked_file(&root, MAIN, false);
    checked_file(&root, &full_path, true);
    fs::remove_dir_all(root).unwrap();
}
