//! Real imports exercise local aliases, owner identity and cache remapping.

use super::{temp_dir, write};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::run::run_command_outcome::{RunRepoResult, RunSessionError};
use crate::run_module::{run_file_with_config, run_project};
use std::fs;
use std::path::{Path, PathBuf};

fn project(root: &Path) -> RunRepoResult {
    run_project(LaunchCommand::Repository {
        path: root.to_path_buf(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
    .expect("run actual project")
}

#[test]
fn undefined_local_predicate_goal_cannot_be_exported_and_captured_by_the_caller() {
    let root = temp_dir("predicate_goal_preflight");
    write(&root.join("litex.config"), "[import]\nOther = \"./library\"\n[export]\nmain = \"./main.lit\"\n");
    write(&root.join("library/litex.config"), "[export]\nfacts = \"./facts.lit\"\n");
    write(&root.join("library/facts.lit"), "claim:\n    ? $chosen(0)\n    prop chosen(x R):\n        x = 0\n    by def $chosen(0)\nthm ready:\n    ? $chosen(0)\n");
    write(&root.join("main.lit"), "prop chosen(x R):\n    x = 1\nrelease thm Other::facts::ready\n0 = 1\n");
    for _ in 0..2 {
        let result = project(&root);
        assert!(!result.run.success, "a malformed library may not prove 0=1");
        assert!(!root.join("library/__litex_knowledge_base__/manifest.json").exists(),
            "failed library execution must not write a reusable cache");
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn same_predicate_spelling_with_different_arities_keeps_its_owner_in_cached_imports() {
    let root = temp_dir("predicate_signature_owners");
    write(&root.join("litex.config"), "[import]\nLeft = \"./left\"\nRight = \"./right\"\n[export]\nmain = \"./main.lit\"\n");
    for (module, source) in [
        ("left", "prop relation(x R):\n    x = 0\n"),
        ("right", "prop relation(x, y R):\n    x = y\n"),
    ] {
        write(&root.join(format!("{module}/litex.config")), "[export]\nfacts = \"./facts.lit\"\n");
        write(&root.join(format!("{module}/facts.lit")), source);
    }
    write(&root.join("main.lit"), "prop relation(a, b, c R):\n    a = b\n    b = c\nby def $Left::facts::relation(0)\nby def $Right::facts::relation(1, 1)\nby def $relation(2, 2, 2)\n");
    let cold = project(&root);
    assert!(cold.run.success, "{:?}", cold.run.session_error);
    let warm = project(&root);
    assert!(warm.run.success, "{:?}", warm.run.session_error);
    assert_eq!(warm.files.len(), 1, "imported files must actually come from cache");
    write(&root.join("main.lit"), "forall x R:\n    $Left::facts::relation(x, x)\n    =>:\n        $Left::facts::relation(x, x)\n");
    let invalid = run_file_with_config(LaunchCommand::File {
        path: root.join("main.lit"), session: false, strict: true,
        language: OutputLanguage::English,
    }).unwrap();
    assert!(invalid.run.session_error.is_none(), "{:?}", invalid.run.session_error);
    assert!(!invalid.run.success, "the right owner's arity must not rescue Left's invalid call");
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn forall_source_replay_keeps_same_named_imported_objects_separate() {
    let root = temp_dir("forall_source_owners");
    write(&root.join("litex.config"), "[import]\nOther = \"./library\"\n[export]\nmain = \"./main.lit\"\n");
    write(&root.join("library/litex.config"), "[export]\nfacts = \"./facts.lit\"\n");
    write(&root.join("library/facts.lit"), "have value R = 0\nthm fixed:\n    ? forall t R:\n        exist! y R st {y = value}\n    witness exist! y R st {y = value} from value\n");
    let valid = "have value R = 1\nrelease obj def Other::facts::value\nclaim:\n    ? forall t R:\n        exist! y R st {y = Other::facts::value}\n    release thm Other::facts::fixed(t)\nhave fn selected by exist!:\n    ? forall x R:\n        exist! z R st {z = Other::facts::value}\nselected(2) = Other::facts::value\nselected(2) = 0\nvalue = 1\n";
    write(&root.join("main.lit"), valid);
    let cold = project(&root);
    assert!(cold.run.success, "{:?}", cold.run.session_error);
    let repeated = project(&root);
    assert!(repeated.run.success, "{:?}", repeated.run.session_error);
    assert_eq!(repeated.files.len(), 2, "exist! theorem is outside the existing cache codec subset; verify source fallback");
    assert!(!root.join("library/__litex_knowledge_base__/manifest.json").exists());
    let target = root.join("invalid.lit");
    write(&target, &valid.replace("selected(2) = 0", "selected(2) = 1"));
    let invalid = run_file_with_config(LaunchCommand::File {
        path: target, session: false, strict: true, language: OutputLanguage::English,
    }).unwrap();
    assert!(invalid.run.session_error.is_none(), "{:?}", invalid.run.session_error);
    assert!(!invalid.run.success, "local value may not replace the imported owner");
    fs::remove_dir_all(root).unwrap();
}

fn dependency_fixture() -> PathBuf {
    let root = temp_dir("local_alias_owners");
    // This authored label also collides with the first generated suffix.
    write(
        &root.join("sentinel/litex.config"),
        "[export]\nfacts = \"./facts.lit\"\n",
    );
    write(&root.join("sentinel/facts.lit"), "have value R = 10\n");
    for (module, offset) in [("left", 0), ("right", 1)] {
        write(
            &root.join(format!("{module}/litex.config")),
            "[import]\nCommon = \"./dep\"\n[export]\nfacts = \"./facts.lit\"\n",
        );
        write(
            &root.join(format!("{module}/dep/litex.config")),
            "[export]\nfacts = \"./facts.lit\"\n",
        );
        write(
            &root.join(format!("{module}/dep/facts.lit")),
            &format!("have value R = {offset}\n"),
        );
        write(&root.join(format!("{module}/facts.lit")), &format!(
            "release obj def Common::facts::value\nhave value R = Common::facts::value\nthm ready:\n    ? value = {offset}\n"
        ));
    }
    write_root_config(&root, false);
    write(&root.join("main.lit"), "release obj def Left::facts::value\nrelease obj def Right::facts::value\nrelease obj def Common__m3::facts::value\nrelease thm Left::facts::ready\nrelease thm Right::facts::ready\nLeft::facts::value = 0\nRight::facts::value = 1\nCommon__m3::facts::value = 10\n");
    root
}

fn write_root_config(root: &Path, reverse: bool) {
    let imports = if reverse {
        "Right = \"./right\"\nLeft = \"./left\"\n"
    } else {
        "Left = \"./left\"\nRight = \"./right\"\n"
    };
    write(
        &root.join("litex.config"),
        &format!(
            "[import]\nCommon__m3 = \"./sentinel\"\n{imports}[export]\nmain = \"./main.lit\"\n"
        ),
    );
}

#[test]
fn same_dependency_alias_is_local_in_cold_and_cached_imports() {
    let root = dependency_fixture();
    let cold = project(&root);
    assert!(cold.run.success, "{:?}", cold.run.session_error);
    assert_eq!(cold.files.len(), 6, "five distinct imports and the root");
    for module in ["sentinel", "left", "left/dep", "right", "right/dep"] {
        assert!(root
            .join(module)
            .join("__litex_knowledge_base__/manifest.json")
            .is_file());
    }
    let cached = project(&root);
    assert!(cached.run.success, "{:?}", cached.run.session_error);
    assert_eq!(
        cached.files.len(),
        1,
        "cache must actually skip imported exports"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn cached_dependency_owners_survive_changed_import_order() {
    let root = dependency_fixture();
    assert!(project(&root).run.success);
    write_root_config(&root, true);
    let reordered = project(&root);
    assert!(reordered.run.success, "{:?}", reordered.run.session_error);
    assert!(
        reordered.files.len() < 6,
        "reordered run must actually reuse at least one cached import"
    );
    assert_eq!(reordered.files.last().unwrap().path, root.join("main.lit"));
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn wrong_same_name_owner_value_is_rejected_after_all_imports_load() {
    let root = dependency_fixture();
    assert!(project(&root).run.success);
    let main = root.join("main.lit");
    let source = fs::read_to_string(&main).unwrap();
    write(&main, &(source + "Left::facts::value = 1\n"));
    let wrong = project(&root);
    assert!(!wrong.run.success);
    assert!(matches!(
        wrong.run.session_error,
        Some(RunSessionError::FailToImport)
    ));
    assert_eq!(
        wrong.files.len(),
        1,
        "only the cached-import root should execute"
    );
    assert_eq!(wrong.files[0].path, main);
    assert!(
        !wrong.files[0].run.success,
        "reject the equation, not the import graph"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn two_aliases_for_one_canonical_path_share_the_same_definition() {
    let root = temp_dir("same_path_aliases");
    write(
        &root.join("library/litex.config"),
        "[export]\nfacts = \"./facts.lit\"\n",
    );
    write(
        &root.join("library/facts.lit"),
        "have fn ident(x R) R = x\n",
    );
    write(&root.join("litex.config"), "[import]\nFirst = \"./library\"\nSecond = \"./library/../library\"\n[export]\nmain = \"./main.lit\"\n");
    write(&root.join("main.lit"), "release obj def First::facts::ident\nrelease obj def Second::facts::ident\nFirst::facts::ident = Second::facts::ident\nFirst::facts::ident(2) = 2\nSecond::facts::ident(2) = 2\n");
    let cold = project(&root);
    assert!(cold.run.success, "{:?}", cold.run.session_error);
    assert_eq!(cold.files.len(), 2, "same-path library executes once");
    let cached = project(&root);
    assert!(cached.run.success);
    assert_eq!(cached.files.len(), 1);
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn same_alias_repeated_within_one_config_is_still_invalid() {
    let root = temp_dir("duplicate_local_alias");
    write(
        &root.join("litex.config"),
        "[import]\nCommon = \"./left\"\nCommon = \"./right\"\n[export]\nmain = \"./main.lit\"\n",
    );
    write(&root.join("main.lit"), "0 = 0\n");
    let result = run_project(LaunchCommand::Repository {
        path: root.clone(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    assert!(
        result.is_err(),
        "aliases must stay unique inside a single config"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn qualified_algo_eval_never_falls_back_to_a_local_same_name() {
    let root = temp_dir("qualified_algo_eval");
    write(
        &root.join("library/litex.config"),
        "[export]\nfacts = \"./facts.lit\"\n",
    );
    write(
        &root.join("library/facts.lit"),
        "algo flag(x R) R by cases:\n    case x = 0: 1\n    case x != 0: 1\n",
    );
    write(
        &root.join("litex.config"),
        "[import]\nOther = \"./library\"\n[export]\nseed = \"./seed.lit\"\n",
    );
    write(&root.join("seed.lit"), "0 = 0\n");
    let target = root.join("target.lit");
    write(&target, "algo flag(x R) R by cases:\n    case x = 0: 0\n    case x != 0: 0\neval flag(0)\neval Other::facts::flag(0)\n");
    let result = run_file_with_config(LaunchCommand::File {
        path: target,
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
    .unwrap();
    assert!(result.run.session_error.is_none());
    assert!(
        !result.run.success,
        "qualified algo evaluation is currently unsupported"
    );
    assert!(
        !result.run.statement_results[1].is_failed(),
        "local eval stays usable"
    );
    assert!(
        result.run.statement_results[2].is_failed(),
        "qualified eval must not select local flag"
    );
    fs::remove_dir_all(root).unwrap();
}
