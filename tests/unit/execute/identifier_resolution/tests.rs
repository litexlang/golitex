use crate::ast::fact::{AtomicFact, Fact};
use crate::ast::stmt::Stmt;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::run_module::{load_config, run_export_file};
use crate::runtime::{CodeSource, RealOrVirtualPath, Runtime};
use crate::tokenize::Tokenizer;

#[test]
fn qualified_values_use_their_own_export_definition() {
    let mut rt = mounted_runtime();
    assert_success(
        &mut rt,
        "have k R = 1\nlet item = 1\nhave fn shift(x R) R = x + 1\n",
    );
    assert_success(
        &mut rt,
        "release obj def base::shift\nrelease obj def Values::base::shift",
    );
    for code in [
        "base::k = 0",
        "Values::base::k = 2",
        "base::item = 0",
        "Values::base::item = 2",
        "base::shift(3) = 3",
        "Values::base::shift(3) = 5",
        "k = 1",
        "shift(3) = 4",
    ] {
        assert_success(&mut rt, code);
    }
    for code in [
        "base::k = 1",
        "Values::base::k = 1",
        "base::item = 1",
        "Values::base::item = 1",
        "base::shift(3) = 4",
        "Values::base::shift(3) = 4",
        "0 = 1",
    ] {
        assert_rejected(&mut rt, code);
    }
}

#[test]
fn qualified_unknown_objects_are_not_well_defined() {
    let mut rt = mounted_runtime();
    // A same-named local definition cannot validate an unknown export member.
    assert_success(&mut rt, "let ghost = 1");
    for code in [
        "base::ghost = base::ghost",
        "Values::base::ghost = Values::base::ghost",
        "let x = base::ghost",
        "let y = Values::base::ghost",
        "base::ghost $in R",
    ] {
        assert_rejected(&mut rt, code);
    }
}

#[test]
fn qualified_lookup_supports_the_live_export_and_compound_objects() {
    let mut rt = mounted_runtime();
    assert_success(
        &mut rt,
        "have k R = 1\nmain::k = 1\nlet pair = (base::k, Values::base::k)\nrelease obj def base::k\nrelease obj def Values::base::k\npair $in finite_seq(R,2)\npair(1)=base::k\npair(2)=Values::base::k\n",
    );
    let tokens = Tokenizer::new()
        .tokenize(
            "k = k\nmain::k = main::k\npair(1)=pair(1)\nmain::pair(1)=main::pair(1)",
            rt.current_file.clone(),
        )
        .unwrap();
    let stmts = rt.parse(&tokens).unwrap();
    let objects: Vec<_> = stmts
        .iter()
        .map(|stmt| {
            let Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(eq))) = stmt else {
                panic!("expected equality");
            };
            eq.left.ir()
        })
        .collect();
    assert_eq!(objects[0], objects[1], "same canonical object key");
    assert_eq!(
        objects[2], objects[3],
        "same canonical compound application key"
    );
    for code in [
        "release thm fn_set_member(pair, finite_seq(R,3))",
        "pair(3)=Values::base::k",
        "pair(1)=Values::base::k",
    ] {
        assert_rejected(&mut rt, code);
    }
}

#[test]
fn identifier_resolution_registered_imported_fixture() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples/module_manager/identifier_resolution");
    let result = crate::run_module::run_project(LaunchCommand::Repository {
        path: root,
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
    .unwrap();
    assert!(result.run.success, "{:?}", result.run.session_error);
    assert!(result.files.iter().all(|file| file.run.success));
}

#[test]
fn live_export_reference_cannot_capture_a_proof_local_name() {
    let mut rt = mounted_runtime();
    let result = rt
        .run_litex_code("sketch:\n    let k = 1\n    main::k = 1\nhave k R = 0\nmain::k = 0\n")
        .unwrap();
    assert!(result.session_error.is_none());
    assert!(result.statement_results[0].is_failed());
    assert!(result.statement_results[1..].iter().all(|r| !r.is_failed()));
}

fn mounted_runtime() -> Runtime {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples/module_manager/identifier_resolution");
    let library = root.join("library");
    let mut rt = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    rt.abort_file();
    rt.global_module_manager
        .set_root_config(load_config(&root, &root).unwrap());
    let config = load_config(&library, &root).unwrap();
    let mod_id = rt
        .global_module_manager
        .record_import("Values".into(), library.clone(), config.clone())
        .unwrap();
    for (file_id, export) in config.exports.iter().enumerate() {
        let run = run_export_file(
            &mut rt,
            &export.name,
            &export.path,
            file_id,
            Some(mod_id),
            CodeSource::ImportedExport {
                global_mod_id: mod_id,
                export_file_id: file_id,
            },
            false,
        )
        .unwrap();
        assert!(
            run.run.success,
            "{}\n{}",
            export.path.display(),
            crate::json_output::emit_run_normal(&run.run, &rt, "file", None)
        );
    }
    let run = run_export_file(
        &mut rt,
        "base",
        &root.join("base.lit"),
        0,
        None,
        CodeSource::RootExport { export_file_id: 0 },
        false,
    )
    .unwrap();
    assert!(run.run.success);
    rt.set_code_source(CodeSource::RootExport { export_file_id: 1 });
    rt.begin_file(RealOrVirtualPath::Eval);
    rt
}

fn assert_success(rt: &mut Runtime, code: &str) {
    let result = rt.run_litex_code(code).unwrap();
    assert!(
        result.success,
        "{code}\n{}",
        crate::json_output::emit_run_normal(&result, rt, "eval", None)
    );
}

fn assert_rejected(rt: &mut Runtime, code: &str) {
    let result = rt.run_litex_code(code).unwrap();
    assert!(
        result.session_error.is_none(),
        "{code}: {:?}",
        result.session_error
    );
    assert!(!result.success, "accepted {code}");
}
