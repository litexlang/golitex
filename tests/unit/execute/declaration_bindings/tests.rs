use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::{CodeSource, RealOrVirtualPath, Runtime};
use crate::tokenize::Tokenizer;

#[test]
fn local_function_retains_its_binding() {
    for source in sources() {
        assert_success(
            source,
            "sketch:\n    have fn ident(x R) R = x\n    ident(1) = 1\n",
        );
    }
}

#[test]
fn local_preimage_retains_its_binding() {
    for source in sources() {
        assert_success(source, "have fn shift(x R) R = x + 1\nshift(2) $in fn_range(shift)\nsketch:\n    have by fn_preimage: source from shift(2) $in fn_range(shift)\n    source $in R\n    shift(2) = shift(source)\n");
    }
}

#[test]
fn later_root_names_do_not_capture_local_declarations() {
    for source in sources() {
        assert_success(source, "sketch:\n    have fn ident(x R) R = x\n    ident(1) = 1\n    ident(2) $in fn_range(ident)\n    have by fn_preimage: source from ident(2) $in fn_range(ident)\n    source $in R\n    ident(2) = ident(source)\nlet ident = 0\nlet source = 1\nident = 0\nsource = 1\n");
    }
}

#[test]
fn completed_scopes_allow_fresh_function_and_preimage_names() {
    let body = "    have fn ident(x R) R = x\n    ident(2) $in fn_range(ident)\n    have by fn_preimage: source from ident(2) $in fn_range(ident)\n    ident(source) = ident(2)\n";
    let code =
        format!("claim:\n    ? 1 = 1\n{body}thm trivial:\n    ? 1 = 1\n{body}sketch:\n{body}");
    for source in sources() {
        assert_success(source, &code);
    }
}

#[test]
fn wrong_local_equations_remain_unprovable() {
    for source in sources() {
        for code in [
            "sketch:\n    have fn ident(x R) R = x\n    ident(1) = 2\n",
            "have fn shift(x R) R = x + 1\nsketch:\n    have by fn_preimage: source from shift(2) $in fn_range(shift)\n    shift(source) = shift(2) + 1\n",
        ] {
            let mut rt = runtime(source.clone());
            let result = rt.run_litex_code(code).expect("execution must not panic or return an internal error");
            assert!(result.session_error.is_none(), "{:?}", result.session_error);
            assert!(!result.success);
            assert!(result.statement_results.last().unwrap().is_failed());
        }
    }
}

#[test]
fn local_names_do_not_escape() {
    for source in sources() {
        for code in [
            "sketch:\n    have fn ident(x R) R = x\nident(1) = 1\n",
            "have fn shift(x R) R = x + 1\nsketch:\n    have by fn_preimage: source from shift(2) $in fn_range(shift)\nsource $in R\n",
        ] {
            let mut rt = runtime(source.clone());
            let tokens = Tokenizer::new().tokenize(code, rt.current_file.clone()).unwrap();
            let error = rt.parse(&tokens).expect_err("local name must not escape");
            assert!(format!("{error:?}").contains("undefined name"));
        }
    }
}

#[test]
fn duplicate_visible_names_remain_rejected() {
    for source in sources() {
        for code in [
            "have fn ident(x R) R = x\nhave fn ident(y R) R = y\n",
            "have fn shift(x R) R = x + 1\nhave by fn_preimage: source from shift(2) $in fn_range(shift)\nhave by fn_preimage: source from shift(3) $in fn_range(shift)\n",
        ] {
            let mut rt = runtime(source.clone());
            let tokens = Tokenizer::new().tokenize(code, rt.current_file.clone()).unwrap();
            let error = rt.parse(&tokens).expect_err("visible name must not be replaced");
            assert!(format!("{error:?}").contains("already bound"));
        }
    }
}

#[test]
fn failed_proof_discards_declarations_and_preserves_later_names() {
    for source in sources() {
        let mut rt = runtime(source);
        let result = rt.run_litex_code("claim:\n    ? 0 = 1\n    have fn ident(x R) R = x\n    ident(2) $in fn_range(ident)\n    have by fn_preimage: source from ident(2) $in fn_range(ident)\n    ident(source) = ident(2)\nlet ident = 0\nlet source = 1\nident = 0\nsource = 1\n0 = 1\n").unwrap();
        assert!(result.session_error.is_none(), "{:?}", result.session_error);
        let failed: Vec<_> = result
            .statement_results
            .iter()
            .map(|r| r.is_failed())
            .collect();
        assert_eq!(failed, vec![true, false, false, false, false, true]);
        assert_eq!(rt.execution_environments_stack.len(), 1);
        assert!(matches!(
            &result.statement_results[0],
            crate::execute::ExecStmtResult::ProofBlock(
                crate::execute::execute_proof_block_stmt::ExecProofBlockStmtResult::Claim(
                    crate::execute::execute_proof_block_stmt::ExecClaimStmtResult::Failed(
                        crate::execute::execute_proof_block_stmt::ExecClaimStmtFailed::Conclusion { .. }
                    )
                )
            )
        ), "the local declarations must succeed before the false conclusion is rejected");
    }
}

#[test]
fn multiple_preimages_preserve_each_coordinate_binding() {
    for source in sources() {
        assert_success(source, "have fn add2(x R, y R) R = x + y\nsketch:\n    have by fn_preimage: a, b from add2(1, 2) $in fn_range(add2)\n    a $in R\n    b $in R\n    add2(1, 2) = add2(a, b)\nlet a = 0\nlet b = 1\na = 0\nb = 1\n");
    }
}

#[test]
fn missing_range_membership_does_not_create_a_preimage() {
    for source in sources() {
        let mut rt = runtime(source);
        let result = rt.run_litex_code("have fn zero(x R) R = 0\nhave by fn_preimage: source from 1 $in fn_range(zero)\n0 = 1\n").unwrap();
        assert!(result.session_error.is_none());
        assert!(!result.statement_results[0].is_failed());
        assert!(result.statement_results[1..].iter().all(|r| r.is_failed()));
        assert!(!rt.execution_environments_stack[0]
            .definitions
            .identifiers
            .contains_key("source"));
    }
}

#[test]
fn registered_and_imported_functions_preserve_distinct_owners() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples/module_manager/declaration_bindings");
    let result = crate::run_module::run_project(LaunchCommand::Repository {
        path: root.clone(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
    .expect("run registered/imported fixture");
    assert!(result.run.success, "{:?}", result.run.session_error);
    assert!(result.files.len() >= 2);
    assert!(result.files.iter().all(|file| file.run.success));
    let library = root.join("library").canonicalize().unwrap();
    let config = crate::module_manager::parse_litex_config(
        &std::fs::read_to_string(library.join("litex.config")).unwrap(),
        &library,
        &library,
    ).unwrap();
    let fingerprint = crate::knowledge_base::fingerprint_module_recursive(
        &library, &config, &library,
    ).unwrap();
    crate::knowledge_base::try_mount_module(
        &library,
        &fingerprint,
        &crate::knowledge_base::GlobalIdsSnapshot::new(1, 1, 1, 1),
        &std::collections::HashMap::from([(library.to_string_lossy().to_string(), 0)]),
    ).unwrap_or_else(|error| panic!("fixture cache mount: {error:?}"));
    let warm = crate::run_module::run_project(LaunchCommand::Repository {
        path: root,
        session: false,
        strict: true,
        language: OutputLanguage::English,
    }).expect("run cached fixture");
    assert!(warm.run.success, "{:?}", warm.run.session_error);
    assert_eq!(warm.files.len(), 2, "cached import must skip the library export");
}

fn sources() -> [CodeSource; 3] {
    [
        CodeSource::StandaloneFile,
        CodeSource::RootExport { export_file_id: 0 },
        CodeSource::ImportedExport {
            global_mod_id: 0,
            export_file_id: 0,
        },
    ]
}

fn runtime(source: CodeSource) -> Runtime {
    let mut rt = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    rt.finish_file();
    rt.set_code_source(source);
    rt.begin_file(RealOrVirtualPath::Eval);
    rt
}

fn assert_success(source: CodeSource, code: &str) {
    let mut rt = runtime(source);
    let result = rt.run_litex_code(code).expect("parse/execute");
    assert!(
        result.success,
        "{}",
        crate::json_output::emit_run_detailed(&result, &rt, "declaration binding", None)
    );
}
