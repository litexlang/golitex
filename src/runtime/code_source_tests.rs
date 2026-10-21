use crate::prelude::*;

#[test]
fn one_source_stamps_paths_ast_and_export_identity() {
    for source in [
        CodeSource::Eval,
        CodeSource::Repl,
        CodeSource::Real("standalone.lit".into()),
        CodeSource::RootExport {
            path: "root.lit".into(),
            export_file_id: 2,
        },
        CodeSource::ImportedExport {
            path: "lib/base.lit".into(),
            global_mod_id: 3,
            export_file_id: 2,
        },
    ] {
        let mut runtime = Runtime::new(LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        });
        runtime.abort_source();
        runtime.begin_source(source.clone());
        assert_eq!(
            runtime
                .top_exec_env()
                .session_view
                .as_ref()
                .unwrap()
                .code_source,
            source,
        );
        let blocks = crate::tokenize::Tokenizer::new()
            .tokenize("have n N", runtime.current_file.clone())
            .unwrap();
        assert_eq!(blocks[0].source_path, source);
        let statement = runtime.parse_token_block(&blocks[0]).unwrap();
        let Stmt::Definition(DefinitionStmt::DefineObj(DefineObjStmt::HaveObjInNonemptySetStmt(
            have,
        ))) = &statement
        else {
            panic!("have statement");
        };
        assert_eq!(have.line_file.origin, source);
        assert!(!runtime.exec_stmt(&statement).unwrap().is_failed());
        let reference = runtime
            .identifier_obj_for_plain_free_ref("n".into())
            .unwrap();
        match source {
            CodeSource::RootExport { export_file_id, .. } => {
                assert!(
                    matches!(reference, IdentifierObj::WithExportFileId { export_file_id: id, .. } if id == export_file_id)
                );
            }
            CodeSource::ImportedExport {
                global_mod_id,
                export_file_id,
                ..
            } => {
                assert!(
                    matches!(reference, IdentifierObj::WithModAndExportFileId { global_mod_id: m, export_file_id: f, .. } if m == global_mod_id && f == export_file_id)
                );
            }
            CodeSource::Eval | CodeSource::Repl | CodeSource::Real(_) => {
                assert!(matches!(reference, IdentifierObj::Plain { .. }));
            }
        }
        let error = runtime
            .run_litex_code("have")
            .unwrap()
            .input_error
            .unwrap()
            .error;
        assert_eq!(error.path, source);
    }
}

#[test]
fn continued_repl_keeps_the_open_environment_and_original_snapshot() {
    let source = CodeSource::Real("initial.lit".into());
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: true,
        strict: true,
        language: OutputLanguage::English,
    });
    runtime.abort_source();
    runtime.begin_source(source.clone());
    assert!(runtime.run_litex_code("have k N\nk >= 0").unwrap().success);
    let original_id = runtime.resolve_plain_atom("k").unwrap();
    runtime.current_file = CodeSource::Repl;
    let result = runtime.run_litex_code("k >= 0\n1 = 2\nk >= 0").unwrap();
    assert!(result.session_error.is_none());
    assert_eq!(
        result
            .statement_results
            .iter()
            .map(|s| s.is_failed())
            .collect::<Vec<_>>(),
        [false, true, false]
    );
    assert_eq!(runtime.resolve_plain_atom("k").unwrap(), original_id);
    assert_eq!(runtime.execution_environments_stack.len(), 1);
    assert_eq!(runtime.parse_scope_stack.len(), 1);
    assert_eq!(
        runtime
            .top_exec_env()
            .session_view
            .as_ref()
            .unwrap()
            .code_source,
        source
    );
    let error = runtime
        .run_litex_code("$is_finite_set(1, 2)")
        .unwrap()
        .input_error
        .unwrap()
        .error;
    assert_eq!(error.path, CodeSource::Repl);
}
