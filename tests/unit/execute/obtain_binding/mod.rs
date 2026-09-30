use crate::ast::stmt::{DefineObjStmt, DefinitionStmt, Stmt};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::{CodeSource, RealOrVirtualPath, Runtime};
use crate::tokenize::Tokenizer;

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
        crate::json_output::emit_run_detailed(&result, &rt, "obtain binding", None)
    );
}

const NAMED: &str = "prop odd(a Z):\n    exist t Z st {a = 2 * t + 1}\nclaim:\n    ? forall n Z:\n        $odd(n)\n        =>:\n            $odd(n)\n    obtain k from $odd(n)\n    n = 2 * k + 1\n";

#[test]
fn local_obtain_equation_works_in_every_code_source() {
    for source in sources() {
        assert_success(source, NAMED);
    }
}

#[test]
fn source_exist_binder_ends_before_same_named_witness_begins() {
    for source in sources() {
        let mut rt = runtime(source);
        let code =
            "witness exist k Z st {k > 0} from 1\nobtain k from exist k Z st {k > 0}\nk > 0\n";
        let tokens = Tokenizer::new()
            .tokenize(code, rt.current_file.clone())
            .unwrap();
        let stmts = rt.parse(&tokens).unwrap();
        let Stmt::Definition(DefinitionStmt::DefineObj(DefineObjStmt::ObtainObjFromExistFact(o))) =
            &stmts[1]
        else {
            panic!("obtain AST");
        };
        let source_id = o.fact.plain().typed_parameters.ordered_param_ids()[0];
        assert_ne!(
            source_id, o.equal_tos[0].id,
            "quantifier and new witness must be distinct bindings"
        );
        assert_eq!(rt.resolve_plain_atom("k").unwrap(), o.equal_tos[0].id);
        for stmt in &stmts {
            assert!(!rt.exec_stmt(stmt).unwrap().is_failed());
        }
    }
}

#[test]
fn wrong_equation_remains_unprovable() {
    for source in sources() {
        let mut rt = runtime(source);
        let result = rt
            .run_litex_code(&NAMED.replace("    n = 2 * k + 1", "    n = 2 * k + 2"))
            .unwrap();
        assert!(!result.success);
        assert!(result.session_error.is_none());
        assert!(result.statement_results[1].is_failed());
    }
}

#[test]
fn repeated_visible_name_is_rejected_like_let_and_have() {
    for source in sources() {
        for code in [
            "let k = 0\nlet k = 1\n0 = 1\n",
            "have k Z\nhave k Z\n",
            "witness exist t Z st {t = 0} from 0\nobtain k from exist t Z st {t = 0}\nwitness exist u Z st {u = 1} from 1\nobtain k from exist u Z st {u = 1}\n0 = 1\n",
            "let k = 0\nsketch:\n    obtain k from exist t Z st {t = 1}\n",
            "obtain k, k from exist a Z, b Z st {a = b}\n",
        ] {
            let mut rt = runtime(source.clone());
            let tokens = Tokenizer::new().tokenize(code, rt.current_file.clone()).unwrap();
            let error = rt.parse(&tokens).expect_err("visible name must not be overwritten");
            assert!(format!("{error:?}").contains("already bound"), "{error:?}");
            assert!(rt.execution_environments_stack[0].facts.facts_by_id.is_empty());
        }
    }
}

#[test]
fn different_witnesses_do_not_prove_zero_equals_one() {
    for source in sources() {
        let mut rt = runtime(source);
        let result = rt.run_litex_code("witness exist t Z st {t = 0} from 0\nobtain k from exist t Z st {t = 0}\nwitness exist u Z st {u = 1} from 1\nobtain j from exist u Z st {u = 1}\nk = 0\nj = 1\n0 = 1\n").unwrap();
        assert!(result.session_error.is_none());
        assert!(result.statement_results[..6].iter().all(|r| !r.is_failed()));
        assert!(result.statement_results[6].is_failed());
    }
}

#[test]
fn completed_proof_scopes_allow_name_reuse_and_do_not_capture_later_export() {
    for source in sources() {
        assert_success(source, "claim:\n    ? 1 = 1\n    witness exist k Z st {k = 0} from 0\n    obtain k from exist k Z st {k = 0}\n    k = 0\nthm trivial:\n    ? 1 = 1\n    witness exist k Z st {k = 1} from 1\n    obtain k from exist k Z st {k = 1}\n    k = 1\nsketch:\n    let k = 2\n    k = 2\nsketch:\n    have k Z = 3\n    k = 3\nlet k = 4\nk = 4\n");
    }
}

#[test]
fn proof_local_witness_does_not_escape() {
    for source in sources() {
        let mut rt = runtime(source);
        let code = "claim:\n    ? 1 = 1\n    witness exist t Z st {t = 0} from 0\n    obtain k from exist t Z st {t = 0}\nk = 0\n";
        let tokens = Tokenizer::new()
            .tokenize(code, rt.current_file.clone())
            .unwrap();
        let error = rt.parse(&tokens).expect_err("local name cannot escape");
        assert!(
            format!("{error:?}").contains("undefined name `k`"),
            "{error:?}"
        );
    }
}

#[test]
fn failed_proof_discards_witness_facts_and_preserves_later_definition() {
    for source in sources() {
        let mut rt = runtime(source);
        let result = rt.run_litex_code("witness exist t Z st {t = 0} from 0\nclaim:\n    ? 0 = 1\n    obtain k from exist t Z st {t = 0}\n    k = 0\nlet k = 1\nk = 1\n0 = 1\n").unwrap();
        assert!(result.session_error.is_none());
        let failed: Vec<_> = result
            .statement_results
            .iter()
            .map(|r| r.is_failed())
            .collect();
        assert_eq!(failed, vec![false, true, false, false, true]);
        assert_eq!(rt.execution_environments_stack.len(), 1);
        assert!(rt.execution_environments_stack[0]
            .definitions
            .identifiers
            .contains_key("k"));
    }
}

#[test]
fn case_arms_parse_independent_witness_bindings() {
    for source in sources() {
        let mut rt = runtime(source);
        let code = "by cases:\n    ? 1 = 1\n    case 0 = 0:\n        witness exist t Z st {t = 0} from 0\n        obtain k from exist t Z st {t = 0}\n        k = 0\n    case 0 != 0:\n        witness exist t Z st {t = 1} from 1\n        obtain k from exist t Z st {t = 1}\n        k = 1\n";
        let tokens = Tokenizer::new()
            .tokenize(code, rt.current_file.clone())
            .unwrap();
        let stmts = rt.parse(&tokens).unwrap();
        let Stmt::By(crate::ast::stmt::ByStmt::ByCasesStmt(cases)) = &stmts[0] else {
            panic!("cases AST");
        };
        let ids: Vec<_> = cases
            .proofs
            .iter()
            .map(|proof| {
                let Stmt::Definition(DefinitionStmt::DefineObj(
                    DefineObjStmt::ObtainObjFromExistFact(o),
                )) = &proof[1]
                else {
                    panic!("obtain AST");
                };
                o.equal_tos[0].id
            })
            .collect();
        assert_ne!(ids[0], ids[1]);
        assert!(
            rt.resolve_plain_atom("k").is_err(),
            "case-local witness must not escape"
        );
    }
}

#[test]
fn multiple_witnesses_substitute_distinct_ids_in_body() {
    for source in sources() {
        assert_success(source, "witness exist a Z, b Z st {a = 0, b = a + 1} from 0, 1\nobtain a, b from exist a Z, b Z st {a = 0, b = a + 1}\na = 0\nb = a + 1\nb = a + 1 = 0 + 1 = 1\n");
    }
}

#[test]
fn missing_exist_source_does_not_create_a_witness() {
    for source in sources() {
        let mut rt = runtime(source);
        let result = rt
            .run_litex_code("obtain k from exist t Z st {t = 0, t = 1}\n0 = 1\n")
            .unwrap();
        assert!(result.session_error.is_none());
        assert!(result.statement_results.iter().all(|r| r.is_failed()));
        assert!(!rt.execution_environments_stack[0]
            .definitions
            .identifiers
            .contains_key("k"));
        assert!(rt.execution_environments_stack[0]
            .facts
            .facts_by_id
            .is_empty());
    }
}

#[test]
fn registered_and_imported_exports_preserve_obtained_witness_identity() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples/module_manager/obtain_bindings");
    let result = crate::run_module::run_project(LaunchCommand::Repository {
        path: root,
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
    .expect("run registered module");
    assert!(result.run.success, "{:?}", result.run.session_error);
    assert_eq!(result.files.len(), 3);
    assert!(result.files.iter().all(|file| file.run.success));
}
