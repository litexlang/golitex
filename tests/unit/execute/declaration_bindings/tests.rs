use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::{CodeSource, Runtime};
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
                        crate::execute::execute_proof_block_stmt::ExecClaimStmtFailed::Local(crate::execute::execute_proof_block_stmt::ExecClaimLocalFailure { body: crate::execute::execute_proof_block_stmt::ExecClaimBodyFailed::NonForall(crate::execute::execute_proof_block_stmt::ExecClaimNonForallFailed::Conclusion { .. }), .. })
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
    let source = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples/module_manager/declaration_bindings");
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "litex-binding-cache-{}-{unique}",
        std::process::id()
    ));
    for relative in [
        "litex.config",
        "local.lit",
        "main.lit",
        "library/litex.config",
        "library/functions.lit",
    ] {
        let target = root.join(relative);
        std::fs::create_dir_all(target.parent().unwrap()).unwrap();
        std::fs::copy(source.join(relative), target).unwrap();
    }
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
    )
    .unwrap();
    let fingerprint =
        crate::knowledge_base::fingerprint_module_recursive(&library, &config, &library).unwrap();
    crate::knowledge_base::try_mount_module(
        &library,
        &fingerprint,
        &crate::knowledge_base::GlobalIdsSnapshot::new(1, 1, 1, 1),
        &std::collections::HashMap::from([(library.to_string_lossy().to_string(), 0)]),
    )
    .unwrap_or_else(|error| panic!("fixture cache mount: {error:?}"));
    let warm = crate::run_module::run_project(LaunchCommand::Repository {
        path: root.clone(),
        session: false,
        strict: false,
        language: OutputLanguage::English,
    })
    .expect("run cached fixture");
    assert!(warm.run.success, "{:?}", warm.run.session_error);
    assert_eq!(
        warm.files.len(),
        2,
        "cached import must skip the library export"
    );
    std::fs::remove_dir_all(root).unwrap();
}

fn sources() -> [CodeSource; 3] {
    [
        CodeSource::Real("test.lit".into()),
        CodeSource::RootExport {
            path: "test.lit".into(),
            export_file_id: 0,
        },
        CodeSource::ImportedExport {
            path: "test.lit".into(),
            global_mod_id: 0,
            export_file_id: 0,
        },
    ]
}

fn runtime(source: CodeSource) -> Runtime {
    let mut rt = Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    );
    rt.finish_source();
    rt.begin_source(source);
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

fn remaining_function_families() -> [(&'static str, &'static str, &'static str, &'static str); 5] {
    [
        (
            "cases",
            "flag",
            r#""#,
            r#"    have fn flag(x R) R by cases:
        case x = 0: 0
        case x != 0: 1
    flag(0) = 0
    flag(2) = 1
"#,
        ),
        (
            "induc",
            "countdown",
            r#""#,
            r#"    have fn countdown(n N) N by induc n from 0:
        case n = 0: 0
        case n >= 1: countdown(n - 1)
    countdown(0) = 0
"#,
        ),
        (
            "exist",
            "ident",
            r#"claim:
    ? forall x R:
        exist! y R st {y = x}
    witness exist! y R st {y = x} from x
"#,
            r#"    have fn ident by exist!:
        ? forall x R:
            exist! y R st {y = x}
    ident(1) = 1
"#,
        ),
        (
            "algo-cases",
            "flag",
            r#""#,
            r#"    algo flag(x R) R by cases:
        case x = 0: 0
        case x != 0: 1
    flag(0) = 0
    flag(2) = 1
"#,
        ),
        (
            "algo-induc",
            "countdown",
            r#""#,
            r#"    algo countdown(n N) N by induc n from 0:
        case n = 0: 0
        case n >= 1: countdown(n - 1)
    countdown(0) = 0
"#,
        ),
    ]
}

#[test]
fn remaining_local_function_families_retain_bindings() {
    for source in sources() {
        for (_, _, prefix, body) in remaining_function_families() {
            assert_success(source.clone(), &format!("{prefix}sketch:\n{body}"));
        }
    }
}

#[test]
fn remaining_function_families_ignore_later_same_name_roots() {
    for source in sources() {
        for (_, name, prefix, body) in remaining_function_families() {
            assert_success(
                source.clone(),
                &format!("{prefix}sketch:\n{body}let {name} = 7\n{name} = 7\n"),
            );
        }
    }
}

#[test]
fn remaining_function_families_reuse_names_after_completed_scopes() {
    for source in sources() {
        for (_, name, prefix, body) in remaining_function_families() {
            assert_success(source.clone(), &format!("{prefix}claim:\n    ? 1 = 1\n{body}thm trivial:\n    ? 1 = 1\n{body}sketch:\n{body}let {name} = 7\n{name} = 7\n"));
        }
    }
}

#[test]
fn remaining_failed_claims_discard_declarations_before_root_reuse() {
    for source in sources() {
        for (_, name, prefix, body) in remaining_function_families() {
            let mut rt = runtime(source.clone());
            let result = rt
                .run_litex_code(&format!(
                    "{prefix}claim:\n    ? 0 = 1\n{body}let {name} = 7\n{name} = 7\n0 = 1\n"
                ))
                .expect("no panic or internal error");
            assert!(result.session_error.is_none());
            let offset = usize::from(!prefix.is_empty());
            assert_eq!(
                result.statement_results[offset..]
                    .iter()
                    .map(|r| r.is_failed())
                    .collect::<Vec<_>>(),
                vec![true, false, false, true]
            );
            assert_eq!(rt.execution_environments_stack.len(), 1);
            assert!(matches!(&result.statement_results[offset], crate::execute::ExecStmtResult::ProofBlock(crate::execute::execute_proof_block_stmt::ExecProofBlockStmtResult::Claim(crate::execute::execute_proof_block_stmt::ExecClaimStmtResult::Failed(crate::execute::execute_proof_block_stmt::ExecClaimStmtFailed::Local(crate::execute::execute_proof_block_stmt::ExecClaimLocalFailure { body: crate::execute::execute_proof_block_stmt::ExecClaimBodyFailed::NonForall(crate::execute::execute_proof_block_stmt::ExecClaimNonForallFailed::Conclusion { .. }), .. }))))), "local definitions must pass before the false conclusion fails");
        }
    }
}

#[test]
fn qualified_predicate_witness_and_obtain_keep_their_owner() {
    for (library, code, should_pass) in [
        (
            r#"prop get(a R):
    exist x R st {x = 0}
thm ready:
    ? $get(0)
    witness $get(0) from 0
"#,
            r#"prop get(a R):
    exist x R st {x = 1}
release thm Other::definitions::ready
obtain k from $Other::definitions::get(0)
k = 1
"#,
            false,
        ),
        (
            r#"prop get(a R):
    exist x R st {x = 0}
thm ready:
    ? $get(0)
    witness $get(0) from 0
"#,
            r#"release thm Other::definitions::ready
obtain k from $Other::definitions::get(0)
k = 0
"#,
            true,
        ),
        (
            r#"prop get(a R):
    exist x R st {x = 0}
"#,
            r#"prop get(a R):
    exist x R st {x = 1}
witness $Other::definitions::get(0) from 1
"#,
            false,
        ),
        (
            r#"prop get(a R):
    exist x R st {x = 0}
"#,
            r#"witness $Other::definitions::get(0) from 0
"#,
            true,
        ),
    ] {
        let result = run_owner_fixture(library, code);
        assert!(
            result.run.session_error.is_none(),
            "{:?}",
            result.run.session_error
        );
        assert_eq!(result.run.success, should_pass, "{code}");
        if !should_pass {
            assert!(result.run.statement_results.last().unwrap().is_failed());
            assert!(
                result.run.statement_results[..result.run.statement_results.len() - 1]
                    .iter()
                    .all(|r| !r.is_failed()),
                "reject the false obligation, not the valid premise"
            );
        }
    }
}

#[test]
fn qualified_predicate_inference_keeps_definition_and_parameter_types() {
    for (library, code, should_pass) in [
        (
            r#"prop zero(x R):
    x = 0
thm ready:
    ? $zero(0)
"#,
            r#"prop zero(x R):
    x = 1
release thm Other::definitions::ready
0 = 1
"#,
            false,
        ),
        (
            r#"prop tagged(x R):
    x = x
thm ready:
    ? $tagged(1 / 2)
"#,
            r#"prop tagged(x N):
    x = x
release thm Other::definitions::ready
1 / 2 $in N
"#,
            false,
        ),
    ] {
        let result = run_owner_fixture(library, code);
        assert!(
            result.run.session_error.is_none(),
            "{:?}",
            result.run.session_error
        );
        assert_eq!(result.run.success, should_pass, "{code}");
        if !should_pass {
            assert!(result.run.statement_results.last().unwrap().is_failed());
            assert!(
                result.run.statement_results[..result.run.statement_results.len() - 1]
                    .iter()
                    .all(|r| !r.is_failed()),
                "reject the false obligation, not the valid premise"
            );
        }
    }
}

#[test]
fn foreign_same_name_induction_retains_its_own_return_domain() {
    for (library, code, should_pass) in [
        (
            r#"have fn step(n N) N = 1
"#,
            r#"release obj def Other::definitions::step
have fn step(n N) N by induc n from 0:
    case n = 0: 0
    case n >= 1: Other::definitions::step(n - 1)
step(1) = Other::definitions::step(1 - 1)
Other::definitions::step(1 - 1) = 1
step(1) = 1
"#,
            true,
        ),
        (
            r#"have fn step(n N) R = 1 / 2
"#,
            r#"release obj def Other::definitions::step
have fn step(n N) N by induc n from 0:
    case n = 0: 0
    case n >= 1: Other::definitions::step(n - 1)
"#,
            false,
        ),
    ] {
        for code in [
            code.to_owned(),
            code.replace("have fn step(n N)", "algo step(n N)"),
        ] {
            let result = run_owner_fixture(library, &code);
            assert!(
                result.run.session_error.is_none(),
                "{:?}",
                result.run.session_error
            );
            assert_eq!(result.run.success, should_pass, "{code}");
            assert!(
                !result.run.statement_results[0].is_failed(),
                "imported signature must release"
            );
        }
    }
}

#[test]
fn template_self_rewrite_preserves_foreign_same_name_calls() {
    for (library, code, should_pass) in [
        (
            r#"have fn step(n N) N = 1
"#,
            r#"release obj def Other::definitions::step
template<t R>:
    have fn step(n N) N by induc n from 0:
        case n = 0: 0
        case n >= 1: Other::definitions::step(n - 1)
\step<0>(1) = Other::definitions::step(1 - 1)
Other::definitions::step(1 - 1) = 1
\step<0>(1) = 1
"#,
            true,
        ),
        (
            r#"have fn step(n N) N = 1
"#,
            r#"release obj def Other::definitions::step
template<t R>:
    have fn step(n N) N by induc n from 0:
        case n = 0: 0
        case n >= 1: Other::definitions::step(n - 1)
\step<0>(1) = \step<0>(1 - 1)
\step<0>(1 - 1) = \step<0>(0)
\step<0>(0) = 0
\step<0>(1) = 0
"#,
            false,
        ),
    ] {
        let result = run_owner_fixture(library, code);
        assert!(
            result.run.session_error.is_none(),
            "{:?}",
            result.run.session_error
        );
        assert_eq!(result.run.success, should_pass, "{code}");
        if !should_pass {
            assert!(
                result.run.statement_results[..2]
                    .iter()
                    .all(|r| !r.is_failed()),
                "legal imported signature and template must pass"
            );
            assert!(
                result.run.statement_results[2].is_failed(),
                "reject the wrong equation at first use"
            );
        }
    }
}

fn run_owner_fixture(library: &str, code: &str) -> crate::run::RunFileResult {
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let id = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let root = std::env::temp_dir().join(format!(
        "litex-function-family-owners-{}-{id}",
        std::process::id()
    ));
    std::fs::create_dir_all(root.join("library")).unwrap();
    std::fs::write(
        root.join("litex.config"),
        "[import]\nOther = \"./library\"\n[export]\ntarget = \"./target.lit\"\n",
    )
    .unwrap();
    std::fs::write(
        root.join("library/litex.config"),
        "[export]\ndefinitions = \"./definitions.lit\"\n",
    )
    .unwrap();
    std::fs::write(root.join("library/definitions.lit"), library).unwrap();
    std::fs::write(root.join("target.lit"), code).unwrap();
    let result = crate::run_module::run_file_with_config(LaunchCommand::File {
        path: root.join("target.lit"),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
    .expect("run registered/imported owner fixture");
    std::fs::remove_dir_all(root).unwrap();
    result
}

#[test]
fn qualified_template_payloads_use_their_own_export_definition() {
    use crate::ast::fact::{AtomicFact, Fact};
    use crate::ast::obj::{FnObjHead, Obj};
    use crate::ast::stmt::Stmt;
    for (library, local, query) in [
        ("template<t R>:\n    have item R = 1\n", "template<t R>:\n    have item R = 0\n", "\\item<0>"),
        ("template<t R>:\n    have fn item(x R) R = 1\n", "template<t R>:\n    have fn item(x R) R = 0\n", "\\item<0>(0)"),
        ("template<t R>:\n    have fn item(x R) R by cases:\n        case x = 0: 1\n        case x != 0: 1\n", "template<t R>:\n    have fn item(x R) R by cases:\n        case x = 0: 0\n        case x != 0: 0\n", "\\item<0>(0)"),
        ("template<t R>:\n    have fn item(n N) N by induc n from 0:\n        case n = 0: 1\n        case n >= 1: item(n - 1)\n", "template<t R>:\n    have fn item(n N) N by induc n from 0:\n        case n = 0: 0\n        case n >= 1: item(n - 1)\n", "\\item<0>(0)"),
    ] {
        for (value, should_pass) in [(0, false), (1, true)] {
            let (mut rt, root) = mounted_owner_runtime(library, local);
            // Qualified template surface syntax is not wired yet. Test the
            // existing qualified AST contract directly, retaining the real loader.
            let code = format!("{query} = {value}\n");
            let tokens = Tokenizer::new().tokenize(&code, rt.current_file.clone()).unwrap();
            let mut statements = rt.parse(&tokens).unwrap();
            let Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(eq))) = &mut statements[0] else { panic!("equal query") };
            let inst = match &mut eq.left {
                Obj::InstantiatedTemplateObj(inst) => inst,
                Obj::FnObj(app) => match app.head.as_mut() {
                    FnObjHead::InstantiatedTemplateObj(inst) => inst,
                    _ => panic!("template head"),
                },
                _ => panic!("template surface"),
            };
            inst.template_name = imported_owner_name("item");
            let result = rt.exec_stmt(&statements[0]).unwrap();
            assert_eq!(!result.is_failed(), should_pass, "{code}");
            std::fs::remove_dir_all(root).unwrap();
        }
    }
}

#[test]
fn qualified_struct_payloads_keep_their_field_carriers() {
    use crate::ast::fact::Fact;
    use crate::ast::obj::{Obj, StructAndFieldAccessObj};
    use crate::ast::param::ParamType;
    use crate::ast::stmt::Stmt;
    for (carrier, should_pass) in [("N", false), ("R", true)] {
        let (mut rt, root) = mounted_owner_runtime(
            "struct Pair:\n    x R\n    y R\n",
            "struct Pair:\n    x N\n    y N\n",
        );
        let code = format!("forall p &Pair:\n    p.x $in {carrier}\n");
        let tokens = Tokenizer::new()
            .tokenize(&code, rt.current_file.clone())
            .unwrap();
        let mut statements = rt.parse(&tokens).unwrap();
        let Stmt::Fact(Fact::ForallFact(forall)) = &mut statements[0] else {
            panic!("forall query")
        };
        let ParamType::Obj(Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(view))) =
            &mut forall.typed_parameters.groups[0].param_type
        else {
            panic!("struct carrier")
        };
        view.name = imported_owner_name("Pair");
        let result = rt.exec_stmt(&statements[0]).unwrap();
        assert_eq!(!result.is_failed(), should_pass, "{code}");
        std::fs::remove_dir_all(root).unwrap();
    }
}

fn imported_owner_name(name: &str) -> crate::ast::names::AtomicName {
    crate::ast::names::AtomicName::WithModAndExportFileId {
        global_mod_id: 0,
        export_file_id: 0,
        name: name.into(),
    }
}

fn mounted_owner_runtime(library: &str, local: &str) -> (Runtime, std::path::PathBuf) {
    use crate::run_module::{load_config, run_export_file};
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let id = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let root = std::env::temp_dir().join(format!(
        "litex-function-family-payloads-{}-{id}",
        std::process::id()
    ));
    let lib = root.join("library");
    std::fs::create_dir_all(&lib).unwrap();
    std::fs::write(
        root.join("litex.config"),
        "[import]\nOther = \"./library\"\n[export]\ntarget = \"./target.lit\"\n",
    )
    .unwrap();
    std::fs::write(
        lib.join("litex.config"),
        "[export]\ndefinitions = \"./definitions.lit\"\n",
    )
    .unwrap();
    std::fs::write(lib.join("definitions.lit"), library).unwrap();
    let mut rt = runtime(CodeSource::RootExport {
        path: "test.lit".into(),
        export_file_id: 0,
    });
    rt.abort_source();
    rt.global_module_manager
        .set_root_config(load_config(&root, &root).unwrap());
    let config = load_config(&lib, &root).unwrap();
    let mod_id = rt
        .global_module_manager
        .record_import("Other".into(), lib.clone(), config.clone())
        .unwrap();
    let run = run_export_file(
        &mut rt,
        "definitions",
        CodeSource::ImportedExport {
            path: lib.join("definitions.lit"),
            global_mod_id: mod_id,
            export_file_id: 0,
        },
        false,
    )
    .unwrap();
    assert!(run.run.success, "{:?}", run.run.session_error);
    rt.begin_source(CodeSource::RootExport {
        path: "test.lit".into(),
        export_file_id: 0,
    });
    let result = rt.run_litex_code(local).unwrap();
    assert!(result.success, "{:?}", result.session_error);
    (rt, root)
}

#[test]
fn qualified_registration_uses_its_own_predicate_arity() {
    let library = "prop eq(a, b set):\n    a = b\n";
    let local = "prop eq(a, b, c set):\n    a = a\n";
    for code in [
        "register reflexive:\n    ? forall x set:\n        $Other::definitions::eq(x, x)\n",
        "register symmetric:\n    ? forall x, y set:\n        $Other::definitions::eq(x, y)\n        =>:\n            $Other::definitions::eq(y, x)\n",
        "register transitive:\n    ? forall x, y, z set:\n        $Other::definitions::eq(x, y)\n        $Other::definitions::eq(y, z)\n        =>:\n            $Other::definitions::eq(x, z)\n",
    ] {
        let result = run_owner_fixture(library, &format!("{local}{code}"));
        assert!(result.run.session_error.is_none());
        assert!(result.run.success, "{code}");
    }
    let result = run_owner_fixture("prop eq(a, b set):\n    a != a\n", "prop eq(a, b set):\n    a = a\nregister reflexive:\n    ? forall x set:\n        $Other::definitions::eq(x, x)\n");
    assert!(result.run.session_error.is_none());
    assert!(
        !result.run.success,
        "a true local predicate cannot prove foreign reflexivity"
    );
}

#[test]
fn exist_function_source_binders_precede_the_new_function() {
    for source in sources() {
        assert_success(source.clone(), "claim:\n    ? forall f R:\n        exist! y R st {y = f}\n    witness exist! y R st {y = f} from f\nhave fn f by exist!:\n    ? forall f R:\n        exist! y R st {y = f}\nf(1) = 1\n");
        assert_success(source, "claim:\n    ? forall x R:\n        exist! f R st {f = x}\n    witness exist! f R st {f = x} from x\nhave fn f by exist!:\n    ? forall x R:\n        exist! f R st {f = x}\nf(1) = 1\n");
    }
}

#[test]
fn exported_have_bodies_and_dependent_carriers_keep_their_published_identity() {
    for source in sources() {
        assert_success(source.clone(), "witness exist q N+ st {q > 0} from 1\nhave positive N+:\n    positive > 0\npositive > 0\nrelease obj def positive\npositive > 0\n");
        assert_success(source.clone(), "have A nonempty_set, x A\nx $in A\n");
        assert_success(
            source.clone(),
            "have A set, x A = R, 0\nx $in A\nrelease obj def x\nx $in A\n",
        );
        assert_success(source, "have fn identity(t R) R = t\nhave by fn_preimage: pre from identity(2) $in fn_range(identity)\nrelease obj def pre\npre $in R\nidentity(pre) = identity(2)\n");
    }
}

#[test]
fn indexed_struct_carriers_and_negated_claim_binders_are_usable() {
    for code in [
        "struct S:\n    f R\n    g R\nforall v finite_seq(&S,2):\n    v(1).g $in R\n",
        "struct S:\n    f R\n    g R\nforall v seq(&S):\n    v(3).g $in R\n",
        "struct S:\n    f R\n    g R\nforall v matrix(&S,2,2):\n    v(1,2).g $in R\n",
        "claim:\n    ? not forall n Z:\n        n > 0\n    have n Z = 0\n    n <= 0\n    witness exist k Z st {not k > 0} from n\n",
    ] { assert_success(CodeSource::Eval, code); }
}

#[test]
fn run_examples_round3_repair_tracers() {
    for path in [
        "examples/stmt_nodes/by/induction_binding_isolation.lit",
        "examples/stmt_nodes/by/negated_forall_witness_scope.lit",
        "examples/wd/refined_indexed_carriers.lit",
        "examples/real_analysis/multivariable_symbolic_coordinates.lit",
    ] {
        let source =
            std::fs::read_to_string(std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(path))
                .unwrap();
        assert_success(CodeSource::Eval, &source);
    }
}

#[test]
fn existential_witness_dependencies_follow_the_complete_object_tree() {
    for source in sources() {
        let mut rt = runtime(source);
        let accepted = rt.run_litex_code("exist x R st {x > -1}\nexist x R st {x = 1+1}\nhave a R = 1\nexist x R st {x = a}\nhave fn value(t R) R = t\nexist x R st {x > value(0)}\n").unwrap();
        assert!(
            accepted.success,
            "{}",
            crate::json_output::emit_run_detailed(&accepted, &rt, "existential dependencies", None)
        );
        for invalid in ["exist x R st {x = x+1}", "exist x R st {x > x}"] {
            assert!(!rt.run_litex_code(invalid).unwrap().success, "{invalid}");
        }
        assert!(rt.run_litex_code("a = 1").unwrap().success);
    }
}

#[test]
fn refined_and_stored_prefix_function_carriers_preserve_later_application_layers() {
    for source in sources() {
        assert_success(
            source.clone(),
            "forall f fn(x R) {u fn(t R) R: u(0)=0}:\n    f(1)(0)=f(1)(0)\n",
        );
        assert_success(
            source,
            "forall S set,f fn(x R) S:\n    f(1) $in fn(t R) R\n    =>:\n        f(1)(2) $in R\n",
        );
    }
}

#[test]
fn derived_memberships_expand_their_existing_carrier_conditions() {
    for source in sources() {
        for code in [
            r#"forall x intersect({t R: t>0},{t R: t<1}):
    x>0
    x<1
"#,
            r#"forall x set_minus({t R: t>0},{0}):
    x>0
"#,
            r#"have fn f(u {t R: t>0}) R=u
forall x preimage(f,1):
    x>0
"#,
            r#"have fn f(u {t R: t>0}) R=u
forall x preimage_set(f,{1,2}):
    x>0
"#,
            r#"have fn g(v finite_seq(R,2)) R=v(1)
forall x preimage(g,1):
    x(1) $in R
"#,
            r#"have fn h(u R) finite_seq(R,2)=(u,u)
forall z fn_range(h):
    z(1) $in R
"#,
            r#"forall A,B set,x A:
    A={t B: t=t}
    B={t A: t=t}
    =>:
        x $in A
        x $in B
"#,
        ] {
            assert_success(source.clone(), code);
        }
    }
}

#[test]
fn projected_memberships_preserve_branches_and_statement_scope() {
    for source in sources() {
        let mut rt = runtime(source);
        let failed = rt
            .run_litex_code(
                r#"forall x union({t R: t>0},{t R: t<0}):
    x>0
"#,
            )
            .unwrap();
        assert!(!failed.success && failed.session_error.is_none());
        assert!(
            rt.run_litex_code(
                r#"forall x intersect({t R: t>0},{t R: t<1}):
    x>0
    x<1
"#
            )
            .unwrap()
            .success
        );
        let failed = rt.run_litex_code("forall x R:\n    x>0").unwrap();
        assert!(!failed.success && failed.session_error.is_none());
        assert!(!rt.run_litex_code("1=0").unwrap().success);
        assert!(rt.run_litex_code("2+1=3").unwrap().success);
    }
}

#[test]
fn struct_typed_function_binders_publish_their_existing_field_conditions() {
    for source in sources() {
        assert_success(
            source,
            r#"struct PosPair:
    a R
    b R
    <=>:
        a>0
have fn inv_a(p &PosPair) R=1/p.a
have f fn(p &PosPair) R
let selected={p &PosPair: 1/p.a>0}
struct Nested:
    pair &PosPair
    marker R
    <=>:
        1/pair.a>0
have fn piecewise_inv(p &PosPair) R by cases:
    case p.a>0: 1/p.a
"#,
        );
    }
}

#[test]
fn struct_witness_introductions_publish_their_existing_field_conditions() {
    let code = r#"struct PositiveRecord:
    a R
    b R
    <=>:
        a>0
have fn record_id(p &PositiveRecord) &PositiveRecord=p
claim:
    ? forall p &PositiveRecord:
        p=p
    have chosen &PositiveRecord:
        chosen=p
    1/chosen.a=1/chosen.a
    witness exist other &PositiveRecord st {other=p} from p
    obtain obtained from exist other &PositiveRecord st {other=p}
    1/obtained.a=1/obtained.a
    witness exist checked &PositiveRecord st {1/checked.a=1/checked.a} from p
    record_id(p) $in fn_range(record_id)
    have by fn_preimage: pre from record_id(p) $in fn_range(record_id)
    1/pre.a=1/pre.a
"#;
    for source in sources() {
        assert_success(source, code);
    }
}

#[test]
fn struct_parameter_opening_does_not_invent_or_leak_field_conditions() {
    for source in sources() {
        let mut rt = runtime(source);
        assert!(
            rt.run_litex_code(
                r#"struct PositivePair:
    a R
    b R
    <=>:
        a>0
have fn good(p &PositivePair) R=1/p.a
struct PlainPair:
    a R
    b R
"#
            )
            .unwrap()
            .success
        );
        let failed = rt
            .run_litex_code("have fn bad(p &PlainPair) R=1/p.a")
            .unwrap();
        assert!(!failed.success && failed.session_error.is_none());
        assert!(!rt.run_litex_code("1=0").unwrap().success);
        assert!(
            rt.run_litex_code(
                r#"have anchor R=2
anchor+1=3"#
            )
            .unwrap()
            .success
        );
    }
}
