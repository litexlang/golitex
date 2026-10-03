use crate::ast::fact::Fact;
use crate::ast::stmt::{ByStmt, Stmt};
use crate::execute::execute_by_stmt::result::{
    ByContradictionClosingFailed, ExecByContraStmtFailed,
};
use crate::execute::execute_by_stmt::{ExecByContraStmtResult, ExecByStmtResult};
use crate::execute::ExecStmtResult;
use crate::knowledge_base::JsonValue;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

#[test]
fn every_representable_closing_family_retains_both_real_proofs() {
    for (family, source) in closing_sources() {
        let mut rt = runtime();
        let run = rt.run_litex_code(&source).unwrap();
        let json = crate::json_output::emit_run_detailed(&run, &rt, "eval", None);
        assert!(run.success, "{family}: {json}");
        let ExecStmtResult::By(ExecByStmtResult::Contra(ExecByContraStmtResult::Success(s))) =
            run.statement_results.last().unwrap()
        else {
            panic!("{family}: contra result");
        };
        assert_eq!(fact_family(&s.closing.impossible_fact), family);
        assert!(!s.closing.impossible.is_failed(), "{family}: P");
        assert!(!s.closing.negated_impossible.is_failed(), "{family}: not P");
        assert_eq!(rt.execution_environments_stack.len(), 1);
        assert!(s
            .local_env
            .facts
            .facts_by_id
            .contains_key(&s.reverse_assumption_fact_id));
        assert!(!rt
            .top_exec_env()
            .facts
            .facts_by_id
            .contains_key(&s.reverse_assumption_fact_id));
    }
}

#[test]
fn partial_conjunction_and_unproved_opposite_cannot_close() {
    for (source, missing_positive) in [
        (
            "by contra:\n    ? 1 = 1\n    impossible 1 = 1 and 0 = 1",
            true,
        ),
        (
            "by contra:\n    ? 1 = 2\n    impossible 1 = 1 and 0 = 0",
            false,
        ),
        (
            "by contra:\n    ? 1 = 2\n    impossible 1 = 1 or 0 = 1",
            false,
        ),
        ("by contra:\n    ? 1 = 2\n    impossible 0 <= 1 <= 2", false),
    ] {
        let mut rt = runtime();
        let run = rt.run_litex_code(source).unwrap();
        assert!(!run.success && run.session_error.is_none(), "{source}");
        let ExecStmtResult::By(ExecByStmtResult::Contra(ExecByContraStmtResult::Failed(
            ExecByContraStmtFailed::Closing(failure),
        ))) = &run.statement_results[0]
        else {
            panic!("expected closing failure: {source}");
        };
        match failure {
            ByContradictionClosingFailed::Impossible(proof) if missing_positive => {
                assert!(proof.is_failed())
            }
            ByContradictionClosingFailed::NegatedImpossible(proof) if !missing_positive => {
                assert!(proof.is_failed())
            }
            _ => panic!("wrong missing side: {source}"),
        }
        let json = crate::json_output::emit_run_detailed(&run, &rt, "eval", None);
        assert!(json.contains(if missing_positive {
            "\"phase\": \"impossible\""
        } else {
            "\"phase\": \"negated_impossible\""
        }));
    }
}

#[test]
fn quantifier_closing_uses_the_complete_body_and_keeps_wd_obligations() {
    for source in [
        "by contra:\n    ? 1 = 1\n    impossible forall y {0}:\n        y = 0\n        y = 1",
        "by contra:\n    ? 1 = 1\n    impossible exist y {0} st {1 / y = 1 / y}",
        "by contra:\n    ? 1 = 1\n    impossible forall y {0}:\n        1 / y = 1 / y",
    ] {
        let mut rt = runtime();
        let run = rt.run_litex_code(source).unwrap();
        assert!(!run.success && run.session_error.is_none(), "{source}");
        let ExecStmtResult::By(ExecByStmtResult::Contra(ExecByContraStmtResult::Failed(
            ExecByContraStmtFailed::Closing(ByContradictionClosingFailed::Impossible(proof)),
        ))) = &run.statement_results[0]
        else {
            panic!("complete closing or WD must fail: {source}");
        };
        assert!(proof.is_failed());
    }
}

#[test]
fn unsupported_nested_quantifier_closing_fails_without_publishing_the_goal() {
    let source = "forall x {0}:\n    exist y {0} st {y = x}\nby contra:\n    ? 1 = 1\n    impossible forall z {0}:\n        exist w {0} st {w = z}";
    let mut rt = runtime();
    let run = rt.run_litex_code(source).unwrap();
    assert!(!run.success && run.session_error.is_none());
    assert!(!run.statement_results[0].is_failed());
    let ExecStmtResult::By(ExecByStmtResult::Contra(ExecByContraStmtResult::Failed(
        ExecByContraStmtFailed::Closing(ByContradictionClosingFailed::NegateImpossibleUnsupported(
            message,
        )),
    ))) = &run.statement_results[1]
    else {
        panic!(
            "{}",
            crate::json_output::emit_run_detailed(&run, &rt, "eval", None)
        );
    };
    assert!(message.contains("existential conclusion"));
    let json = crate::json_output::emit_run_detailed(&run, &rt, "eval", None);
    assert!(json.contains("\"phase\": \"negate_impossible\""));
    assert!(rt
        .top_exec_env()
        .facts
        .facts_by_id
        .values()
        .all(|fact| { fact.readable_string() != "1 != 1" }));
}

#[test]
fn successful_and_failed_closings_keep_binder_and_proof_names_local() {
    let source = "forall x {0}:\n    x = 0\nby contra:\n    ? forall n {0}:\n        n = 0\n    have temporary R = 2\n    impossible forall q {0}:\n        q = 0";
    let mut rt = runtime();
    let run = rt.run_litex_code(source).unwrap();
    assert!(
        run.success,
        "{}",
        crate::json_output::emit_run_detailed(&run, &rt, "eval", None)
    );
    for name in ["temporary", "q", "n"] {
        assert!(!rt.run_litex_code(&format!("{name} = 0")).unwrap().success);
        assert!(
            rt.run_litex_code(&format!("have {name} R = 3"))
                .unwrap()
                .success
        );
    }
    let mut rt = runtime();
    let run = rt
        .run_litex_code(
            "by contra:\n    ? 1 = 2\n    have temporary R = 2\n    impossible 1 = 1 and 0 = 0",
        )
        .unwrap();
    assert!(!run.success && run.session_error.is_none());
    assert!(rt.run_litex_code("have temporary R = 3").unwrap().success);
    assert!(!rt.run_litex_code("1 = 2").unwrap().success);
}

#[test]
fn compound_closing_ids_cite_only_actual_local_facts() {
    let mut rt = runtime();
    let run = rt
        .run_litex_code("by contra:\n    ? 1 = 1 and 0 = 0\n    impossible 1 != 1 or 0 != 0")
        .unwrap();
    assert!(run.success);
    let ExecStmtResult::By(ExecByStmtResult::Contra(ExecByContraStmtResult::Success(s))) =
        &run.statement_results[0]
    else {
        panic!("contra");
    };
    assert_eq!(
        s.closing.impossible_fact_id,
        Some(s.reverse_assumption_fact_id)
    );
    assert!(matches!(
        s.local_env.facts.facts_by_id[&s.reverse_assumption_fact_id],
        Fact::OrFact(_)
    ));
    assert!(s.closing.negated_impossible_fact_id.is_none());
}

#[test]
fn displayed_compound_and_multiline_tails_reparse_and_execute() {
    for (family, source) in closing_sources() {
        let mut rt = runtime();
        let blocks = Tokenizer::new()
            .tokenize(&source, rt.current_file.clone())
            .unwrap();
        let statements = rt.parse(&blocks).unwrap();
        let Stmt::By(ByStmt::ByContraStmt(last)) = statements.last().unwrap() else {
            panic!("contra");
        };
        assert_eq!(fact_family(&last.impossible_fact), family);
        let readable = statements
            .iter()
            .map(Stmt::readable_string)
            .collect::<Vec<_>>()
            .join("\n");
        let mut replay = runtime();
        let run = replay.run_litex_code(&readable).unwrap();
        assert!(
            run.success,
            "{family}: {readable}\n{}",
            crate::json_output::emit_run_detailed(&run, &replay, "eval", None)
        );
    }
}

#[test]
fn malformed_tails_and_cases_compound_tail_stay_rejected() {
    for source in [
        "by contra:\n    ? 1 = 1\n    impossible 1 = 1 and 0 = 0 trailing",
        "by contra:\n    ? 1 = 1\n    impossible 1 = 1\n        0 = 0",
        "by contra:\n    ? 1 = 1\n    impossible exist q {0} st {q = 0}\n        0 = 0",
        "by contra:\n    ? 1 = 1\n    impossible forall q {0}:",
        "by contra:\n    ? 1 = 1\n    impossible not exist! q {0} st {q = 0}",
        "by cases:\n    ? 1 = 1\n    case 1 != 1:\n        impossible 1 = 1 and 0 = 0",
    ] {
        let mut rt = runtime();
        match rt.run_litex_code(source) {
            Ok(run) => assert!(!run.success && run.session_error.is_some(), "{source}"),
            Err(error) => assert!(matches!(error, crate::runtime::RuntimeError::ParseError(_))),
        }
        assert!(rt.run_litex_code("have q R = 2").unwrap().success);
    }
    assert!(runtime().run_litex_code("by cases:\n    ? 1 = 1\n    case 1 = 1\n    case 1 != 1:\n        impossible 1 = 1").unwrap().success);
}

#[test]
fn detailed_output_retains_both_closing_proofs_after_scope_is_taken() {
    let mut rt = runtime();
    let run = rt
        .run_litex_code("by contra:\n    ? 1 = 1\n    impossible 1 = 1 and 0 = 0")
        .unwrap();
    assert!(run.success);
    let text = crate::json_output::emit_run_detailed(&run, &rt, "eval", None);
    let output = JsonValue::parse(&text).unwrap();
    let JsonValue::Object(output) = output else {
        panic!("object")
    };
    let JsonValue::Array(statements) = output.get("statement_results").unwrap() else {
        panic!("statements")
    };
    let JsonValue::Object(statement) = &statements[0] else {
        panic!("statement")
    };
    let JsonValue::Object(closing) = statement.get("closing").unwrap() else {
        panic!("closing")
    };
    assert_eq!(
        closing.get("fact"),
        Some(&JsonValue::String("1 = 1 and 0 = 0".into()))
    );
    for key in ["impossible", "negated_impossible"] {
        let JsonValue::Object(proof) = closing.get(key).unwrap() else {
            panic!("proof")
        };
        assert_eq!(proof.get("success"), Some(&JsonValue::Bool(true)), "{key}");
    }
}

#[test]
fn induction_recovery_can_find_a_parameter_used_only_in_compound_closing() {
    let mut rt = runtime();
    let source = "claim:\n    ? forall n N:\n        n = n\n    by contra:\n        ? 1 = 1\n        impossible n = n and 1 = 1";
    let blocks = Tokenizer::new()
        .tokenize(source, rt.current_file.clone())
        .unwrap();
    let Stmt::ProofBlock(crate::ast::stmt::ProofBlockStmt::ClaimStmt(claim)) =
        rt.parse(&blocks).unwrap().remove(0)
    else {
        panic!("claim")
    };
    let Fact::ForallFact(goal) = &claim.fact else {
        panic!("forall")
    };
    let param = &goal.typed_parameters.groups[0].params[0];
    let recovered =
        crate::execute::execute_by_stmt::recover_induction_param::recover_induction_param(
            "n",
            &[],
            &[&claim.proof],
        )
        .unwrap();
    assert_eq!(recovered.id, param.id);
}

#[test]
fn parameterless_quantifiers_and_guarded_iff_closings_replay() {
    for source in [
        "by contra:\n    ? forall:\n        1 = 1\n    impossible forall:\n        1 = 1",
        "by contra:\n    ? forall:\n        =>:\n            1 = 1\n        <=>:\n            1 = 1\n    impossible forall:\n        =>:\n            1 = 1\n        <=>:\n            1 = 1",
        "by contra:\n    ? forall n {0}:\n        n = 0\n        =>:\n            n = 0\n        <=>:\n            n + 0 = 0\n    impossible forall q {0}:\n        q = 0\n        =>:\n            q = 0\n        <=>:\n            q + 0 = 0",
    ] {
        let mut rt = runtime();
        let blocks = Tokenizer::new()
            .tokenize(source, rt.current_file.clone())
            .unwrap();
        let readable = rt.parse(&blocks).unwrap().iter()
            .map(Stmt::readable_string).collect::<Vec<_>>().join("\n");
        for code in [source, readable.as_str()] {
            let mut replay = runtime();
            let run = replay.run_litex_code(code).unwrap();
            assert!(run.success, "{code}\n{}",
                crate::json_output::emit_run_detailed(&run, &replay, "eval", None));
        }
    }
}

#[test]
fn false_existence_uniqueness_and_equivalence_cannot_close() {
    for closing in [
        "exist x {0} st {x = 1}",
        "not exist x {0} st {x = 0}",
        "exist! x {0, 1} st {x = x}",
        "forall x {0}:\n        =>:\n            x = 0\n        <=>:\n            x = 1",
    ] {
        let source = format!("by contra:\n    ? 1 = 2\n    impossible {closing}");
        let mut rt = runtime();
        let run = rt.run_litex_code(&source).unwrap();
        assert!(!run.success && run.session_error.is_none(), "{source}");
        assert!(matches!(
            &run.statement_results[0],
            ExecStmtResult::By(ExecByStmtResult::Contra(ExecByContraStmtResult::Failed(
                ExecByContraStmtFailed::Closing(ByContradictionClosingFailed::Impossible(_))
            )))
        ));
        assert!(!rt.run_litex_code("1 = 2").unwrap().success);
    }
}

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

fn fact_family(fact: &Fact) -> &'static str {
    match fact {
        Fact::AtomicFact(_) => "atomic",
        Fact::AndFact(_) => "and",
        Fact::OrFact(_) => "or",
        Fact::ChainFact(_) => "chain",
        Fact::ExistFact(_) => "exist",
        Fact::NotExistFact(_) => "not-exist",
        Fact::ExistUniqueFact(_) => "unique",
        Fact::ForallFact(_) => "forall",
        Fact::ForallFactWithIff(_) => "iff",
        Fact::NotForall(_) => "not-forall",
    }
}

fn closing_sources() -> Vec<(&'static str, String)> {
    let negative_exist = "by enumerate finite_set:\n    ? forall x {0}:\n        x != 1\nby contra:\n    ? not exist x {0} st {x = 1}\n    obtain a from exist x {0} st {x = 1}\n    a != 1\n    impossible a = 1\n";
    let unique = "by contra:\n    ? exist! x {0} st {x = 0}\n    obtain a from exist y {0} st {y = 0, y != 0}\n    impossible a != 0\n";
    vec![
        ("atomic", "by contra:\n    ? 1 = 1\n    impossible 1 = 1".into()),
        ("and", "by contra:\n    ? 1 = 1\n    impossible 1 = 1 and 0 = 0".into()),
        ("or", "by contra:\n    ? 1 = 1\n    impossible 1 = 1 or 0 = 1".into()),
        ("chain", "by contra:\n    ? 1 = 1\n    impossible 1 = 1 = 1".into()),
        ("exist", format!("{negative_exist}by contra:\n    ? not exist z {{0}} st {{z = 1}}\n    impossible exist w {{0}} st {{w = 1}}")),
        ("not-exist", format!("{negative_exist}by contra:\n    ? not exist z {{0}} st {{z = 1}}\n    impossible not exist w {{0}} st {{w = 1}}")),
        ("unique", format!("{unique}by contra:\n    ? exist! z {{0}} st {{z = 0}}\n    impossible exist! w {{0}} st {{w = 0}}")),
        ("forall", "forall x {0}:\n    x = 0\nby contra:\n    ? forall n {0}:\n        n = 0\n    impossible forall q {0}:\n        q = 0".into()),
        ("not-forall", "by contra:\n    ? not forall n {0}:\n        n = 1\n    impossible 0 = 1\nby contra:\n    ? not forall k {0}:\n        k = 1\n    impossible not forall q {0}:\n        q = 1".into()),
        ("iff", "by contra:\n    ? forall n {0}:\n        =>:\n            0 = 0\n        <=>:\n            0 = 0\n    impossible forall q {0}:\n        =>:\n            0 = 0\n        <=>:\n            0 = 0".into()),
    ]
}
