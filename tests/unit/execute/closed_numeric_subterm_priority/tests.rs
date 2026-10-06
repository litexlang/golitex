use super::rewrite_closed_numeric_subterms;
use crate::ast::fact::{AtomicFact, Fact};
use crate::ast::obj::Obj;
use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::helper::replace_obj_matching_ir;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::{RealOrVirtualPath, Runtime};
use crate::tokenize::Tokenizer;

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: true,
        strict: true,
        language,
    })
}

fn left(rt: &mut Runtime, code: &str) -> Obj {
    let blocks = Tokenizer::new()
        .tokenize(code, RealOrVirtualPath::Eval)
        .unwrap();
    let mut parsed = rt.parse(&blocks).unwrap();
    let Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(f))) = parsed.remove(0) else {
        panic!("equality");
    };
    f.left
}

#[test]
fn actual_whole_numeric_source_wins_in_every_row_permutation() {
    let mut rt = runtime(OutputLanguage::English);
    let run = rt
        .run_litex_code("have a R = 0\ncos(a)=cos(0)=1\n")
        .unwrap();
    assert!(run.success && run.session_error.is_none());
    let object = left(&mut rt, "cos(a)=1");
    let argument = left(&mut rt, "a=0");
    let closed_cosine = left(&mut rt, "cos(0)=1");
    let visible = rt.visible_closed_numeric_equal_entries();
    let keys = [argument.ir(), object.ir(), closed_cosine.ir()];
    let rows: Vec<_> = keys
        .iter()
        .map(|key| {
            visible
                .iter()
                .find(|(from, _, _)| from == key)
                .unwrap()
                .clone()
        })
        .collect();
    let expected = left(&mut rt, "1=1").ir();
    for order in [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ] {
        let entries: Vec<_> = order.into_iter().map(|i| rows[i].clone()).collect();
        let (rewritten, citations) = rewrite_closed_numeric_subterms(&object, &entries);
        assert_eq!(rewritten.ir(), expected);
        assert_eq!(citations, vec![rows[1].2]);
    }
}

#[test]
fn rebuilt_parent_uses_actual_source_without_changing_single_replacement_contract() {
    let mut rt = runtime(OutputLanguage::English);
    assert!(
        rt.run_litex_code("have a R = 0\ncos(0)=1\n")
            .unwrap()
            .success
    );
    let object = left(&mut rt, "cos(a)=1");
    let entries = rt.visible_closed_numeric_equal_entries();
    for reverse in [false, true] {
        let mut rows = entries.clone();
        if reverse {
            rows.reverse();
        }
        let (rewritten, citations) = rewrite_closed_numeric_subterms(&object, &rows);
        assert_eq!(rewritten.ir(), left(&mut rt, "1=1").ir());
        assert_eq!(citations.len(), 2);
    }
    // Pure value transformation, not a verifier premise: original-only exact
    // replacement must not visit a parent newly formed by replacing a child.
    let nested = left(&mut rt, "(0+0)+0=0");
    let sum = left(&mut rt, "0+0=0");
    let zero = left(&mut rt, "0=0");
    assert_eq!(
        replace_obj_matching_ir(&nested, &sum.ir(), &zero).ir(),
        sum.ir()
    );
}

#[test]
fn public_endpoint_claim_is_stable_and_retains_numeric_rewrite_in_ten_languages() {
    let source = include_str!("../../../../examples/proof_nodes/atomic/by_builtin_rewrite/closed_numeric_subterm_priority.lit");
    assert!(!source.contains("trust"));
    for language in OutputLanguage::ALL {
        for _ in 0..12 {
            let mut rt = runtime(language);
            let run = rt.run_litex_code(source).unwrap();
            assert!(run.success && run.session_error.is_none());
            let detail =
                crate::json_output::project_run_detailed(&run, &rt, "eval", None).stringify();
            assert!(detail.contains("ClosedNumericEqualSubstitution"));
            crate::json_output::project_stmt_normal(&run.statement_results[0], &rt);
        }
    }
}

#[test]
fn wrong_numeric_conclusions_and_failed_source_reuse_still_reject() {
    let good = "claim:\n    ? forall a,b R:\n        a=0\n        b=pi\n        =>:\n            cos(b)<cos(a)\n    cos(a)=cos(0)=1\n    cos(b)=cos(pi)=-1\n    cos(b)<cos(a)\n";
    let bad = good.replace("cos(b)<cos(a)", "cos(a)<cos(b)");
    let mut rt = runtime(OutputLanguage::English);
    assert!(!rt.run_litex_code(&bad).unwrap().success);
    assert!(rt.run_litex_code(good).unwrap().success);
    let repeat = "forall a,b R:\n    a=0\n    b=pi\n    =>:\n        cos(b)<cos(a)\n";
    let run = rt.run_litex_code(repeat).unwrap();
    assert!(run.success);
    assert!(
        crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt)
            .stringify()
            .contains("by_known_forall_fact")
    );
    assert!(!rt.run_litex_code(&bad).unwrap().success);
    assert_eq!(rt.execution_environments_stack.len(), 1);
}

#[test]
fn equality_and_eval_share_checked_whole_numeric_sources() {
    use crate::execute::execute_eval_stmt::{ExecCommandStmtResult, ExecEvalStmtResult};
    use crate::execute::ExecStmtResult;
    let mut rt = runtime(OutputLanguage::English);
    let source = "have a R = 0\nhave b R = pi\ncos(a)=cos(0)=1\ncos(b)=cos(pi)=-1\ncos(a)+cos(b)=0\neval cos(a)+2\n";
    let run = rt.run_litex_code(source).unwrap();
    assert!(run.success && run.session_error.is_none());
    let equality =
        crate::json_output::project_stmt_detailed(&run.statement_results[4], &rt).stringify();
    assert!(equality.contains("ClosedNumericEqualSubstitution"));
    let ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(eval))) =
        &run.statement_results[5]
    else {
        panic!("evaluated source");
    };
    assert_eq!(eval.evaluated_object.readable_string(), "3");
    assert!(!eval.cited_equal_fact_ids.is_empty());
}
