use crate::execute::ExecStmtResult;
use crate::execute::execute_by_stmt::{ExecByStmtResult, ExecByThmStmtResult};
use crate::execute::execute_fact_stmt::VerifyFactResult;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    EqualFactSearchedProof, EqualFactSearchedProofByEquivalenceClass, VerifyEqualityResult,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::{
    AtomicExceptEqualityFactSearchedProof, VerifyAtomicExceptEqualityFactResult,
};
use crate::json_output::{project_stmt_detailed, project_stmt_normal};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

const REFLEXIVE: &str = "thm reflexive:\n    ? forall x R:\n        x = x";

#[test]
fn named_enumeration_callbacks_keep_definition_and_bijection_obligations() {
    let mut rt = runtime();
    let source = include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/named_enumeration_callbacks.lit");
    let run = rt.run_litex_code(source).unwrap();
    assert!(run.success && run.session_error.is_none());
    let detail = project_stmt_detailed(run.statement_results.last().unwrap(), &rt).stringify();
    assert!(detail.contains("cite_fact_id"), "named definitions need real citations: {detail}");

    let mut rt = runtime();
    let before = count_facts(&rt);
    let source = include_str!("../../../../examples/negative/named_enumeration_callbacks/missing_bijection.lit");
    let run = rt.run_litex_code(source).unwrap();
    assert!(!run.success && run.session_error.is_none());
    assert_eq!(count_facts(&rt), before, "a failed theorem must not publish its result");
}

#[test]
fn run_examples_by_thm_strict_selection_tracer() {
    let mut rt = runtime();
    let run = rt.run_litex_code(include_str!("../../../../examples/stmt_nodes/by/by_thm_strict_selection.lit")).unwrap();
    assert!(run.success && run.session_error.is_none());
    for source in [
        include_str!("../../../../examples/test_statements/negative/by_thm_stmt/unrelated-true-target.lit"),
        include_str!("../../../../examples/test_statements/negative/by_thm_stmt/combined-theorem-results.lit"),
    ] {
        let mut rt = runtime();
        let run = rt.run_litex_code(source).unwrap();
        assert!(!run.success && run.session_error.is_none());
        assert!(!run.statement_results[0].is_failed());
        assert!(run.statement_results[1].is_failed());
    }
}

#[test]
fn by_thm_rejects_unrelated_calculation_and_identity_targets() {
    for target in ["2 + 3 = 5", "1 = 1", "2 != 3"] {
        let mut rt = runtime();
        assert!(!execute(&mut rt, REFLEXIVE).is_failed());
        let before = count_facts(&rt);
        let result = execute(&mut rt, &format!("by thm reflexive(7) => {target}"));
        assert!(result.is_failed(), "accepted unrelated target: {target}");
        assert_eq!(count_facts(&rt), before, "failed selection published facts");
    }
}

#[test]
fn by_thm_rejects_unrelated_definition_folding() {
    let mut rt = runtime();
    assert!(!execute(&mut rt, "prop positive(x R):\n    x > 0").is_failed());
    assert!(!execute(&mut rt, REFLEXIVE).is_failed());
    let before = count_facts(&rt);
    let result = execute(&mut rt, "by thm reflexive(7) => $positive(2)");
    assert!(result.is_failed(), "accepted unrelated definition proof");
    assert_eq!(count_facts(&rt), before);
    assert!(!execute(&mut rt, "by def $positive(2)").is_failed());
}

#[test]
fn by_thm_rejects_an_unrelated_already_known_fact() {
    let mut rt = runtime();
    assert!(!execute(&mut rt, "have a R = 2").is_failed());
    assert!(!execute(&mut rt, "a = 2").is_failed());
    assert!(!execute(&mut rt, REFLEXIVE).is_failed());
    let before = count_facts(&rt);
    let result = execute(&mut rt, "by thm reflexive(7) => a = 2");
    assert!(result.is_failed(), "accepted unrelated ambient equality");
    assert_eq!(count_facts(&rt), before);
    assert!(!execute(&mut rt, "a = 2").is_failed());
}

#[test]
fn by_thm_rejects_an_unrelated_abstract_predicate_premise() {
    let mut rt = runtime();
    assert!(!execute(&mut rt, "abstract_prop P(x)").is_failed());
    assert!(!execute(&mut rt, REFLEXIVE).is_failed());
    let before = count_facts(&rt);
    let result = execute(&mut rt, "claim:\n    ? forall x R:\n        $P(x)\n        =>:\n            $P(x)\n    by thm reflexive(7) => $P(x)");
    assert!(result.is_failed(), "accepted ambient abstract premise");
    assert_eq!(count_facts(&rt), before);
}

#[test]
fn by_thm_exact_equality_cites_this_instance_even_when_the_goal_is_already_known() {
    let mut rt = runtime();
    assert!(!execute(&mut rt, "7 = 7").is_failed());
    assert!(!execute(&mut rt, REFLEXIVE).is_failed());
    let old_ids: Vec<_> = rt.execution_environments_stack.iter()
        .flat_map(|env| env.facts.facts_by_id.keys().copied()).collect();
    let result = execute(&mut rt, "by thm reflexive(7) => 7 = 7");
    let ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(success))) = &result else {
        panic!("direct equality selection: {}", project_stmt_detailed(&result, &rt).stringify());
    };
    let VerifyFactResult::Equality(proof) = &success.selected_proof else { panic!("equality proof"); };
    let VerifyEqualityResult::Success(proof) = proof.as_ref() else { panic!("successful proof"); };
    let EqualFactSearchedProof::ByEquivalenceClass(EqualFactSearchedProofByEquivalenceClass::AlphaEndpoints(cite)) = &proof.searched_proof else {
        panic!("selection must cite the returned equality, not identity or calculation");
    };
    assert!(!old_ids.contains(&cite.cited.fact_id));
    assert!(success.local_env.facts.facts_by_id.contains_key(&cite.cited.fact_id));
    assert!(!cite.reversed);
    let detail = project_stmt_detailed(&result, &rt).stringify();
    assert!(detail.contains("cite_fact_id") && detail.contains("alpha_endpoints"), "{detail}");
}

#[test]
fn by_thm_exact_predicate_cites_this_instance_even_when_the_goal_is_already_known() {
    let mut rt = runtime();
    assert!(!execute(&mut rt, "prop positive(x R):\n    x > 0").is_failed());
    assert!(!execute(&mut rt, "thm positive_intro:\n    ? forall x R:\n        x > 0\n        =>:\n            $positive(x)\n    by def $positive(x)").is_failed());
    assert!(!execute(&mut rt, "by def $positive(2)").is_failed());
    let old_ids: Vec<_> = rt.execution_environments_stack.iter()
        .flat_map(|env| env.facts.facts_by_id.keys().copied()).collect();
    let result = execute(&mut rt, "by thm positive_intro(2) => $positive(2)");
    let ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(success))) = &result else { panic!("direct predicate selection"); };
    let VerifyFactResult::AtomicExceptEquality(proof) = &success.selected_proof else { panic!("atomic proof"); };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_ref() else { panic!("successful proof"); };
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) = &proof.searched_proof else {
        panic!("selection must cite the returned predicate, not unfold its definition");
    };
    assert!(!old_ids.contains(&cite.cite_fact_id));
    assert!(success.local_env.facts.facts_by_id.contains_key(&cite.cite_fact_id));
    for target in ["2 > 0", "2 $in R", "$positive(1 + 1)"] {
        assert!(execute(&mut rt, &format!("by thm positive_intro(2) => {target}")).is_failed(), "accepted inferred or rewritten target: {target}");
    }
}

#[test]
fn by_thm_direct_selection_preserves_alpha_equivalence_and_negative_conclusions() {
    let mut rt = runtime();
    assert!(!execute(&mut rt, "thm alpha_identity:\n    ? fn(k R) R {k} = fn(j R) R {j}").is_failed());
    assert!(!execute(&mut rt, "by thm alpha_identity => fn(x R) R {x} = fn(y R) R {y}").is_failed());
    assert!(execute(&mut rt, "by thm alpha_identity => fn(x R) R {x} = fn(y R) R {y + 1}").is_failed());
    assert!(rt.run_litex_code(include_str!("../../../../examples/_internal/regression/lambda_alpha_equivalence.lit")).unwrap().success);
    assert!(!execute(&mut rt, "thm nonzero:\n    ? forall x R:\n        x > 0\n        =>:\n            x != 0").is_failed());
    assert!(!execute(&mut rt, "by thm nonzero(3) => 3 != 0").is_failed());
    assert!(execute(&mut rt, "by thm nonzero(3) => 3 = 0").is_failed());
}

#[test]
fn by_thm_selects_direct_package_components_without_combining_or_reversing_them() {
    for body in ["x + 0 = x\n        0 + x = x", "x + 0 = x = 0 + x", "x + 0 = x and 0 + x = x"] {
        let mut rt = runtime();
        assert!(!execute(&mut rt, &format!("thm sides:\n    ? forall x R:\n        {body}")).is_failed());
        assert!(!execute(&mut rt, "by thm sides(2) => 2 + 0 = 2").is_failed());
        for target in ["2 + 0 = 0 + 2", "2 = 2 + 0", "1 + 1 = 2"] {
            let before = count_facts(&rt);
            let result = execute(&mut rt, &format!("by thm sides(2) => {target}"));
            assert!(result.is_failed(), "selected a derived conclusion: {body}\n{target}");
            assert_eq!(count_facts(&rt), before);
            let normal = project_stmt_normal(&result, &rt).stringify();
            assert!(normal.contains("not_returned") && normal.contains("returned_conclusions"), "{normal}");
        }
        // Authors can explicitly release the package before a separate derivation.
        assert!(!execute(&mut rt, "release thm sides(2)").is_failed());
        assert!(!execute(&mut rt, "2 + 0 = 0 + 2").is_failed());
        assert!(!execute(&mut rt, "by thm sides(2)").is_failed());
    }
}

#[test]
fn by_thm_does_not_select_an_existential_body() {
    let mut rt = runtime();
    assert!(execute(&mut rt, "by thm rational_between_reals(2, 3) => 2 < 5 / 2").is_failed());
    assert!(!execute(&mut rt, "thm has_zero:\n    ? exist x R st {x = 0}\n    witness exist x R st {x = 0} from 0").is_failed());
    assert!(execute(&mut rt, "by thm has_zero => 0 = 0").is_failed());
}

#[test]
fn by_thm_rejects_the_symbolic_combined_conclusion_chosen_by_the_user() {
    let mut rt = runtime();
    assert!(!execute(&mut rt, "thm two_equalities:\n    ? forall a, b, c R:\n        a = b\n        b = c\n        =>:\n            a = b\n            b = c").is_failed());
    let before = count_facts(&rt);
    let result = execute(&mut rt, "claim:\n    ? forall a, b, c R:\n        a = b\n        b = c\n        =>:\n            a = c\n    by thm two_equalities(a, b, c) => a = c");
    assert!(result.is_failed(), "a = c was not directly returned");
    assert_eq!(count_facts(&rt), before);
    assert!(!execute(&mut rt, "claim:\n    ? forall a, b, c R:\n        a = b\n        b = c\n        =>:\n            a = c\n    release thm two_equalities(a, b, c)\n    a = c").is_failed());
}

#[test]
fn by_thm_selection_outputs_preserve_the_failure_reason_and_citation_in_all_languages() {
    for language in OutputLanguage::ALL {
        let mut rt = Runtime::new(LaunchCommand::Eval {
            code: String::new(), session: false, strict: true, language,
        });
        assert!(!execute(&mut rt, REFLEXIVE).is_failed());
        let failed = execute(&mut rt, "by thm reflexive(7) => 1 = 1");
        assert!(failed.is_failed());
        for json in [project_stmt_normal(&failed, &rt), project_stmt_detailed(&failed, &rt)] {
            let text = json.stringify();
            assert!(text.contains("not_returned") && text.contains("7 = 7") && text.contains("1 = 1"), "{language:?}: {text}");
        }
        let success = execute(&mut rt, "by thm reflexive(7) => 7 = 7");
        assert!(!success.is_failed());
        let detail = project_stmt_detailed(&success, &rt).stringify();
        assert!(detail.contains("alpha_endpoints"), "{language:?}: {detail}");
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

fn execute(rt: &mut Runtime, code: &str) -> ExecStmtResult {
    let blocks = Tokenizer::new().tokenize(code, rt.current_file.clone()).unwrap();
    let mut statements = rt.parse(&blocks).unwrap();
    assert_eq!(statements.len(), 1, "{code}");
    rt.exec_stmt(&statements.remove(0)).unwrap()
}

fn count_facts(rt: &Runtime) -> usize {
    rt.execution_environments_stack.iter().map(|env| env.facts.facts_by_id.len()).sum()
}
