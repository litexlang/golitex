use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::LitexToLeanCompiler;
use crate::execute::execute_by_stmt::{
    ByCasesBranchClosingSuccess, ExecByCasesStmtResult, ExecByCasesStmtSuccess,
    ExecByContraStmtResult, ExecByContraStmtSuccess,
};
use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rewrite::{
    AtomicExceptEqualityFactSearchProofByBuiltinRewrite,
    AtomicExceptEqualityFactSearchProofByClosedNumericEqualSubstitution,
};

const CONTRA: &str = "have a C\nby contra:\n    ? a = a\n    a = a\n    impossible a = a\na = a\n";
const CASES: &str = "have a R\nby cases:\n    ? a = a\n    case a = 0:\n        a = a\n    case a != 0:\n        a = a\na = a\n";
const COMPOUND_CONTRA: &str = "have a R\nby contra:\n    ? a = a and a = a\n    impossible a = a and a = a\na = a and a = a\n";
const EXTENSION: &str = "thm subset_antisymmetry:\n    ? forall A, B set:\n        A $subset B\n        B $subset A\n        =>:\n            A = B\n    by extension A = B\n";
const SET_CONTRA: &str = "thm member_prevents_subset:\n    ? forall A, B set, a set:\n        a $in A\n        not a $in B\n        =>:\n            not A $subset B\n    by contra:\n        ? not A $subset B\n        impossible a $in B\n";

#[test]
fn membership_cases_replay_the_original_union_projection() {
    let (result, compiler) = checked(include_str!(
        "../../../lean/examples/membership_distinguishes_sets/statement.lit"
    ));
    let lean = compiler.compile_run(&result, "membership_cases").unwrap();
    assert!(lean.contains("Litex.inUnion_iff"));
    assert!(lean.contains("Or.elim"));
}

#[test]
fn membership_projection_rejects_reordered_union_store() {
    let (mut result, compiler) = checked(include_str!(
        "../../../lean/examples/membership_distinguishes_sets/statement.lit"
    ));
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(theorem),
    )) = &mut result.statement_results[2]
    else {
        panic!("theorem");
    };
    let ExecDefThmBodyProof::Forall(body) = &mut theorem.body else {
        panic!("body");
    };
    let Some(crate::store_fact_and_infer::InferResult::AtomicFact(
        crate::store_fact_and_infer::InferAtomicFactResult::InFact(rules),
    )) = &mut body.assumed_dom_facts[0].store_and_infer.infer
    else {
        panic!("membership inference");
    };
    let crate::store_fact_and_infer::InferInFactResult::UnionOr(projection) = rules
        .iter_mut()
        .find(|r| {
            matches!(
                r,
                crate::store_fact_and_infer::InferInFactResult::UnionOr(_)
            )
        })
        .unwrap()
    else {
        unreachable!()
    };
    let StoreFactResult::OrFact(stored) = &mut projection.derived.store else {
        panic!("or store");
    };
    stored.fact.facts.swap(0, 1);
    assert!(compiler.compile_run(&result, "reordered_union").is_err());
}

#[test]
fn complementary_atomic_rejects_changed_selected_certificate() {
    let (mut result, compiler) = checked("have a R\na = a or a != a\n");
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) =
        &mut result.statement_results[1]
    else {
        panic!("fact");
    };
    let VerifyFactResult::OrFact(result_or) = &mut statement.verify_result else {
        panic!("or");
    };
    let VerifyOrFactResult::Success(proof) = result_or.as_mut() else {
        panic!("success");
    };
    let OrFactSearchedProof::ByBuiltinRule(OrFactSearchProofByBuiltinRule::ComplementaryAtomic(
        selected,
    )) = &mut proof.searched_proof
    else {
        panic!("complementary builtin");
    };
    selected.right = selected.left.clone();
    assert_eq!(
        compiler
            .compile_run(&result, "changed_complement")
            .unwrap_err()
            .route,
        "Or/ComplementarySubject"
    );
}

#[test]
fn contra_replays_negative_membership_and_subset() {
    for goal in ["A != B", "not A $subset B"] {
        let source = SET_CONTRA.replace("not A $subset B", goal);
        let (result, compiler) = checked(&source);
        let lean = compiler.compile_run(&result, "set_contradiction").unwrap();
        assert!(lean.contains("¬ Litex.In"));
        assert!(lean.contains("Classical.byContradiction"));
    }
}

#[test]
fn contra_rejects_changed_compound_closing() {
    let (mut result, compiler) = checked(COMPOUND_CONTRA);
    let closing = &mut contra(&mut result).closing;
    std::mem::swap(&mut closing.impossible, &mut closing.negated_impossible);
    assert!(compiler
        .compile_run(&result, "changed_compound_closing")
        .is_err());
}

#[test]
fn compound_contra_does_not_export_local_names() {
    let mut runtime = Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    );
    let result = runtime.run_litex_code("by contra:\n    ? 0 = 0 and 1 = 1\n    have local_witness R = 2\n    impossible 0 = 0 and 1 = 1\nlocal_witness = 2\n").unwrap();
    assert!(!result.success);
    let compiler = LitexToLeanCompiler::new(runtime);
    assert_eq!(
        compiler
            .compile_run(&result, "local_leak")
            .unwrap_err()
            .route,
        "source_failed"
    );
}

#[test]
fn set_extension_replays_both_original_subset_directions() {
    let (result, compiler) = checked(EXTENSION);
    let lean = compiler.compile_run(&result, "set_extension").unwrap();
    assert!(lean.contains("Litex.SetSemantics.ext"));
    assert!(lean.contains("_extension_forward"));
    assert!(lean.contains("_extension_reverse"));
}

#[test]
fn set_extension_rejects_changed_subset_direction() {
    let (mut result, compiler) = checked(EXTENSION);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(theorem),
    )) = &mut result.statement_results[0]
    else {
        panic!("theorem");
    };
    let ExecDefThmBodyProof::Forall(body) = &mut theorem.body else {
        panic!("forall body");
    };
    let ExecStmtResult::By(ExecByStmtResult::Extension(
        crate::execute::execute_by_stmt::ExecByExtensionStmtResult::Success(proof),
    )) = &mut body.proof_steps[0]
    else {
        panic!("extension");
    };
    std::mem::swap(&mut proof.left_to_right, &mut proof.right_to_left);
    assert_eq!(
        compiler
            .compile_run(&result, "changed_extension")
            .unwrap_err()
            .route,
        "Theorem/ProofStepCapture"
    );
}

#[test]
fn contra_replays_classified_compound_negation() {
    for goal in [
        "a = a and a = a",
        "a = a or a != a",
        "a = a = a",
        "a = a and a = a or a != a and a != a",
    ] {
        let source = format!("have a R\nby contra:\n    ? {goal}\n    impossible {goal}\n");
        let (result, compiler) = checked(&source);
        let lean = compiler
            .compile_run(&result, "compound_contra")
            .unwrap_or_else(|e| panic!("{goal}: {e:?}"));
        assert!(lean.contains("simpa only [not_and_or, not_or, not_not"));
    }
}

#[test]
fn contra_rejects_changed_compound_negation() {
    let (mut result, compiler) = checked(COMPOUND_CONTRA);
    let proof = contra(&mut result);
    proof.reverse_assumption = proof.goal.clone();
    assert_eq!(
        compiler
            .compile_run(&result, "wrong_compound_negation")
            .unwrap_err()
            .route,
        "By/NegationSubject"
    );
}

#[test]
fn contra_rejects_missing_compound_negation_branch() {
    let (mut result, compiler) = checked(COMPOUND_CONTRA);
    let Fact::OrFact(negative) = &mut contra(&mut result).reverse_assumption else {
        panic!("conjunction has a disjunctive negation");
    };
    negative.facts.pop();
    assert_eq!(
        compiler
            .compile_run(&result, "incomplete_compound_negation")
            .unwrap_err()
            .route,
        "By/NegationSubject"
    );
}
// Original geo theorem: its closing proof rewrites `not z > 0` via `z = 0`.
const CONTRA_POSITIVE_FACTOR: &str = "thm cancel_positive_right_factor:\n    ? forall a, b, z R:\n        z > 0\n        a * z = b * z\n        =>:\n            a = b\n    by contra:\n        ? z != 0\n        impossible z > 0\n    a = (a * z) / z = (b * z) / z = b\n";

fn positive_factor_contra(result: &mut RunLitexCodeResult) -> &mut ExecByContraStmtSuccess {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(theorem),
    )) = &mut result.statement_results[0]
    else {
        panic!("original named theorem")
    };
    let ExecDefThmBodyProof::Forall(body) = &mut theorem.body else {
        panic!("original forall body")
    };
    let ExecStmtResult::By(ExecByStmtResult::Contra(ExecByContraStmtResult::Success(proof))) =
        &mut body.proof_steps[0]
    else {
        panic!("original nested contra")
    };
    proof
}

fn negative_order_rewrite(
    result: &mut RunLitexCodeResult,
) -> &mut AtomicExceptEqualityFactSearchProofByClosedNumericEqualSubstitution {
    let VerifyFactResult::AtomicExceptEquality(verification) =
        &mut positive_factor_contra(result).closing.negated_impossible
    else {
        panic!("original negative order verification")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(verification) = verification.as_mut() else {
        panic!("successful negative order")
    };
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRewrite(
        AtomicExceptEqualityFactSearchProofByBuiltinRewrite::ClosedNumericEqualSubstitution(proof),
    ) = &mut verification.searched_proof
    else {
        panic!("original closed numeric substitution")
    };
    proof
}

fn negative_order_calculation(
    result: &mut RunLitexCodeResult,
) -> &mut ClosedComparisonCalculationProof {
    let VerifyFactResult::AtomicExceptEquality(verification) =
        &mut negative_order_rewrite(result).proof_of_rewritten_fact
    else {
        panic!("original negative closed child")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(verification) = verification.as_mut() else {
        panic!("successful closed child")
    };
    let AtomicExceptEqualityFactSearchedProof::ByClosedCalculation(
        ClosedAtomicExceptEqualityCalculationProof::NotGreater(proof),
    ) = &mut verification.searched_proof
    else {
        panic!("original not-greater calculation")
    };
    proof
}

#[test]
fn geo_contra_transports_original_negative_order_equality() {
    let (mut result, compiler) = checked(CONTRA_POSITIVE_FACTOR);
    assert_eq!(
        negative_order_rewrite(&mut result)
            .cited_equal_fact_ids
            .len(),
        1
    );
    let lean = compiler
        .compile_run(&result, "geo_contra_positive_factor")
        .expect("original contra compiles");
    assert!(lean.contains("fun _rewrite_positive =>"));
    assert!(lean.contains("Litex.ltOfSame"));
}

#[test]
fn geo_contra_rejects_missing_negative_order_citation() {
    let (mut result, compiler) = checked(CONTRA_POSITIVE_FACTOR);
    negative_order_rewrite(&mut result)
        .cited_equal_fact_ids
        .clear();
    assert_eq!(
        compiler
            .compile_run(&result, "geo_contra_missing_equality")
            .unwrap_err()
            .route,
        "AtomicRewrite/Citations"
    );
}

#[test]
fn geo_contra_rejects_changed_negative_order_child_subject() {
    let (mut result, compiler) = checked(CONTRA_POSITIVE_FACTOR);
    let goal = crate::compile_to_lean::helper::source_subject(
        &positive_factor_contra(&mut result)
            .closing
            .negated_impossible,
    )
    .expect("original goal");
    negative_order_rewrite(&mut result).rewritten_fact = goal;
    assert_eq!(
        compiler
            .compile_run(&result, "geo_contra_wrong_residual")
            .unwrap_err()
            .route,
        "AtomicRewrite/ChildSubject"
    );
}

#[test]
fn geo_contra_rejects_reordered_closing_verifications() {
    let (mut result, compiler) = checked(CONTRA_POSITIVE_FACTOR);
    let closing = &mut positive_factor_contra(&mut result).closing;
    std::mem::swap(&mut closing.impossible, &mut closing.negated_impossible);
    assert_eq!(
        compiler
            .compile_run(&result, "geo_contra_swapped_closing")
            .unwrap_err()
            .route,
        "Theorem/ProofStepCapture"
    );
}

#[test]
fn geo_contra_rejects_changed_negative_closed_comparison() {
    let (mut result, compiler) = checked(CONTRA_POSITIVE_FACTOR);
    negative_order_calculation(&mut result).comparison =
        crate::rational_expression::NumberCompareResult::Greater;
    assert_eq!(
        compiler
            .compile_run(&result, "geo_contra_wrong_closed_comparison")
            .unwrap_err()
            .route,
        "Order/ClosedValues"
    );
}

#[test]
fn geo_contra_rejects_changed_negative_closed_values() {
    let (mut result, compiler) = checked(CONTRA_POSITIVE_FACTOR);
    let ClosedValuePair::Decimal { left, .. } = &mut negative_order_calculation(&mut result).values
    else {
        panic!("original closed zero decimals")
    };
    *left = "1".into();
    assert_eq!(
        compiler
            .compile_run(&result, "geo_contra_wrong_closed_values")
            .unwrap_err()
            .route,
        "Order/ClosedValues"
    );
}

#[test]
fn geo_contra_negative_closed_calculation_ignores_presentation() {
    let (mut result, compiler) = checked(CONTRA_POSITIVE_FACTOR);
    let expected = compiler
        .compile_run(&result, "geo_contra_presentation")
        .expect("original negative comparison");
    let calculation = negative_order_calculation(&mut result);
    calculation.left_normal = "presentation only".into();
    calculation.right_normal = "not an expression".into();
    assert_eq!(
        compiler
            .compile_run(&result, "geo_contra_presentation")
            .expect("typed values remain unchanged"),
        expected
    );
}

fn checked(source: &str) -> (RunLitexCodeResult, LitexToLeanCompiler) {
    let mut runtime = Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    );
    let result = runtime.run_litex_code(source).expect("source execution");
    assert!(
        result.success && result.session_error.is_none(),
        "source rejected: {source}"
    );
    (result, LitexToLeanCompiler::new(runtime))
}

fn contra(result: &mut RunLitexCodeResult) -> &mut ExecByContraStmtSuccess {
    let ExecStmtResult::By(ExecByStmtResult::Contra(ExecByContraStmtResult::Success(proof))) =
        &mut result.statement_results[1]
    else {
        panic!("original contra result")
    };
    proof
}

fn cases(result: &mut RunLitexCodeResult) -> &mut ExecByCasesStmtSuccess {
    let ExecStmtResult::By(ExecByStmtResult::Cases(ExecByCasesStmtResult::Success(proof))) =
        &mut result.statement_results[1]
    else {
        panic!("original cases result")
    };
    proof
}

#[test]
fn contra_replays_original_steps_and_exports_the_goal() {
    let (mut result, compiler) = checked(CONTRA);
    let proof = contra(&mut result);
    assert_eq!(proof.proof_steps.len(), 1);
    let id = proof.reverse_assumption_fact_id;
    let lean = compiler
        .compile_run(&result, "contra_original_steps")
        .expect("contra compiles");
    assert!(lean.contains(&format!("intro h_{}", id.value())));
}

#[test]
fn contra_negative_goal_uses_double_negation_elimination() {
    let (result, compiler) = checked("by contra:\n    ? 1 != 0\n    impossible 1 = 0\n");
    let lean = compiler
        .compile_run(&result, "contra_negative_goal")
        .expect("negative goal compiles");
    assert!(lean.contains("Classical.byContradiction _litex_negated_goal"));
}

#[test]
fn contra_rejects_changed_reverse_assumption() {
    let (mut result, compiler) = checked(CONTRA);
    let proof = contra(&mut result);
    proof.reverse_assumption = proof.goal.clone();
    assert_eq!(
        compiler
            .compile_run(&result, "contra_wrong_reverse")
            .unwrap_err()
            .route,
        "By/NegationSubject"
    );
}

#[test]
fn contra_rejects_missing_assumption_capture() {
    let (mut result, compiler) = checked(CONTRA);
    contra(&mut result).assumption_components.clear();
    assert_eq!(
        compiler
            .compile_run(&result, "contra_missing_capture")
            .unwrap_err()
            .route,
        "By/AssumptionCapture"
    );
}

#[test]
fn contra_rejects_changed_impossible_subject() {
    let (mut result, compiler) = checked(CONTRA);
    let proof = contra(&mut result);
    proof.closing.impossible_fact = proof.reverse_assumption.clone();
    assert_eq!(
        compiler
            .compile_run(&result, "contra_wrong_closing")
            .unwrap_err()
            .route,
        "By/ImpossibleSubject"
    );
}

#[test]
fn cases_replays_complementary_coverage_and_both_original_branches() {
    let (mut result, compiler) = checked(CASES);
    let proof = cases(&mut result);
    assert_eq!(proof.branches.len(), 2);
    let ids: Vec<_> = proof
        .branches
        .iter()
        .map(|p| p.assumption_fact_id)
        .collect();
    let lean = compiler
        .compile_run(&result, "cases_original_branches")
        .expect("cases compile");
    assert!(lean.contains("Classical.em"));
    for id in ids {
        assert!(lean.contains(&format!("fun (h_{} :", id.value())));
    }
}

#[test]
fn cases_rejects_reordered_branches() {
    let (mut result, compiler) = checked(CASES);
    cases(&mut result).branches.swap(0, 1);
    assert_eq!(
        compiler
            .compile_run(&result, "cases_wrong_order")
            .unwrap_err()
            .route,
        "Cases/CoverageBranches"
    );
}

#[test]
fn cases_rejects_missing_branch_conclusion() {
    let (mut result, compiler) = checked(CASES);
    let ByCasesBranchClosingSuccess::ThenFacts { proved_then_facts } =
        &mut cases(&mut result).branches[0].closing
    else {
        panic!("ordinary branch closing")
    };
    proved_then_facts.clear();
    assert_eq!(
        compiler
            .compile_run(&result, "cases_missing_conclusion")
            .unwrap_err()
            .route,
        "Cases/ClosingArity"
    );
}

#[test]
fn cases_rejects_missing_output_formation() {
    let (mut result, compiler) = checked(CASES);
    cases(&mut result).stored_wd.clear();
    assert_eq!(
        compiler
            .compile_run(&result, "cases_missing_output_wd")
            .unwrap_err()
            .route,
        "Cases/Stages"
    );
}

#[test]
fn branch_assumptions_are_not_visible_after_the_cases_statement() {
    let (mut result, compiler) = checked(CASES);
    let id = cases(&mut result).branches[0].assumption_fact_id;
    let completed = SourcePosition::new(
        None,
        SourceOwner::Run(&result),
        result.statement_results.len(),
    );
    assert!(compiler.cited_fact_reference(id, &completed).is_err());
}

#[test]
fn contra_goal_is_not_visible_before_its_caller_output_store() {
    let (mut result, compiler) = checked(CONTRA);
    let id = contra(&mut result).stored.primary_fact_id();
    let run = SourcePosition::new(None, SourceOwner::Run(&result), 1);
    let output_wd_complete = SourcePosition::new(
        Some(&run),
        SourceOwner::Statement(&result.statement_results[1]),
        3,
    );
    assert!(compiler
        .cited_fact_reference(id, &output_wd_complete)
        .is_err());
    let stored = SourcePosition {
        before: 4,
        ..output_wd_complete
    };
    assert!(compiler.cited_fact_reference(id, &stored).is_ok());
}

#[test]
fn cases_goal_is_not_visible_before_its_caller_output_store() {
    let (mut result, compiler) = checked(CASES);
    let proof = cases(&mut result);
    let id = proof.stored[0].primary_fact_id();
    let head = proof.then_facts_wd.len() + 2;
    let run = SourcePosition::new(None, SourceOwner::Run(&result), 1);
    let output_wd_complete = SourcePosition::new(
        Some(&run),
        SourceOwner::Statement(&result.statement_results[1]),
        head + 1,
    );
    assert!(compiler
        .cited_fact_reference(id, &output_wd_complete)
        .is_err());
    let stored = SourcePosition {
        before: head + 2,
        ..output_wd_complete
    };
    assert!(compiler.cited_fact_reference(id, &stored).is_ok());
}

#[test]
fn a_case_cannot_cite_another_branch_assumption() {
    let (mut result, compiler) = checked(CASES);
    let id = cases(&mut result).branches[0].assumption_fact_id;
    let ExecStmtResult::By(ExecByStmtResult::Cases(ExecByCasesStmtResult::Success(proof))) =
        &result.statement_results[1]
    else {
        panic!("cases result")
    };
    let run = SourcePosition::new(None, SourceOwner::Run(&result), 1);
    let caller = SourcePosition::new(
        Some(&run),
        SourceOwner::Statement(&result.statement_results[1]),
        proof.then_facts_wd.len() + 1,
    );
    let sibling = SourcePosition::new(
        Some(&caller),
        SourceOwner::CasesBranch(&proof.branches[1]),
        2,
    );
    assert!(compiler.cited_fact_reference(id, &sibling).is_err());
}

#[test]
fn function_extensionality_replays_both_domain_inclusion_proofs() {
    use crate::execute::execute_fact_stmt::function_domain::FunctionDomainComparisonProof;
    let (run, compiler) = checked(include_str!(
        "../../../lean/examples/equal_positive_shifts/statement.lit"
    ));
    let ExecStmtResult::By(ExecByStmtResult::FnExtension(
        crate::execute::execute_by_stmt::ExecByFnExtensionStmtResult::Success(p),
    )) = &run.statement_results[3]
    else {
        panic!("extension");
    };
    assert!(matches!(
        p.domain_match.comparison,
        FunctionDomainComparisonProof::MutualInclusion { .. }
    ));
    let lean = compiler.compile_run(&run, "equal_positive_shifts").unwrap();
    assert!(lean.contains("Litex.SetSemantics.ext"));
    assert_eq!(
        lean,
        compiler.compile_run(&run, "equal_positive_shifts").unwrap()
    );
}

#[test]
fn function_extensionality_rejects_corrupt_domain_inclusions() {
    use crate::execute::execute_fact_stmt::function_domain::FunctionDomainComparisonProof;
    for mutation in 0..4 {
        let (mut run, compiler) = checked(include_str!(
            "../../../lean/examples/equal_positive_shifts/statement.lit"
        ));
        let ExecStmtResult::By(ExecByStmtResult::FnExtension(
            crate::execute::execute_by_stmt::ExecByFnExtensionStmtResult::Success(p),
        )) = &mut run.statement_results[3]
        else {
            panic!();
        };
        let FunctionDomainComparisonProof::MutualInclusion {
            forward,
            forward_proof,
            reverse,
            reverse_proof,
        } = &mut p.domain_match.comparison
        else {
            panic!();
        };
        match mutation {
            0 => {
                std::mem::swap(forward, reverse);
                std::mem::swap(forward_proof, reverse_proof);
            }
            1 => std::mem::swap(forward_proof, reverse_proof),
            2 => {
                let Fact::ForallFact(f) = forward else {
                    panic!();
                };
                f.then_facts.pop();
            }
            3 => p.domain_match.comparison = FunctionDomainComparisonProof::AlphaEquivalent,
            _ => unreachable!(),
        }
        assert!(
            compiler.compile_run(&run, "bad_domains").is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn function_extensionality_domain_facts_remain_local_to_its_proof() {
    use crate::execute::execute_fact_stmt::function_domain::FunctionDomainComparisonProof;
    let (run, compiler) = checked(include_str!(
        "../../../lean/examples/equal_positive_shifts/statement.lit"
    ));
    let ExecStmtResult::By(ExecByStmtResult::FnExtension(
        crate::execute::execute_by_stmt::ExecByFnExtensionStmtResult::Success(p),
    )) = &run.statement_results[3]
    else {
        panic!();
    };
    let FunctionDomainComparisonProof::MutualInclusion {
        forward, reverse, ..
    } = &p.domain_match.comparison
    else {
        panic!();
    };
    let root = SourcePosition::new(None, SourceOwner::Run(&run), 4);
    let caller = SourcePosition::new(
        Some(&root),
        SourceOwner::Statement(&run.statement_results[3]),
        2,
    );
    let local = SourcePosition::new(Some(&caller), SourceOwner::FnExtension(p), 0);
    for fact in [forward, reverse] {
        assert_eq!(
            compiler
                .cited_fact_reference(fact.fact_id(), &local)
                .unwrap()
                .1,
            format!("h_{}", fact.fact_id().value())
        );
        assert!(compiler
            .cited_fact_reference(fact.fact_id(), &root)
            .is_err());
    }
}

#[test]
fn function_extensionality_replays_binary_and_positive_inputs() {
    let (run, compiler) = checked(include_str!(
        "../../../lean/examples/equal_binary_sums/statement.lit"
    ));
    let lean = compiler.compile_run(&run, "binary_extension").unwrap();
    assert!(lean.contains("Litex.FiniteFunction.reconstruct"));
    assert!(lean.contains("Litex.positiveReal_members"));
}

#[test]
fn function_extensionality_replays_binary_guard_inclusions_with_distinct_return_bounds() {
    let (run, compiler) = checked(include_str!(
        "../../../lean/examples/equal_guarded_quotients/statement.lit"
    ));
    let lean = compiler.compile_run(&run, "guarded_quotients").unwrap();
    assert!(lean.contains("Litex.SetSemantics.ext"));
    assert!(lean.contains("Litex.FiniteFunction.reconstruct"));
}

#[test]
fn function_extensionality_rejects_reordered_pointwise_arguments() {
    let (mut run, compiler) = checked(include_str!(
        "../../../lean/examples/equal_binary_sums/statement.lit"
    ));
    let ExecStmtResult::By(ExecByStmtResult::FnExtension(
        crate::execute::execute_by_stmt::ExecByFnExtensionStmtResult::Success(p),
    )) = &mut run.statement_results[2]
    else {
        panic!();
    };
    let VerifyFactResult::ForallFact(p) = &mut p.pointwise_proof else {
        panic!();
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(p)) = p.as_mut()
    else {
        panic!();
    };
    p.fact.typed_parameters.groups[0].params.swap(0, 1);
    assert!(compiler.compile_run(&run, "bad_parameter_order").is_err());
}

#[test]
fn function_extensionality_does_not_identify_a_function_with_a_restriction() {
    let source = "have fn all(x R) R = x\nhave fn positive(x R: x > 0) R = x\nby fn_extension all = positive\n";
    let command = LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    };
    let mut runtime =
        Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
    let run = runtime.run_litex_code(source).unwrap();
    assert!(!run.success);
    assert!(LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "unequal_domains")
        .is_err());
}

#[test]
fn function_extensionality_replays_complete_domains_and_the_original_pointwise_forall() {
    let (result, compiler) = checked(include_str!(
        "../../../lean/examples/equal_shift_functions/statement.lit"
    ));
    let output = compiler
        .compile_run(&result, "equal_shift_functions")
        .unwrap();
    assert!(output.contains("Litex.functionExtOnDomain"));
    assert!(output.contains("have _pointwise :"));
}

#[test]
fn function_extensionality_rejects_changed_domains_and_pointwise_subjects() {
    for change in ["carrier", "function", "guard", "conclusion"] {
        let (mut result, compiler) = checked(include_str!(
            "../../../lean/examples/equal_shift_functions/statement.lit"
        ));
        let ExecStmtResult::By(ExecByStmtResult::FnExtension(
            crate::execute::execute_by_stmt::ExecByFnExtensionStmtResult::Success(proof),
        )) = &mut result.statement_results[5]
        else {
            panic!("extension")
        };
        match change {
            "carrier" => proof.carrier.ret_set = Box::new(Obj::StandardSet(StandardSet::N)),
            "function" => proof.domain_match.source.signature.dom_facts.clear(),
            _ => {
                let VerifyFactResult::ForallFact(p) = &mut proof.pointwise_proof else {
                    panic!("forall")
                };
                let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(p)) =
                    p.as_mut()
                else {
                    panic!("pointwise introduction")
                };
                if change == "guard" {
                    p.fact.dom_facts.clear();
                } else {
                    p.fact.then_facts.clear();
                }
            }
        }
        assert!(
            compiler
                .compile_run(&result, "corrupted_function_extension")
                .is_err(),
            "{change}"
        );
    }
}

#[test]
fn finite_enumeration_replays_original_assignments_and_false_antecedent() {
    let (result, compiler) = checked(include_str!(
        "../../../lean/examples/finite_square_values/statement.lit"
    ));
    let output = compiler
        .compile_run(&result, "finite_square_values")
        .unwrap();
    assert!(output.contains("Litex.SetSemantics.insert_members"));
    assert!(output.contains("have _excluded"));
}

#[test]
fn finite_enumeration_rejects_missing_reordered_or_changed_assignments() {
    for change in ["missing", "order", "binding", "premise"] {
        let (mut result, compiler) = checked(include_str!(
            "../../../lean/examples/finite_square_values/statement.lit"
        ));
        let ExecStmtResult::By(ExecByStmtResult::For(
            crate::execute::execute_by_stmt::ExecByForStmtResult::Success(proof),
        )) = &mut result.statement_results[2]
        else {
            panic!("for")
        };
        match change {
            "missing" => {
                proof.assignments.pop();
            }
            "order" => proof.assignments.swap(0, 1),
            "binding" => {
                let StoreFactResult::AtomicFact(f) = &mut proof.assignments[1].binding_assumptions
                    [0]
                .store_and_infer
                .store
                else {
                    panic!("binding")
                };
                let AtomicFact::EqualFact(f) = &mut f.fact else {
                    panic!("equality")
                };
                f.right = Obj::Literal(Literal::Number(Number::new("7".into())));
            }
            "premise" => {
                let crate::execute::execute_by_stmt::EnumerateAssignmentOutcome::Skipped {
                    premise_index,
                    ..
                } = &mut proof.assignments[0].outcome
                else {
                    panic!("skipped")
                };
                *premise_index = 1;
            }
            _ => unreachable!(),
        }
        assert!(
            compiler
                .compile_run(&result, "corrupted_enumeration")
                .is_err(),
            "{change}"
        );
    }
}

#[test]
fn selected_or_branch_keeps_original_negative_assumptions_local() {
    let (mut result, compiler) = checked("have selected_or_value R\nselected_or_value = selected_or_value or selected_or_value = 0\n");
    compiler.compile_run(&result, "selected_or_local").unwrap();
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(fact)) = &mut result.statement_results[1]
    else {
        panic!("fact")
    };
    let VerifyFactResult::OrFact(proof) = &mut fact.verify_result else {
        panic!("or")
    };
    let VerifyOrFactResult::Success(proof) = proof.as_mut() else {
        panic!("or success")
    };
    let OrFactSearchedProof::BySelectedBranch(selected) = &mut proof.searched_proof else {
        panic!("selected original branch")
    };
    assert!(!selected.assumed_negated_branches.is_empty());
    selected.assumed_negated_branches[0].branch_index = selected.selected_index;
    assert!(compiler
        .compile_run(&result, "wrong_selected_negative")
        .unwrap_err()
        .route
        .starts_with("Or/Selected"));
}

#[test]
fn finite_assignment_hypotheses_do_not_escape_to_siblings_or_callers() {
    let (result, compiler) = checked(include_str!(
        "../../../lean/examples/finite_square_values/statement.lit"
    ));
    let ExecStmtResult::By(ExecByStmtResult::For(
        crate::execute::execute_by_stmt::ExecByForStmtResult::Success(proof),
    )) = &result.statement_results[0]
    else {
        panic!("for")
    };
    let StoreFactResult::ForallFact(goal) = &proof.stored.store else {
        panic!("forall")
    };
    let root = SourcePosition::new(None, SourceOwner::Run(&result), 0);
    let branch = SourcePosition::new(
        Some(&root),
        SourceOwner::EnumerationAssignment(&goal.fact, &proof.assignments[1]),
        2,
    );
    let foreign = proof.assignments[0].binding_assumptions[0]
        .store_and_infer
        .primary_fact_id();
    assert!(branch.visible_fact(foreign, &compiler.runtime).is_err());
    let future = proof.assignments[1].binding_assumptions[0]
        .store_and_infer
        .primary_fact_id();
    assert!(SourcePosition {
        before: 1,
        ..branch
    }
    .visible_fact(future, &compiler.runtime)
    .is_err());
    let after = SourcePosition::new(None, SourceOwner::Run(&result), 1);
    assert!(after.visible_fact(foreign, &compiler.runtime).is_err());
}

#[test]
fn finite_numeric_membership_rejects_changed_or_missing_ordered_member_evidence() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
    let source = "forall listed_real {0, 1}:\n    listed_real $in R\n";
    for change in ["members", "order", "source"] {
        let (mut result, compiler) = checked(source);
        compiler.compile_run(&result, "listed_reals").unwrap();
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(f)) = &mut result.statement_results[0]
        else {
            panic!("forall")
        };
        let VerifyFactResult::ForallFact(f) = &mut f.verify_result else {
            panic!("forall")
        };
        let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(f)) =
            f.as_mut()
        else {
            panic!("introduction")
        };
        let VerifyFactResult::AtomicExceptEquality(p) = &mut f.proved_then_facts[0].verify_result
        else {
            panic!("membership")
        };
        let VerifyAtomicExceptEqualityFactResult::Success(p) = p.as_mut() else {
            panic!("membership success")
        };
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
                InFactSearchProofByBuiltinRule::FiniteSetSubsetMembership(p),
            ),
        ) = &mut p.searched_proof
        else {
            panic!("original finite subset rule")
        };
        match change {
            "members" => {
                p.member_in_proofs.pop();
            }
            "order" => p.member_in_proofs.swap(0, 1),
            "source" => p.source_set = Obj::StandardSet(StandardSet::R),
            _ => unreachable!(),
        }
        assert!(
            compiler
                .compile_run(&result, "corrupted_finite_membership")
                .unwrap_err()
                .route
                .starts_with("FiniteSetMembership/"),
            "{change}"
        );
    }
}

#[test]
fn proof_adapters_keep_their_declared_domain_boundaries() {
    for (source, route) in [
        (
            "by strong_induc n from 1:\n    ? n=n\n    n=n\n",
            "Induction/ZeroLowerBoundAndGoals",
        ),
        (
            "have fn f(x,y,z R) R=x+y+z\nhave fn g(a,b,c R) R=c+b+a\nby fn_extension f=g\n",
            "FnExtension/Arity",
        ),
        (
            "by for:\n    ? forall n {0,1}, m {n}:\n        m=m\n    m=m\n",
            "Enumeration/DependentDomain",
        ),
    ] {
        let (result, compiler) = checked(source);
        assert_eq!(
            compiler
                .compile_run(&result, "outside_adapter_domain")
                .unwrap_err()
                .route,
            route
        );
    }
}

#[test]
fn selected_or_assumptions_have_only_their_original_completed_prefix() {
    let (result, compiler) = checked("have selected_or_value R\nselected_or_value = selected_or_value or selected_or_value = 0\n");
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(fact)) = &result.statement_results[1]
    else {
        panic!("fact")
    };
    let VerifyFactResult::OrFact(proof) = &fact.verify_result else {
        panic!("or")
    };
    let VerifyOrFactResult::Success(proof) = proof.as_ref() else {
        panic!("success")
    };
    let OrFactSearchedProof::BySelectedBranch(selected) = &proof.searched_proof else {
        panic!("selected")
    };
    let id = selected.assumed_negated_branches[0]
        .store_and_infer
        .primary_fact_id();
    let root = SourcePosition::new(None, SourceOwner::Run(&result), 1);
    let scope = SourcePosition::new(Some(&root), SourceOwner::OrSelected(selected), 0);
    assert!(scope.visible_fact(id, &compiler.runtime).is_err());
    assert!(SourcePosition { before: 2, ..scope }
        .visible_fact(id, &compiler.runtime)
        .is_ok());
    let after = SourcePosition::new(None, SourceOwner::Run(&result), 2);
    assert!(after.visible_fact(id, &compiler.runtime).is_err());
}
