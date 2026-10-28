use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof;
use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::SearchProofByKnownForallFact;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_equal::NotEqualFactSearchProofByBuiltinRule;

fn quotient_children_mut(result: &mut RunLitexCodeResult) -> &mut Vec<VerifyFactResult> {
    let forall = super::forall_proof_mut(&mut result.statement_results[0]);
    let atomic = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(
            NotEqualFactSearchProofByBuiltinRule::DivNonzeroFromFactors(rule),
        ),
    ) = &mut atomic.searched_proof
    else {
        panic!("actual selected quotient rule")
    };
    &mut rule.proof_of_requirement_facts
}

fn difference_premise_mut(result: &mut RunLitexCodeResult) -> &mut crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof{
    let forall = super::forall_proof_mut(&mut result.statement_results[0]);
    let atomic = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(
            NotEqualFactSearchProofByBuiltinRule::InequalityFromDifferenceNonzero(rule),
        ),
    ) = &mut atomic.searched_proof
    else {
        panic!("actual selected difference reflection")
    };
    &mut rule.premise_proof
}

const QUOTIENT: &str = "forall a, b R:\n    a!=0\n    b!=0\n    =>:\n        a/b!=0\n";
const REFLECTION: &str = "forall a, b R:\n    a-b!=0\n    =>:\n        a!=b\n";
const KNOWN_QUOTIENT: &str = "forall x R:\n    x!=0\n    =>:\n        2/x!=0\nforall y R:\n    y!=1\n    =>:\n        2/(y-1)!=0\n";
// The extra identity conclusion keeps this an atomic instantiation probe,
// rather than selecting the valid whole-forall alpha-reuse route.
// The additional conclusion prevents whole-forall alpha-renaming and isolates
// the atomic function-call application whose recorded child slots are tested.
const KNOWN_FUNCTION: &str = "have fn reciprocal(x R: x!=0) R=1/x\nforall x R:\n    x!=0\n    =>:\n        reciprocal(x)!=0\nforall y R:\n    y!=0\n    =>:\n        reciprocal(y)!=0\n        y=y\n";

#[test]
fn atomic_known_forall_preserves_function_prefix_and_argument_slots() {
    for corrupt in [false, true] {
        let (mut result, compiler) = super::execute(KNOWN_FUNCTION);
        let forall = super::forall_proof_mut(&mut result.statement_results[2]);
        let atomic = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(known) =
            &mut atomic.searched_proof
        else {
            panic!("actual known function conclusion")
        };
        let DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } =
            known.as_detailed_mut().unwrap().arg_match_proofs[0]
                .as_detailed_mut()
                .unwrap()
        else {
            panic!("captured call structure")
        };
        assert_eq!(child_matches.len(), 2);
        if corrupt {
            child_matches.swap(0, 1);
        }
        let output = super::compile_run(&result, &compiler, "known_function");
        if corrupt {
            assert!(output.is_err());
        } else {
            assert!(output
                .unwrap()
                .contains("Litex.FunctionSemantics.callValue"));
        }
    }
}

fn known_quotient_mut(result: &mut RunLitexCodeResult) -> &mut SearchProofByKnownForallFact {
    let forall = super::forall_proof_mut(&mut result.statement_results[1]);
    let atomic = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(known) =
        &mut atomic.searched_proof
    else {
        panic!("actual selected atomic forall application")
    };
    known
}

#[test]
fn atomic_known_forall_replays_original_instantiation_requirements() {
    let (mut result, compiler) = super::execute(KNOWN_QUOTIENT);
    assert_eq!(
        known_quotient_mut(&mut result)
            .detailed_ref()
            .instantiation_requirements
            .detailed_ref()
            .proof_of_dom_facts
            .len(),
        1
    );
    let output = super::compile_run(&result, &compiler, "known_quotient").unwrap();
    assert!(output.contains("Litex.notSameOfSame"));
}

#[test]
fn atomic_known_forall_rejects_deleted_changed_or_reordered_evidence() {
    for change in ["domain", "types", "matching", "parameter", "producer"] {
        let (mut result, compiler) = super::execute(KNOWN_QUOTIENT);
        let known = known_quotient_mut(&mut result);
        match change {
            "domain" => known
                .as_detailed_mut()
                .unwrap()
                .instantiation_requirements
                .as_detailed_mut()
                .unwrap()
                .proof_of_dom_facts
                .clear(),
            "types" => known
                .as_detailed_mut()
                .unwrap()
                .instantiation_requirements
                .as_detailed_mut()
                .unwrap()
                .param_type_requirements
                .clear(),
            "matching" => known.as_detailed_mut().unwrap().arg_match_proofs.swap(0, 1),
            "parameter" => {
                known
                    .as_detailed_mut()
                    .unwrap()
                    .forall_parameters_match_what_args[0] =
                    Obj::Literal(Literal::Number(Number::new("1".into())))
            }
            "producer" => {
                result.statement_results.remove(0);
            }
            _ => unreachable!(),
        }
        assert!(
            super::compile_run(&result, &compiler, "corrupted_known_quotient").is_err(),
            "{change}"
        );
    }
}

#[test]
fn quotient_nonzero_replays_ordered_children_and_both_zero_orientations() {
    for carrier in ["N", "Z", "Q", "R", "C"] {
        for conclusion in ["a/b!=0", "0!=a/b", "a/b!=1-1", "1-1!=a/b"] {
            let source = format!(
                "forall a, b {carrier}:\n    a!=0\n    b!=0\n    =>:\n        {conclusion}\n"
            );
            let (mut result, compiler) = super::execute(&source);
            assert_eq!(quotient_children_mut(&mut result).len(), 2);
            let output = super::compile_run(&result, &compiler, "quotient_nonzero").unwrap();
            assert!(output.contains("Litex.divNonzero"), "{source}");
            assert!(output.contains("Representation M"));
        }
    }
}

#[test]
fn quotient_nonzero_rejects_deleted_added_or_reordered_children() {
    for change in ["deleted", "empty", "added", "reordered"] {
        let (mut result, compiler) = super::execute(QUOTIENT);
        let children = quotient_children_mut(&mut result);
        if change == "deleted" {
            children.pop();
        } else if change == "empty" {
            children.clear();
        } else if change == "reordered" {
            children.swap(0, 1);
        } else {
            let (mut donor, _) = super::execute(QUOTIENT);
            children.push(quotient_children_mut(&mut donor).pop().unwrap());
        }
        assert!(super::compile_run(&result, &compiler, "corrupted_quotient_children").is_err());
    }
}

#[test]
fn quotient_nonzero_rejects_changed_child_and_missing_producer() {
    for missing in [false, true] {
        let (mut result, compiler) = super::execute(QUOTIENT);
        if missing {
            super::forall_proof_mut(&mut result.statement_results[0])
                .assumed_dom_facts
                .clear();
        } else {
            let child = super::atomic_proof_mut(&mut quotient_children_mut(&mut result)[0]);
            let AtomicFact::NotEqualFact(fact) = &mut child.fact else {
                panic!("factor inequality")
            };
            fact.right = Obj::Literal(Literal::Number(Number::new("1".into())));
        }
        assert!(super::compile_run(&result, &compiler, "missing_quotient_evidence").is_err());
    }
}

#[test]
fn difference_reflection_replays_known_citation_in_either_order() {
    for carrier in ["N", "Z", "Q", "R", "C"] {
        for difference in ["a-b", "b-a"] {
            let source =
                format!("forall a, b {carrier}:\n    {difference}!=0\n    =>:\n        a!=b\n");
            let (mut result, compiler) = super::execute(&source);
            difference_premise_mut(&mut result);
            let output = super::compile_run(&result, &compiler, "difference_reflection").unwrap();
            assert!(output.contains("Litex.notSameOfSubNonzero"));
        }
    }
}

#[test]
fn difference_reflection_rejects_wrong_zero_endpoint_and_removed_producer() {
    for missing in [false, true] {
        let (mut result, compiler) = super::execute(REFLECTION);
        if missing {
            super::forall_proof_mut(&mut result.statement_results[0])
                .assumed_dom_facts
                .clear();
        } else {
            let AtomicFact::NotEqualFact(fact) = &mut difference_premise_mut(&mut result).fact
            else {
                panic!("difference inequality")
            };
            fact.right = Obj::Literal(Literal::Number(Number::new("1".into())));
        }
        assert!(super::compile_run(&result, &compiler, "corrupted_reflection").is_err());
    }
}
