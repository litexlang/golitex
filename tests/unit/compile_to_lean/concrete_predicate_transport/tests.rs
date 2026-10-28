use crate::execute::execute_by_stmt::ExecByDefStmtResult;
use crate::prelude::*;

const SINGLE: &str = "prop transport_nonnegative(x R):\n    x>=0\nby def $transport_nonnegative(2)\nhave transported_real R=2\n$transport_nonnegative(transported_real)\n";
const TWO: &str = "prop transport_ordered(x Q,y R):\n    x<=y\nby def $transport_ordered(2,5)\nhave transported_rational Q=2\nhave transported_upper R=5\n$transport_ordered(transported_rational,transported_upper)\n";
const MULTICLAUSE: &str = "prop transport_reciprocal_certificate(x R):\n    x!=0\n    (1/x)*x=1\nby def $transport_reciprocal_certificate(2)\nhave transported_denominator R=2\n$transport_reciprocal_certificate(transported_denominator)\nhave fn transported_inverse(x R: $transport_reciprocal_certificate(x)) R=1/x\ntransported_inverse(transported_denominator)=1/2\n";
const GENERIC: &str = "prop transport_nonnegative(x R):\n    x>=0\nhave fn transport_guarded_square(x R: $transport_nonnegative(x)) R=x^2\nforall a,b R:\n    a=b\n    $transport_nonnegative(a)\n    =>:\n        $transport_nonnegative(b)\n        transport_guarded_square(b)=b^2\n";
const GENERIC_NONZERO: &str = "prop transport_nonzero(x R):\n    x!=0\nhave fn transport_inverse_generic(x R: $transport_nonzero(x)) R=1/x\nforall a,b R:\n    a=b\n    $transport_nonzero(a)\n    =>:\n        $transport_nonzero(b)\n        transport_inverse_generic(b)*b=1\n";

fn known_normal(
    result: &mut VerifyFactResult,
) -> &mut AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
    let atomic = super::atomic_proof_mut(result);
    assert!(matches!(atomic.fact, AtomicFact::NormalAtomicFact(_)));
    match &mut atomic.searched_proof {
        AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(proof) => proof,
        _ => panic!("the actual outer Normal winner is an original atomic citation"),
    }
}

fn statement_known(
    statement: &mut ExecStmtResult,
) -> &mut AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
    known_normal(&mut super::fact_statement_mut(statement).verify_result)
}

fn ordered_path(proof: &mut EqualFactSearchedProof) -> &mut KnownEqualityPathProof {
    match proof {
        EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
        ) => path,
        _ => panic!("this selected parameter equality has its original oriented path"),
    }
}

fn defining_equal_id(statement: &mut ExecStmtResult) -> FactId {
    super::have_equal_mut(statement)
        .store_and_infer_result
        .store_and_infer_results
        .iter()
        .flat_map(|store| store.store.atomic_components())
        .find_map(|(id, fact)| matches!(fact, AtomicFact::EqualFact(_)).then_some(id))
        .expect("the actual typed-value definition's equality store")
}

fn by_definition_id(statement: &ExecStmtResult) -> FactId {
    match statement {
        ExecStmtResult::By(ExecByStmtResult::Def(ExecByDefStmtResult::Success(proof))) => {
            proof.stored.primary_fact_id()
        }
        _ => panic!("the actual successful by-definition producer"),
    }
}

#[test]
fn concrete_predicate_transport_replays_original_single_and_two_argument_citations() {
    for (source, target, arity) in [(SINGLE, 3, 1), (TWO, 4, 2), (MULTICLAUSE, 3, 1)] {
        let (mut result, compiler) = super::execute(source);
        let cited = by_definition_id(&result.statement_results[1]);
        let known = statement_known(&mut result.statement_results[target]);
        assert_eq!(known.cite_fact_id, cited);
        assert_eq!(
            known.why_parameters_of_known_fact_are_equal_to_givens.len(),
            arity
        );
        for equality in &mut known.why_parameters_of_known_fact_are_equal_to_givens {
            assert_eq!(ordered_path(equality).path.len(), 1);
        }
        let output = super::compile_run(&result, &compiler, "concrete_transport")
            .expect("the original Normal citation and ordered equality winners replay");
        assert!(output.contains("have _known_citation :"));
        assert!(output.contains("exact Eq.mp"));
        assert!(output.contains("congrArg (fun (_known_value : M.Value)"));
        assert!(!output.contains("sorry") && !output.contains("admit"));
    }
}

#[test]
fn concrete_predicate_transport_preserves_generic_hosts_and_transported_guard_use() {
    for source in [GENERIC, GENERIC_NONZERO] {
        let (mut result, compiler) = super::execute(source);
        let theorem = super::forall_proof_mut(&mut result.statement_results[2]);
        assert_eq!(theorem.proved_then_facts.len(), 2);
        let known = known_normal(&mut theorem.proved_then_facts[0].verify_result);
        assert_eq!(
            known.why_parameters_of_known_fact_are_equal_to_givens.len(),
            1
        );
        assert_eq!(
            ordered_path(&mut known.why_parameters_of_known_fact_are_equal_to_givens[0])
                .path
                .len(),
            1
        );
        let output = super::compile_run(&result, &compiler, "generic_concrete_transport")
            .expect("original generic equality transports the predicate and supports the guard");
        assert!(output.contains("Litex.Representation M _Host_i"));
        assert!(output.contains("exact Eq.mp"));
        // Both actual winners replay a captured anonymous-body expansion:
        // HaveFnEqual normalization or FnApplicationUnfoldSubstitution.
        // That expansion emits formula beta and call congruence bridges.
        assert!(output.contains("Litex.callFormula_denote"));
        assert!(output.contains("Litex.callCongr"));
    }
}

#[test]
fn concrete_predicate_transport_rejects_missing_wrong_and_reordered_argument_evidence() {
    for change in [
        "missing_argument",
        "missing_path",
        "wrong_endpoint",
        "wrong_equal_citation",
        "reordered_arguments",
    ] {
        let (mut result, compiler) = super::execute(TWO);
        let wrong_equal = by_definition_id(&result.statement_results[1]);
        let known = statement_known(&mut result.statement_results[4]);
        let equalities = &mut known.why_parameters_of_known_fact_are_equal_to_givens;
        assert_eq!(equalities.len(), 2);
        match change {
            "missing_argument" => {
                equalities.pop();
            }
            "missing_path" => ordered_path(&mut equalities[0]).path.clear(),
            "wrong_endpoint" => {
                ordered_path(&mut equalities[0]).path[0].0 = super::number_object("7")
            }
            "wrong_equal_citation" => ordered_path(&mut equalities[0]).path[0].2 = wrong_equal,
            "reordered_arguments" => equalities.swap(0, 1),
            _ => unreachable!(),
        }
        super::phase2_rejected(
            &result,
            &compiler,
            change,
            &["KnownAtomic", "Equality/", "FactId/"],
        );
    }
}

#[test]
fn concrete_predicate_transport_rejects_a_wrong_or_missing_original_predicate_citation() {
    for change in ["missing", "different_family"] {
        let (mut result, compiler) = super::execute(SINGLE);
        let wrong_id = defining_equal_id(&mut result.statement_results[2]);
        let known = statement_known(&mut result.statement_results[3]);
        known.cite_fact_id = if change == "missing" {
            FactId::new(u64::MAX)
        } else {
            wrong_id
        };
        super::phase2_rejected(&result, &compiler, change, &["KnownAtomic", "FactId/"]);
    }
}

#[test]
fn concrete_predicate_transport_rejects_removed_and_future_predicate_producers() {
    for change in [
        "removed_citation",
        "future_citation",
        "removed_definition",
        "future_definition",
    ] {
        let (mut result, compiler) = super::execute(SINGLE);
        match change {
            "removed_citation" => {
                result.statement_results.remove(1);
            }
            "future_citation" => {
                let producer = result.statement_results.remove(1);
                result.statement_results.push(producer);
            }
            "removed_definition" => {
                result.statement_results.remove(0);
            }
            "future_definition" => {
                let definition = result.statement_results.remove(0);
                result.statement_results.push(definition);
            }
            _ => unreachable!(),
        }
        super::phase2_rejected(
            &result,
            &compiler,
            change,
            &["FactId/", "WD/", "Prop", "Function/", "KnownAtomic"],
        );
    }
}

#[test]
fn concrete_predicate_transport_rejects_actual_future_equalities_and_predicate_citations() {
    let source = format!(
        "{SINGLE}have transported_future R=2\nby def $transport_nonnegative(transported_real)\n"
    );
    for change in ["future_equality", "future_predicate"] {
        let (mut result, compiler) = super::execute(&source);
        let future_equal = defining_equal_id(&mut result.statement_results[4]);
        let future_predicate = by_definition_id(&result.statement_results[5]);
        let known = statement_known(&mut result.statement_results[3]);
        if change == "future_equality" {
            ordered_path(&mut known.why_parameters_of_known_fact_are_equal_to_givens[0]).path[0]
                .2 = future_equal;
        } else {
            known.cite_fact_id = future_predicate;
        }
        super::phase2_rejected(
            &result,
            &compiler,
            change,
            &["FactId/", "Equality/", "KnownAtomic"],
        );
    }
}

#[test]
fn concrete_predicate_transport_rejects_a_changed_original_target_wd_subject() {
    let (mut result, compiler) = super::execute(SINGLE);
    let atomic = super::atomic_proof_mut(
        &mut super::fact_statement_mut(&mut result.statement_results[3]).verify_result,
    );
    super::replace_wd_subject(
        &mut atomic
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .well_defined_of_each_parameter[0],
        super::number_object("7"),
    );
    super::phase2_rejected(&result, &compiler, "wrong_target_wd", &["WD/", "FactId/"]);
}

#[test]
fn concrete_predicate_transport_rejects_wrong_source_predicate_identity() {
    let (mut result, compiler) = super::execute(TWO);
    let atomic = super::atomic_proof_mut(
        &mut super::fact_statement_mut(&mut result.statement_results[4]).verify_result,
    );
    let AtomicFact::NormalAtomicFact(goal) = &mut atomic.fact else {
        unreachable!()
    };
    goal.predicate = AtomicName::Plain {
        name: "transport_missing_identity".to_string(),
    };
    super::phase2_rejected(
        &result,
        &compiler,
        "wrong_predicate_identity",
        &["WD/", "Prop", "FactId/", "KnownAtomic"],
    );
}
