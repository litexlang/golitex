use super::LitexToLeanCompiler;
use crate::prelude::*;

fn checked() -> (Runtime, RunLitexCodeResult) {
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let result = runtime
        .run_litex_code("prop nonzero(x R):\n    x != 0\n$nonzero(1)\n1 $in C\n")
        .unwrap();
    assert!(result.success && result.session_error.is_none());
    (runtime, result)
}

fn predicate_wd(result: &mut RunLitexCodeResult) -> &mut AtomicFactWellDefinedProof {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) =
        &mut result.statement_results[1]
    else {
        panic!("predicate statement");
    };
    let VerifyFactResult::AtomicExceptEquality(proof) = &mut statement.verify_result else {
        panic!("atomic predicate proof");
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_mut() else {
        panic!("successful predicate proof");
    };
    &mut proof.well_defined_proof
}

#[test]
fn concrete_prop_formation_preserves_its_actual_empty_domain_route() {
    let (runtime, mut result) = checked();
    let PredicateDomainProof::ByRequirements(requirements) =
        &mut predicate_wd(&mut result).predicate_domain
    else {
        panic!("actual predicate formation route");
    };
    assert!(requirements.is_empty());
    LitexToLeanCompiler::new(runtime)
        .compile_run(&result, "empty_predicate_domain")
        .unwrap();
}

#[test]
fn concrete_prop_rejects_an_added_true_domain_stage_the_producer_did_not_execute() {
    let (runtime, mut result) = checked();
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(other)) =
        result.statement_results.pop().unwrap()
    else {
        panic!("actual true complex membership");
    };
    let other = other.verify_result;
    let PredicateDomainProof::ByRequirements(requirements) =
        &mut predicate_wd(&mut result).predicate_domain
    else {
        panic!("actual predicate formation route");
    };
    let VerifyFactResult::AtomicExceptEquality(proof) = &other else {
        panic!("atomic membership proof");
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_ref() else {
        panic!("successful membership proof");
    };
    let requirement = Fact::AtomicFact(proof.fact.clone());
    requirements.push(
        crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainWellDefinedProof {
            requirement,
            result: Box::new(other),
        },
    );
    let error = LitexToLeanCompiler::new(runtime)
        .compile_run(&result, "different_parameter_carrier")
        .unwrap_err();
    assert_eq!(error.route, "WD/PropDomain");
}

#[test]
fn concrete_prop_rejects_counterfeit_builtin_predicate_signature() {
    let (runtime, mut result) = checked();
    predicate_wd(&mut result).predicate_signature = PredicateSignatureWellDefinedProof::Builtin;
    let error = LitexToLeanCompiler::new(runtime)
        .compile_run(&result, "wrong_signature_family")
        .unwrap_err();
    assert_eq!(error.route, "Prop/SignatureFamily");
}

#[test]
fn checked_argument_domains_compile_and_reject_changed_indices_or_subjects() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::closed_calculation_proof::{
        ClosedMembershipCalculationProof, ClosedScalarValue,
    };
    use crate::execute::execute_fact_stmt::verify_atomic_fact::structural_membership_proof::{
        StructuralMembershipProof, StructuralMembershipReason,
    };
    use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainArgumentMembershipProof;
    for change in [
        "valid",
        "index",
        "subject",
        "carrier",
        "missing",
        "reordered",
    ] {
        let mut runtime = Runtime::new(LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        });
        let mut result = runtime.run_litex_code("1 < 2").unwrap();
        assert!(result.success);
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) =
            &mut result.statement_results[0]
        else {
            panic!("comparison")
        };
        let VerifyFactResult::AtomicExceptEquality(proof) = &mut statement.verify_result else {
            panic!("atomic")
        };
        let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_mut() else {
            panic!("success")
        };
        let domain = std::mem::replace(
            &mut proof.well_defined_proof.predicate_domain,
            PredicateDomainProof::ByRequirements(Vec::new()),
        );
        let PredicateDomainProof::ByRequirements(requirements) = domain else {
            panic!("ordinary comparison domain")
        };
        let mut checked = Vec::new();
        for (index, requirement) in requirements.into_iter().enumerate() {
            let Fact::AtomicFact(AtomicFact::InFact(member)) = &requirement.requirement else {
                panic!("member")
            };
            let membership = StructuralMembershipProof::new(
                member.element.clone(),
                StandardSet::R,
                StructuralMembershipReason::Closed(ClosedMembershipCalculationProof::StandardSet {
                    value: ClosedScalarValue::Decimal((index + 1).to_string()),
                    set: StandardSet::R,
                }),
            );
            checked.push(PredicateDomainArgumentMembershipProof::new(
                requirement.requirement,
                index,
                membership,
            ));
        }
        match change {
            "index" => checked[0].argument_index = 1,
            "subject" => checked[0].membership.element = checked[1].membership.element.clone(),
            "carrier" => checked[0].membership.set = StandardSet::C,
            "missing" => {
                checked.pop();
            }
            "reordered" => checked.swap(0, 1),
            _ => {}
        }
        proof.well_defined_proof.predicate_domain =
            PredicateDomainProof::ByCheckedArguments(checked);
        let compilation =
            LitexToLeanCompiler::new(runtime).compile_run(&result, "checked_argument_domain");
        if change == "valid" {
            compilation.unwrap();
        } else {
            assert_eq!(
                compilation.unwrap_err().route,
                "WD/OrderRealDomain",
                "{change}"
            );
        }
    }
}
