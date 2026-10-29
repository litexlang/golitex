use super::LitexToLeanCompiler;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::{
    AtomicExceptEqualityFactSearchProofByKnownSpecialProperty, InFactSearchProofByKnownSpecialProperty,
    SignatureCodomainUseProof,
};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence;
use crate::prelude::*;

const NAMED: &str = "have fn return_pair(x R, y R: y != 0) R = x / y\nreturn_pair(3, 2) $in C\n";
const ANONYMOUS: &str = "fn(x R) R {x}(2) $in C\n";
const WEAKER: &str = "have fn call_weak_return(x R) C = x\n$is_set(call_weak_return(2))\nforall call_unused R:\n    call_weak_return $in fn(y R) R\n    =>:\n        call_weak_return(2) $in R\n";

#[test]
fn function_return_template_standard_superset_is_explicitly_unsupported() {
    use super::source_position::{SourceOwner, SourcePosition};
    let (result, compiler) = checked(
        "template<S set>:\n    have fn real_identity(x R) R = x\nforall x R:\n    \\real_identity<R>(x) $in C\n",
    );
    let VerifyFactResult::ForallFact(proof) = verified(&result.statement_results[1]) else {
        panic!("actual forall result");
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(proof)) =
        proof.as_ref()
    else {
        panic!("actual local introduction");
    };
    let success = atomic(&proof.proved_then_facts[0].verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(
        AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(
            rule
            @ InFactSearchProofByKnownSpecialProperty::TemplateApplicationInStandardSuperset(_),
        ),
    ) = &success.searched_proof
    else {
        panic!("actual template standard-return evidence")
    };
    let AtomicFact::InFact(goal) = &success.fact else {
        panic!("actual membership")
    };
    let position = SourcePosition::new(None, SourceOwner::Run(&result), 1);
    let error = compiler
        .compile_fn_return_rule(goal, rule, &position)
        .unwrap_err();
    assert_eq!(error.route, "FunctionReturn/TemplateStandardSuperset");
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
    let result = runtime.run_litex_code(source).unwrap();
    assert!(result.success && result.session_error.is_none(), "{source}");
    (result, LitexToLeanCompiler::new(runtime))
}

fn verified(result: &ExecStmtResult) -> &VerifyFactResult {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(result)) = result else {
        panic!("successful source fact");
    };
    &result.verify_result
}

fn atomic(result: &VerifyFactResult) -> &VerifyAtomicExceptEqualityFactSuccess {
    let VerifyFactResult::AtomicExceptEquality(result) = result else {
        panic!("actual atomic return fact");
    };
    let VerifyAtomicExceptEqualityFactResult::Success(result) = result.as_ref() else {
        panic!("successful atomic fact");
    };
    result
}

fn atomic_mut(result: &mut VerifyFactResult) -> &mut VerifyAtomicExceptEqualityFactSuccess {
    let VerifyFactResult::AtomicExceptEquality(result) = result else {
        panic!("actual atomic return fact");
    };
    let VerifyAtomicExceptEqualityFactResult::Success(result) = result.as_mut() else {
        panic!("successful atomic fact");
    };
    result
}

fn forall_body(result: &RunLitexCodeResult) -> &VerifyAtomicExceptEqualityFactSuccess {
    let VerifyFactResult::ForallFact(proof) = verified(&result.statement_results[2]) else {
        panic!("conditional forall");
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(proof)) =
        proof.as_ref()
    else {
        panic!("local introduction");
    };
    atomic(&proof.proved_then_facts[0].verify_result)
}

fn forall_body_mut(result: &mut RunLitexCodeResult) -> &mut VerifyAtomicExceptEqualityFactSuccess {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(proof)) = &mut result.statement_results[2]
    else {
        panic!("forall statement");
    };
    let VerifyFactResult::ForallFact(proof) = &mut proof.verify_result else {
        panic!("conditional forall");
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(proof)) =
        proof.as_mut()
    else {
        panic!("local introduction");
    };
    atomic_mut(&mut proof.proved_then_facts[0].verify_result)
}

fn original_weak_citation(result: &RunLitexCodeResult) -> FactId {
    let proof = atomic(verified(&result.statement_results[1]));
    let DetailedObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::FnObj(call),
        ..
    } = (&proof
        .well_defined_proof
        .detailed_ref()
        .well_defined_of_each_parameter[0])
        .as_detailed()
        .unwrap()
    else {
        panic!("original weak call constructor");
    };
    let Some(FnObjDomainFnSetEvidence::InFunctionSet {
        fn_set, fact_id, ..
    }) = &call.domain_fn_set
    else {
        panic!("original signature");
    };
    assert_eq!(fn_set.ret_set.as_ref(), &Obj::StandardSet(StandardSet::C));
    *fact_id
}

fn codomain_mut(result: &mut RunLitexCodeResult) -> &mut crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::FnApplicationInCodomainKnownSpecialPropertyProof{
    let AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(
        AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(
            InFactSearchProofByKnownSpecialProperty::FnApplicationInCodomain(proof),
        ),
    ) = &mut forall_body_mut(result).searched_proof
    else {
        panic!("actual stronger codomain route");
    };
    proof
}

#[test]
fn function_return_replays_named_real_to_complex_original_signature_rows() {
    let (result, compiler) = checked(NAMED);
    let source = atomic(verified(&result.statement_results[1]));
    let AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(
        AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(
            InFactSearchProofByKnownSpecialProperty::FnApplicationInStandardSuperset(payload),
        ),
    ) = &source.searched_proof
    else {
        panic!("actual source-selected named upper-bound rule");
    };
    assert_eq!(payload.target_set, StandardSet::C);
    assert!(payload
        .signature_returns
        .iter()
        .all(|entry| entry.source_set == StandardSet::R));
    let DetailedObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::FnObj(wd),
        ..
    } = (&source
        .well_defined_proof
        .detailed_ref()
        .well_defined_of_each_parameter[0])
        .as_detailed()
        .unwrap()
    else {
        panic!("actual call WD");
    };
    let Some(FnObjDomainFnSetEvidence::InFunctionSet { fact_id, .. }) = &wd.domain_fn_set else {
        panic!("recorded WD source");
    };
    assert!(payload
        .signature_returns
        .iter()
        .any(|entry| entry.cite_signature_fact_id == *fact_id));
    let output = compiler
        .compile_run(&result, "named_return_to_complex")
        .unwrap();
    assert!(output.contains(&format!("h_{}", fact_id.value())));
    assert!(output.contains("Litex.realToComplex"));
}

#[test]
fn function_return_replays_actual_anonymous_scalar_codomain_rule() {
    let (result, compiler) = checked(ANONYMOUS);
    let source = atomic(verified(&result.statement_results[0]));
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
            InFactSearchProofByBuiltinRule::AnonymousFnApplicationScalarCodomain(payload),
        ),
    ) = &source.searched_proof
    else {
        panic!("actual source-selected scalar literal rule");
    };
    assert_eq!(payload.codomain, StandardSet::R);
    compiler
        .compile_run(&result, "anonymous_scalar_return")
        .expect("owned literal return followed by R-to-C inclusion");
}

#[test]
fn function_return_uses_stronger_selected_truth_after_actual_weaker_cached_wd() {
    let (result, compiler) = checked(WEAKER);
    let weak = original_weak_citation(&result);
    let body = forall_body(&result);
    assert!(
        matches!(
            (&body
                .well_defined_proof
                .detailed_ref()
                .well_defined_of_each_parameter[0])
                .as_detailed()
                .unwrap(),
            DetailedObjWellDefinedProof::ByKnown { .. }
        ),
        "this source really reuses the earlier C-returning constructor"
    );
    let AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(
        AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(
            InFactSearchProofByKnownSpecialProperty::FnApplicationInCodomain(payload),
        ),
    ) = &body.searched_proof
    else {
        panic!("actual selected stronger truth");
    };
    assert_ne!(payload.cite_property_fact_id, weak);
    assert!(payload.signature_uses.iter().any(|entry| matches!(entry, SignatureCodomainUseProof::SameCallDomains { cite_signature_fact_id, domains, .. } if *cite_signature_fact_id == weak && domains.layers.len() == 1)));
    let output = compiler
        .compile_run(&result, "stronger_selected_return")
        .unwrap();
    assert!(output.contains(&format!("h_{}", payload.cite_property_fact_id.value())));
    assert!(
        output.contains("Litex.FunctionSemantics.call_mem"),
        "the R conclusion must consume the selected R signature; the cached C output law is insufficient"
    );
}

#[test]
fn function_return_rejects_upper_bound_table_missing_actual_wd_source() {
    let (mut result, compiler) = checked(NAMED);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) =
        &mut result.statement_results[1]
    else {
        panic!("source return fact");
    };
    let source = atomic_mut(&mut statement.verify_result);
    let DetailedObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::FnObj(wd),
        ..
    } = (&source
        .well_defined_proof
        .detailed_ref()
        .well_defined_of_each_parameter[0])
        .as_detailed()
        .unwrap()
    else {
        panic!("source call WD");
    };
    let Some(FnObjDomainFnSetEvidence::InFunctionSet { fact_id, .. }) = &wd.domain_fn_set else {
        panic!("selected source");
    };
    let id = *fact_id;
    let AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(
        AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(
            InFactSearchProofByKnownSpecialProperty::FnApplicationInStandardSuperset(payload),
        ),
    ) = &mut source.searched_proof
    else {
        panic!("upper-bound table");
    };
    payload
        .signature_returns
        .retain(|entry| entry.cite_signature_fact_id != id);
    assert!(
        !payload.signature_returns.is_empty(),
        "another real source row remains, but it cannot replace the actual selected source"
    );
    assert_eq!(
        compiler
            .compile_run(&result, "missing_wd_return_row")
            .unwrap_err()
            .route,
        "FunctionReturn/SelectedSignature"
    );
}

#[test]
fn function_return_rejects_wrong_or_missing_main_selected_signature() {
    let (mut wrong, compiler) = checked(WEAKER);
    let weak = original_weak_citation(&wrong);
    codomain_mut(&mut wrong).cite_property_fact_id = weak;
    assert_eq!(
        compiler
            .compile_run(&wrong, "wrong_selected_source")
            .unwrap_err()
            .route,
        "FunctionReturn/SameDomains"
    );

    let (mut missing, compiler) = checked(WEAKER);
    let payload = codomain_mut(&mut missing);
    let main = payload.cite_property_fact_id;
    payload.signature_uses.retain(|entry| match entry {
        SignatureCodomainUseProof::ReturnSetMatch(entry) => entry.cite_signature_fact_id != main,
        SignatureCodomainUseProof::SameCallDomains {
            cite_signature_fact_id,
            ..
        } => *cite_signature_fact_id != main,
    });
    assert_eq!(
        compiler
            .compile_run(&missing, "missing_main_return_row")
            .unwrap_err()
            .route,
        "FunctionReturn/SelectedSignature"
    );
}

#[test]
fn function_return_rejects_corrupted_recorded_same_domain_signatures() {
    let (mut result, compiler) = checked(WEAKER);
    let weak = original_weak_citation(&result);
    let payload = codomain_mut(&mut result);
    let entry = payload.signature_uses.iter_mut().find(|entry| matches!(entry, SignatureCodomainUseProof::SameCallDomains { cite_signature_fact_id, .. } if *cite_signature_fact_id == weak)).expect("actual weak/strong comparison");
    let SignatureCodomainUseProof::SameCallDomains { domains, .. } = entry else {
        unreachable!();
    };
    domains.layers[0].selected.ret_set = Box::new(Obj::StandardSet(StandardSet::C));
    assert_eq!(
        compiler
            .compile_run(&result, "wrong_recorded_domain_source")
            .unwrap_err()
            .route,
        "FunctionReturn/SameDomains"
    );
}

#[test]
fn function_return_matrix_wd_consumes_stored_signature_citations() {
    for carrier in ["R", "C"] {
        let source = format!(
            "zero_matrix(4,4) $in fn(u closed_range(1,4), v closed_range(1,4)) {carrier}\nzero_matrix(4,4)(1,1) $in C"
        );
        let (result, compiler) = checked(&source);
        let proof = atomic(verified(&result.statement_results[1]));
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FnObj(wd),
            ..
        } = (&proof
            .well_defined_proof
            .detailed_ref()
            .well_defined_of_each_parameter[0])
            .as_detailed()
            .unwrap()
        else {
            panic!("matrix call WD")
        };
        assert!(matches!(
            &wd.domain_fn_set,
            Some(FnObjDomainFnSetEvidence::Matrix(_))
        ));
        let AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(
            AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(rule),
        ) = &proof.searched_proof
        else {
            panic!("recorded function-return citation")
        };
        let ids: Vec<FactId> = match rule {
            InFactSearchProofByKnownSpecialProperty::FnApplicationInStandardSuperset(p)
                if carrier == "R" =>
            {
                p.signature_returns
                    .iter()
                    .map(|e| e.cite_signature_fact_id)
                    .collect()
            }
            InFactSearchProofByKnownSpecialProperty::FnApplicationInCodomain(p)
                if carrier == "C" =>
            {
                vec![p.cite_property_fact_id]
            }
            _ => panic!("original matrix-return route"),
        };
        let lean = compiler
            .compile_run(&result, "matrix_signature_return")
            .unwrap();
        assert!(ids
            .iter()
            .all(|id| lean.contains(&format!("h_{}", id.value()))));
        assert!(lean.contains("Litex.FunctionSemantics.call_mem"));
    }
}

#[test]
fn function_return_matrix_wd_rejects_missing_citations_and_changed_domain() {
    for carrier in ["R", "C"] {
        for change in 0..2 {
            let source = format!(
                "zero_matrix(4,4) $in fn(u closed_range(1,4), v closed_range(1,4)) {carrier}\nzero_matrix(4,4)(1,1) $in C"
            );
            let (mut result, compiler) = checked(&source);
            let ExecStmtResult::Fact(ExecFactStmtResult::Success(fact)) =
                &mut result.statement_results[1]
            else {
                panic!("call fact")
            };
            let proof = atomic_mut(&mut fact.verify_result);
            if change == 0 {
                let AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(
                    AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(rule),
                ) = &mut proof.searched_proof
                else {
                    panic!("return citation")
                };
                match rule {
                    InFactSearchProofByKnownSpecialProperty::FnApplicationInStandardSuperset(p) => {
                        p.signature_returns.clear()
                    }
                    InFactSearchProofByKnownSpecialProperty::FnApplicationInCodomain(p) => {
                        p.signature_uses.clear()
                    }
                    _ => panic!("matrix return route"),
                }
            } else {
                let DetailedObjWellDefinedProof::ByDef {
                    proof: ObjWellDefinedProofByDef::FnObj(wd),
                    ..
                } = (&mut proof
                    .well_defined_proof
                    .as_detailed_mut()
                    .unwrap()
                    .well_defined_of_each_parameter[0])
                    .as_detailed_mut()
                    .unwrap()
                else {
                    panic!("call WD")
                };
                let Some(FnObjDomainFnSetEvidence::Matrix(p)) = &mut wd.domain_fn_set else {
                    panic!("native matrix")
                };
                p.function.body.set_bound_parameters.groups[0].param_type =
                    Box::new(Obj::StandardSet(StandardSet::R));
            }
            assert!(compiler.compile_run(&result, "bad_matrix_return").is_err());
        }
    }
}

#[test]
fn checked_order_argument_function_return_is_replayed() {
    let source = "thm guarded_real_order:\n    ? forall f fn(x R:x>0) R,n R:\n        n>0\n        =>:\n            f(n+1)<=f(n+1)\n";
    let (result, compiler) = checked(source);
    let lean = compiler
        .compile_run(&result, "checked_order_function_return")
        .unwrap();
    assert!(lean.contains("theorem"));
}

#[test]
fn checked_order_function_return_rejects_changed_membership_carrier() {
    let source = "forall f fn(x R:x>0) R,n R:\n    n>0\n    =>:\n        f(n+1)<=f(n+1)\n";
    let (mut result, compiler) = checked(source);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) =
        &mut result.statement_results[0]
    else {
        panic!("checked forall statement");
    };
    let VerifyFactResult::ForallFact(proof) = &mut statement.verify_result else {
        panic!("checked forall");
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(proof)) =
        proof.as_mut()
    else {
        panic!("local introduction");
    };
    let atomic = atomic_mut(&mut proof.proved_then_facts[0].verify_result);
    let PredicateDomainProof::ByRequirements(requirements) = &mut atomic
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .predicate_domain
    else {
        panic!("checked argument return evidence");
    };
    let Fact::AtomicFact(AtomicFact::InFact(member)) = &mut requirements[0].requirement else {
        panic!("real membership requirement")
    };
    member.set = Obj::StandardSet(StandardSet::C);
    let error = compiler
        .compile_run(&result, "changed_return_argument")
        .unwrap_err();
    assert_eq!(error.route, "WD/OrderRealDomain");
}

#[test]
fn checked_return_membership_composes_through_arithmetic_in_lean() {
    let source = "thm composed_real_return:\n    ? forall f fn(x R:x>0) R,n R:\n        n>0\n        =>:\n            (f(n+1)+1)*(f(n+1)-1) $in R\n";
    let (result, compiler) = checked(source);
    let lean = compiler
        .compile_run(&result, "composed_real_return")
        .unwrap();
    assert!(lean.contains("theorem"));
    assert!(lean.contains("call"));
}

#[test]
fn checked_return_composition_rejects_changed_leaf_carrier() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::structural_membership_proof::StructuralMembershipReason;
    let source = "forall f fn(x R:x>0) R,n R:\n    n>0\n    =>:\n        (f(n+1)+1) $in R\n";
    let (mut result, compiler) = checked(source);
    let VerifyFactResult::ForallFact(universal) = (match &mut result.statement_results[0] {
        ExecStmtResult::Fact(ExecFactStmtResult::Success(s)) => &mut s.verify_result,
        _ => panic!("source forall"),
    }) else {
        panic!("forall proof")
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(proof)) =
        universal.as_mut()
    else {
        panic!("local scope")
    };
    let atomic = atomic_mut(&mut proof.proved_then_facts[0].verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByStructuralMembership(tree) =
        &mut atomic.searched_proof
    else {
        panic!("shared membership proof")
    };
    let StructuralMembershipReason::Add { left, .. } = &mut tree.reason else {
        panic!("addition")
    };
    let StructuralMembershipReason::FunctionReturn { membership, .. } = &mut left.reason else {
        panic!("function return")
    };
    membership.set = Obj::StandardSet(StandardSet::C);
    let error = compiler
        .compile_run(&result, "changed_function_leaf")
        .unwrap_err();
    assert_eq!(error.route, "StructuralMembership/FunctionReturnSubject");
}
