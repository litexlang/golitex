use super::{
    ExecHaveObjInNonemptySetStmtResult, ExecHaveObjInNonemptySetStmtSuccessResult,
    StoreHaveObjAndInferResult,
};
use crate::launch_command::OutputLanguage;
use crate::prelude::*;
use crate::rational_expression::NumberCompareResult;
use crate::store_fact_and_infer::{
    InferAtomicExceptEqualityResult, InferAtomicFactResult, InferFactResult,
};
use std::rc::Rc;

fn runtime() -> Runtime {
    // The internal Eval profile accepts an empty initial input; CLI -e does not.
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

fn have(result: &ExecStmtResult) -> &ExecHaveObjInNonemptySetStmtSuccessResult {
    match result {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjInNonemptySet(
                ExecHaveObjInNonemptySetStmtResult::Success(p),
            ),
        )) => p,
        _ => panic!("successful ordinary have"),
    }
}

fn into_have(result: ExecStmtResult) -> ExecHaveObjInNonemptySetStmtSuccessResult {
    match result {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjInNonemptySet(
                ExecHaveObjInNonemptySetStmtResult::Success(p),
            ),
        )) => p,
        _ => panic!("successful ordinary have"),
    }
}

fn ids_from_receipts(result: &StoreHaveObjAndInferResult) -> Vec<FactId> {
    result
        .store_and_infer_results
        .iter()
        .flat_map(|stored| stored.stored_fact_ids())
        .collect()
}

fn seed(stored: &StoreFactAndInferResult) -> &AtomicFact {
    match &stored.store {
        StoreFactResult::AtomicFact(p) => &p.fact,
        _ => panic!("numeric declaration's atomic seed"),
    }
}

fn natural_nonnegative(stored: &StoreFactAndInferResult) -> &StoreFactAndInferResult {
    let InferFactResult::AtomicFact(InferAtomicFactResult::ExceptEquality(rules)) = &stored.infer
    else {
        panic!("atomic membership inference")
    };
    let mut signed = rules.iter().filter_map(|rule| match rule {
        InferAtomicExceptEqualityResult::InFactSignedStandardSetSign(p) => Some(p),
        _ => None,
    });
    let signed = signed.next().unwrap();
    assert_eq!(signed.derived.len(), 1);
    &signed.derived[0]
}

#[test]
fn producer_numeric_capture_keeps_actual_ordered_group_and_aggregate_stores() {
    let mut rt = runtime();
    let run = rt
        .run_litex_code("have n, m N, z Z, q Q, r R, c C\n")
        .unwrap();
    assert!(run.success && run.session_error.is_none());
    let p = have(&run.statement_results[0]);
    assert_eq!(p.groups.len(), 5);
    assert_eq!(p.store_and_infer_result.store_and_infer_results.len(), 6);
    assert_eq!(
        p.store_and_infer_result.stored_fact_ids,
        ids_from_receipts(&p.store_and_infer_result)
    );
    let mut offset = 0;
    for (group, source_group) in p.groups.iter().zip(&p.statement.param_def.groups) {
        assert_eq!(
            group.defined_params.stored_fact_ids,
            ids_from_receipts(&group.defined_params)
        );
        assert_eq!(
            group.defined_params.store_and_infer_results.len(),
            source_group.params.len()
        );
        for (stored, parameter) in group
            .defined_params
            .store_and_infer_results
            .iter()
            .zip(&source_group.params)
        {
            assert!(Rc::ptr_eq(
                stored,
                &p.store_and_infer_result.store_and_infer_results[offset]
            ));
            let AtomicFact::InFact(member) = seed(stored) else {
                panic!("recorded member seed")
            };
            assert_eq!(
                member.element.ir(),
                Obj::Identifier(IdentifierObj::from_bound_name(parameter)).ir()
            );
            let ParamType::Obj(set) = &source_group.param_type else {
                panic!("numeric carrier")
            };
            assert_eq!(&member.set, set);
            assert_eq!(
                rt.fact_by_id_in_stack(stored.primary_fact_id()),
                Some(&Fact::AtomicFact(seed(stored).clone()))
            );
            offset += 1;
        }
    }
    for stored in &p.groups[0].defined_params.store_and_infer_results {
        let AtomicFact::InFact(member) = seed(stored) else {
            panic!()
        };
        let derived = natural_nonnegative(stored);
        let AtomicFact::LessEqualFact(bound) = seed(derived) else {
            panic!("N publishes weak nonnegativity")
        };
        assert_eq!(bound.right.ir(), member.element.ir());
        assert_eq!(
            bound.left.ir(),
            Obj::Literal(Literal::Number(Number {
                normalized_value: "0".into()
            }))
            .ir()
        );
        assert!(p
            .store_and_infer_result
            .stored_fact_ids
            .contains(&derived.primary_fact_id()));
    }
    let detail = crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt);
    let object = detail.as_object().unwrap();
    assert_eq!(object.get("groups").unwrap().as_array().unwrap().len(), 5);
    let stores = object.get("store_and_infer").unwrap().as_object().unwrap();
    assert_eq!(
        stores.get("stores").unwrap().as_array().unwrap().len(),
        p.store_and_infer_result.stored_fact_ids.len()
    );
    assert!(stores.get("infers").unwrap().as_array().unwrap().is_empty());
    assert_eq!(
        stores
            .get("store_and_infer_results")
            .unwrap()
            .as_array()
            .unwrap()
            .len(),
        6
    );
}

#[test]
fn producer_numeric_capture_keeps_typed_rhs_seed_and_equality_stores() {
    let mut rt = runtime();
    let run = rt.run_litex_code("have n N, half Q = 1, 1 / 2\n").unwrap();
    assert!(run.success && run.session_error.is_none());
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(p)),
    )) = &run.statement_results[0]
    else {
        panic!("typed RHS declaration")
    };
    let captured = &p.store_and_infer_result;
    assert_eq!(captured.store_and_infer_results.len(), 4);
    assert_eq!(captured.stored_fact_ids, ids_from_receipts(captured));
    let parameters: Vec<_> = p
        .statement
        .param_def
        .groups
        .iter()
        .flat_map(|g| &g.params)
        .collect();
    for (index, parameter) in parameters.iter().enumerate() {
        let AtomicFact::InFact(member) = seed(&captured.store_and_infer_results[index]) else {
            panic!("membership before equality")
        };
        assert_eq!(
            member.element.ir(),
            Obj::Identifier(IdentifierObj::from_bound_name(parameter)).ir()
        );
        let AtomicFact::EqualFact(equal) = seed(&captured.store_and_infer_results[index + 2])
        else {
            panic!("actual defining equality store")
        };
        assert_eq!(equal.left.ir(), member.element.ir());
        assert_eq!(equal.right.ir(), p.statement.objs_equal_to[index].ir());
    }
    assert!(captured
        .stored_fact_ids
        .contains(&natural_nonnegative(&captured.store_and_infer_results[0]).primary_fact_id()));
    let preflight = &p.type_preflight.defined_params;
    assert_eq!(preflight.stored_fact_ids, ids_from_receipts(preflight));
    assert_ne!(
        preflight.store_and_infer_results[0].primary_fact_id(),
        captured.store_and_infer_results[0].primary_fact_id()
    );
}

#[test]
fn producer_numeric_capture_owns_the_inferred_fact_cited_by_a_forall_conclusion() {
    let mut rt = runtime();
    let run = rt
        .run_litex_code("thm natural_nonnegative:\n    ? forall n N:\n        0 <= n\n")
        .unwrap();
    assert!(run.success && run.session_error.is_none());
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = &run.statement_results[0]
    else {
        panic!("named forall")
    };
    let ExecDefThmBodyProof::Forall(body) = &p.body else {
        panic!()
    };
    let introduced = &body.introduced_params.defined_params;
    let derived = natural_nonnegative(&introduced.store_and_infer_results[0]);
    let VerifyFactResult::AtomicExceptEquality(result) = &body.conclusion_proofs[0] else {
        panic!("order conclusion")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(result) = result.as_ref() else {
        panic!()
    };
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) = &result.searched_proof
    else {
        panic!("actual N inference citation")
    };
    assert_eq!(cite.cite_fact_id, derived.primary_fact_id());
    assert_eq!(result.fact.ir(), seed(derived).ir());
    assert_eq!(
        p.local_env.facts.facts_by_id.get(&cite.cite_fact_id),
        Some(&Fact::AtomicFact(seed(derived).clone()))
    );
    let VerifyFactWellDefinedResult::Success(FactWellDefinedProof::ForallFact(wd)) = &p.goal_wd
    else {
        panic!()
    };
    let wd_stores = &wd.introduced_params.defined_params;
    assert_eq!(wd_stores.stored_fact_ids, ids_from_receipts(wd_stores));
    assert_ne!(
        natural_nonnegative(&wd_stores.store_and_infer_results[0]).primary_fact_id(),
        cite.cite_fact_id
    );
}

#[test]
fn producer_numeric_capture_deleted_or_changed_receipts_cannot_be_hidden_by_flat_ids() {
    let mut rt = runtime();
    let mut run = rt.run_litex_code("have n N, q Q\n").unwrap();
    let mut p = into_have(run.statement_results.remove(0));
    let removed = p.store_and_infer_result.store_and_infer_results.remove(0);
    assert_ne!(
        p.store_and_infer_result.stored_fact_ids,
        ids_from_receipts(&p.store_and_infer_result)
    );
    assert!(Rc::ptr_eq(
        &removed,
        &p.groups[0].defined_params.store_and_infer_results[0]
    ));
    p.store_and_infer_result
        .store_and_infer_results
        .insert(0, removed);
    p.groups.clear();
    let captured = &mut p.store_and_infer_result;
    let stored = Rc::get_mut(&mut captured.store_and_infer_results[0]).unwrap();
    let StoreFactResult::AtomicFact(atomic) = &mut stored.store else {
        panic!()
    };
    let AtomicFact::InFact(member) = &mut atomic.fact else {
        panic!()
    };
    member.set = Obj::StandardSet(StandardSet::C);
    // IDs alone still agree: the source subject and actual resolver entry do not.
    assert_eq!(captured.stored_fact_ids, ids_from_receipts(captured));
    let stored = &captured.store_and_infer_results[0];
    assert_ne!(
        rt.fact_by_id_in_stack(stored.primary_fact_id()),
        Some(&Fact::AtomicFact(seed(stored).clone()))
    );
    assert!(matches!(
        &p.statement.param_def.groups[0].param_type,
        ParamType::Obj(Obj::StandardSet(StandardSet::N))
    ));
}

fn comparison(result: &ExecStmtResult) -> &ClosedComparisonCalculationProof {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = result else {
        panic!("successful comparison statement")
    };
    let VerifyFactResult::AtomicExceptEquality(p) = &p.verify_result else {
        panic!()
    };
    let VerifyAtomicExceptEqualityFactResult::Success(p) = p.as_ref() else {
        panic!()
    };
    match &p.searched_proof {
        AtomicExceptEqualityFactSearchedProof::ByClosedCalculation(
            ClosedAtomicExceptEqualityCalculationProof::Less(p)
            | ClosedAtomicExceptEqualityCalculationProof::LessEqual(p),
        ) => p,
        _ => panic!("actual direct closed comparison route"),
    }
}

#[test]
fn producer_numeric_capture_comparisons_keep_exact_values_and_compatibility_normals() {
    let mut rt = runtime();
    let run = rt
        .run_litex_code("1 / 3 < 1 / 2\n0.125 <= 0.25\n(i * i) < 0\n")
        .unwrap();
    assert!(run.success && run.session_error.is_none());
    let p = comparison(&run.statement_results[0]);
    let ClosedValuePair::Rational { left, right } = &p.values else {
        panic!("nonterminating fractions stay exact")
    };
    assert_eq!(left, &EvalRational::new(1, 3).unwrap());
    assert_eq!(right, &EvalRational::new(1, 2).unwrap());
    assert_eq!(p.left_normal, left.to_obj().readable_string());
    assert_eq!(p.right_normal, right.to_obj().readable_string());
    assert_eq!(p.comparison, NumberCompareResult::Less);
    let p = comparison(&run.statement_results[1]);
    let ClosedValuePair::Decimal { left, right } = &p.values else {
        panic!("finite decimal representation")
    };
    assert_eq!(left, "0.125");
    assert_eq!(right, "0.25");
    assert_eq!((&p.left_normal, &p.right_normal), (left, right));
    let p = comparison(&run.statement_results[2]);
    let ClosedValuePair::Complex {
        left_real,
        left_imaginary,
        right_real,
        right_imaginary,
    } = &p.values
    else {
        panic!("closed complex expression retains its coordinates")
    };
    assert_eq!(left_real, &EvalRational::new(-1, 1).unwrap());
    assert!(left_imaginary.is_zero() && right_real.is_zero() && right_imaginary.is_zero());
    let detail =
        crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt).stringify();
    assert!(
        detail.contains("rational")
            && detail.contains("left_normal")
            && detail.contains("right_normal")
            && detail.contains("comparison")
    );
}

#[test]
fn producer_numeric_capture_comparison_payload_is_independent_of_presentation() {
    let mut rt = runtime();
    let mut run = rt.run_litex_code("1 / 3 < 1 / 2\n").unwrap();
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = &mut run.statement_results[0] else {
        panic!()
    };
    let VerifyFactResult::AtomicExceptEquality(p) = &mut p.verify_result else {
        panic!()
    };
    let VerifyAtomicExceptEqualityFactResult::Success(p) = p.as_mut() else {
        panic!()
    };
    let AtomicExceptEqualityFactSearchedProof::ByClosedCalculation(
        ClosedAtomicExceptEqualityCalculationProof::Less(p),
    ) = &mut p.searched_proof
    else {
        panic!()
    };
    p.left_normal = "edited human presentation".into();
    let ClosedValuePair::Rational { left, right } = &mut p.values else {
        panic!()
    };
    assert_eq!(left, &EvalRational::new(1, 3).unwrap());
    assert_eq!(right, &EvalRational::new(1, 2).unwrap());
    *left = EvalRational::new(1, 1).unwrap();
    // A counterfeit typed payload is detectably inconsistent with its selected comparison.
    assert_ne!(left.compare(right), Some(p.comparison));
    assert!(!rt.run_litex_code("1 / 2 < 1 / 3\n").unwrap().success);
    let large_left = format!("1{}", "0".repeat(80));
    let large_right = format!("2{}", "0".repeat(80));
    let run = rt
        .run_litex_code(&format!("{large_left} < {large_right}\n"))
        .unwrap();
    assert!(run.success && run.session_error.is_none());
    let ClosedValuePair::Decimal { left, right } = &comparison(&run.statement_results[0]).values
    else {
        panic!()
    };
    assert_eq!(left, &large_left);
    assert_eq!(right, &large_right);
}
