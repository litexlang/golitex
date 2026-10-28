use crate::execute::execute_by_stmt::{ExecByDefStmtResult, ExecByDefStmtSuccess};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::{
    AtomicExceptEqualityFactSearchProofByDefinition,
    AtomicExceptEqualityFactSearchProofByKnownAtomicFact, UserDefinedPropDefinitionProof,
};
use crate::execute::ExecDefPropStmtResult;
use crate::prelude::*;

const SQUARES: &str = "prop is_nonnegative(x R):\n    x >= 0\nthm squares:\n    ? forall x R:\n        $is_nonnegative(x^2)\n    by def $is_nonnegative(x^2)\n";
const CALLER_CONSTRUCTION: &str = "prop is_nonnegative(x R):\n    x >= 0\nthm square_definition:\n    ? forall x R:\n        x = x\n    by def $is_nonnegative(x^2)\n    let square = x^2\n    square = x^2\n";
const GUARDED: &str = "prop is_nonzero(x R):\n    x != 0\nthm nonzero_copy:\n    ? forall x R:\n        x != 0\n        =>:\n            $is_nonzero(x)\n    by def $is_nonzero(x)\n    x != 0\n";

fn by_definition(statement: &mut ExecStmtResult) -> &mut ExecByDefStmtSuccess {
    match statement {
        ExecStmtResult::By(ExecByStmtResult::Def(ExecByDefStmtResult::Success(proof))) => proof,
        _ => panic!("actual successful explicit definition request"),
    }
}

fn theorem_steps(statement: &mut ExecStmtResult) -> &mut Vec<ExecStmtResult> {
    match &mut super::named_theorem_mut(statement).body {
        ExecDefThmBodyProof::Forall(proof) => &mut proof.proof_steps,
        ExecDefThmBodyProof::NonForall(proof) => &mut proof.proof_steps,
    }
}

fn goal_argument(proof: &mut ExecByDefStmtSuccess) -> &mut ObjWellDefinedProof {
    match &mut proof.goal_wd {
        VerifyFactWellDefinedResult::Success(FactWellDefinedProof::AtomicExceptEquality(wd)) => {
            &mut wd.as_detailed_mut().unwrap().well_defined_of_each_parameter[0]
        }
        _ => panic!("actual concrete predicate goal formation"),
    }
}

fn definition_requirements(
    proof: &mut ExecByDefStmtSuccess,
) -> &mut UserDefinedPropDefinitionProof {
    match &mut super::atomic_proof_mut(&mut proof.proof).searched_proof {
        AtomicExceptEqualityFactSearchedProof::ByDefinition(
            AtomicExceptEqualityFactSearchProofByDefinition::UserDefinedProp(proof),
        ) => proof,
        _ => panic!("actual selected concrete definition proof"),
    }
}

#[test]
fn by_definition_in_theorem_replays_direct_forall_and_atomic_bodies() {
    for source in [
        SQUARES,
        "prop is_one(x R):\n    x = 1\nthm one:\n    ? $is_one(1)\n    by def $is_one(1)\n",
    ] {
        let (mut result, compiler) = super::execute(source);
        let steps = theorem_steps(&mut result.statement_results[1]);
        assert_eq!(
            steps.len(),
            1,
            "the original body is a direct definition request"
        );
        assert!(matches!(
            super::atomic_proof_mut(&mut by_definition(&mut steps[0]).proof).searched_proof,
            AtomicExceptEqualityFactSearchedProof::ByDefinition(_)
        ));
        let output = super::compile_run(&result, &compiler, "named_definition")
            .expect("the named theorem consumes its original explicit definition proof");
        assert!(output.contains("Exists.intro"));
        assert!(!output.contains("sorry") && !output.contains("admit"));
    }
}

#[test]
fn by_definition_in_theorem_exports_only_the_caller_compound_formation() {
    let (mut result, compiler) = super::execute(CALLER_CONSTRUCTION);
    let proof = by_definition(&mut theorem_steps(&mut result.statement_results[1])[0]);
    assert!(matches!(
        (goal_argument(proof)).as_detailed_mut().unwrap(),
        DetailedObjWellDefinedProof::ByDef { .. }
    ));
    let output = super::compile_run(&result, &compiler, "definition_caller_wd")
        .expect("the following alias cites the completed caller's original square constructor");
    assert!(!output.contains("sorry") && !output.contains("admit"));
}

#[test]
fn by_definition_in_theorem_rejects_a_different_source_or_proof_subject() {
    for change in ["source", "proof"] {
        let (mut result, compiler) = super::execute(SQUARES);
        let theorem = super::named_theorem_mut(&mut result.statement_results[1]);
        let normal = if change == "source" {
            match &mut theorem.statement.prove_process[0] {
                Stmt::By(ByStmt::ByDefStmt(stmt)) => match &mut stmt.fact {
                    AtomicFact::NormalAtomicFact(normal) => normal,
                    _ => panic!("actual source predicate request"),
                },
                _ => panic!("actual source definition statement"),
            }
        } else {
            let step = match &mut theorem.body {
                ExecDefThmBodyProof::Forall(body) => &mut body.proof_steps[0],
                _ => panic!("actual forall body"),
            };
            match &mut super::atomic_proof_mut(&mut by_definition(step).proof).fact {
                AtomicFact::NormalAtomicFact(normal) => normal,
                _ => panic!("actual verified predicate request"),
            }
        };
        normal.body[0] = super::number_object("7");
        super::phase2_rejected(&result, &compiler, change, &["Theorem/ProofStepCapture"]);
    }
}

#[test]
fn by_definition_in_theorem_rejects_deleted_or_wrong_goal_formation() {
    for change in ["deleted", "wrong", "missing"] {
        let (mut result, compiler) = super::execute(CALLER_CONSTRUCTION);
        let proof = by_definition(&mut theorem_steps(&mut result.statement_results[1])[0]);
        match change {
            "deleted" => match &mut proof.goal_wd {
                VerifyFactWellDefinedResult::Success(
                    FactWellDefinedProof::AtomicExceptEquality(wd),
                ) => {
                    wd.as_detailed_mut()
                        .unwrap()
                        .well_defined_of_each_parameter
                        .clear();
                }
                _ => panic!("actual predicate goal WD"),
            },
            "wrong" => super::replace_wd_subject(goal_argument(proof), super::number_object("7")),
            "missing" => {
                let object = goal_argument(proof).obj().clone();
                *goal_argument(proof) =
                    crate::execute::execute_fact_stmt::ObjWellDefinedProof::Detailed(Box::new(
                        DetailedObjWellDefinedProof::ByKnown {
                            obj: object,
                            wd_id: WellDefinednessId::new(u64::MAX),
                        },
                    ));
            }
            _ => unreachable!(),
        }
        super::phase2_rejected(&result, &compiler, change, &["WD/", "WdId/"]);
    }
}

#[test]
fn by_definition_in_theorem_rejects_deleted_or_reordered_definition_requirements() {
    for change in ["deleted", "reordered", "wrong"] {
        let (mut result, compiler) = super::execute(SQUARES);
        let proof = by_definition(&mut theorem_steps(&mut result.statement_results[1])[0]);
        let requirements = definition_requirements(proof);
        assert_eq!(requirements.requirement_facts.len(), 2);
        match change {
            "deleted" => requirements.proof_of_requirement_facts.clear(),
            "reordered" => requirements.requirement_facts.swap(0, 1),
            "wrong" => match &mut requirements.requirement_facts[0] {
                Fact::AtomicFact(AtomicFact::InFact(member)) => {
                    member.element = super::number_object("7")
                }
                _ => panic!("actual definition domain requirement"),
            },
            _ => unreachable!(),
        }
        super::phase2_rejected(&result, &compiler, change, &["Prop/Fold"]);
    }
}

#[test]
fn by_definition_in_theorem_preserves_the_explicit_definition_route() {
    let (mut result, compiler) = super::execute(SQUARES);
    let proof = by_definition(&mut theorem_steps(&mut result.statement_results[1])[0]);
    let id = proof.stored.primary_fact_id();
    super::atomic_proof_mut(&mut proof.proof).searched_proof =
        AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(
            AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
                cite_fact_id: id,
                why_parameters_of_known_fact_are_equal_to_givens: Vec::new(),
            },
        );
    super::phase2_rejected(
        &result,
        &compiler,
        "replacement_search_route",
        &["ByDef/Route"],
    );
}

#[test]
fn by_definition_in_theorem_rejects_a_store_for_another_predicate_argument() {
    let (mut result, compiler) = super::execute(SQUARES);
    let proof = by_definition(&mut theorem_steps(&mut result.statement_results[1])[0]);
    match &mut proof.stored.store {
        StoreFactResult::AtomicFact(stored) => match &mut stored.fact {
            AtomicFact::NormalAtomicFact(normal) => normal.body[0] = super::number_object("7"),
            _ => panic!("actual predicate store"),
        },
        _ => panic!("actual atomic store"),
    }
    super::phase2_rejected(&result, &compiler, "wrong_store", &["Store/Subject"]);
}

#[test]
fn by_definition_in_theorem_cannot_use_its_own_later_wd_cache() {
    let (mut result, compiler) = super::execute(CALLER_CONSTRUCTION);
    super::compile_run(&result, &compiler, "definition_wd_order").unwrap();
    let steps = theorem_steps(&mut result.statement_results[1]);
    let (object, wd_id) = match (&super::let_definition(&steps[1]).value_well_defined)
        .as_detailed_success()
        .unwrap()
    {
        Some(DetailedObjWellDefinedProof::ByKnown { obj, wd_id }) => (obj.clone(), *wd_id),
        _ => panic!("the later alias cites the completed caller's cached constructor"),
    };
    *goal_argument(by_definition(&mut steps[0])) =
        crate::execute::execute_fact_stmt::ObjWellDefinedProof::Detailed(Box::new(
            DetailedObjWellDefinedProof::ByKnown { obj: object, wd_id },
        ));
    super::phase2_rejected(&result, &compiler, "later_caller_cache", &["WD/", "WdId/"]);
}

#[test]
fn by_definition_in_theorem_cannot_export_a_closed_definition_constructor() {
    let source = "have anchor R\nprop unchanged(x R):\n    anchor + 0 = anchor\nthm local_definition:\n    ? anchor = anchor\n    by def $unchanged(anchor)\n    let shifted = anchor + 0\n    shifted = anchor\n";
    let (mut result, compiler) = super::execute(source);
    super::compile_run(&result, &compiler, "closed_definition_constructor").unwrap();
    let (object, wd_id) = match &result.statement_results[1] {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
            ExecDefPropStmtResult::Success(proof),
        )) => {
            let object = match &proof.statement.iff_facts[0] {
                Fact::AtomicFact(AtomicFact::EqualFact(equal)) => equal.left.clone(),
                _ => panic!("actual defining clause's sum"),
            };
            let wd_id = proof
                .local_env
                .well_defined_objects
                .lookup(&object)
                .expect("the actual closed defining-clause store recorded this constructor");
            assert_eq!(
                proof
                    .local_env
                    .well_defined_objects
                    .wd_id_to_object
                    .get(&wd_id),
                Some(&object),
            );
            (object, wd_id)
        }
        _ => panic!("actual concrete definition's closed result"),
    };
    let steps = theorem_steps(&mut result.statement_results[2]);
    let proof = by_definition(&mut steps[0]);
    let requirements = definition_requirements(proof);
    assert_eq!(requirements.proof_of_requirement_facts.len(), 2);
    assert_eq!(
        super::equality_proof(&requirements.proof_of_requirement_facts[1])
            .well_defined_proof
            .detailed_ref()
            .left
            .obj()
            .ir(),
        object.ir(),
        "the actual definition proof uses the same sum with the outer source identity",
    );
    let alias = match &mut steps[1] {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(proof)),
        )) => proof,
        _ => panic!("actual alias after the closed definition proof"),
    };
    alias.value_well_defined = VerifyObjWellDefinedResult::Success(
        crate::execute::execute_fact_stmt::ObjWellDefinedProof::Detailed(Box::new(
            DetailedObjWellDefinedProof::ByKnown { obj: object, wd_id },
        )),
    );
    super::phase2_rejected(
        &result,
        &compiler,
        "closed_definition_wd",
        &["WD/", "WdId/"],
    );
}

#[test]
fn by_definition_in_theorem_cannot_cite_closed_or_future_fact_producers() {
    for change in ["closed", "future"] {
        let (mut result, compiler) = super::execute(GUARDED);
        super::compile_run(&result, &compiler, "definition_fact_order").unwrap();
        let closed = match &result.statement_results[0] {
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
                ExecDefPropStmtResult::Success(proof),
            )) => proof.defined_params.store_and_infer_results[0].primary_fact_id(),
            _ => panic!("actual predicate's closed binder membership"),
        };
        let steps = theorem_steps(&mut result.statement_results[1]);
        let future = super::fact_statement(&steps[1])
            .store_and_infer_result
            .primary_fact_id();
        let requirements = definition_requirements(by_definition(&mut steps[0]));
        let checked =
            &mut requirements.proof_of_requirement_facts[if change == "closed" { 0 } else { 1 }];
        match &mut super::atomic_proof_mut(checked).searched_proof {
            AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(proof) => {
                proof.cite_fact_id = if change == "closed" { closed } else { future };
            }
            _ => panic!("actual definition requirement cites the source premise"),
        }
        super::phase2_rejected(&result, &compiler, change, &["FactId/"]);
    }
}

#[test]
fn by_definition_in_theorem_keeps_a_false_definition_request_rejected() {
    let source = "prop is_nonzero(x R):\n    x != 0\nthm false_definition:\n    ? $is_nonzero(0)\n    by def $is_nonzero(0)\n";
    let command =
        parse_launch_command(&["-strict".to_string(), "-e".to_string(), source.to_string()])
            .unwrap();
    let mut runtime =
        Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
    let result = runtime.run_litex_code(source).unwrap();
    assert!(!result.success && result.session_error.is_none());
    assert!(!result.statement_results[0].is_failed());
    assert!(result.statement_results[1].is_failed());
    let compiler = super::LitexToLeanCompiler::new(runtime);
    let error = super::compile_run(&result, &compiler, "false_definition")
        .expect_err("a failed explicit definition cannot become a theorem");
    assert_eq!(error.route, "source_failed");
}
