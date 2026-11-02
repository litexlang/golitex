use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof;
use crate::prelude::*;
pub(super) const SOURCES55:&[(&str,&str)]=&[
("add_all_operands","forall sc55a_m,sc55a_n,sc55a_p,sc55a_q N,sc55a_A1,sc55a_A2 matrix(C,sc55a_m,sc55a_n),sc55a_B1,sc55a_B2 matrix(C,sc55a_p,sc55a_q):\n    sc55a_A1=sc55a_B1\n    sc55a_A2=sc55a_B2\n    sc55a_m=sc55a_p\n    sc55a_n=sc55a_q\n    =>:\n        matrix_add(sc55a_A1,sc55a_A2,sc55a_m,sc55a_n)=matrix_add(sc55a_B1,sc55a_B2,sc55a_p,sc55a_q)\n"),
("forall_add","forall sc55b_A1,sc55b_A2 matrix(C,2,3),sc55b_P fn(sc55b_T1,sc55b_T2 matrix(C,2,3)) matrix(C,2,3):\n    forall sc55b_X,sc55b_Y matrix(C,2,3):\n        matrix_add(sc55b_X,sc55b_Y,2,3)=sc55b_P(sc55b_X,sc55b_Y)\n    =>:\n        matrix_add(sc55b_A1,sc55b_A2,2,3)=sc55b_P(sc55b_A1,sc55b_A2)\n")];
fn addition55(object: &Obj) -> [&Obj; 4] {
    let Obj::MatrixOperator(MatrixOperator::Add(a)) = object else {
        panic!("original matrix addition")
    };
    [
        a.left.as_ref(),
        a.right.as_ref(),
        a.rows.as_ref(),
        a.cols.as_ref(),
    ]
}
#[test]
fn matrix_entrywise_original_four_changed_operands_audit() {
    let source = SOURCES55[0].1;
    let (run, compiler) = super::execute(source);
    let outer = super::forall_proof(&run.statement_results[0]);
    let equal = super::equality_proof(&outer.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByMatchingOneArgByOne(p) = &equal.searched_proof else {
        panic!("original direct route")
    };
    let a = addition55(&equal.fact.left);
    let b = addition55(&equal.fact.right);
    assert_eq!(p.corresponding_arg_equal_proofs.len(), 4);
    for (index, child) in p.corresponding_arg_equal_proofs.iter().enumerate() {
        let child = super::equality_proof(child);
        assert_eq!(child.fact.left.ir(), a[index].ir());
        assert_eq!(child.fact.right.ir(), b[index].ir());
        let EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
        ) = &child.searched_proof
        else {
            panic!("original ordered given equality")
        };
        assert_eq!(path.path.len(), 1);
        assert_eq!(path.path[0].2, outer.fact.dom_facts[index].fact_id());
        eprintln!(
            "ORIGINAL55 direct operand:{index} left:{} right:{} cite:{}",
            child.fact.left.ir(),
            child.fact.right.ir(),
            path.path[0].2.value()
        );
    }
    assert_eq!(
        compiler
            .compile_run(&run, "Matrix55OriginalDirect")
            .unwrap()
            .contains("_constructor"),
        true
    );
}

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    DetailedSearchProofByKnownForallFact, ForallConclusionArgMatchProof,
};
fn equal55(run: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    let outer = super::forall_proof_mut(&mut run.statement_results[0]);
    super::equality_proof_mut(&mut outer.proved_then_facts[0].verify_result)
}
fn direct_children55(run: &mut RunLitexCodeResult) -> &mut Vec<VerifyFactResult> {
    let EqualFactSearchedProof::ByMatchingOneArgByOne(p) = &mut equal55(run).searched_proof else {
        panic!()
    };
    &mut p.corresponding_arg_equal_proofs
}
fn application55(run: &mut RunLitexCodeResult) -> &mut DetailedSearchProofByKnownForallFact {
    let EqualFactSearchedProof::ByKnownForallFact(p) = &mut equal55(run).searched_proof else {
        panic!()
    };
    p.as_detailed_mut().unwrap()
}
fn matching_children55(run: &mut RunLitexCodeResult) -> &mut Vec<ForallConclusionArgMatchProof> {
    let DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } =
        application55(run).arg_match_proofs[0]
            .as_detailed_mut()
            .unwrap()
    else {
        panic!()
    };
    child_matches
}
fn reject55(run: &RunLitexCodeResult, compiler: &crate::compile_to_lean::LitexToLeanCompiler) {
    compiler
        .compile_run(run, "Matrix55ChangedEvidence")
        .expect_err("changed original certificate must reject");
}
#[test]
fn matrix_entrywise_requires_all_four_original_equalities() {
    for change in ["missing_fourth", "empty", "extra"] {
        let (mut run, compiler) = super::execute(SOURCES55[0].1);
        match change {
            "missing_fourth" => {
                direct_children55(&mut run).pop();
            }
            "empty" => direct_children55(&mut run).clear(),
            _ => {
                let (mut other, _) = super::execute(SOURCES55[0].1);
                let extra = direct_children55(&mut other).pop().unwrap();
                direct_children55(&mut run).push(extra);
            }
        }
        assert_eq!(
            compiler
                .compile_run(&run, "Matrix55Arity")
                .unwrap_err()
                .route,
            "ArithmeticCongruence/Children"
        );
    }
}
#[test]
fn matrix_entrywise_rejects_matrix_and_dimension_operand_reorder() {
    for (a, b) in [(0, 1), (2, 3)] {
        let (mut run, compiler) = super::execute(SOURCES55[0].1);
        direct_children55(&mut run).swap(a, b);
        assert_eq!(
            compiler
                .compile_run(&run, "Matrix55Order")
                .unwrap_err()
                .route,
            "ArithmeticCongruence/ChildSubject"
        );
    }
}
#[test]
fn matrix_entrywise_requires_the_fourth_operand_subject() {
    let (mut run, compiler) = super::execute(SOURCES55[0].1);
    let (mut other, _) = super::execute(SOURCES55[0].1);
    let row = direct_children55(&mut other).remove(2);
    direct_children55(&mut run)[3] = row;
    assert_eq!(
        compiler
            .compile_run(&run, "Matrix55FourthSubject")
            .unwrap_err()
            .route,
        "ArithmeticCongruence/ChildSubject"
    );
}
#[test]
fn matrix_entrywise_rejects_foreign_and_self_fourth_operand_citations() {
    for own in [false, true] {
        let (mut run, compiler) = super::execute(SOURCES55[0].1);
        let child = super::equality_proof_mut(&mut direct_children55(&mut run)[3]);
        let own_id = child.fact.fact_id;
        let EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
        ) = &mut child.searched_proof
        else {
            panic!()
        };
        path.path[0].2 = if own { own_id } else { FactId::new(u64::MAX) };
        reject55(&run, &compiler);
    }
}
#[test]
fn matrix_entrywise_rejects_later_sibling_fourth_operand_citation() {
    let source = SOURCES55[0].1;
    let (mut run, compiler) =
        super::execute(&format!("{}{}", source, source.replace("sc55a_", "sc55z_")));
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(sibling)) = &run.statement_results[1]
    else {
        panic!()
    };
    let Fact::ForallFact(sibling) =
        crate::compile_to_lean::helper::source_subject(&sibling.verify_result).unwrap()
    else {
        panic!()
    };
    let id = sibling.dom_facts[3].fact_id();
    let child = super::equality_proof_mut(&mut direct_children55(&mut run)[3]);
    let EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
    ) = &mut child.searched_proof
    else {
        panic!()
    };
    path.path[0].2 = id;
    reject55(&run, &compiler);
}
#[test]
fn matrix_entrywise_rejects_same_endpoints_from_later_then_fact() {
    let source = format!("{}        sc55a_n=sc55a_q\n", SOURCES55[0].1);
    let (mut run, compiler) = super::execute(&source);
    let outer = super::forall_proof(&run.statement_results[0]);
    assert_eq!(outer.proved_then_facts.len(), 2);
    let future = super::equality_proof(&outer.proved_then_facts[1].verify_result);
    let future_id = future.fact.fact_id;
    let endpoints = (future.fact.left.ir(), future.fact.right.ir());
    let child = super::equality_proof_mut(&mut direct_children55(&mut run)[3]);
    assert_eq!((child.fact.left.ir(), child.fact.right.ir()), endpoints);
    assert_ne!(child.fact.fact_id, future_id);
    let EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
    ) = &mut child.searched_proof
    else {
        panic!()
    };
    path.path[0].2 = future_id;
    reject55(&run, &compiler);
}
#[test]
fn matrix_entrywise_forall_requires_four_captured_operand_matches() {
    for extra in [false, true] {
        let (mut run, compiler) = super::execute(SOURCES55[1].1);
        if extra {
            let (mut other, _) = super::execute(SOURCES55[1].1);
            let added = matching_children55(&mut other).pop().unwrap();
            matching_children55(&mut run).push(added);
        } else {
            matching_children55(&mut run).pop();
        }
        assert_eq!(
            compiler
                .compile_run(&run, "Matrix55MatchArity")
                .unwrap_err()
                .route,
            "CompoundKnown/StructureArity"
        );
    }
}
#[test]
fn matrix_entrywise_forall_requires_original_fourth_captured_literal() {
    let (mut run, compiler) = super::execute(SOURCES55[1].1);
    let children = matching_children55(&mut run);
    let DetailedForallConclusionArgMatchProof::NonParamEqual { goal_arg, .. } =
        children[2].as_detailed().unwrap()
    else {
        panic!()
    };
    let wrong = goal_arg.clone();
    let DetailedForallConclusionArgMatchProof::NonParamEqual { goal_arg, .. } =
        children[3].as_detailed_mut().unwrap()
    else {
        panic!()
    };
    *goal_arg = wrong;
    reject55(&run, &compiler);
}
#[test]
fn matrix_entrywise_forall_requires_both_original_binder_identities() {
    for index in [0, 1] {
        for foreign in [false, true] {
            let (mut run, compiler) = super::execute(SOURCES55[1].1);
            let DetailedForallConclusionArgMatchProof::BoundParam { param_id, .. } =
                matching_children55(&mut run)[1 - index]
                    .as_detailed()
                    .unwrap()
            else {
                panic!()
            };
            let other = *param_id;
            let DetailedForallConclusionArgMatchProof::BoundParam { param_id, .. } =
                matching_children55(&mut run)[index]
                    .as_detailed_mut()
                    .unwrap()
            else {
                panic!()
            };
            *param_id = if foreign {
                IdentifierId::new(u64::MAX)
            } else {
                other
            };
            reject55(&run, &compiler);
        }
    }
}
#[test]
fn matrix_entrywise_forall_requires_both_type_and_source_identities() {
    for change in ["first_type", "second_type", "source", "goal_subject"] {
        let (mut run, compiler) = super::execute(SOURCES55[1].1);
        match change {
            "first_type" => {
                application55(&mut run)
                    .instantiation_requirements
                    .as_detailed_mut()
                    .unwrap()
                    .param_type_requirements[0]
                    .param_id = IdentifierId::new(u64::MAX)
            }
            "second_type" => {
                application55(&mut run)
                    .instantiation_requirements
                    .as_detailed_mut()
                    .unwrap()
                    .param_type_requirements[1]
                    .param_id = IdentifierId::new(u64::MAX)
            }
            "source" => application55(&mut run).cite.fact_id = FactId::new(u64::MAX),
            _ => {
                let DetailedForallConclusionArgMatchProof::ByStructure {
                    pattern, goal_arg, ..
                } = application55(&mut run).arg_match_proofs[0]
                    .as_detailed_mut()
                    .unwrap()
                else {
                    panic!()
                };
                *goal_arg = pattern.clone();
            }
        }
        reject55(&run, &compiler);
    }
}
#[test]
fn matrix_entrywise_forall_preserves_original_argument_order() {
    let (mut run, compiler) = super::execute(SOURCES55[1].1);
    application55(&mut run)
        .forall_parameters_match_what_args
        .swap(0, 1);
    reject55(&run, &compiler);
}
#[test]
fn matrix_entrywise_requires_parent_and_fourth_child_original_formations() {
    for child in [false, true] {
        let (mut run, compiler) = super::execute(SOURCES55[0].1);
        let equal = if child {
            super::equality_proof_mut(&mut direct_children55(&mut run)[3])
        } else {
            equal55(&mut run)
        };
        let wd = equal.well_defined_proof.as_detailed_mut().unwrap();
        std::mem::swap(&mut wd.left, &mut wd.right);
        reject55(&run, &compiler);
    }
}
#[test]
fn matrix_entrywise_preserves_arithmetic_strategy_producer_eligibility() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_builtin_strategy_result::ArithmeticCongruenceStrategySingleStep;
    let (mut run, compiler) = super::execute(SOURCES55[0].1);
    let children = std::mem::take(direct_children55(&mut run));
    let requirements = children
        .iter()
        .map(|p| crate::compile_to_lean::helper::source_subject(p).unwrap())
        .collect();
    equal55(&mut run).searched_proof = EqualFactSearchedProof::ByBuiltinStrategy(
        EqualitySearchProofByBuiltinStrategy::ArithmeticCongruence(
            ArithmeticCongruenceStrategySingleStep {
                requirement_facts: requirements,
                proof_of_requirement_facts: children,
            },
        ),
    );
    assert_eq!(
        compiler
            .compile_run(&run, "Matrix55WrongStrategyTag")
            .unwrap_err()
            .route,
        "ArithmeticCongruence/Constructor"
    );
}
#[test]
fn matrix_entrywise_original_forall_four_operand_matches_audit() {
    let source = SOURCES55[1].1;
    let (run, compiler) = super::execute(source);
    let outer = super::forall_proof(&run.statement_results[0]);
    let equal = super::equality_proof(&outer.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByKnownForallFact(p) = &equal.searched_proof else {
        panic!("original forall route")
    };
    let p = p.as_detailed().unwrap();
    assert!(outer
        .fact
        .dom_facts
        .iter()
        .any(|f| f.fact_id() == p.cite.fact_id));
    assert_eq!(p.arg_match_proofs.len(), 2);
    let DetailedForallConclusionArgMatchProof::ByStructure {
        pattern,
        goal_arg,
        child_matches,
    } = p.arg_match_proofs[0].as_detailed().unwrap()
    else {
        panic!("original matrix structure")
    };
    let a = addition55(pattern);
    let b = addition55(goal_arg);
    assert_eq!(child_matches.len(), 4);
    for (index, child) in child_matches.iter().enumerate() {
        match child.as_detailed().unwrap() {
            DetailedForallConclusionArgMatchProof::BoundParam {
                param_id,
                pattern,
                goal_arg,
            } if index < 2 => {
                assert_eq!(pattern.ir(), a[index].ir());
                assert_eq!(goal_arg.ir(), b[index].ir());
                eprintln!(
                    "ORIGINAL55 forall operand:{index} bound:{} pattern:{} goal:{}",
                    param_id.value(),
                    pattern.ir(),
                    goal_arg.ir()
                );
            }
            DetailedForallConclusionArgMatchProof::NonParamEqual {
                pattern,
                pattern_after_subst,
                goal_arg,
                equal,
            } if index >= 2 => {
                assert_eq!(pattern.ir(), a[index].ir());
                assert_eq!(pattern_after_subst.ir(), a[index].ir());
                assert_eq!(goal_arg.ir(), b[index].ir());
                assert_eq!(equal.equal_fact.left.ir(), a[index].ir());
                assert_eq!(equal.equal_fact.right.ir(), b[index].ir());
                eprintln!(
                    "ORIGINAL55 forall operand:{index} literal:{} goal:{}",
                    pattern.ir(),
                    goal_arg.ir()
                );
            }
            _ => panic!("unexpected original match:{index}"),
        }
    }
    let requirements = p.instantiation_requirements.as_detailed().unwrap();
    eprintln!(
        "ORIGINAL55 forall cite:{} parameter_types:{} guards:{}",
        p.cite.fact_id.value(),
        requirements.param_type_requirements.len(),
        requirements.proof_of_dom_facts.len()
    );
    assert_eq!(
        compiler
            .compile_run(&run, "Matrix55OriginalForall")
            .unwrap()
            .contains("_constructor"),
        true
    );
}
