use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof;
use crate::prelude::*;
pub(super) const SOURCES57:&[(&str,&str)]=&[
("multiply_all_operands","forall sc57a_m,sc57a_k,sc57a_n,sc57a_p,sc57a_h,sc57a_q N,sc57a_A1 matrix(C,sc57a_m,sc57a_k),sc57a_A2 matrix(C,sc57a_k,sc57a_n),sc57a_B1 matrix(C,sc57a_p,sc57a_h),sc57a_B2 matrix(C,sc57a_h,sc57a_q):\n    sc57a_A1=sc57a_B1\n    sc57a_A2=sc57a_B2\n    sc57a_m=sc57a_p\n    sc57a_k=sc57a_h\n    sc57a_n=sc57a_q\n    =>:\n        matrix_mul(sc57a_A1,sc57a_A2,sc57a_m,sc57a_k,sc57a_n)=matrix_mul(sc57a_B1,sc57a_B2,sc57a_p,sc57a_h,sc57a_q)\n"),
("forall_multiply","forall sc57b_A1 matrix(C,2,3),sc57b_A2 matrix(C,3,4),sc57b_P fn(sc57b_T1 matrix(C,2,3),sc57b_T2 matrix(C,3,4)) matrix(C,2,4):\n    forall sc57b_X matrix(C,2,3),sc57b_Y matrix(C,3,4):\n        matrix_mul(sc57b_X,sc57b_Y,2,3,4)=sc57b_P(sc57b_X,sc57b_Y)\n    =>:\n        matrix_mul(sc57b_A1,sc57b_A2,2,3,4)=sc57b_P(sc57b_A1,sc57b_A2)\n")];
fn operands57(object: &Obj) -> [&Obj; 5] {
    let Obj::MatrixOperator(MatrixOperator::Multiply(a)) = object else {
        panic!("original matrix multiplication")
    };
    [
        a.left.as_ref(),
        a.right.as_ref(),
        a.rows.as_ref(),
        a.inner.as_ref(),
        a.cols.as_ref(),
    ]
}
#[test]
fn matrix_multiply_original_five_changed_operands_audit() {
    let source = SOURCES57[0].1;
    let (run, compiler) = super::execute(source);
    let outer = super::forall_proof(&run.statement_results[0]);
    let equal = super::equality_proof(&outer.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByMatchingOneArgByOne(p) = &equal.searched_proof else {
        panic!("original direct route")
    };
    let a = operands57(&equal.fact.left);
    let b = operands57(&equal.fact.right);
    assert_eq!(p.corresponding_arg_equal_proofs.len(), 5);
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
            "ORIGINAL57 direct operand:{index} left:{} right:{} cite:{}",
            child.fact.left.ir(),
            child.fact.right.ir(),
            path.path[0].2.value()
        );
    }
    assert_eq!(
        compiler
            .compile_run(&run, "Matrix57OriginalDirect")
            .unwrap()
            .contains("_constructor"),
        true
    );
}
#[test]
fn matrix_multiply_original_forall_five_operand_matches_audit() {
    let source = SOURCES57[1].1;
    let (run, compiler) = super::execute(source);
    let outer = super::forall_proof(&run.statement_results[0]);
    let equal = super::equality_proof(&outer.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByKnownForallFact(p) = &equal.searched_proof else {
        panic!("original forall route")
    };
    let p = p.as_detailed().unwrap();
    let Fact::ForallFact(cited) = &outer.fact.dom_facts[0] else {
        panic!("original source forall")
    };
    assert_eq!(p.cite.fact_id, cited.fact_id);
    let param_ids: Vec<_> = cited
        .typed_parameters
        .groups
        .iter()
        .flat_map(|g| g.params.iter().map(|p| p.id))
        .collect();
    assert_eq!(param_ids.len(), 2);
    assert_eq!(p.arg_match_proofs.len(), 2);
    let DetailedForallConclusionArgMatchProof::ByStructure {
        pattern,
        goal_arg,
        child_matches,
    } = p.arg_match_proofs[0].as_detailed().unwrap()
    else {
        panic!("original matrix structure")
    };
    let a = operands57(pattern);
    let b = operands57(goal_arg);
    assert_eq!(child_matches.len(), 5);
    assert_eq!(p.forall_parameters_match_what_args.len(), 2);
    for i in 0..2 {
        assert_eq!(p.forall_parameters_match_what_args[i].ir(), b[i].ir());
    }
    for (index, child) in child_matches.iter().enumerate() {
        match child.as_detailed().unwrap() {
            DetailedForallConclusionArgMatchProof::BoundParam {
                param_id,
                pattern,
                goal_arg,
            } if index < 2 => {
                assert_eq!(*param_id, param_ids[index]);
                assert_eq!(pattern.ir(), a[index].ir());
                assert_eq!(goal_arg.ir(), b[index].ir());
                eprintln!(
                    "ORIGINAL57 forall operand:{index} bound:{} pattern:{} goal:{}",
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
                    "ORIGINAL57 forall operand:{index} literal:{} goal:{}",
                    pattern.ir(),
                    goal_arg.ir()
                );
            }
            _ => panic!("unexpected original match:{index}"),
        }
    }
    let requirements = p.instantiation_requirements.as_detailed().unwrap();
    assert_eq!(requirements.param_type_requirements.len(), 2);
    assert!(requirements.proof_of_dom_facts.is_empty());
    for (i, requirement) in requirements.param_type_requirements.iter().enumerate() {
        assert_eq!(requirement.param_id, param_ids[i]);
    }
    eprintln!(
        "ORIGINAL57 forall cite:{} parameter_types:{} guards:{}",
        p.cite.fact_id.value(),
        requirements.param_type_requirements.len(),
        requirements.proof_of_dom_facts.len()
    );
    assert_eq!(
        compiler
            .compile_run(&run, "Matrix57OriginalForall")
            .unwrap()
            .contains("_constructor"),
        true
    );
}

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    DetailedSearchProofByKnownForallFact, ForallConclusionArgMatchProof,
};
fn equal57(run: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    let outer = super::forall_proof_mut(&mut run.statement_results[0]);
    super::equality_proof_mut(&mut outer.proved_then_facts[0].verify_result)
}
fn direct_children57(run: &mut RunLitexCodeResult) -> &mut Vec<VerifyFactResult> {
    let EqualFactSearchedProof::ByMatchingOneArgByOne(p) = &mut equal57(run).searched_proof else {
        panic!()
    };
    &mut p.corresponding_arg_equal_proofs
}
fn application57(run: &mut RunLitexCodeResult) -> &mut DetailedSearchProofByKnownForallFact {
    let EqualFactSearchedProof::ByKnownForallFact(p) = &mut equal57(run).searched_proof else {
        panic!()
    };
    p.as_detailed_mut().unwrap()
}
fn matching_children57(run: &mut RunLitexCodeResult) -> &mut Vec<ForallConclusionArgMatchProof> {
    let DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } =
        application57(run).arg_match_proofs[0]
            .as_detailed_mut()
            .unwrap()
    else {
        panic!()
    };
    child_matches
}
fn reject57(run: &RunLitexCodeResult, compiler: &crate::compile_to_lean::LitexToLeanCompiler) {
    compiler
        .compile_run(run, "Matrix57ChangedEvidence")
        .expect_err("changed original certificate must reject");
}
#[test]
fn matrix_multiply_requires_all_five_original_equalities() {
    for change in ["missing_fifth", "empty", "extra"] {
        let (mut run, compiler) = super::execute(SOURCES57[0].1);
        match change {
            "missing_fifth" => {
                direct_children57(&mut run).pop();
            }
            "empty" => direct_children57(&mut run).clear(),
            _ => {
                let (mut other, _) = super::execute(SOURCES57[0].1);
                let extra = direct_children57(&mut other).pop().unwrap();
                direct_children57(&mut run).push(extra);
            }
        }
        assert_eq!(
            compiler
                .compile_run(&run, "Matrix57Arity")
                .unwrap_err()
                .route,
            "ArithmeticCongruence/Children"
        );
    }
}
#[test]
fn matrix_multiply_rejects_matrix_and_dimension_operand_reorder() {
    for (a, b) in [(0, 1), (2, 3), (3, 4)] {
        let (mut run, compiler) = super::execute(SOURCES57[0].1);
        direct_children57(&mut run).swap(a, b);
        assert_eq!(
            compiler
                .compile_run(&run, "Matrix57Order")
                .unwrap_err()
                .route,
            "ArithmeticCongruence/ChildSubject"
        );
    }
}
#[test]
fn matrix_multiply_requires_the_fifth_operand_subject() {
    let (mut run, compiler) = super::execute(SOURCES57[0].1);
    let (mut other, _) = super::execute(SOURCES57[0].1);
    let row = direct_children57(&mut other).remove(3);
    direct_children57(&mut run)[4] = row;
    assert_eq!(
        compiler
            .compile_run(&run, "Matrix57FourthSubject")
            .unwrap_err()
            .route,
        "ArithmeticCongruence/ChildSubject"
    );
}
#[test]
fn matrix_multiply_rejects_foreign_and_self_fifth_operand_citations() {
    for own in [false, true] {
        let (mut run, compiler) = super::execute(SOURCES57[0].1);
        let child = super::equality_proof_mut(&mut direct_children57(&mut run)[4]);
        let own_id = child.fact.fact_id;
        let EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
        ) = &mut child.searched_proof
        else {
            panic!()
        };
        path.path[0].2 = if own { own_id } else { FactId::new(u64::MAX) };
        reject57(&run, &compiler);
    }
}
#[test]
fn matrix_multiply_rejects_later_sibling_fifth_operand_citation() {
    let source = SOURCES57[0].1;
    let (mut run, compiler) =
        super::execute(&format!("{}{}", source, source.replace("sc57a_", "sc57z_")));
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(sibling)) = &run.statement_results[1]
    else {
        panic!()
    };
    let Fact::ForallFact(sibling) =
        crate::compile_to_lean::helper::source_subject(&sibling.verify_result).unwrap()
    else {
        panic!()
    };
    let id = sibling.dom_facts[4].fact_id();
    let child = super::equality_proof_mut(&mut direct_children57(&mut run)[4]);
    let EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
    ) = &mut child.searched_proof
    else {
        panic!()
    };
    path.path[0].2 = id;
    reject57(&run, &compiler);
}
#[test]
fn matrix_multiply_rejects_same_endpoints_from_later_then_fact() {
    let source = format!("{}        sc57a_n=sc57a_q\n", SOURCES57[0].1);
    let (mut run, compiler) = super::execute(&source);
    let outer = super::forall_proof(&run.statement_results[0]);
    assert_eq!(outer.proved_then_facts.len(), 2);
    let future = super::equality_proof(&outer.proved_then_facts[1].verify_result);
    let future_id = future.fact.fact_id;
    let endpoints = (future.fact.left.ir(), future.fact.right.ir());
    let child = super::equality_proof_mut(&mut direct_children57(&mut run)[4]);
    assert_eq!((child.fact.left.ir(), child.fact.right.ir()), endpoints);
    assert_ne!(child.fact.fact_id, future_id);
    let EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
    ) = &mut child.searched_proof
    else {
        panic!()
    };
    path.path[0].2 = future_id;
    reject57(&run, &compiler);
}
#[test]
fn matrix_multiply_forall_requires_five_captured_operand_matches() {
    for extra in [false, true] {
        let (mut run, compiler) = super::execute(SOURCES57[1].1);
        if extra {
            let (mut other, _) = super::execute(SOURCES57[1].1);
            let added = matching_children57(&mut other).pop().unwrap();
            matching_children57(&mut run).push(added);
        } else {
            matching_children57(&mut run).pop();
        }
        assert_eq!(
            compiler
                .compile_run(&run, "Matrix57MatchArity")
                .unwrap_err()
                .route,
            "CompoundKnown/StructureArity"
        );
    }
}
#[test]
fn matrix_multiply_forall_requires_original_fifth_captured_literal() {
    let (mut run, compiler) = super::execute(SOURCES57[1].1);
    let children = matching_children57(&mut run);
    let DetailedForallConclusionArgMatchProof::NonParamEqual { goal_arg, .. } =
        children[3].as_detailed().unwrap()
    else {
        panic!()
    };
    let wrong = goal_arg.clone();
    let DetailedForallConclusionArgMatchProof::NonParamEqual { goal_arg, .. } =
        children[4].as_detailed_mut().unwrap()
    else {
        panic!()
    };
    *goal_arg = wrong;
    reject57(&run, &compiler);
}
#[test]
fn matrix_multiply_forall_requires_both_original_binder_identities() {
    for index in [0, 1] {
        for foreign in [false, true] {
            let (mut run, compiler) = super::execute(SOURCES57[1].1);
            let DetailedForallConclusionArgMatchProof::BoundParam { param_id, .. } =
                matching_children57(&mut run)[1 - index]
                    .as_detailed()
                    .unwrap()
            else {
                panic!()
            };
            let other = *param_id;
            let DetailedForallConclusionArgMatchProof::BoundParam { param_id, .. } =
                matching_children57(&mut run)[index]
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
            reject57(&run, &compiler);
        }
    }
}
#[test]
fn matrix_multiply_forall_requires_both_type_and_source_identities() {
    for change in ["first_type", "second_type", "source", "goal_subject"] {
        let (mut run, compiler) = super::execute(SOURCES57[1].1);
        match change {
            "first_type" => {
                application57(&mut run)
                    .instantiation_requirements
                    .as_detailed_mut()
                    .unwrap()
                    .param_type_requirements[0]
                    .param_id = IdentifierId::new(u64::MAX)
            }
            "second_type" => {
                application57(&mut run)
                    .instantiation_requirements
                    .as_detailed_mut()
                    .unwrap()
                    .param_type_requirements[1]
                    .param_id = IdentifierId::new(u64::MAX)
            }
            "source" => application57(&mut run).cite.fact_id = FactId::new(u64::MAX),
            _ => {
                let DetailedForallConclusionArgMatchProof::ByStructure {
                    pattern, goal_arg, ..
                } = application57(&mut run).arg_match_proofs[0]
                    .as_detailed_mut()
                    .unwrap()
                else {
                    panic!()
                };
                *goal_arg = pattern.clone();
            }
        }
        reject57(&run, &compiler);
    }
}
#[test]
fn matrix_multiply_forall_preserves_original_argument_order() {
    let (mut run, compiler) = super::execute(SOURCES57[1].1);
    application57(&mut run)
        .forall_parameters_match_what_args
        .swap(0, 1);
    reject57(&run, &compiler);
}
#[test]
fn matrix_multiply_requires_parent_and_fifth_child_original_formations() {
    for child in [false, true] {
        let (mut run, compiler) = super::execute(SOURCES57[0].1);
        let equal = if child {
            super::equality_proof_mut(&mut direct_children57(&mut run)[4])
        } else {
            equal57(&mut run)
        };
        let wd = equal.well_defined_proof.as_detailed_mut().unwrap();
        std::mem::swap(&mut wd.left, &mut wd.right);
        reject57(&run, &compiler);
    }
}
#[test]
fn matrix_multiply_preserves_arithmetic_strategy_producer_eligibility() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_builtin_strategy_result::ArithmeticCongruenceStrategySingleStep;
    let (mut run, compiler) = super::execute(SOURCES57[0].1);
    let children = std::mem::take(direct_children57(&mut run));
    let requirements = children
        .iter()
        .map(|p| crate::compile_to_lean::helper::source_subject(p).unwrap())
        .collect();
    equal57(&mut run).searched_proof = EqualFactSearchedProof::ByBuiltinStrategy(
        EqualitySearchProofByBuiltinStrategy::ArithmeticCongruence(
            ArithmeticCongruenceStrategySingleStep {
                requirement_facts: requirements,
                proof_of_requirement_facts: children,
            },
        ),
    );
    assert_eq!(
        compiler
            .compile_run(&run, "Matrix57WrongStrategyTag")
            .unwrap_err()
            .route,
        "ArithmeticCongruence/Constructor"
    );
}

#[test]
fn matrix_multiply_forall_preserves_all_three_distinct_dimension_matches() {
    for (a, b) in [(2, 3), (3, 4), (2, 4)] {
        let (mut run, compiler) = super::execute(SOURCES57[1].1);
        matching_children57(&mut run).swap(a, b);
        reject57(&run, &compiler);
    }
}
