use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof;
use crate::prelude::*;
pub(super) const SOURCES56:&[(&str,&str)]=&[
("sub_all_operands","forall sc56a_m,sc56a_n,sc56a_p,sc56a_q N,sc56a_A1,sc56a_A2 matrix(C,sc56a_m,sc56a_n),sc56a_B1,sc56a_B2 matrix(C,sc56a_p,sc56a_q):\n    sc56a_A1=sc56a_B1\n    sc56a_A2=sc56a_B2\n    sc56a_m=sc56a_p\n    sc56a_n=sc56a_q\n    =>:\n        matrix_sub(sc56a_A1,sc56a_A2,sc56a_m,sc56a_n)=matrix_sub(sc56a_B1,sc56a_B2,sc56a_p,sc56a_q)\n"),
("scale_all_operands","forall sc56b_m,sc56b_n,sc56b_p,sc56b_q N,sc56b_c,sc56b_d C,sc56b_A matrix(C,sc56b_m,sc56b_n),sc56b_B matrix(C,sc56b_p,sc56b_q):\n    sc56b_c=sc56b_d\n    sc56b_A=sc56b_B\n    sc56b_m=sc56b_p\n    sc56b_n=sc56b_q\n    =>:\n        matrix_scale(sc56b_c,sc56b_A,sc56b_m,sc56b_n)=matrix_scale(sc56b_d,sc56b_B,sc56b_p,sc56b_q)\n"),
("forall_sub","forall sc56c_A1,sc56c_A2 matrix(C,2,3),sc56c_P fn(sc56c_T1,sc56c_T2 matrix(C,2,3)) matrix(C,2,3):\n    forall sc56c_X,sc56c_Y matrix(C,2,3):\n        matrix_sub(sc56c_X,sc56c_Y,2,3)=sc56c_P(sc56c_X,sc56c_Y)\n    =>:\n        matrix_sub(sc56c_A1,sc56c_A2,2,3)=sc56c_P(sc56c_A1,sc56c_A2)\n"),
("forall_scale","forall sc56d_c C,sc56d_A matrix(C,2,3),sc56d_P fn(sc56d_t C,sc56d_T matrix(C,2,3)) matrix(C,2,3):\n    forall sc56d_s C,sc56d_X matrix(C,2,3):\n        matrix_scale(sc56d_s,sc56d_X,2,3)=sc56d_P(sc56d_s,sc56d_X)\n    =>:\n        matrix_scale(sc56d_c,sc56d_A,2,3)=sc56d_P(sc56d_c,sc56d_A)\n")];
fn operands56(object: &Obj) -> [&Obj; 4] {
    match object {
        Obj::MatrixOperator(MatrixOperator::Subtract(a)) => [
            a.left.as_ref(),
            a.right.as_ref(),
            a.rows.as_ref(),
            a.cols.as_ref(),
        ],
        Obj::MatrixOperator(MatrixOperator::Scale(a)) => [
            a.scalar.as_ref(),
            a.matrix.as_ref(),
            a.rows.as_ref(),
            a.cols.as_ref(),
        ],
        _ => panic!("original subtract/scale"),
    }
}
#[test]
fn matrix_linear_original_four_changed_operands_audit() {
    for (_, source) in &SOURCES56[..2] {
        let (run, compiler) = super::execute(source);
        let outer = super::forall_proof(&run.statement_results[0]);
        let equal = super::equality_proof(&outer.proved_then_facts[0].verify_result);
        let EqualFactSearchedProof::ByMatchingOneArgByOne(p) = &equal.searched_proof else {
            panic!("original direct route")
        };
        let a = operands56(&equal.fact.left);
        let b = operands56(&equal.fact.right);
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
                "ORIGINAL56 direct operand:{index} left:{} right:{} cite:{}",
                child.fact.left.ir(),
                child.fact.right.ir(),
                path.path[0].2.value()
            );
        }
        assert_eq!(
            compiler
                .compile_run(&run, "Matrix56OriginalDirect")
                .unwrap()
                .contains("_constructor"),
            true
        );
    }
}
#[test]
fn matrix_linear_original_forall_four_operand_matches_audit() {
    for (_, source) in &SOURCES56[2..] {
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
        let a = operands56(pattern);
        let b = operands56(goal_arg);
        assert_eq!(child_matches.len(), 4);
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
                        "ORIGINAL56 forall operand:{index} bound:{} pattern:{} goal:{}",
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
                        "ORIGINAL56 forall operand:{index} literal:{} goal:{}",
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
            "ORIGINAL56 forall cite:{} parameter_types:{} guards:{}",
            p.cite.fact_id.value(),
            requirements.param_type_requirements.len(),
            requirements.proof_of_dom_facts.len()
        );
        assert_eq!(
            compiler
                .compile_run(&run, "Matrix56OriginalForall")
                .unwrap()
                .contains("_constructor"),
            true
        );
    }
}

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    DetailedSearchProofByKnownForallFact, ForallConclusionArgMatchProof,
};
fn equal56(run: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    let outer = super::forall_proof_mut(&mut run.statement_results[0]);
    super::equality_proof_mut(&mut outer.proved_then_facts[0].verify_result)
}
fn direct_children56(run: &mut RunLitexCodeResult) -> &mut Vec<VerifyFactResult> {
    let EqualFactSearchedProof::ByMatchingOneArgByOne(p) = &mut equal56(run).searched_proof else {
        panic!()
    };
    &mut p.corresponding_arg_equal_proofs
}
fn application56(run: &mut RunLitexCodeResult) -> &mut DetailedSearchProofByKnownForallFact {
    let EqualFactSearchedProof::ByKnownForallFact(p) = &mut equal56(run).searched_proof else {
        panic!()
    };
    p.as_detailed_mut().unwrap()
}
fn matching_children56(run: &mut RunLitexCodeResult) -> &mut Vec<ForallConclusionArgMatchProof> {
    let DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } =
        application56(run).arg_match_proofs[0]
            .as_detailed_mut()
            .unwrap()
    else {
        panic!()
    };
    child_matches
}
fn reject56(run: &RunLitexCodeResult, compiler: &crate::compile_to_lean::LitexToLeanCompiler) {
    compiler
        .compile_run(run, "Matrix56ChangedEvidence")
        .expect_err("changed original certificate must reject");
}
#[test]
fn matrix_linear_requires_all_four_original_equalities() {
    for (_, source) in &SOURCES56[..2] {
        for change in ["missing_fourth", "empty", "extra"] {
            let (mut run, compiler) = super::execute(source);
            match change {
                "missing_fourth" => {
                    direct_children56(&mut run).pop();
                }
                "empty" => direct_children56(&mut run).clear(),
                _ => {
                    let (mut other, _) = super::execute(source);
                    let extra = direct_children56(&mut other).pop().unwrap();
                    direct_children56(&mut run).push(extra);
                }
            }
            assert_eq!(
                compiler
                    .compile_run(&run, "Matrix56Arity")
                    .unwrap_err()
                    .route,
                "ArithmeticCongruence/Children"
            );
        }
    }
}
#[test]
fn matrix_linear_rejects_matrix_and_dimension_operand_reorder() {
    for (_, source) in &SOURCES56[..2] {
        for (a, b) in [(0, 1), (2, 3)] {
            let (mut run, compiler) = super::execute(source);
            direct_children56(&mut run).swap(a, b);
            assert_eq!(
                compiler
                    .compile_run(&run, "Matrix56Order")
                    .unwrap_err()
                    .route,
                "ArithmeticCongruence/ChildSubject"
            );
        }
    }
}
#[test]
fn matrix_linear_requires_the_fourth_operand_subject() {
    for (_, source) in &SOURCES56[..2] {
        let (mut run, compiler) = super::execute(source);
        let (mut other, _) = super::execute(source);
        let row = direct_children56(&mut other).remove(2);
        direct_children56(&mut run)[3] = row;
        assert_eq!(
            compiler
                .compile_run(&run, "Matrix56FourthSubject")
                .unwrap_err()
                .route,
            "ArithmeticCongruence/ChildSubject"
        );
    }
}
#[test]
fn matrix_linear_rejects_foreign_and_self_fourth_operand_citations() {
    for (_, source) in &SOURCES56[..2] {
        for own in [false, true] {
            let (mut run, compiler) = super::execute(source);
            let child = super::equality_proof_mut(&mut direct_children56(&mut run)[3]);
            let own_id = child.fact.fact_id;
            let EqualFactSearchedProof::ByEquivalenceClass(
                EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
            ) = &mut child.searched_proof
            else {
                panic!()
            };
            path.path[0].2 = if own { own_id } else { FactId::new(u64::MAX) };
            reject56(&run, &compiler);
        }
    }
}
#[test]
fn matrix_linear_rejects_later_sibling_fourth_operand_citation() {
    for (_, source) in &SOURCES56[..2] {
        let source = source;
        let (mut run, compiler) = super::execute(&format!(
            "{}{}",
            source,
            source
                .replace("sc56a_", "sc56z_")
                .replace("sc56b_", "sc56w_")
        ));
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
        let child = super::equality_proof_mut(&mut direct_children56(&mut run)[3]);
        let EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
        ) = &mut child.searched_proof
        else {
            panic!()
        };
        path.path[0].2 = id;
        reject56(&run, &compiler);
    }
}
#[test]
fn matrix_linear_rejects_same_endpoints_from_later_then_fact() {
    for (_, source) in &SOURCES56[..2] {
        let source = format!(
            "{}        {}\n",
            source,
            if source.contains("sc56a_") {
                "sc56a_n=sc56a_q"
            } else {
                "sc56b_n=sc56b_q"
            }
        );
        let (mut run, compiler) = super::execute(&source);
        let outer = super::forall_proof(&run.statement_results[0]);
        assert_eq!(outer.proved_then_facts.len(), 2);
        let future = super::equality_proof(&outer.proved_then_facts[1].verify_result);
        let future_id = future.fact.fact_id;
        let endpoints = (future.fact.left.ir(), future.fact.right.ir());
        let child = super::equality_proof_mut(&mut direct_children56(&mut run)[3]);
        assert_eq!((child.fact.left.ir(), child.fact.right.ir()), endpoints);
        assert_ne!(child.fact.fact_id, future_id);
        let EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
        ) = &mut child.searched_proof
        else {
            panic!()
        };
        path.path[0].2 = future_id;
        reject56(&run, &compiler);
    }
}
#[test]
fn matrix_linear_forall_requires_four_captured_operand_matches() {
    for (_, source) in &SOURCES56[2..] {
        for extra in [false, true] {
            let (mut run, compiler) = super::execute(source);
            if extra {
                let (mut other, _) = super::execute(source);
                let added = matching_children56(&mut other).pop().unwrap();
                matching_children56(&mut run).push(added);
            } else {
                matching_children56(&mut run).pop();
            }
            assert_eq!(
                compiler
                    .compile_run(&run, "Matrix56MatchArity")
                    .unwrap_err()
                    .route,
                "CompoundKnown/StructureArity"
            );
        }
    }
}
#[test]
fn matrix_linear_forall_requires_original_fourth_captured_literal() {
    for (_, source) in &SOURCES56[2..] {
        let (mut run, compiler) = super::execute(source);
        let children = matching_children56(&mut run);
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
        reject56(&run, &compiler);
    }
}
#[test]
fn matrix_linear_forall_requires_both_original_binder_identities() {
    for (_, source) in &SOURCES56[2..] {
        for index in [0, 1] {
            for foreign in [false, true] {
                let (mut run, compiler) = super::execute(source);
                let DetailedForallConclusionArgMatchProof::BoundParam { param_id, .. } =
                    matching_children56(&mut run)[1 - index]
                        .as_detailed()
                        .unwrap()
                else {
                    panic!()
                };
                let other = *param_id;
                let DetailedForallConclusionArgMatchProof::BoundParam { param_id, .. } =
                    matching_children56(&mut run)[index]
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
                reject56(&run, &compiler);
            }
        }
    }
}
#[test]
fn matrix_linear_forall_requires_both_type_and_source_identities() {
    for (_, source) in &SOURCES56[2..] {
        for change in ["first_type", "second_type", "source", "goal_subject"] {
            let (mut run, compiler) = super::execute(source);
            match change {
                "first_type" => {
                    application56(&mut run)
                        .instantiation_requirements
                        .as_detailed_mut()
                        .unwrap()
                        .param_type_requirements[0]
                        .param_id = IdentifierId::new(u64::MAX)
                }
                "second_type" => {
                    application56(&mut run)
                        .instantiation_requirements
                        .as_detailed_mut()
                        .unwrap()
                        .param_type_requirements[1]
                        .param_id = IdentifierId::new(u64::MAX)
                }
                "source" => application56(&mut run).cite.fact_id = FactId::new(u64::MAX),
                _ => {
                    let DetailedForallConclusionArgMatchProof::ByStructure {
                        pattern,
                        goal_arg,
                        ..
                    } = application56(&mut run).arg_match_proofs[0]
                        .as_detailed_mut()
                        .unwrap()
                    else {
                        panic!()
                    };
                    *goal_arg = pattern.clone();
                }
            }
            reject56(&run, &compiler);
        }
    }
}
#[test]
fn matrix_linear_forall_preserves_original_argument_order() {
    for (_, source) in &SOURCES56[2..] {
        let (mut run, compiler) = super::execute(source);
        application56(&mut run)
            .forall_parameters_match_what_args
            .swap(0, 1);
        reject56(&run, &compiler);
    }
}
#[test]
fn matrix_linear_requires_parent_and_fourth_child_original_formations() {
    for (_, source) in &SOURCES56[..2] {
        for child in [false, true] {
            let (mut run, compiler) = super::execute(source);
            let equal = if child {
                super::equality_proof_mut(&mut direct_children56(&mut run)[3])
            } else {
                equal56(&mut run)
            };
            let wd = equal.well_defined_proof.as_detailed_mut().unwrap();
            std::mem::swap(&mut wd.left, &mut wd.right);
            reject56(&run, &compiler);
        }
    }
}
#[test]
fn matrix_linear_preserves_arithmetic_strategy_producer_eligibility() {
    for (_, source) in &SOURCES56[..2] {
        use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_builtin_strategy_result::ArithmeticCongruenceStrategySingleStep;
        let (mut run, compiler) = super::execute(source);
        let children = std::mem::take(direct_children56(&mut run));
        let requirements = children
            .iter()
            .map(|p| crate::compile_to_lean::helper::source_subject(p).unwrap())
            .collect();
        equal56(&mut run).searched_proof = EqualFactSearchedProof::ByBuiltinStrategy(
            EqualitySearchProofByBuiltinStrategy::ArithmeticCongruence(
                ArithmeticCongruenceStrategySingleStep {
                    requirement_facts: requirements,
                    proof_of_requirement_facts: children,
                },
            ),
        );
        assert_eq!(
            compiler
                .compile_run(&run, "Matrix56WrongStrategyTag")
                .unwrap_err()
                .route,
            "ArithmeticCongruence/Constructor"
        );
    }
}

#[test]
fn matrix_linear_same_arity_does_not_merge_operation_families() {
    let (sub, _) = super::execute(SOURCES56[0].1);
    let (scale, _) = super::execute(SOURCES56[1].1);
    let (add, _) = super::execute(super::matrix_entrywise_context_tests::SOURCES55[0].1);
    let objects = [&sub, &scale, &add].map(|run| {
        let outer = super::forall_proof(&run.statement_results[0]);
        &super::equality_proof(&outer.proved_then_facts[0].verify_result)
            .fact
            .left
    });
    for (i, a) in objects.iter().enumerate() {
        for (j, b) in objects.iter().enumerate() {
            if i != j {
                assert!(
                    crate::compile_to_lean::helper::arithmetic_constructor_pairs(a, b).is_none()
                );
            }
        }
    }
}
