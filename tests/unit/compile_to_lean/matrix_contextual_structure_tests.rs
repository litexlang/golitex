use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof;
use crate::prelude::*;
pub(super) const SOURCES54:&[(&str,&str)]=&[
("direct_transpose","forall sc54a_A,sc54a_B matrix(C,2,3):\n    sc54a_A=sc54a_B\n    =>:\n        transpose(sc54a_A,2,3)=transpose(sc54a_B,2,3)\n"),
("forall_transpose","forall sc54b_A matrix(C,2,3),sc54b_p fn(sc54b_t matrix(C,2,3)) matrix(C,3,2):\n    forall sc54b_X matrix(C,2,3):\n        transpose(sc54b_X,2,3)=sc54b_p(sc54b_X)\n    =>:\n        transpose(sc54b_A,2,3)=sc54b_p(sc54b_A)\n"),
("direct_symbolic_transpose","forall sc54c_m,sc54c_n N,sc54c_A,sc54c_B matrix(C,sc54c_m,sc54c_n):\n    sc54c_A=sc54c_B\n    =>:\n        transpose(sc54c_A,sc54c_m,sc54c_n)=transpose(sc54c_B,sc54c_m,sc54c_n)\n"),
("direct_all_operands_changed","forall sc54f_m,sc54f_n,sc54f_p,sc54f_q N,sc54f_A matrix(C,sc54f_m,sc54f_n),sc54f_B matrix(C,sc54f_p,sc54f_q):\n    sc54f_A=sc54f_B\n    sc54f_m=sc54f_p\n    sc54f_n=sc54f_q\n    =>:\n        transpose(sc54f_A,sc54f_m,sc54f_n)=transpose(sc54f_B,sc54f_p,sc54f_q)\n"),
("atomic_explicit","forall sc54d_A,sc54d_B matrix(C,2,3),sc54d_S set:\n    sc54d_A=sc54d_B\n    transpose(sc54d_A,2,3) $in sc54d_S\n    =>:\n        transpose(sc54d_A,2,3)=transpose(sc54d_B,2,3)\n        transpose(sc54d_B,2,3) $in sc54d_S\n"),
("identity_explicit","have fn sc54id(sc54id_X matrix(C,2,3)) matrix(C,2,3) = sc54id_X\nforall sc54id_A matrix(C,2,3):\n    sc54id(sc54id_A)=sc54id_A\n    transpose(sc54id(sc54id_A),2,3)=transpose(sc54id_A,2,3)\n")];
fn transpose54(object: &Obj) -> [&Obj; 3] {
    let Obj::MatrixOperator(MatrixOperator::Transpose(p)) = object else {
        panic!("original transpose")
    };
    [p.matrix.as_ref(), p.rows.as_ref(), p.cols.as_ref()]
}
#[test]
fn matrix_context_original_direct_three_operand_audit() {
    for (name, source) in SOURCES54.iter().filter(|(n, _)| n.starts_with("direct")) {
        let (run, compiler) = super::execute(source);
        let outer = super::forall_proof(&run.statement_results[0]);
        let equal = super::equality_proof(&outer.proved_then_facts[0].verify_result);
        let EqualFactSearchedProof::ByMatchingOneArgByOne(p) = &equal.searched_proof else {
            panic!("original direct route:{name}")
        };
        let a = transpose54(&equal.fact.left);
        let b = transpose54(&equal.fact.right);
        assert_eq!(p.corresponding_arg_equal_proofs.len(), 3);
        for (index, child) in p.corresponding_arg_equal_proofs.iter().enumerate() {
            let child = super::equality_proof(child);
            assert_eq!(child.fact.left.ir(), a[index].ir());
            assert_eq!(child.fact.right.ir(), b[index].ir());
            eprintln!(
                "ORIGINAL54 {name} operand:{index} left:{} right:{}",
                child.fact.left.ir(),
                child.fact.right.ir()
            );
            if index == 0 || *name == "direct_all_operands_changed" {
                let EqualFactSearchedProof::ByEquivalenceClass(
                    EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
                ) = &child.searched_proof
                else {
                    panic!("original ordered operand citation")
                };
                assert_eq!(path.path.len(), 1);
                assert_eq!(
                    path.path[0].2,
                    outer.fact.dom_facts[if *name == "direct_all_operands_changed" {
                        index
                    } else {
                        0
                    }]
                    .fact_id()
                );
            } else {
                assert!(matches!(
                    child.searched_proof,
                    EqualFactSearchedProof::ByTheyAreTheSame(_)
                ));
            }
        }
        assert_eq!(
            compiler
                .compile_run(&run, "Matrix54OriginalDirect")
                .unwrap()
                .contains("_constructor"),
            true
        );
    }
}
#[test]
fn matrix_context_original_forall_three_operand_audit() {
    let source = SOURCES54
        .iter()
        .find(|(n, _)| *n == "forall_transpose")
        .unwrap()
        .1;
    let (run, compiler) = super::execute(source);
    let outer = super::forall_proof(&run.statement_results[0]);
    let equal = super::equality_proof(&outer.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByKnownForallFact(p) = &equal.searched_proof else {
        panic!("original known forall")
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
    let a = transpose54(pattern);
    let b = transpose54(goal_arg);
    assert_eq!(child_matches.len(), 3);
    for (index, child) in child_matches.iter().enumerate() {
        match child.as_detailed().unwrap() {
            DetailedForallConclusionArgMatchProof::BoundParam {
                param_id,
                pattern,
                goal_arg,
            } if index == 0 => {
                assert_eq!(pattern.ir(), a[index].ir());
                assert_eq!(goal_arg.ir(), b[index].ir());
                eprintln!(
                    "ORIGINAL54 forall operand:{index} bound:{} pattern:{} goal:{}",
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
            } if index > 0 => {
                assert_eq!(pattern.ir(), a[index].ir());
                assert_eq!(pattern_after_subst.ir(), a[index].ir());
                assert_eq!(goal_arg.ir(), b[index].ir());
                assert_eq!(equal.equal_fact.left.ir(), a[index].ir());
                assert_eq!(equal.equal_fact.right.ir(), b[index].ir());
                eprintln!(
                    "ORIGINAL54 forall operand:{index} literal:{} goal:{}",
                    pattern.ir(),
                    goal_arg.ir()
                );
            }
            _ => panic!("unexpected original operand route:{index}"),
        }
    }
    let requirements = p.instantiation_requirements.as_detailed().unwrap();
    eprintln!(
        "ORIGINAL54 forall cite:{} parameter_types:{} guards:{}",
        p.cite.fact_id.value(),
        requirements.param_type_requirements.len(),
        requirements.proof_of_dom_facts.len()
    );
    assert_eq!(
        compiler
            .compile_run(&run, "Matrix54OriginalForall")
            .unwrap()
            .contains("_constructor"),
        true
    );
}

fn source54(name: &str) -> &'static str {
    SOURCES54.iter().find(|(n, _)| *n == name).unwrap().1
}
#[test]
fn matrix_context_original_atomic_stored_congruence_audit() {
    let (mut run, compiler) = super::execute(source54("atomic_explicit"));
    {
        let outer = super::forall_proof_mut(&mut run.statement_results[0]);
        assert_eq!(outer.proved_then_facts.len(), 2);
        let first = super::equality_proof(&outer.proved_then_facts[0].verify_result);
        let id = first.fact.fact_id;
        assert!(matches!(
            first.searched_proof,
            EqualFactSearchedProof::ByMatchingOneArgByOne(_)
        ));
        let source = outer.fact.dom_facts[1].fact_id();
        let atomic = super::atomic_proof_mut(&mut outer.proved_then_facts[1].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(p) = &atomic.searched_proof
        else {
            panic!("original atomic source")
        };
        assert_eq!(p.cite_fact_id, source);
        assert_eq!(p.why_parameters_of_known_fact_are_equal_to_givens.len(), 2);
        let EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
        ) = &p.why_parameters_of_known_fact_are_equal_to_givens[0]
        else {
            panic!("original stored transpose equality")
        };
        assert_eq!(path.path.len(), 1);
        assert_eq!(path.path[0].2, id);
        assert!(matches!(
            p.why_parameters_of_known_fact_are_equal_to_givens[1],
            EqualFactSearchedProof::ByTheyAreTheSame(_)
        ));
        eprintln!(
            "ORIGINAL54 atomic source:{} stored_equal:{} argument_equalities:2",
            source.value(),
            id.value()
        );
    }
    assert_eq!(
        compiler
            .compile_run(&run, "Matrix54OriginalAtomicStored")
            .unwrap()
            .contains("_constructor"),
        true
    );
}
fn equality_family54(p: &EqualFactSearchedProof) -> &'static str {
    match p {
        EqualFactSearchedProof::ByClosedCalculation(_) => "ByClosedCalculation",
        EqualFactSearchedProof::ByTheyAreTheSame(_) => "ByTheyAreTheSame",
        EqualFactSearchedProof::ByKnownSpecialProperty(_) => "ByKnownSpecialProperty",
        EqualFactSearchedProof::ByBuiltinRule(_) => "ByBuiltinRule",
        EqualFactSearchedProof::ByEquivalenceClass(_) => "ByEquivalenceClass",
        EqualFactSearchedProof::ByObjectDefinition(_) => "ByObjectDefinition",
        EqualFactSearchedProof::ByBuiltinStrategy(_) => "ByBuiltinStrategy",
        EqualFactSearchedProof::ByMatchingOneArgByOne(_) => "ByMatchingOneArgByOne",
        EqualFactSearchedProof::ByKnownForallFact(_) => "ByKnownForallFact",
        EqualFactSearchedProof::ByKnownForallFactViaSymmetry(_) => "ByKnownForallFactViaSymmetry",
        EqualFactSearchedProof::ByBuiltinRewrite(_) => "ByBuiltinRewrite",
    }
}
#[test]
fn matrix_context_original_function_instance_store_audit() {
    let (run, compiler) = super::execute(source54("identity_explicit"));
    let outer = super::forall_proof(&run.statement_results[1]);
    assert_eq!(outer.proved_then_facts.len(), 2);
    let first = super::equality_proof(&outer.proved_then_facts[0].verify_result);
    let second = super::equality_proof(&outer.proved_then_facts[1].verify_result);
    let EqualFactSearchedProof::ByMatchingOneArgByOne(p) = &second.searched_proof else {
        panic!("original enclosing transpose")
    };
    assert_eq!(p.corresponding_arg_equal_proofs.len(), 3);
    let child = super::equality_proof(&p.corresponding_arg_equal_proofs[0]);
    let a = transpose54(&second.fact.left);
    let b = transpose54(&second.fact.right);
    assert_eq!(child.fact.left.ir(), a[0].ir());
    assert_eq!(child.fact.right.ir(), b[0].ir());
    let EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
    ) = &child.searched_proof
    else {
        panic!("original stored function instance")
    };
    assert_eq!(path.path.len(), 1);
    assert_eq!(path.path[0].2, first.fact.fact_id);
    eprintln!(
        "ORIGINAL54 function instance_route:{} stored_equal:{} transpose_operands:3",
        equality_family54(&first.searched_proof),
        first.fact.fact_id.value()
    );
    assert_eq!(
        compiler
            .compile_run(&run, "Matrix54OriginalFunctionStored")
            .unwrap()
            .contains("_constructor"),
        true
    );
}

const EVAL_MATRIX54:&str="have fn sc54eval_A(sc54eval_r,sc54eval_c closed_range(1,2)) C = 1\nsc54eval_A $in matrix(C,2,2)\neval trace(transpose(sc54eval_A,2,2),2)\n";
#[test]
fn matrix_context_original_scalar_eval_parent_boundary_audit() {
    use crate::execute::{ExecCommandStmtResult, ExecEvalStmtResult};
    let (run, _compiler) = super::execute(EVAL_MATRIX54);
    let ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(p))) =
        &run.statement_results[2]
    else {
        panic!("original native matrix eval")
    };
    assert!(!p.matrix_scalar_evaluations.is_empty());
    eprintln!("ORIGINAL54 eval source:{} result:{} matrix_records:{} function_records:{} aggregate_records:{} algo_records:{}",p.source_object.ir(),p.evaluated_object.ir(),p.matrix_scalar_evaluations.len(),p.function_evaluations.len(),p.aggregate_evaluations.len(),p.algo_evaluations.len());
    assert_eq!(p.evaluated_object.ir().to_string(), "2");
}

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    DetailedSearchProofByKnownForallFact, ForallConclusionArgMatchProof,
};
fn equal54(run: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    let outer = super::forall_proof_mut(run.statement_results.last_mut().unwrap());
    super::equality_proof_mut(&mut outer.proved_then_facts[0].verify_result)
}
fn direct_children54(run: &mut RunLitexCodeResult) -> &mut Vec<VerifyFactResult> {
    let EqualFactSearchedProof::ByMatchingOneArgByOne(p) = &mut equal54(run).searched_proof else {
        panic!()
    };
    &mut p.corresponding_arg_equal_proofs
}
fn application54(run: &mut RunLitexCodeResult) -> &mut DetailedSearchProofByKnownForallFact {
    let EqualFactSearchedProof::ByKnownForallFact(p) = &mut equal54(run).searched_proof else {
        panic!()
    };
    p.as_detailed_mut().unwrap()
}
fn matching_children54(run: &mut RunLitexCodeResult) -> &mut Vec<ForallConclusionArgMatchProof> {
    let DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } =
        application54(run).arg_match_proofs[0]
            .as_detailed_mut()
            .unwrap()
    else {
        panic!()
    };
    child_matches
}
fn reject54(run: &RunLitexCodeResult, compiler: &crate::compile_to_lean::LitexToLeanCompiler) {
    compiler
        .compile_run(run, "Matrix54ChangedEvidence")
        .expect_err("changed original certificate must reject");
}
#[test]
fn matrix_context_requires_all_three_original_equalities() {
    for change in ["missing_third", "empty", "extra"] {
        let (mut run, compiler) = super::execute(source54("direct_all_operands_changed"));
        match change {
            "missing_third" => {
                direct_children54(&mut run).pop();
            }
            "empty" => direct_children54(&mut run).clear(),
            _ => {
                let (mut other, _) = super::execute(source54("direct_all_operands_changed"));
                let extra = direct_children54(&mut other).pop().unwrap();
                direct_children54(&mut run).push(extra);
            }
        }
        assert_eq!(
            compiler
                .compile_run(&run, "Matrix54Arity")
                .unwrap_err()
                .route,
            "ArithmeticCongruence/Children"
        );
    }
}
#[test]
fn matrix_context_rejects_reordered_row_and_column_equalities() {
    let (mut run, compiler) = super::execute(source54("direct_all_operands_changed"));
    direct_children54(&mut run).swap(1, 2);
    assert_eq!(
        compiler
            .compile_run(&run, "Matrix54Order")
            .unwrap_err()
            .route,
        "ArithmeticCongruence/ChildSubject"
    );
}
#[test]
fn matrix_context_requires_the_third_operand_subject() {
    let (mut run, compiler) = super::execute(source54("direct_all_operands_changed"));
    let (mut other, _) = super::execute(source54("direct_all_operands_changed"));
    let row = direct_children54(&mut other).remove(1);
    direct_children54(&mut run)[2] = row;
    assert_eq!(
        compiler
            .compile_run(&run, "Matrix54ThirdSubject")
            .unwrap_err()
            .route,
        "ArithmeticCongruence/ChildSubject"
    );
}
#[test]
fn matrix_context_rejects_foreign_and_self_third_operand_citations() {
    for own in [false, true] {
        let (mut run, compiler) = super::execute(source54("direct_all_operands_changed"));
        let child = super::equality_proof_mut(&mut direct_children54(&mut run)[2]);
        let own_id = child.fact.fact_id;
        let EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
        ) = &mut child.searched_proof
        else {
            panic!()
        };
        path.path[0].2 = if own { own_id } else { FactId::new(u64::MAX) };
        reject54(&run, &compiler);
    }
}
#[test]
fn matrix_context_rejects_later_sibling_dimension_citation() {
    let source = source54("direct_all_operands_changed");
    let (mut run, compiler) =
        super::execute(&format!("{}{}", source, source.replace("sc54f_", "sc54z_")));
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(sibling)) = &run.statement_results[1]
    else {
        panic!()
    };
    let Fact::ForallFact(sibling) =
        crate::compile_to_lean::helper::source_subject(&sibling.verify_result).unwrap()
    else {
        panic!()
    };
    let id = sibling.dom_facts[2].fact_id();
    let outer = super::forall_proof_mut(&mut run.statement_results[0]);
    let equal = super::equality_proof_mut(&mut outer.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByMatchingOneArgByOne(p) = &mut equal.searched_proof else {
        panic!()
    };
    let child = super::equality_proof_mut(&mut p.corresponding_arg_equal_proofs[2]);
    let EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
    ) = &mut child.searched_proof
    else {
        panic!()
    };
    path.path[0].2 = id;
    reject54(&run, &compiler);
}
#[test]
fn matrix_context_forall_requires_three_captured_operand_matches() {
    for extra in [false, true] {
        let (mut run, compiler) = super::execute(source54("forall_transpose"));
        if extra {
            let (mut other, _) = super::execute(source54("forall_transpose"));
            let added = matching_children54(&mut other).pop().unwrap();
            matching_children54(&mut run).push(added);
        } else {
            matching_children54(&mut run).pop();
        }
        assert_eq!(
            compiler
                .compile_run(&run, "Matrix54MatchArity")
                .unwrap_err()
                .route,
            "CompoundKnown/StructureArity"
        );
    }
}
#[test]
fn matrix_context_forall_requires_original_third_captured_literal() {
    let (mut run, compiler) = super::execute(source54("forall_transpose"));
    let children = matching_children54(&mut run);
    let DetailedForallConclusionArgMatchProof::NonParamEqual { goal_arg, .. } =
        children[1].as_detailed().unwrap()
    else {
        panic!()
    };
    let wrong = goal_arg.clone();
    let DetailedForallConclusionArgMatchProof::NonParamEqual { goal_arg, .. } =
        children[2].as_detailed_mut().unwrap()
    else {
        panic!()
    };
    *goal_arg = wrong;
    reject54(&run, &compiler);
}
#[test]
fn matrix_context_forall_requires_source_binder_and_type_identities() {
    for change in ["binder", "type", "source", "goal_subject"] {
        let (mut run, compiler) = super::execute(source54("forall_transpose"));
        match change {
            "binder" => {
                let DetailedForallConclusionArgMatchProof::BoundParam { param_id, .. } =
                    matching_children54(&mut run)[0].as_detailed_mut().unwrap()
                else {
                    panic!()
                };
                *param_id = IdentifierId::new(u64::MAX);
            }
            "type" => {
                application54(&mut run)
                    .instantiation_requirements
                    .as_detailed_mut()
                    .unwrap()
                    .param_type_requirements[0]
                    .param_id = IdentifierId::new(u64::MAX)
            }
            "source" => application54(&mut run).cite.fact_id = FactId::new(u64::MAX),
            _ => {
                let DetailedForallConclusionArgMatchProof::ByStructure {
                    pattern, goal_arg, ..
                } = application54(&mut run).arg_match_proofs[0]
                    .as_detailed_mut()
                    .unwrap()
                else {
                    panic!()
                };
                *goal_arg = pattern.clone();
            }
        }
        reject54(&run, &compiler);
    }
}
#[test]
fn matrix_context_requires_parent_and_third_child_original_formations() {
    for child in [false, true] {
        let (mut run, compiler) = super::execute(source54("direct_all_operands_changed"));
        let equal = if child {
            super::equality_proof_mut(&mut direct_children54(&mut run)[2])
        } else {
            equal54(&mut run)
        };
        let wd = equal.well_defined_proof.as_detailed_mut().unwrap();
        std::mem::swap(&mut wd.left, &mut wd.right);
        reject54(&run, &compiler);
    }
}
#[test]
fn matrix_context_preserves_arithmetic_strategy_producer_eligibility() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_builtin_strategy_result::ArithmeticCongruenceStrategySingleStep;
    let (mut run, compiler) = super::execute(source54("direct_all_operands_changed"));
    let children = std::mem::take(direct_children54(&mut run));
    let requirements = children
        .iter()
        .map(|p| crate::compile_to_lean::helper::source_subject(p).unwrap())
        .collect();
    equal54(&mut run).searched_proof = EqualFactSearchedProof::ByBuiltinStrategy(
        EqualitySearchProofByBuiltinStrategy::ArithmeticCongruence(
            ArithmeticCongruenceStrategySingleStep {
                requirement_facts: requirements,
                proof_of_requirement_facts: children,
            },
        ),
    );
    assert_eq!(
        compiler
            .compile_run(&run, "Matrix54WrongStrategyTag")
            .unwrap_err()
            .route,
        "ArithmeticCongruence/Constructor"
    );
}
#[test]
fn matrix_context_atomic_stored_path_cannot_cite_untransposed_matrix_equality() {
    let (mut run, compiler) = super::execute(source54("atomic_explicit"));
    let outer = super::forall_proof_mut(&mut run.statement_results[0]);
    let wrong = outer.fact.dom_facts[0].fact_id();
    let atomic = super::atomic_proof_mut(&mut outer.proved_then_facts[1].verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(p) = &mut atomic.searched_proof
    else {
        panic!()
    };
    let EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
    ) = &mut p.why_parameters_of_known_fact_are_equal_to_givens[0]
    else {
        panic!()
    };
    path.path[0].2 = wrong;
    reject54(&run, &compiler);
}

#[test]
fn matrix_context_rejects_identical_endpoint_citation_from_later_then_fact() {
    let source = format!(
        "{}        sc54f_n=sc54f_q\n",
        source54("direct_all_operands_changed")
    );
    let (mut run, compiler) = super::execute(&source);
    let outer = super::forall_proof(&run.statement_results[0]);
    assert_eq!(outer.proved_then_facts.len(), 2);
    let future = super::equality_proof(&outer.proved_then_facts[1].verify_result);
    let future_id = future.fact.fact_id;
    let endpoints = (future.fact.left.ir(), future.fact.right.ir());
    let child = super::equality_proof_mut(&mut direct_children54(&mut run)[2]);
    assert_eq!((child.fact.left.ir(), child.fact.right.ir()), endpoints);
    assert_ne!(child.fact.fact_id, future_id);
    let EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
    ) = &mut child.searched_proof
    else {
        panic!()
    };
    path.path[0].2 = future_id;
    reject54(&run, &compiler);
}
