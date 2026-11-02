use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof;
use crate::prelude::*;
pub(super) const SOURCES58:&[(&str,&str)]=&[
("conjugate_transpose_all_operands","forall sc58a_m,sc58a_n,sc58a_p,sc58a_q N,sc58a_A matrix(C,sc58a_m,sc58a_n),sc58a_B matrix(C,sc58a_p,sc58a_q):\n    sc58a_A=sc58a_B\n    sc58a_m=sc58a_p\n    sc58a_n=sc58a_q\n    =>:\n        conjugate_transpose(sc58a_A,sc58a_m,sc58a_n)=conjugate_transpose(sc58a_B,sc58a_p,sc58a_q)\n"),
("outer_all_operands","forall sc58b_m,sc58b_n,sc58b_p,sc58b_q N,sc58b_a fn(sc58b_i closed_range(1,sc58b_m)) C,sc58b_b fn(sc58b_j closed_range(1,sc58b_n)) C,sc58b_c fn(sc58b_k closed_range(1,sc58b_p)) C,sc58b_d fn(sc58b_l closed_range(1,sc58b_q)) C:\n    sc58b_a=sc58b_c\n    sc58b_b=sc58b_d\n    sc58b_m=sc58b_p\n    sc58b_n=sc58b_q\n    =>:\n        outer_product(sc58b_a,sc58b_b,sc58b_m,sc58b_n)=outer_product(sc58b_c,sc58b_d,sc58b_p,sc58b_q)\n"),
("diagonal_all_operands","forall sc58c_n,sc58c_p N,sc58c_v fn(sc58c_i closed_range(1,sc58c_n)) C,sc58c_w fn(sc58c_j closed_range(1,sc58c_p)) C:\n    sc58c_v=sc58c_w\n    sc58c_n=sc58c_p\n    =>:\n        diagonal_matrix(sc58c_v,sc58c_n)=diagonal_matrix(sc58c_w,sc58c_p)\n"),
("forall_conjugate_transpose","forall sc58d_A matrix(C,2,3),sc58d_P fn(sc58d_T matrix(C,2,3)) matrix(C,3,2):\n    forall sc58d_X matrix(C,2,3):\n        conjugate_transpose(sc58d_X,2,3)=sc58d_P(sc58d_X)\n    =>:\n        conjugate_transpose(sc58d_A,2,3)=sc58d_P(sc58d_A)\n"),
("forall_outer","forall sc58e_a fn(sc58e_i closed_range(1,2)) C,sc58e_b fn(sc58e_j closed_range(1,3)) C,sc58e_P fn(sc58e_t1 fn(sc58e_u closed_range(1,2)) C,sc58e_t2 fn(sc58e_v closed_range(1,3)) C) matrix(C,2,3):\n    forall sc58e_x fn(sc58e_k closed_range(1,2)) C,sc58e_y fn(sc58e_l closed_range(1,3)) C:\n        outer_product(sc58e_x,sc58e_y,2,3)=sc58e_P(sc58e_x,sc58e_y)\n    =>:\n        outer_product(sc58e_a,sc58e_b,2,3)=sc58e_P(sc58e_a,sc58e_b)\n"),
("forall_diagonal","forall sc58f_v fn(sc58f_i closed_range(1,2)) C,sc58f_P fn(sc58f_t fn(sc58f_j closed_range(1,2)) C) matrix(C,2,2):\n    forall sc58f_x fn(sc58f_k closed_range(1,2)) C:\n        diagonal_matrix(sc58f_x,2)=sc58f_P(sc58f_x)\n    =>:\n        diagonal_matrix(sc58f_v,2)=sc58f_P(sc58f_v)\n")];
fn operands58(object: &Obj) -> Vec<&Obj> {
    match object {
        Obj::MatrixOperator(MatrixOperator::ConjugateTranspose(a)) => {
            vec![&a.matrix, &a.rows, &a.cols]
        }
        Obj::MatrixOperator(MatrixOperator::OuterProduct(a)) => {
            vec![&a.left, &a.right, &a.rows, &a.cols]
        }
        Obj::MatrixOperator(MatrixOperator::Diagonal(a)) => vec![&a.vector, &a.order],
        _ => panic!("original58 matrix graph constructor"),
    }
}
#[test]
fn matrix_graph_original_all_changed_operands_audit() {
    for (name, source) in &SOURCES58[..3] {
        let (run, compiler) = super::execute(source);
        let outer = super::forall_proof(&run.statement_results[0]);
        let equal = super::equality_proof(&outer.proved_then_facts[0].verify_result);
        let EqualFactSearchedProof::ByMatchingOneArgByOne(p) = &equal.searched_proof else {
            panic!("original direct route:{name}")
        };
        let a = operands58(&equal.fact.left);
        let b = operands58(&equal.fact.right);
        assert_eq!(p.corresponding_arg_equal_proofs.len(), a.len());
        assert_eq!(a.len(), outer.fact.dom_facts.len());
        for (index, child) in p.corresponding_arg_equal_proofs.iter().enumerate() {
            let child = super::equality_proof(child);
            assert_eq!(child.fact.left.ir(), a[index].ir());
            assert_eq!(child.fact.right.ir(), b[index].ir());
            let EqualFactSearchedProof::ByEquivalenceClass(
                EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
            ) = &child.searched_proof
            else {
                panic!("original ordered equality")
            };
            assert_eq!(path.path.len(), 1);
            assert_eq!(path.path[0].2, outer.fact.dom_facts[index].fact_id());
            eprintln!(
                "ORIGINAL58 {name} direct operand:{index} left:{} right:{} cite:{}",
                child.fact.left.ir(),
                child.fact.right.ir(),
                path.path[0].2.value()
            );
        }
        assert_eq!(
            compiler
                .compile_run(&run, "Matrix58OriginalDirect")
                .unwrap()
                .contains(if name.starts_with("conjugate") {
                    "matrixConjugateTransposeBody"
                } else if name.starts_with("outer") {
                    "matrixOuterBody"
                } else {
                    "matrixDiagonalBody"
                }),
            true
        );
    }
}
#[test]
fn matrix_graph_original_forall_constructor_matches_audit() {
    for (name, source) in &SOURCES58[3..] {
        let (run, compiler) = super::execute(source);
        let outer = super::forall_proof(&run.statement_results[0]);
        let equal = super::equality_proof(&outer.proved_then_facts[0].verify_result);
        let EqualFactSearchedProof::ByKnownForallFact(p) = &equal.searched_proof else {
            panic!("original known forall:{name}")
        };
        let p = p.as_detailed().unwrap();
        let Fact::ForallFact(cited) = &outer.fact.dom_facts[0] else {
            panic!()
        };
        assert_eq!(p.cite.fact_id, cited.fact_id);
        let ids: Vec<_> = cited
            .typed_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(|p| p.id))
            .collect();
        assert_eq!(p.arg_match_proofs.len(), 2);
        let DetailedForallConclusionArgMatchProof::ByStructure {
            pattern,
            goal_arg,
            child_matches,
        } = p.arg_match_proofs[0].as_detailed().unwrap()
        else {
            panic!("original matrix structure:{name}")
        };
        let a = operands58(pattern);
        let b = operands58(goal_arg);
        assert_eq!(child_matches.len(), a.len());
        assert_eq!(p.forall_parameters_match_what_args.len(), ids.len());
        for (index, child) in child_matches.iter().enumerate() {
            match child.as_detailed().unwrap() {
                DetailedForallConclusionArgMatchProof::BoundParam {
                    param_id,
                    pattern,
                    goal_arg,
                } if index < ids.len() => {
                    assert_eq!(*param_id, ids[index]);
                    assert_eq!(pattern.ir(), a[index].ir());
                    assert_eq!(goal_arg.ir(), b[index].ir());
                    assert_eq!(
                        p.forall_parameters_match_what_args[index].ir(),
                        b[index].ir()
                    );
                    eprintln!(
                        "ORIGINAL58 {name} forall operand:{index} bound:{} pattern:{} goal:{}",
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
                } if index >= ids.len() => {
                    assert_eq!(pattern.ir(), a[index].ir());
                    assert_eq!(pattern_after_subst.ir(), a[index].ir());
                    assert_eq!(goal_arg.ir(), b[index].ir());
                    assert_eq!(equal.equal_fact.left.ir(), a[index].ir());
                    assert_eq!(equal.equal_fact.right.ir(), b[index].ir());
                    eprintln!(
                        "ORIGINAL58 {name} forall operand:{index} literal:{} goal:{}",
                        pattern.ir(),
                        goal_arg.ir()
                    );
                }
                _ => panic!("original operand route:{name}:{index}"),
            }
        }
        let requirements = p.instantiation_requirements.as_detailed().unwrap();
        assert_eq!(requirements.param_type_requirements.len(), ids.len());
        assert!(requirements.proof_of_dom_facts.is_empty());
        for (i, requirement) in requirements.param_type_requirements.iter().enumerate() {
            assert_eq!(requirement.param_id, ids[i]);
        }
        eprintln!(
            "ORIGINAL58 {name} forall cite:{} parameter_types:{} guards:{}",
            p.cite.fact_id.value(),
            requirements.param_type_requirements.len(),
            requirements.proof_of_dom_facts.len()
        );
        assert_eq!(
            compiler
                .compile_run(&run, "Matrix58OriginalForall")
                .unwrap()
                .contains(if name.ends_with("conjugate_transpose") {
                    "matrixConjugateTransposeBody"
                } else if name.ends_with("outer") {
                    "matrixOuterBody"
                } else {
                    "matrixDiagonalBody"
                }),
            true
        );
    }
}

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    DetailedSearchProofByKnownForallFact, ForallConclusionArgMatchProof,
};
fn equal58(run: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    let outer = super::forall_proof_mut(&mut run.statement_results[0]);
    super::equality_proof_mut(&mut outer.proved_then_facts[0].verify_result)
}
fn children58(run: &mut RunLitexCodeResult) -> &mut Vec<VerifyFactResult> {
    let EqualFactSearchedProof::ByMatchingOneArgByOne(p) = &mut equal58(run).searched_proof else {
        panic!()
    };
    &mut p.corresponding_arg_equal_proofs
}
fn app58(run: &mut RunLitexCodeResult) -> &mut DetailedSearchProofByKnownForallFact {
    let EqualFactSearchedProof::ByKnownForallFact(p) = &mut equal58(run).searched_proof else {
        panic!()
    };
    p.as_detailed_mut().unwrap()
}
fn matches58(run: &mut RunLitexCodeResult) -> &mut Vec<ForallConclusionArgMatchProof> {
    let DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } =
        app58(run).arg_match_proofs[0].as_detailed_mut().unwrap()
    else {
        panic!()
    };
    child_matches
}
fn reject58(run: &RunLitexCodeResult, compiler: &crate::compile_to_lean::LitexToLeanCompiler) {
    compiler
        .compile_run(run, "Matrix58ChangedEvidence")
        .expect_err("changed original certificate must reject");
}
#[test]
fn matrix_graph_requires_every_original_operand_equality() {
    for (_, source) in &SOURCES58[..3] {
        for change in ["missing", "empty", "extra"] {
            let (mut run, compiler) = super::execute(source);
            match change {
                "missing" => {
                    children58(&mut run).pop();
                }
                "empty" => children58(&mut run).clear(),
                _ => {
                    let (mut other, _) = super::execute(source);
                    let extra = children58(&mut other).pop().unwrap();
                    children58(&mut run).push(extra);
                }
            }
            assert_eq!(
                compiler
                    .compile_run(&run, "Matrix58Arity")
                    .unwrap_err()
                    .route,
                "ArithmeticCongruence/Children"
            );
        }
    }
}
#[test]
fn matrix_graph_preserves_first_and_last_operand_order() {
    for (_, source) in &SOURCES58[..3] {
        let (mut run, compiler) = super::execute(source);
        let last = children58(&mut run).len() - 1;
        children58(&mut run).swap(0, last);
        assert_eq!(
            compiler
                .compile_run(&run, "Matrix58Order")
                .unwrap_err()
                .route,
            "ArithmeticCongruence/ChildSubject"
        );
    }
}
#[test]
fn matrix_graph_requires_the_last_operand_subject() {
    for (_, source) in &SOURCES58[..3] {
        let (mut run, compiler) = super::execute(source);
        let (mut other, _) = super::execute(source);
        let last = children58(&mut run).len() - 1;
        let wrong = children58(&mut other).remove(last - 1);
        children58(&mut run)[last] = wrong;
        assert_eq!(
            compiler
                .compile_run(&run, "Matrix58LastSubject")
                .unwrap_err()
                .route,
            "ArithmeticCongruence/ChildSubject"
        );
    }
}
#[test]
fn matrix_graph_rejects_foreign_and_self_last_operand_citations() {
    for (_, source) in &SOURCES58[..3] {
        for own in [false, true] {
            let (mut run, compiler) = super::execute(source);
            let last = children58(&mut run).len() - 1;
            let child = super::equality_proof_mut(&mut children58(&mut run)[last]);
            let own_id = child.fact.fact_id;
            let EqualFactSearchedProof::ByEquivalenceClass(
                EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
            ) = &mut child.searched_proof
            else {
                panic!()
            };
            path.path[0].2 = if own { own_id } else { FactId::new(u64::MAX) };
            reject58(&run, &compiler);
        }
    }
}
#[test]
fn matrix_graph_rejects_later_sibling_dimension_citation() {
    for (_, source) in &SOURCES58[..3] {
        let sibling = source
            .replace("sc58a_", "sc58x_")
            .replace("sc58b_", "sc58y_")
            .replace("sc58c_", "sc58z_");
        let (mut run, compiler) = super::execute(&format!("{}{}", source, sibling));
        let last = children58(&mut run).len() - 1;
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(sibling)) = &run.statement_results[1]
        else {
            panic!()
        };
        let Fact::ForallFact(sibling) =
            crate::compile_to_lean::helper::source_subject(&sibling.verify_result).unwrap()
        else {
            panic!()
        };
        let id = sibling.dom_facts[last].fact_id();
        let child = super::equality_proof_mut(&mut children58(&mut run)[last]);
        let EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
        ) = &mut child.searched_proof
        else {
            panic!()
        };
        path.path[0].2 = id;
        reject58(&run, &compiler);
    }
}
#[test]
fn matrix_graph_rejects_same_endpoints_from_future_then_fact() {
    for (name, source) in &SOURCES58[..3] {
        let (mut original, _) = super::execute(source);
        let last = children58(&mut original).len() - 1;
        let later_equality = match *name {
            "conjugate_transpose_all_operands" => "sc58a_n=sc58a_q",
            "outer_all_operands" => "sc58b_n=sc58b_q",
            "diagonal_all_operands" => "sc58c_n=sc58c_p",
            _ => panic!("original direct profile"),
        };
        let source = format!("{}        {}\n", source, later_equality);
        let (mut run, compiler) = super::execute(&source);
        let outer = super::forall_proof(&run.statement_results[0]);
        assert_eq!(outer.proved_then_facts.len(), 2);
        let future = super::equality_proof(&outer.proved_then_facts[1].verify_result);
        let id = future.fact.fact_id;
        let endpoints = (future.fact.left.ir(), future.fact.right.ir());
        let child = super::equality_proof_mut(&mut children58(&mut run)[last]);
        assert_eq!((child.fact.left.ir(), child.fact.right.ir()), endpoints);
        assert_ne!(child.fact.fact_id, id);
        let EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
        ) = &mut child.searched_proof
        else {
            panic!()
        };
        path.path[0].2 = id;
        reject58(&run, &compiler);
    }
}
#[test]
fn matrix_graph_forall_requires_actual_constructor_match_arity() {
    for (_, source) in &SOURCES58[3..] {
        for extra in [false, true] {
            let (mut run, compiler) = super::execute(source);
            if extra {
                let (mut other, _) = super::execute(source);
                let added = matches58(&mut other).pop().unwrap();
                matches58(&mut run).push(added);
            } else {
                matches58(&mut run).pop();
            }
            assert_eq!(
                compiler
                    .compile_run(&run, "Matrix58MatchArity")
                    .unwrap_err()
                    .route,
                "CompoundKnown/StructureArity"
            );
        }
    }
}
#[test]
fn matrix_graph_forall_requires_exact_captured_dimension_literal() {
    for (_, source) in &SOURCES58[3..] {
        let (mut run, compiler) = super::execute(source);
        let last = matches58(&mut run).len() - 1;
        let DetailedForallConclusionArgMatchProof::NonParamEqual { goal_arg, .. } =
            matches58(&mut run)[last].as_detailed().unwrap()
        else {
            panic!()
        };
        let expected = goal_arg.ir();
        let (mut donor, _) = super::execute(SOURCES58[3].1);
        let index = if expected.to_string() == "2" { 2 } else { 1 };
        let DetailedForallConclusionArgMatchProof::NonParamEqual { goal_arg, .. } =
            matches58(&mut donor)[index].as_detailed().unwrap()
        else {
            panic!()
        };
        let wrong = goal_arg.clone();
        assert_ne!(expected, wrong.ir());
        let DetailedForallConclusionArgMatchProof::NonParamEqual { goal_arg, .. } =
            matches58(&mut run)[last].as_detailed_mut().unwrap()
        else {
            panic!()
        };
        *goal_arg = wrong;
        reject58(&run, &compiler);
    }
}
#[test]
fn matrix_graph_forall_requires_each_original_binder_identity() {
    for (_, source) in &SOURCES58[3..] {
        let (mut baseline, _) = super::execute(source);
        let count = app58(&mut baseline).forall_parameters_match_what_args.len();
        for index in 0..count {
            let (mut run, compiler) = super::execute(source);
            let DetailedForallConclusionArgMatchProof::BoundParam { param_id, .. } =
                matches58(&mut run)[index].as_detailed_mut().unwrap()
            else {
                panic!()
            };
            *param_id = IdentifierId::new(u64::MAX);
            reject58(&run, &compiler);
        }
        if count == 2 {
            let (mut run, compiler) = super::execute(source);
            let DetailedForallConclusionArgMatchProof::BoundParam { param_id, .. } =
                matches58(&mut run)[0].as_detailed().unwrap()
            else {
                panic!()
            };
            let first = *param_id;
            let DetailedForallConclusionArgMatchProof::BoundParam { param_id, .. } =
                matches58(&mut run)[1].as_detailed_mut().unwrap()
            else {
                panic!()
            };
            *param_id = first;
            reject58(&run, &compiler);
        }
    }
}
#[test]
fn matrix_graph_forall_requires_original_type_and_source_identities() {
    for (_, source) in &SOURCES58[3..] {
        for change in ["type", "source", "goal"] {
            let (mut run, compiler) = super::execute(source);
            match change {
                "type" => {
                    let p = app58(&mut run)
                        .instantiation_requirements
                        .as_detailed_mut()
                        .unwrap();
                    p.param_type_requirements.last_mut().unwrap().param_id =
                        IdentifierId::new(u64::MAX);
                }
                "source" => app58(&mut run).cite.fact_id = FactId::new(u64::MAX),
                _ => {
                    let DetailedForallConclusionArgMatchProof::ByStructure {
                        pattern,
                        goal_arg,
                        ..
                    } = app58(&mut run).arg_match_proofs[0]
                        .as_detailed_mut()
                        .unwrap()
                    else {
                        panic!()
                    };
                    *goal_arg = pattern.clone();
                }
            }
            reject58(&run, &compiler);
        }
    }
}
#[test]
fn matrix_graph_forall_preserves_argument_order_or_single_argument_identity() {
    for (_, source) in &SOURCES58[3..] {
        let (mut run, compiler) = super::execute(source);
        if app58(&mut run).forall_parameters_match_what_args.len() == 2 {
            app58(&mut run).forall_parameters_match_what_args.swap(0, 1);
        } else {
            let last = matches58(&mut run).len() - 1;
            let DetailedForallConclusionArgMatchProof::NonParamEqual { goal_arg, .. } =
                matches58(&mut run)[last].as_detailed().unwrap()
            else {
                panic!()
            };
            let wrong = goal_arg.clone();
            app58(&mut run).forall_parameters_match_what_args[0] = wrong;
        }
        reject58(&run, &compiler);
    }
}
#[test]
fn matrix_graph_requires_parent_and_last_child_original_formations() {
    for (_, source) in &SOURCES58[..3] {
        for child in [false, true] {
            let (mut run, compiler) = super::execute(source);
            let last = children58(&mut run).len() - 1;
            let equal = if child {
                super::equality_proof_mut(&mut children58(&mut run)[last])
            } else {
                equal58(&mut run)
            };
            let wd = equal.well_defined_proof.as_detailed_mut().unwrap();
            std::mem::swap(&mut wd.left, &mut wd.right);
            reject58(&run, &compiler);
        }
    }
}
#[test]
fn matrix_graph_preserves_native_arithmetic_strategy_eligibility() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_builtin_strategy_result::ArithmeticCongruenceStrategySingleStep;
    for (_, source) in &SOURCES58[..3] {
        let (mut run, compiler) = super::execute(source);
        let children = std::mem::take(children58(&mut run));
        let requirements = children
            .iter()
            .map(|p| crate::compile_to_lean::helper::source_subject(p).unwrap())
            .collect();
        equal58(&mut run).searched_proof = EqualFactSearchedProof::ByBuiltinStrategy(
            EqualitySearchProofByBuiltinStrategy::ArithmeticCongruence(
                ArithmeticCongruenceStrategySingleStep {
                    requirement_facts: requirements,
                    proof_of_requirement_facts: children,
                },
            ),
        );
        assert_eq!(
            compiler
                .compile_run(&run, "Matrix58WrongStrategy")
                .unwrap_err()
                .route,
            "ArithmeticCongruence/Constructor"
        );
    }
}
#[test]
fn matrix_graph_same_arity_preserves_distinct_operation_families() {
    let (conj, _) = super::execute(SOURCES58[0].1);
    let (plain, _) = super::execute(super::matrix_contextual_structure_tests::SOURCES54[0].1);
    let (outer, _) = super::execute(SOURCES58[1].1);
    let (add, _) = super::execute(super::matrix_entrywise_context_tests::SOURCES55[0].1);
    let left = |run: &RunLitexCodeResult| {
        let outer = super::forall_proof(&run.statement_results[0]);
        super::equality_proof(&outer.proved_then_facts[0].verify_result)
            .fact
            .left
            .clone()
    };
    for (a, b) in [(left(&conj), left(&plain)), (left(&outer), left(&add))] {
        assert!(crate::compile_to_lean::helper::arithmetic_constructor_pairs(&a, &b).is_none());
        assert!(crate::compile_to_lean::helper::arithmetic_constructor_pairs(&b, &a).is_none());
    }
}
