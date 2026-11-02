use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    DetailedForallConclusionArgMatchProof, ForallConclusionArgMatchProof,
};
use crate::prelude::*;
pub(super) const SOURCES59:&[(&str,&str)]=&[
("zero_all_operands","forall sc59a_m,sc59a_n,sc59a_p,sc59a_q N:\n    sc59a_m=sc59a_p\n    sc59a_n=sc59a_q\n    =>:\n        zero_matrix(sc59a_m,sc59a_n)=zero_matrix(sc59a_p,sc59a_q)\n"),
("identity_order","forall sc59b_n,sc59b_p N:\n    sc59b_n=sc59b_p\n    =>:\n        identity_matrix(sc59b_n)=identity_matrix(sc59b_p)\n"),
("forall_zero","forall sc59c_n N,sc59c_P fn(sc59c_j N) matrix(C,2,3):\n    sc59c_n=2\n    forall sc59c_k N:\n        sc59c_k=2\n        =>:\n            zero_matrix(sc59c_k,3)=sc59c_P(sc59c_k)\n    =>:\n        zero_matrix(sc59c_n,3)=sc59c_P(sc59c_n)\n"),
("forall_identity","forall sc59d_n N,sc59d_P fn(sc59d_j N) matrix(C,2,2):\n    sc59d_n=2\n    forall sc59d_k N:\n        sc59d_k=2\n        =>:\n            identity_matrix(sc59d_k)=sc59d_P(sc59d_k)\n    =>:\n        identity_matrix(sc59d_n)=sc59d_P(sc59d_n)\n")];
fn operands59(object: &Obj) -> Vec<&Obj> {
    match object {
        Obj::MatrixOperator(MatrixOperator::ZeroMatrix(a)) => vec![&a.rows, &a.cols],
        Obj::MatrixOperator(MatrixOperator::IdentityMatrix(a)) => vec![&a.order],
        _ => panic!("original59 constant matrix constructor"),
    }
}
fn walk59(
    proof: &ForallConclusionArgMatchProof,
    binder: IdentifierId,
    argument: &Obj,
    stats: &mut [usize; 4],
    name: &str,
) {
    match proof.as_detailed().unwrap() {
        DetailedForallConclusionArgMatchProof::BoundParam {
            param_id,
            pattern,
            goal_arg,
        } => {
            assert_eq!(*param_id, binder);
            assert_eq!(goal_arg.ir(), argument.ir());
            stats[0] += 1;
            eprintln!(
                "ORIGINAL59 {name} bound:{} pattern:{} goal:{}",
                param_id.value(),
                pattern.ir(),
                goal_arg.ir()
            );
        }
        DetailedForallConclusionArgMatchProof::ReboundParamEqual {
            param_id,
            previous,
            goal_arg,
            equal,
        } => {
            assert_eq!(*param_id, binder);
            assert_eq!(previous.ir(), argument.ir());
            assert_eq!(equal.equal_fact.left.ir(), previous.ir());
            assert_eq!(equal.equal_fact.right.ir(), goal_arg.ir());
            stats[1] += 1;
            eprintln!(
                "ORIGINAL59 {name} rebound:{} previous:{} goal:{}",
                param_id.value(),
                previous.ir(),
                goal_arg.ir()
            );
        }
        DetailedForallConclusionArgMatchProof::NonParamEqual {
            pattern,
            pattern_after_subst,
            goal_arg,
            equal,
        } => {
            assert_eq!(equal.equal_fact.left.ir(), pattern_after_subst.ir());
            assert_eq!(equal.equal_fact.right.ir(), goal_arg.ir());
            stats[2] += 1;
            eprintln!(
                "ORIGINAL59 {name} fixed:{} after:{} goal:{}",
                pattern.ir(),
                pattern_after_subst.ir(),
                goal_arg.ir()
            );
        }
        DetailedForallConclusionArgMatchProof::ByStructure {
            pattern,
            goal_arg,
            child_matches,
        } => {
            stats[3] += 1;
            eprintln!(
                "ORIGINAL59 {name} structure:{} goal:{} children:{}",
                pattern.ir(),
                goal_arg.ir(),
                child_matches.len()
            );
            for child in child_matches {
                walk59(child, binder, argument, stats, name);
            }
        }
    }
}
#[test]
fn matrix_constant_original_ordered_operands_audit() {
    for (name, source) in &SOURCES59[..2] {
        let (run, compiler) = super::execute(source);
        let outer = super::forall_proof(&run.statement_results[0]);
        let equal = super::equality_proof(&outer.proved_then_facts[0].verify_result);
        let EqualFactSearchedProof::ByMatchingOneArgByOne(p) = &equal.searched_proof else {
            panic!("original direct route:{name}")
        };
        let a = operands59(&equal.fact.left);
        let b = operands59(&equal.fact.right);
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
                panic!("original ordered citation")
            };
            assert_eq!(path.path.len(), 1);
            assert_eq!(path.path[0].2, outer.fact.dom_facts[index].fact_id());
            eprintln!(
                "ORIGINAL59 {name} direct operand:{index} left:{} right:{} cite:{}",
                child.fact.left.ir(),
                child.fact.right.ir(),
                path.path[0].2.value()
            );
        }
        let compiled = compiler
            .compile_run(&run, "Matrix59OriginalDirect")
            .unwrap();
        assert!(compiled.contains("M.standard .real"));
        assert!(compiled.contains(if name.contains("identity") {
            "matrixIdentityBody"
        } else {
            "M.number 0"
        }));
    }
}
#[test]
fn matrix_constant_original_forall_and_guard_audit() {
    for (name, source) in &SOURCES59[2..] {
        let (run, compiler) = super::execute(source);
        let outer = super::forall_proof(&run.statement_results[0]);
        let equal = super::equality_proof(&outer.proved_then_facts[0].verify_result);
        let EqualFactSearchedProof::ByKnownForallFact(p) = &equal.searched_proof else {
            panic!("original known forall:{name}")
        };
        let p = p.as_detailed().unwrap();
        let Fact::ForallFact(cited) = &outer.fact.dom_facts[1] else {
            panic!()
        };
        assert_eq!(p.cite.fact_id, cited.fact_id);
        let ids: Vec<_> = cited
            .typed_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(|p| p.id))
            .collect();
        assert_eq!(ids.len(), 1);
        assert_eq!(p.arg_match_proofs.len(), 2);
        assert_eq!(p.forall_parameters_match_what_args.len(), 1);
        let DetailedForallConclusionArgMatchProof::ByStructure {
            pattern,
            goal_arg,
            child_matches,
        } = p.arg_match_proofs[0].as_detailed().unwrap()
        else {
            panic!("original operator structure")
        };
        let a = operands59(pattern);
        let b = operands59(goal_arg);
        assert_eq!(child_matches.len(), a.len());
        let DetailedForallConclusionArgMatchProof::BoundParam {
            param_id,
            pattern,
            goal_arg,
        } = child_matches[0].as_detailed().unwrap()
        else {
            panic!()
        };
        assert_eq!(*param_id, ids[0]);
        assert_eq!(pattern.ir(), a[0].ir());
        assert_eq!(goal_arg.ir(), b[0].ir());
        assert_eq!(p.forall_parameters_match_what_args[0].ir(), b[0].ir());
        if name.ends_with("zero") {
            let DetailedForallConclusionArgMatchProof::NonParamEqual {
                pattern,
                pattern_after_subst,
                goal_arg,
                ..
            } = child_matches[1].as_detailed().unwrap()
            else {
                panic!()
            };
            assert_eq!(pattern.ir(), a[1].ir());
            assert_eq!(pattern_after_subst.ir(), a[1].ir());
            assert_eq!(goal_arg.ir(), b[1].ir());
            assert_eq!(goal_arg.ir().to_string(), "3");
        }
        let mut stats = [0; 4];
        for child in &p.arg_match_proofs {
            walk59(
                child,
                ids[0],
                &p.forall_parameters_match_what_args[0],
                &mut stats,
                name,
            );
        }
        assert_eq!(stats[0], 1);
        assert_eq!(stats[1], 1);
        let requirements = p.instantiation_requirements.as_detailed().unwrap();
        assert_eq!(requirements.param_type_requirements.len(), 1);
        assert_eq!(requirements.param_type_requirements[0].param_id, ids[0]);
        assert_eq!(requirements.dom_facts.len(), 1);
        assert_eq!(requirements.proof_of_dom_facts.len(), 1);
        assert_eq!(
            crate::compile_to_lean::helper::source_subject(&requirements.proof_of_dom_facts[0])
                .unwrap(),
            requirements.dom_facts[0]
        );
        let guard = super::equality_proof(&requirements.proof_of_dom_facts[0]);
        let Fact::AtomicFact(AtomicFact::EqualFact(expected)) = &outer.fact.dom_facts[0] else {
            panic!()
        };
        assert_eq!(guard.fact.left.ir(), expected.left.ir());
        assert_eq!(guard.fact.right.ir(), expected.right.ir());
        let EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
        ) = &guard.searched_proof
        else {
            panic!("original guard citation")
        };
        assert_eq!(path.path.len(), 1);
        assert_eq!(path.path[0].2, expected.fact_id);
        eprintln!(
            "ORIGINAL59 {name} source:{} binder:{} type:{} guard_cite:{}",
            p.cite.fact_id.value(),
            ids[0].value(),
            requirements.param_type_requirements[0].param_id.value(),
            path.path[0].2.value()
        );
        let compiled = compiler
            .compile_run(&run, "Matrix59OriginalForall")
            .unwrap();
        assert!(compiled.contains("M.standard .real"));
        assert!(compiled.contains(if name.contains("identity") {
            "matrixIdentityBody"
        } else {
            "M.number 0"
        }));
    }
}

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedSearchProofByKnownForallFact;
fn equal59(run: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    let outer = super::forall_proof_mut(&mut run.statement_results[0]);
    super::equality_proof_mut(&mut outer.proved_then_facts[0].verify_result)
}
fn children59(run: &mut RunLitexCodeResult) -> &mut Vec<VerifyFactResult> {
    let EqualFactSearchedProof::ByMatchingOneArgByOne(p) = &mut equal59(run).searched_proof else {
        panic!()
    };
    &mut p.corresponding_arg_equal_proofs
}
fn app59(run: &mut RunLitexCodeResult) -> &mut DetailedSearchProofByKnownForallFact {
    let EqualFactSearchedProof::ByKnownForallFact(p) = &mut equal59(run).searched_proof else {
        panic!()
    };
    p.as_detailed_mut().unwrap()
}
fn matches59(run: &mut RunLitexCodeResult) -> &mut Vec<ForallConclusionArgMatchProof> {
    let DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } =
        app59(run).arg_match_proofs[0].as_detailed_mut().unwrap()
    else {
        panic!()
    };
    child_matches
}
fn rebound59(run: &mut RunLitexCodeResult) -> &mut DetailedForallConclusionArgMatchProof {
    let DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } =
        app59(run).arg_match_proofs[1].as_detailed_mut().unwrap()
    else {
        panic!()
    };
    child_matches[0].as_detailed_mut().unwrap()
}
fn guard59(run: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    super::equality_proof_mut(
        &mut app59(run)
            .instantiation_requirements
            .as_detailed_mut()
            .unwrap()
            .proof_of_dom_facts[0],
    )
}
fn reject59(run: &RunLitexCodeResult, compiler: &crate::compile_to_lean::LitexToLeanCompiler) {
    compiler
        .compile_run(run, "Matrix59ChangedEvidence")
        .expect_err("changed original certificate must reject");
}
#[test]
fn matrix_constant_requires_all_original_operands() {
    for (_, source) in &SOURCES59[..2] {
        for extra in [false, true] {
            let (mut run, compiler) = super::execute(source);
            if extra {
                let (mut donor, _) = super::execute(source);
                children59(&mut run).push(children59(&mut donor).pop().unwrap());
            } else {
                children59(&mut run).pop();
            }
            assert_eq!(
                compiler
                    .compile_run(&run, "Matrix59Arity")
                    .unwrap_err()
                    .route,
                "ArithmeticCongruence/Children"
            );
        }
    }
}
#[test]
fn matrix_constant_zero_preserves_row_column_order() {
    let (mut run, compiler) = super::execute(SOURCES59[0].1);
    children59(&mut run).swap(0, 1);
    assert_eq!(
        compiler
            .compile_run(&run, "Matrix59Order")
            .unwrap_err()
            .route,
        "ArithmeticCongruence/ChildSubject"
    );
}
#[test]
fn matrix_constant_requires_each_original_subject() {
    for i in 0..2 {
        let (mut run, compiler) = super::execute(SOURCES59[0].1);
        let (mut donor, _) = super::execute(SOURCES59[0].1);
        children59(&mut run)[i] = children59(&mut donor).remove(1 - i);
        assert_eq!(
            compiler
                .compile_run(&run, "Matrix59ZeroSubject")
                .unwrap_err()
                .route,
            "ArithmeticCongruence/ChildSubject"
        );
    }
    let source = format!("{}        sc59b_p=sc59b_n\n", SOURCES59[1].1);
    let (mut run, compiler) = super::execute(&source);
    compiler
        .compile_run(&run, "Matrix59IdentitySubjectPristine")
        .unwrap();
    let (mut donor, _) = super::execute(&source);
    let wrong = super::forall_proof_mut(&mut donor.statement_results[0])
        .proved_then_facts
        .pop()
        .unwrap()
        .verify_result;
    children59(&mut run)[0] = wrong;
    assert_eq!(
        compiler
            .compile_run(&run, "Matrix59IdentitySubject")
            .unwrap_err()
            .route,
        "ArithmeticCongruence/ChildSubject"
    );
}

#[test]
fn matrix_constant_rejects_foreign_and_self_citations() {
    for (_, source) in &SOURCES59[..2] {
        for own in [false, true] {
            let (mut run, compiler) = super::execute(source);
            let last = children59(&mut run).len() - 1;
            let child = super::equality_proof_mut(&mut children59(&mut run)[last]);
            let id = child.fact.fact_id;
            let EqualFactSearchedProof::ByEquivalenceClass(
                EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
            ) = &mut child.searched_proof
            else {
                panic!()
            };
            assert_ne!(path.path[0].2, id);
            path.path[0].2 = if own { id } else { FactId::new(u64::MAX) };
            reject59(&run, &compiler);
        }
    }
}
#[test]
fn matrix_constant_rejects_same_endpoints_from_future_fact() {
    for (name, source) in &SOURCES59[..2] {
        let later = if *name == "zero_all_operands" {
            "sc59a_n=sc59a_q"
        } else {
            "sc59b_n=sc59b_p"
        };
        let source = format!("{}        {}\n", source, later);
        let (mut run, compiler) = super::execute(&source);
        compiler
            .compile_run(&run, "Matrix59FuturePristine")
            .unwrap();
        let outer = super::forall_proof(&run.statement_results[0]);
        assert_eq!(outer.proved_then_facts.len(), 2);
        let future = super::equality_proof(&outer.proved_then_facts[1].verify_result);
        let id = future.fact.fact_id;
        let endpoints = (future.fact.left.ir(), future.fact.right.ir());
        let last = children59(&mut run).len() - 1;
        let child = super::equality_proof_mut(&mut children59(&mut run)[last]);
        assert_eq!((child.fact.left.ir(), child.fact.right.ir()), endpoints);
        assert_ne!(child.fact.fact_id, id);
        let EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
        ) = &mut child.searched_proof
        else {
            panic!()
        };
        path.path[0].2 = id;
        reject59(&run, &compiler);
    }
}
#[test]
fn matrix_constant_rejects_sibling_dimension_citation() {
    for (_, source) in &SOURCES59[..2] {
        let sibling = source
            .replace("sc59a_", "sc59x_")
            .replace("sc59b_", "sc59y_");
        let (mut run, compiler) = super::execute(&format!("{}{}", source, sibling));
        compiler
            .compile_run(&run, "Matrix59SiblingPristine")
            .unwrap();
        let last = children59(&mut run).len() - 1;
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
        let child = super::equality_proof_mut(&mut children59(&mut run)[last]);
        let EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
        ) = &mut child.searched_proof
        else {
            panic!()
        };
        path.path[0].2 = id;
        reject59(&run, &compiler);
    }
}
#[test]
fn matrix_constant_requires_parent_and_child_formations() {
    for (_, source) in &SOURCES59[..2] {
        for child in [false, true] {
            let (mut run, compiler) = super::execute(source);
            let last = children59(&mut run).len() - 1;
            let equal = if child {
                super::equality_proof_mut(&mut children59(&mut run)[last])
            } else {
                equal59(&mut run)
            };
            let wd = equal.well_defined_proof.as_detailed_mut().unwrap();
            std::mem::swap(&mut wd.left, &mut wd.right);
            reject59(&run, &compiler);
        }
    }
}
#[test]
fn matrix_constant_forall_requires_captured_structure_arity() {
    for (_, source) in &SOURCES59[2..] {
        for extra in [false, true] {
            let (mut run, compiler) = super::execute(source);
            if extra {
                let (mut donor, _) = super::execute(source);
                matches59(&mut run).push(matches59(&mut donor).pop().unwrap());
            } else {
                matches59(&mut run).pop();
            }
            assert_eq!(
                compiler
                    .compile_run(&run, "Matrix59MatchArity")
                    .unwrap_err()
                    .route,
                "CompoundKnown/StructureArity"
            );
        }
    }
}
#[test]
fn matrix_constant_forall_zero_requires_original_fixed_column() {
    let (mut run, compiler) = super::execute(SOURCES59[2].1);
    let wrong = guard59(&mut run).fact.right.clone();
    let DetailedForallConclusionArgMatchProof::NonParamEqual { goal_arg, .. } =
        matches59(&mut run)[1].as_detailed_mut().unwrap()
    else {
        panic!()
    };
    assert_ne!(goal_arg.ir(), wrong.ir());
    *goal_arg = wrong;
    reject59(&run, &compiler);
}
#[test]
fn matrix_constant_forall_preserves_source_binder_type_and_argument_identities() {
    for (_, source) in &SOURCES59[2..] {
        for change in ["source", "binder", "type", "argument"] {
            let (mut run, compiler) = super::execute(source);
            match change {
                "source" => app59(&mut run).cite.fact_id = FactId::new(u64::MAX),
                "binder" => {
                    let DetailedForallConclusionArgMatchProof::BoundParam { param_id, .. } =
                        matches59(&mut run)[0].as_detailed_mut().unwrap()
                    else {
                        panic!()
                    };
                    *param_id = IdentifierId::new(u64::MAX);
                }
                "type" => {
                    app59(&mut run)
                        .instantiation_requirements
                        .as_detailed_mut()
                        .unwrap()
                        .param_type_requirements[0]
                        .param_id = IdentifierId::new(u64::MAX)
                }
                _ => {
                    let wrong = guard59(&mut run).fact.right.clone();
                    app59(&mut run).forall_parameters_match_what_args[0] = wrong;
                }
            }
            reject59(&run, &compiler);
        }
    }
}
#[test]
fn matrix_constant_forall_requires_original_rebound_evidence() {
    for (_, source) in &SOURCES59[2..] {
        for change in ["binder", "previous", "subject"] {
            let (mut run, compiler) = super::execute(source);
            let wrong = guard59(&mut run).fact.right.clone();
            let DetailedForallConclusionArgMatchProof::ReboundParamEqual {
                param_id,
                previous,
                equal,
                ..
            } = rebound59(&mut run)
            else {
                panic!()
            };
            match change {
                "binder" => *param_id = IdentifierId::new(u64::MAX),
                "previous" => *previous = wrong,
                _ => equal.equal_fact.left = wrong,
            };
            reject59(&run, &compiler);
        }
    }
}
#[test]
fn matrix_constant_forall_requires_original_guard_counts_and_subject() {
    for (_, source) in &SOURCES59[2..] {
        for change in ["facts", "proofs", "extra", "subject"] {
            let (mut run, compiler) = super::execute(source);
            if change == "subject" {
                let (mut donor, _) = super::execute(SOURCES59[0].1);
                let wrong = children59(&mut donor).pop().unwrap();
                app59(&mut run)
                    .instantiation_requirements
                    .as_detailed_mut()
                    .unwrap()
                    .proof_of_dom_facts[0] = wrong;
            } else {
                let req = app59(&mut run)
                    .instantiation_requirements
                    .as_detailed_mut()
                    .unwrap();
                match change {
                    "facts" => req.dom_facts.clear(),
                    "proofs" => req.proof_of_dom_facts.clear(),
                    _ => {
                        let added = req.dom_facts[0].clone();
                        req.dom_facts.push(added);
                    }
                }
            }
            reject59(&run, &compiler);
        }
    }
}
#[test]
fn matrix_constant_forall_rejects_foreign_self_and_future_guard_citations() {
    for (name, source) in &SOURCES59[2..] {
        for own in [false, true] {
            let (mut run, compiler) = super::execute(source);
            let guard = guard59(&mut run);
            let id = guard.fact.fact_id;
            let EqualFactSearchedProof::ByEquivalenceClass(
                EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
            ) = &mut guard.searched_proof
            else {
                panic!()
            };
            assert_ne!(path.path[0].2, id);
            path.path[0].2 = if own { id } else { FactId::new(u64::MAX) };
            reject59(&run, &compiler);
        }
        let later = if *name == "forall_zero" {
            "sc59c_n=2"
        } else {
            "sc59d_n=2"
        };
        let source = format!("{}        {}\n", source, later);
        let (mut run, compiler) = super::execute(&source);
        compiler
            .compile_run(&run, "Matrix59GuardFuturePristine")
            .unwrap();
        let outer = super::forall_proof(&run.statement_results[0]);
        assert_eq!(outer.proved_then_facts.len(), 2);
        let future = super::equality_proof(&outer.proved_then_facts[1].verify_result);
        let id = future.fact.fact_id;
        let endpoints = (future.fact.left.ir(), future.fact.right.ir());
        let guard = guard59(&mut run);
        assert_eq!((guard.fact.left.ir(), guard.fact.right.ir()), endpoints);
        assert_ne!(guard.fact.fact_id, id);
        let EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
        ) = &mut guard.searched_proof
        else {
            panic!()
        };
        path.path[0].2 = id;
        reject59(&run, &compiler);
    }
}
#[test]
fn matrix_constant_preserves_native_arithmetic_strategy_eligibility() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_builtin_strategy_result::ArithmeticCongruenceStrategySingleStep;
    for (_, source) in &SOURCES59[..2] {
        let (mut run, compiler) = super::execute(source);
        let children = std::mem::take(children59(&mut run));
        let requirements = children
            .iter()
            .map(|p| crate::compile_to_lean::helper::source_subject(p).unwrap())
            .collect();
        equal59(&mut run).searched_proof = EqualFactSearchedProof::ByBuiltinStrategy(
            EqualitySearchProofByBuiltinStrategy::ArithmeticCongruence(
                ArithmeticCongruenceStrategySingleStep {
                    requirement_facts: requirements,
                    proof_of_requirement_facts: children,
                },
            ),
        );
        assert_eq!(
            compiler
                .compile_run(&run, "Matrix59WrongStrategy")
                .unwrap_err()
                .route,
            "ArithmeticCongruence/Constructor"
        );
    }
}
#[test]
fn matrix_constant_preserves_distinct_operation_contracts() {
    let (zero, _) = super::execute(SOURCES59[0].1);
    let (identity, _) = super::execute(SOURCES59[1].1);
    let (diagonal, _) = super::execute(super::matrix_graph_family_context_tests::SOURCES58[2].1);
    let left = |run: &RunLitexCodeResult| {
        let outer = super::forall_proof(&run.statement_results[0]);
        super::equality_proof(&outer.proved_then_facts[0].verify_result)
            .fact
            .left
            .clone()
    };
    for (a, b) in [
        (left(&zero), left(&diagonal)),
        (left(&zero), left(&identity)),
    ] {
        assert!(crate::compile_to_lean::helper::arithmetic_constructor_pairs(&a, &b).is_none());
        assert!(crate::compile_to_lean::helper::arithmetic_constructor_pairs(&b, &a).is_none());
    }
}
