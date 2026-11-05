use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less_equal::LessEqualFactSearchProofByBuiltinRule;

const SOURCES: [&str; 4] = [
    r#"# An original weak order makes the corresponding owned subtraction nonnegative.
thm ordered_difference_nonnegative:
    ? forall a,b R:
        a<=b
        =>:
            0<=b-a
"#,
    r#"# Keep the original sequence call and its bound in the nonnegative difference.
thm sequence_ordered_difference_nonnegative:
    ? forall a seq(R),n N+,L R:
        L<=a(n)
        =>:
            0<=a(n)-L
"#,
    r#"# An original weak order makes its owned forward difference nonpositive.
thm ordered_difference_nonpositive:
    ? forall a,b R:
        a<=b
        =>:
            a-b<=0
"#,
    r#"# An original nonpositive difference implies the corresponding weak order.
thm nonpositive_difference_implies_order:
    ? forall a,b R:
        a-b<=0
        =>:
            a<=b
"#,
];

fn body(
    run: &mut RunLitexCodeResult,
) -> &mut crate::execute::execute_def_thm_stmt::ExecDefThmForallProof {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(named),
    )) = &mut run.statement_results[0]
    else {
        panic!("named theorem")
    };
    let ExecDefThmBodyProof::Forall(body) = &mut named.body else {
        panic!("forall body")
    };
    body
}

fn premise(
    proof: &mut VerifyAtomicExceptEqualityFactSuccess,
) -> &mut AtomicExceptEqualityFactKnownProof {
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(rule),
    ) = &mut proof.searched_proof
    else {
        panic!("original difference selection")
    };
    match rule {
        LessEqualFactSearchProofByBuiltinRule::NonnegDifferenceFromLessEqual(p) => {
            &mut p.premise_proof
        }
        LessEqualFactSearchProofByBuiltinRule::NonpositiveDifferenceFromLessEqual(p) => {
            &mut p.premise_proof
        }
        LessEqualFactSearchProofByBuiltinRule::LessEqualFromNonpositiveDifference(p) => {
            &mut p.premise_proof
        }
        _ => panic!("selected difference rule"),
    }
}

#[test]
fn nonnegative_difference_replays_original_weak_citation_and_owned_subtraction() {
    for source in SOURCES {
        let (mut run, compiler) = super::execute(source);
        let universal = body(&mut run);
        let id = universal.assumed_dom_facts[0]
            .store_and_infer
            .primary_fact_id();
        let proof = super::atomic_proof_mut(&mut universal.conclusion_proofs[0]);
        assert_eq!(premise(proof).cite_fact_id(), Some(id));
        let lean = compiler
            .compile_run(&run, "nonnegative_difference")
            .unwrap();
        assert!(lean.contains(
            if source.contains("thm nonpositive_difference_implies_order") {
                "Litex.subNonpositiveToLe "
            } else if source.contains("thm ordered_difference_nonpositive") {
                "Litex.subNonpositive "
            } else {
                "Litex.subNonnegative "
            }
        ));
        assert!(lean.contains(&format!("h_{}", id.value())));
        assert_eq!(
            lean,
            compiler
                .compile_run(&run, "nonnegative_difference")
                .unwrap()
        );
    }
}

#[test]
fn nonnegative_difference_rejects_changed_operands_strength_and_zero() {
    for source in SOURCES {
        for change in 0..4 {
            let (mut run, compiler) = super::execute(source);
            let universal = body(&mut run);
            let proof = super::atomic_proof_mut(&mut universal.conclusion_proofs[0]);
            if change == 3 {
                let AtomicFact::LessEqualFact(goal) = &mut proof.fact else {
                    panic!()
                };
                goal.left = super::number_object("1");
            } else {
                let child = premise(proof);
                let AtomicFact::LessEqualFact(order) = &mut child.fact else {
                    panic!()
                };
                match change {
                    0 => std::mem::swap(&mut order.left, &mut order.right),
                    1 => order.right = super::number_object("17"),
                    2 => {
                        child.fact = LessFact {
                            fact_id: order.fact_id,
                            left: order.left.clone(),
                            right: order.right.clone(),
                            line_file: order.line_file.clone(),
                        }
                        .into()
                    }
                    _ => unreachable!(),
                }
            }
            assert!(compiler
                .compile_run(&run, "invalid_difference_subject")
                .is_err());
        }
    }
}

#[test]
fn nonnegative_difference_rejects_future_citation_and_missing_domain() {
    for source in SOURCES {
        for missing_domain in [false, true] {
            let (mut run, compiler) = super::execute(source);
            let universal = body(&mut run);
            let future = match &universal.conclusion_proofs[0] {
                VerifyFactResult::AtomicExceptEquality(p) => match p.as_ref() {
                    VerifyAtomicExceptEqualityFactResult::Success(p) => p.fact.fact_id(),
                    _ => panic!(),
                },
                _ => panic!(),
            };
            let proof = super::atomic_proof_mut(&mut universal.conclusion_proofs[0]);
            if missing_domain {
                proof
                    .well_defined_proof
                    .as_detailed_mut()
                    .unwrap()
                    .predicate_domain = PredicateDomainProof::ByRequirements(Vec::new());
            } else {
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                    premise(proof).searched_proof.as_mut()
                else {
                    panic!()
                };
                cite.cite_fact_id = future;
            }
            assert!(compiler
                .compile_run(&run, "invalid_difference_evidence")
                .is_err());
        }
    }
}

#[test]
fn nonnegative_difference_source_requires_original_order() {
    let source = "forall a,b R:\n    0<=b-a\n";
    let command = parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
    assert!(
        !Runtime::new(command)
            .run_litex_code(source)
            .unwrap()
            .success
    );
}
