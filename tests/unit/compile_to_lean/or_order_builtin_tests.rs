use crate::prelude::*;

const CASES: [(&str, &str); 6] = [
    (
        include_str!("../../../lean/examples/real_trichotomy_equal_first/statement.lit"),
        "realTrichotomyValue",
    ),
    (
        include_str!("../../../lean/examples/real_trichotomy_less_first/statement.lit"),
        "realTrichotomyValue",
    ),
    (
        include_str!("../../../lean/examples/real_trichotomy_greater_first/statement.lit"),
        "realTrichotomyValue",
    ),
    (
        include_str!("../../../lean/examples/real_weak_totality/statement.lit"),
        "realWeakTotalValue",
    ),
    (
        include_str!("../../../lean/examples/natural_zero_or_at_least_one/statement.lit"),
        "naturalZeroOrAtLeastOneValue",
    ),
    (
        include_str!("../../../lean/examples/weak_bound_equality_or_strict/statement.lit"),
        "leEqOrLt",
    ),
];
pub(super) fn target(run: &mut RunLitexCodeResult) -> &mut VerifyOrFactSuccess {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(named),
    )) = &mut run.statement_results[0]
    else {
        panic!("named theorem")
    };
    let ExecDefThmBodyProof::Forall(body) = &mut named.body else {
        panic!("forall body")
    };
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(step)) = &mut body.proof_steps[0] else {
        panic!("original Or verification")
    };
    let VerifyFactResult::OrFact(proof) = &mut step.verify_result else {
        panic!("original Or result")
    };
    let VerifyOrFactResult::Success(proof) = proof.as_mut() else {
        panic!("successful Or result")
    };
    proof
}
fn child(proof: &mut VerifyOrFactSuccess, index: usize) -> &mut VerifyFactResult {
    let OrFactSearchedProof::ByBuiltinRule(rule) = &mut proof.searched_proof else {
        panic!("selected builtin route")
    };
    match rule {
        OrFactSearchProofByBuiltinRule::RealLineTrichotomyEqLessGreater(p) => {
            if index == 0 {
                &mut p.left_in_r
            } else {
                &mut p.right_in_r
            }
        }
        OrFactSearchProofByBuiltinRule::RealLineTrichotomyLessEqGreater(p) => {
            if index == 0 {
                &mut p.left_in_r
            } else {
                &mut p.right_in_r
            }
        }
        OrFactSearchProofByBuiltinRule::RealLineTrichotomyGreaterEqLess(p) => {
            if index == 0 {
                &mut p.left_in_r
            } else {
                &mut p.right_in_r
            }
        }
        OrFactSearchProofByBuiltinRule::WeakOrderLeOrGe(p) => {
            if index == 0 {
                &mut p.left_in_r
            } else {
                &mut p.right_in_r
            }
        }
        OrFactSearchProofByBuiltinRule::NaturalZeroOrAtLeastOne(p) => &mut p.n_in_n,
        OrFactSearchProofByBuiltinRule::EqualityPlusStrictCoversWeak(p) => &mut p.weak_bound,
        _ => panic!("exact supported builtin route"),
    }
}
#[test]
fn or_order_replays_each_original_selected_variant_and_is_deterministic() {
    for (index, (source, law)) in CASES.into_iter().enumerate() {
        let (mut run, compiler) = super::execute(source);
        let p = target(&mut run);
        let OrFactSearchedProof::ByBuiltinRule(selected) = &p.searched_proof else {
            panic!()
        };
        assert!(matches!(
            (index, selected),
            (
                0,
                OrFactSearchProofByBuiltinRule::RealLineTrichotomyEqLessGreater(_)
            ) | (
                1,
                OrFactSearchProofByBuiltinRule::RealLineTrichotomyLessEqGreater(_)
            ) | (
                2,
                OrFactSearchProofByBuiltinRule::RealLineTrichotomyGreaterEqLess(_)
            ) | (3, OrFactSearchProofByBuiltinRule::WeakOrderLeOrGe(_))
                | (
                    4,
                    OrFactSearchProofByBuiltinRule::NaturalZeroOrAtLeastOne(_)
                )
                | (
                    5,
                    OrFactSearchProofByBuiltinRule::EqualityPlusStrictCoversWeak(_)
                )
        ));
        let output = compiler.compile_run(&run, "or_order").unwrap();
        assert!(output.contains(&format!("Litex.{law}")));
        assert_eq!(output, compiler.compile_run(&run, "or_order").unwrap());
    }
}
#[test]
fn or_order_requires_every_original_branch_wd() {
    for (source, _) in CASES {
        let (mut run, compiler) = super::execute(source);
        target(&mut run)
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .branches
            .pop();
        compiler
            .compile_run(&run, "wd")
            .expect_err("each original Or branch must be formed");
    }
}
#[test]
fn or_order_preserves_original_member_carriers_and_citation_visibility() {
    for (index, (source, _)) in CASES.into_iter().enumerate() {
        for slot in 0..if index < 4 { 2 } else { 1 } {
            for future in [false, true] {
                let (mut run, compiler) = super::execute(source);
                let p = target(&mut run);
                let id = p.fact.fact_id;
                let p = super::atomic_proof_mut(child(p, slot));
                if future {
                    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                        &mut p.searched_proof
                    else {
                        panic!("original member or weak-bound citation")
                    };
                    cite.cite_fact_id = id;
                } else if let AtomicFact::InFact(f) = &mut p.fact {
                    f.set = Obj::StandardSet(StandardSet::C);
                } else {
                    let AtomicFact::LessEqualFact(f) = &mut p.fact else {
                        panic!()
                    };
                    std::mem::swap(&mut f.left, &mut f.right);
                }
                compiler
                    .compile_run(&run, "child")
                    .expect_err("preserve exact original domain/bound and earlier citation");
            }
        }
    }
}
#[test]
fn or_order_preserves_rigid_branch_order_and_selected_subjects() {
    for (index, (source, _)) in CASES.into_iter().enumerate() {
        let (mut run, compiler) = super::execute(source);
        let p = target(&mut run);
        let OrFactSearchedProof::ByBuiltinRule(rule) = &mut p.searched_proof else {
            panic!()
        };
        if index < 3 {
            p.fact.facts.swap(0, 2);
        } else {
            match rule {
                OrFactSearchProofByBuiltinRule::WeakOrderLeOrGe(p) => {
                    p.left = Obj::Literal(Literal::Number(Number::new("0".into())))
                }
                OrFactSearchProofByBuiltinRule::NaturalZeroOrAtLeastOne(p) => {
                    p.n = Obj::Literal(Literal::Number(Number::new("0".into())))
                }
                OrFactSearchProofByBuiltinRule::EqualityPlusStrictCoversWeak(p) => {
                    p.left = Obj::Literal(Literal::Number(Number::new("0".into())))
                }
                _ => panic!(),
            }
        }
        compiler
            .compile_run(&run, "subject")
            .expect_err("retain rigid selected order and subjects");
    }
}
#[test]
fn or_order_replays_supported_swaps_duals_and_commuted_equalities() {
    for source in [
        CASES[0].0.replace("a=b or a<b or a>b", "b=a or a<b or a>b"),
        CASES[3].0.replace("a<=b or a>=b", "a>=b or a<=b"),
        CASES[5].0.replace("a=b or a<b", "a<b or b=a"),
        CASES[5]
            .0
            .replace("a<=b", "a>=b")
            .replace("a=b or a<b", "b=a or a>b"),
    ] {
        let (run, compiler) = super::execute(&source);
        compiler.compile_run(&run, "permutation").unwrap();
    }
}

#[test]
fn absolute_sign_split_preserves_selected_argument_orientations_and_constructor_wd() {
    for source in [
        include_str!("../../../lean/examples/absolute_sign_split/statement.lit"),
        include_str!("../../../lean/examples/absolute_sign_split_commuted/statement.lit"),
    ] {
        let (mut run, compiler) = super::execute(source);
        assert!(matches!(
            &target(&mut run).searched_proof,
            OrFactSearchedProof::ByBuiltinRule(OrFactSearchProofByBuiltinRule::AbsSignSplit(_))
        ));
        assert!(compiler
            .compile_run(&run, "abs_split")
            .unwrap()
            .contains("Litex.absoluteSignSplitValue"));
        for mutation in ["argument", "wd", "coverage"] {
            let (mut run, compiler) = super::execute(source);
            let p = target(&mut run);
            match mutation {
                "wd" => p
                    .well_defined_proof
                    .as_detailed_mut()
                    .unwrap()
                    .branches
                    .clear(),
                "argument" => {
                    let OrFactSearchedProof::ByBuiltinRule(
                        OrFactSearchProofByBuiltinRule::AbsSignSplit(p),
                    ) = &mut p.searched_proof
                    else {
                        panic!()
                    };
                    p.arg = Obj::Literal(Literal::Number(Number::new("0".into())));
                }
                _ => p.fact.facts[1] = p.fact.facts[0].clone(),
            }
            compiler.compile_run(&run, mutation).expect_err(
                "retain exact selected absolute argument, both alternatives and their original WD",
            );
        }
    }
}

#[test]
fn integer_discrete_split_replays_integer_children_duals_and_swapped_branches() {
    for source in [
        include_str!("../../../lean/examples/integer_discrete_successor/statement.lit"),
        include_str!("../../../lean/examples/integer_discrete_predecessor/statement.lit"),
    ] {
        for source in [
            source.to_string(),
            source
                .replace("x<=n or x>=n+1", "x>=n+1 or x<=n")
                .replace("x>=n or x<=n-1", "x<=n-1 or x>=n"),
        ] {
            let (mut run, compiler) = super::execute(&source);
            assert!(matches!(
                &target(&mut run).searched_proof,
                OrFactSearchedProof::ByBuiltinRule(
                    OrFactSearchProofByBuiltinRule::IntegerDiscreteSplit(_)
                )
            ));
            let output = compiler.compile_run(&run, "discrete").unwrap();
            assert!(output.contains("Litex.integerDiscrete"));
            assert_eq!(output, compiler.compile_run(&run, "discrete").unwrap());
        }
        for mutation in [
            "wd", "subject", "carrier0", "carrier1", "future0", "future1",
        ] {
            let (mut run, compiler) = super::execute(source);
            let p = target(&mut run);
            let id = p.fact.fact_id;
            if mutation == "wd" {
                p.well_defined_proof
                    .as_detailed_mut()
                    .unwrap()
                    .branches
                    .clear();
            } else {
                let OrFactSearchedProof::ByBuiltinRule(
                    OrFactSearchProofByBuiltinRule::IntegerDiscreteSplit(p),
                ) = &mut p.searched_proof
                else {
                    panic!()
                };
                if mutation == "subject" {
                    p.subject = Obj::Literal(Literal::Number(Number::new("0".into())));
                } else {
                    let c = if mutation.ends_with('0') {
                        &mut p.subject_in_z
                    } else {
                        &mut p.base_in_z
                    };
                    let c = super::atomic_proof_mut(c);
                    if mutation.starts_with("future") {
                        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(c) =
                            &mut c.searched_proof
                        else {
                            panic!()
                        };
                        c.cite_fact_id = id;
                    } else {
                        let AtomicFact::InFact(f) = &mut c.fact else {
                            panic!()
                        };
                        f.set = Obj::StandardSet(StandardSet::R);
                    }
                }
            }
            compiler.compile_run(&run, mutation).expect_err(
                "retain original integer domain, subjects, branch WD and earlier citations",
            );
        }
    }
}
