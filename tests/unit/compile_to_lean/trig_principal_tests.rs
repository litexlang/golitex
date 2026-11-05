use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::{less_equal::LessEqualFactSearchProofByBuiltinRule as Le, not_equal::NotEqualFactSearchProofByBuiltinRule as Ne};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::VerifyEqualitySuccess;
use crate::prelude::*;

const BOUNDS: [(&str, &str, bool); 4] = [
    (
        r#"forall x R => -1<=sin(x)
"#,
        "sineLowerBoundValue",
        true,
    ),
    (
        r#"forall x R => sin(x)<=1
"#,
        "sineUpperBoundValue",
        false,
    ),
    (
        r#"forall x R => -1<=cos(x)
"#,
        "cosineLowerBoundValue",
        true,
    ),
    (
        r#"forall x R => cos(x)<=1
"#,
        "cosineUpperBoundValue",
        false,
    ),
];
const NONZERO: [(&str, &str); 2] = [
    (
        r#"forall x R:
    (-pi)/2<x
    x<pi/2
    =>:
        cos(x)!=0
"#,
        "cosineNonzeroOnPrincipalInterval",
    ),
    (
        r#"forall x R:
    0<x
    x<pi
    =>:
        sin(x)!=0
"#,
        "sineNonzeroOnPrincipalInterval",
    ),
];
const INVERSES: [(&str, &str); 4] = [
    (
        r#"forall x R:
    (-pi)/2<=x
    x<=pi/2
    =>:
        arcsin(sin(x))=x
"#,
        "arcsineSinePrincipalValue",
    ),
    (
        r#"forall x R:
    0<=x
    x<=pi
    =>:
        arccos(cos(x))=x
"#,
        "arccosineCosinePrincipalValue",
    ),
    (
        r#"forall x R:
    (-pi)/2<x
    x<pi/2
    =>:
        arctan(tan(x))=x
"#,
        "arctangentTangentPrincipalValue",
    ),
    (
        r#"forall x R:
    0<x
    x<pi
    =>:
        arccot(cot(x))=x
"#,
        "arccotangentCotangentPrincipalValue",
    ),
];
fn nonzero_children(
    proof: &mut VerifyAtomicExceptEqualityFactSuccess,
    index: usize,
) -> (
    &mut AtomicExceptEqualityFactKnownProof,
    &mut AtomicExceptEqualityFactKnownProof,
) {
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(rule),
    ) = &mut proof.searched_proof
    else {
        panic!("selected nonzero builtin")
    };
    match (index, rule) {
        (0, Ne::CosNonzeroOnOpenHalfPi(p)) => (&mut p.lower_bound_proof, &mut p.upper_bound_proof),
        (1, Ne::SinNonzeroOnOpenPi(p)) => (&mut p.lower_bound_proof, &mut p.upper_bound_proof),
        _ => panic!("selected exact nonzero variant"),
    }
}
fn inverse_children(proof: &mut VerifyEqualitySuccess, index: usize) -> &mut Vec<VerifyFactResult> {
    let EqualFactSearchedProof::ByBuiltinRule(rule) = &mut proof.searched_proof else {
        panic!("selected inverse builtin")
    };
    match (index, rule) {
        (0, EqualitySearchProofByBuiltinRule::ArcsinSinRightInverse(p)) => {
            &mut p.proof_of_requirement_facts
        }
        (1, EqualitySearchProofByBuiltinRule::ArccosCosRightInverse(p)) => {
            &mut p.proof_of_requirement_facts
        }
        (2, EqualitySearchProofByBuiltinRule::ArctanTanRightInverse(p)) => {
            &mut p.proof_of_requirement_facts
        }
        (3, EqualitySearchProofByBuiltinRule::ArccotCotRightInverse(p)) => {
            &mut p.proof_of_requirement_facts
        }
        _ => panic!("selected exact principal inverse variant"),
    }
}
#[test]
fn unit_circle_bounds_select_both_original_variants_for_sine_and_cosine() {
    for (source, law, lower) in BOUNDS {
        let (mut run, compiler) = super::execute(source);
        let root = super::forall_proof_mut(&mut run.statement_results[0]);
        let p = super::atomic_proof_mut(&mut root.proved_then_facts[0].verify_result);
        assert!(matches!(
            (&p.searched_proof, lower),
            (
                AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
                    AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
                        Le::UnitCircleLowerBound(_)
                    )
                ),
                true
            ) | (
                AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
                    AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
                        Le::UnitCircleUpperBound(_)
                    )
                ),
                false
            )
        ));
        let output = compiler.compile_run(&run, "unit_circle").unwrap();
        assert!(output.contains(&format!("Litex.{law}")));
        assert_eq!(output, compiler.compile_run(&run, "unit_circle").unwrap());
    }
}
#[test]
fn principal_nonzero_replays_exact_lower_and_upper_scoped_bounds() {
    for (index, (source, law)) in NONZERO.into_iter().enumerate() {
        let (mut run, compiler) = super::execute(source);
        let root = super::forall_proof_mut(&mut run.statement_results[0]);
        let p = super::atomic_proof_mut(&mut root.proved_then_facts[0].verify_result);
        nonzero_children(p, index);
        let output = compiler.compile_run(&run, "principal_nonzero").unwrap();
        assert!(output.contains(&format!("Litex.{law}")));
        assert_eq!(
            output,
            compiler.compile_run(&run, "principal_nonzero").unwrap()
        );
    }
}
#[test]
fn all_four_principal_inverse_rules_replay_original_two_order_children() {
    for (index, (source, law)) in INVERSES.into_iter().enumerate() {
        let (mut run, compiler) = super::execute(source);
        let root = super::forall_proof_mut(&mut run.statement_results[0]);
        let p = super::equality_proof_mut(&mut root.proved_then_facts[0].verify_result);
        assert_eq!(inverse_children(p, index).len(), 2);
        let output = compiler.compile_run(&run, "principal_inverse").unwrap();
        assert!(output.contains(&format!("Litex.{law}")));
        assert_eq!(
            output,
            compiler.compile_run(&run, "principal_inverse").unwrap()
        );
    }
}
#[test]
fn principal_inverse_requirements_cannot_be_missing_swapped_foreign_or_retyped() {
    for (index, (source, _)) in INVERSES.into_iter().enumerate() {
        for change in ["missing", "swapped", "foreign", "strictness", "wd"] {
            let (mut run, compiler) = super::execute(source);
            let root = super::forall_proof_mut(&mut run.statement_results[0]);
            let p = super::equality_proof_mut(&mut root.proved_then_facts[0].verify_result);
            if change == "wd" {
                let wd = p.well_defined_proof.as_detailed_mut().unwrap();
                std::mem::swap(&mut wd.left, &mut wd.right);
            } else {
                let children = inverse_children(p, index);
                match change {
                    "missing" => {
                        children.pop();
                    }
                    "swapped" => children.swap(0, 1),
                    _ => {
                        let child = super::atomic_proof_mut(&mut children[0]);
                        child.fact = match &child.fact {
                            AtomicFact::LessFact(f) if change == "strictness" => {
                                AtomicFact::LessEqualFact(LessEqualFact {
                                    left: f.left.clone(),
                                    right: f.right.clone(),
                                    fact_id: f.fact_id,
                                    line_file: f.line_file.clone(),
                                })
                            }
                            AtomicFact::LessEqualFact(f) if change == "strictness" => {
                                AtomicFact::LessFact(LessFact {
                                    left: f.left.clone(),
                                    right: f.right.clone(),
                                    fact_id: f.fact_id,
                                    line_file: f.line_file.clone(),
                                })
                            }
                            AtomicFact::LessFact(f) => AtomicFact::LessFact(LessFact {
                                left: Obj::Literal(Literal::Number(Number::new("3".into()))),
                                ..f.clone()
                            }),
                            AtomicFact::LessEqualFact(f) => {
                                AtomicFact::LessEqualFact(LessEqualFact {
                                    left: Obj::Literal(Literal::Number(Number::new("3".into()))),
                                    ..f.clone()
                                })
                            }
                            _ => panic!("order requirement"),
                        };
                    }
                }
            }
            compiler
                .compile_run(&run, change)
                .expect_err("principal inverse preserves original bounds and constructors");
        }
    }
}
#[test]
fn principal_nonzero_bounds_cannot_be_swapped_weakened_or_omit_citations() {
    for (index, (source, _)) in NONZERO.into_iter().enumerate() {
        for change in ["swapped", "weakened", "missing", "future"] {
            let (mut run, compiler) = super::execute(source);
            let root = super::forall_proof_mut(&mut run.statement_results[0]);
            let p = super::atomic_proof_mut(&mut root.proved_then_facts[0].verify_result);
            let future = p.fact.fact_id();
            let (lower, upper) = nonzero_children(p, index);
            match change {
                "swapped" => std::mem::swap(lower, upper),
                "weakened" => {
                    let AtomicFact::LessFact(f) = &lower.fact else {
                        panic!("strict lower bound")
                    };
                    lower.fact = AtomicFact::LessEqualFact(LessEqualFact {
                        left: f.left.clone(),
                        right: f.right.clone(),
                        fact_id: f.fact_id,
                        line_file: f.line_file.clone(),
                    });
                }
                _ => {
                    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) =
                        lower.searched_proof.as_mut()
                    else {
                        panic!("original direct citation")
                    };
                    known.cite_fact_id = if change == "missing" {
                        FactId::new(u64::MAX)
                    } else {
                        future
                    };
                }
            }
            compiler
                .compile_run(&run, change)
                .expect_err("nonzero needs the original two strict visible interval bounds");
        }
    }
}
#[test]
fn principal_identities_allow_reversed_equalities_and_comparison_spelling() {
    for (index, (source, law)) in INVERSES.into_iter().enumerate() {
        let (prefix, last) = source.trim_end().rsplit_once('\n').unwrap();
        let (left, right) = last.trim().split_once('=').unwrap();
        let reversed = format!("{prefix}\n        {right}={left}\n");
        let (mut run, compiler) = super::execute(&reversed);
        let root = super::forall_proof_mut(&mut run.statement_results[0]);
        inverse_children(
            super::equality_proof_mut(&mut root.proved_then_facts[0].verify_result),
            index,
        );
        assert!(compiler
            .compile_run(&run, "inverse_reversed")
            .unwrap()
            .contains(&format!("Litex.{law}")));
    }
}

#[test]
fn known_sine_preserves_original_equality_path_and_two_principal_bounds() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_scalar_extra::ScalarExtraEqualityProof as Extra;
    let source = r#"forall x,y R:
    (-pi)/2<=y
    y<=pi/2
    x=sin(y)
    -1<=x
    x<=1
    =>:
        arcsin(x)=y
"#;
    for change in [
        "unchanged",
        "missing",
        "swapped",
        "path",
        "future",
        "reversed_path",
    ] {
        let (mut run, compiler) = super::execute(source);
        let root = super::forall_proof_mut(&mut run.statement_results[0]);
        let p = super::equality_proof_mut(&mut root.proved_then_facts[0].verify_result);
        let future = p.fact.fact_id;
        let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::ScalarExtra(
            Extra::ArcsinFromKnownSine(e),
        )) = &mut p.searched_proof
        else {
            panic!("selected known sine variant")
        };
        match change {
            "missing" => {
                e.principal_bounds.pop();
            }
            "swapped" => e.principal_bounds.swap(0, 1),
            "path" | "future" | "reversed_path" => {
                let EqualFactSearchedProof::ByEquivalenceClass(
                    EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
                ) = e.sine_equality.as_mut()
                else {
                    panic!("original fixed equality path")
                };
                assert!(!path.path.is_empty());
                if change == "path" {
                    path.path.clear()
                } else if change == "future" {
                    path.path[0].2 = future
                } else {
                    let (a, b, _) = &mut path.path[0];
                    std::mem::swap(a, b)
                };
            }
            _ => {}
        }
        let result = compiler.compile_run(&run, change);
        if change == "unchanged" {
            assert!(result.unwrap().contains("Litex.arcsineFromKnownSineValue"))
        } else {
            result.expect_err(
                "original known sine equality and principal interval proofs are required",
            );
        }
    }
}
