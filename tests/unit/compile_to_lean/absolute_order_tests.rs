use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less_equal::LessEqualFactSearchProofByBuiltinRule as Rule;
use crate::prelude::*;
const CASES: [(&str, &str); 8] = [
    (
        include_str!("../../../lean/examples/absolute_self_upper/statement.lit"),
        "absSelfUpperValue",
    ),
    (
        include_str!("../../../lean/examples/absolute_self_lower/statement.lit"),
        "absSelfLowerValue",
    ),
    (
        include_str!("../../../lean/examples/absolute_triangle/statement.lit"),
        "absTriangleValue",
    ),
    (
        include_str!("../../../lean/examples/absolute_reverse_triangle_add/statement.lit"),
        "absReverseTriangleAddValue",
    ),
    (
        include_str!("../../../lean/examples/absolute_reverse_triangle_sub/statement.lit"),
        "absReverseTriangleSubValue",
    ),
    (
        include_str!("../../../lean/examples/absolute_from_symmetric_bounds/statement.lit"),
        "absFromSymmetricBoundsValue",
    ),
    (
        include_str!("../../../lean/examples/absolute_bound_upper_projection/statement.lit"),
        "absBoundUpperProjectionValue",
    ),
    (
        include_str!("../../../lean/examples/absolute_bound_negative_projection/statement.lit"),
        "absBoundNegativeProjectionValue",
    ),
];
fn target(run: &mut RunLitexCodeResult) -> &mut VerifyAtomicExceptEqualityFactSuccess {
    let root = super::forall_proof_mut(&mut run.statement_results[0]);
    super::atomic_proof_mut(&mut root.proved_then_facts[0].verify_result)
}
fn selected(proof: &mut VerifyAtomicExceptEqualityFactSuccess, index: usize) -> &mut Rule {
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(rule),
    ) = &mut proof.searched_proof
    else {
        panic!("selected weak absolute-value builtin")
    };
    assert!(
        matches!(
            (&*rule, index),
            (Rule::AbsSelfUpper(_), 0)
                | (Rule::AbsSelfLower(_), 1)
                | (Rule::AbsTriangleInequality(_), 2)
                | (Rule::AbsReverseTriangleAdd(_), 3)
                | (Rule::AbsReverseTriangleSub(_), 4)
                | (Rule::AbsLeFromSymmetricBounds(_), 5)
                | (Rule::AbsLeImpliesUpper(_), 6)
                | (Rule::AbsLeImpliesNegUpper(_), 7)
        ),
        "selected absolute-value rule at {index}"
    );
    rule
}
#[test]
fn absolute_order_replays_all_eight_actual_selected_variants_deterministically() {
    for (index, (source, law)) in CASES.into_iter().enumerate() {
        let (mut run, compiler) = super::execute(source);
        selected(target(&mut run), index);
        let output = compiler
            .compile_run(&run, "absolute_order")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
        assert!(output.contains(&format!("Litex.{law}")));
        assert_eq!(
            output,
            compiler.compile_run(&run, "absolute_order").unwrap()
        );
    }
}
#[test]
fn absolute_order_requires_original_endpoints_and_parent_wd() {
    for (index, (source, _)) in CASES.into_iter().enumerate() {
        for change in ["wd", "endpoint"] {
            let (mut run, compiler) = super::execute(source);
            let p = target(&mut run);
            selected(p, index);
            if change == "wd" {
                p.well_defined_proof
                    .as_detailed_mut()
                    .unwrap()
                    .well_defined_of_each_parameter
                    .swap(0, 1)
            } else {
                let AtomicFact::LessEqualFact(f) = &mut p.fact else {
                    panic!()
                };
                f.right = Obj::Literal(Literal::Number(Number::new("7".into())));
            }
            compiler.compile_run(&run, change).expect_err(
                "retain original real-domain constructors and exact absolute/order endpoints",
            );
        }
    }
}
#[test]
fn absolute_symmetric_bounds_retain_both_original_ordered_children() {
    for change in ["swapped", "foreign", "future"] {
        let (mut run, compiler) = super::execute(CASES[5].0);
        let p = target(&mut run);
        let future = p.fact.fact_id();
        let Rule::AbsLeFromSymmetricBounds(e) = selected(p, 5) else {
            panic!()
        };
        if change == "swapped" {
            std::mem::swap(&mut e.upper_proof, &mut e.neg_upper_proof)
        } else {
            let child = super::atomic_proof_mut(&mut e.upper_proof);
            if change == "foreign" {
                let AtomicFact::LessEqualFact(f) = &mut child.fact else {
                    panic!()
                };
                f.left = Obj::Literal(Literal::Number(Number::new("9".into())))
            } else {
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                    &mut child.searched_proof
                else {
                    panic!("original upper-bound citation")
                };
                cite.cite_fact_id = future;
            }
        }
        compiler
            .compile_run(&run, change)
            .expect_err("the original two scoped symmetric bound results are mandatory");
    }
}
#[test]
fn absolute_bound_projections_cannot_use_future_citations_or_another_bound() {
    for index in [6, 7] {
        for change in ["future", "bound"] {
            let (mut run, compiler) = super::execute(CASES[index].0);
            let p = target(&mut run);
            let future = p.fact.fact_id();
            let premise = match selected(p, index) {
                Rule::AbsLeImpliesUpper(e) => &mut e.premise_proof,
                Rule::AbsLeImpliesNegUpper(e) => &mut e.premise_proof,
                _ => panic!(),
            };
            if change == "future" {
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                    premise.searched_proof.as_mut()
                else {
                    panic!()
                };
                cite.cite_fact_id = future;
            } else {
                let AtomicFact::LessEqualFact(f) = &mut premise.fact else {
                    panic!()
                };
                f.right = Obj::Literal(Literal::Number(Number::new("3".into())));
            }
            compiler
                .compile_run(&run, change)
                .expect_err("project the exact prior absolute-value bound only");
        }
    }
}
