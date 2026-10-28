use crate::prelude::*;

#[test]
fn min_max_functions_unfold_and_reuse_named_theorems() {
    let (run, compiler) = super::execute(include_str!(
        "../../../../lean/examples/ordered_min_max_functions/statement.lit"
    ));
    let output = compiler.compile_run(&run, "extrema_functions").unwrap();
    assert!(output.contains("Litex.minMaxValue (M := M) false"));
    assert!(output.contains("Litex.minMaxValue (M := M) true"));
    assert!(output.contains("Litex.minOfLeOperands"));
    assert!(output.contains("Litex.maxOfLeOperands"));
    assert_eq!(
        output,
        compiler.compile_run(&run, "extrema_functions").unwrap()
    );
}

#[test]
fn min_max_replays_each_conditional_rule_in_both_equality_orientations() {
    for (expression, selected, law) in [
        ("min(a, b)", "a", "minOfLeOperands"),
        ("min(b, a)", "a", "minOfGeOperands"),
        ("max(a, b)", "b", "maxOfLeOperands"),
        ("max(b, a)", "b", "maxOfGeOperands"),
    ] {
        for reversed in [false, true] {
            let (left, right) = if reversed {
                (selected, expression)
            } else {
                (expression, selected)
            };
            let source = format!("forall a, b R:\n    a <= b\n    =>:\n        {left} = {right}\n");
            let (run, compiler) = super::execute(&source);
            let output = compiler.compile_run(&run, "selection").unwrap();
            assert!(output.contains(&format!("Litex.{law}")), "{output}");
        }
    }
}

#[test]
fn min_max_selection_rejects_missing_reversed_or_wrong_constructor_evidence() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_equality_identities_wave6::MaxLeftWhenLessEqualBuiltinRuleProof;
    for fault in ["missing", "reversed", "constructor"] {
        let (mut run, compiler) =
            super::execute("forall a, b R:\n    a <= b\n    =>:\n        min(a, b) = a\n");
        let universal = super::forall_proof_mut(&mut run.statement_results[0]);
        let proof = super::equality_proof_mut(&mut universal.proved_then_facts[0].verify_result);
        let EqualFactSearchedProof::ByBuiltinRule(
            EqualitySearchProofByBuiltinRule::MinLeftWhenLessEqual(p),
        ) = &mut proof.searched_proof
        else {
            panic!("original conditional minimum rule")
        };
        match fault {
            "missing" => p.proof_of_requirement_facts.clear(),
            "reversed" => {
                let requirement = super::atomic_proof_mut(&mut p.proof_of_requirement_facts[0]);
                let AtomicFact::LessEqualFact(order) = &mut requirement.fact else {
                    panic!("weak order")
                };
                std::mem::swap(&mut order.left, &mut order.right);
            }
            _ => {
                proof.searched_proof = EqualFactSearchedProof::ByBuiltinRule(
                    EqualitySearchProofByBuiltinRule::MaxLeftWhenLessEqual(
                        MaxLeftWhenLessEqualBuiltinRuleProof {
                            proof_of_requirement_facts: std::mem::take(
                                &mut p.proof_of_requirement_facts,
                            ),
                        },
                    ),
                );
            }
        }
        assert_eq!(
            compiler.compile_run(&run, "selection").unwrap_err().route,
            match fault {
                "missing" => "MinMax/SelectionRequirement",
                "reversed" => "MinMax/SelectionOrder",
                _ => "MinMax/SelectionSubject",
            }
        );
    }
}

const SOURCE: &str = include_str!("../../../../lean/examples/real_min_max/statement.lit");

#[test]
fn min_max_replays_four_identities_and_preserves_integer_membership() {
    let (run, compiler) = super::execute(SOURCE);
    let output = compiler.compile_run(&run, "extrema").unwrap();
    assert_eq!(output.matches("Litex.minMaxIdempotent").count(), 2);
    assert_eq!(output.matches("Litex.minMaxCommutative").count(), 2);
    assert!(output.contains("Litex.minMaxMember"));
    assert!(output.contains("Litex.Z"));
    assert_eq!(output, compiler.compile_run(&run, "extrema").unwrap());
}

#[test]
fn min_max_reuses_the_original_child_with_its_wd() {
    let (run, compiler) =
        super::execute("have a, b R\n$is_set(min(a, b) + 1)\n$is_set(min(a, b))\n");
    let output = compiler.compile_run(&run, "extrema").unwrap();
    assert_eq!(output.matches("Litex.min ").count(), 1, "{output}");
    assert!(output.contains(".val.left"));
    if let Some(directory) = std::env::var_os("LITEX_LEAN_PHASE2_OUTPUT_DIR") {
        std::fs::write(
            std::path::Path::new(&directory).join("min_max_reuse.lean"),
            output,
        )
        .unwrap();
    }
}

#[test]
fn min_max_rejects_missing_or_reordered_real_requirements() {
    for reorder in [false, true] {
        let (mut run, compiler) = super::execute("have a, b R\n$is_set(min(a, b))\n");
        let fact = super::atomic_proof_mut(
            &mut super::fact_statement_mut(&mut run.statement_results[1]).verify_result,
        );
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::ArithmeticOperator(
                    ArithmeticOperatorObjWellDefinedProofByDef::Min(wd),
                ),
            ..
        } = (&mut fact
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .well_defined_of_each_parameter[0])
            .as_detailed_mut()
            .unwrap()
        else {
            panic!("min wd")
        };
        if reorder {
            wd.requirement_fact_verified.swap(0, 1);
        } else {
            wd.requirement_fact_verified.clear();
        }
        assert!(compiler.compile_run(&run, "extrema").is_err());
    }
}

#[test]
fn min_max_rejects_a_certificate_for_another_operation() {
    let (mut run, compiler) = super::execute("have a R\nmin(a, a) = a\n");
    let proof = super::equality_proof_mut(
        &mut super::fact_statement_mut(&mut run.statement_results[1]).verify_result,
    );
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_equality_identities_wave3::MaxIdempotentBuiltinRuleProof;
    proof.searched_proof = EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::MaxIdempotent(MaxIdempotentBuiltinRuleProof {}),
    );
    let error = compiler.compile_run(&run, "extrema").unwrap_err();
    assert_eq!(error.route, "MinMax/IdempotentSubject");
}

#[test]
fn complex_membership_does_not_supply_the_real_min_max_domain() {
    let source = "have z C\n$is_set(min(z, z))\n";
    let command = parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
    let mut runtime =
        Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
    let run = runtime.run_litex_code(source).unwrap();
    assert!(!run.success);
    assert!(super::LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "extrema")
        .is_err());
}

const EVALUATION: &str = include_str!("../../../../lean/examples/min_max_evaluation/statement.lit");
const BOUNDS: &str = include_str!("../../../../lean/examples/min_max_bounds/statement.lit");
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less_equal::LessEqualFactSearchProofByBuiltinRule as OrderRule;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::sign_extremum_order::{MinLowerBoundProof, WeakOrderArgumentProof};

#[test]
fn min_max_closed_calculation_and_recorded_order_rules_compile() {
    for source in [EVALUATION, BOUNDS] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "extrema").unwrap();
        assert_eq!(output, compiler.compile_run(&run, "extrema").unwrap());
        if source == EVALUATION {
            assert!(output.contains("Litex.minMaxDenoteReal"));
        } else {
            assert_eq!(output.matches("Litex.minLeOperands").count(), 2);
            assert_eq!(output.matches("Litex.operandsLeMax").count(), 2);
            assert_eq!(output.matches("Litex.minMaxMonotone").count(), 4);
        }
    }
}

#[test]
fn min_max_closed_calculation_rejects_changed_exact_value() {
    let (mut run, compiler) = super::execute("min(3, 5) = 3\n");
    let proof = super::equality_proof_mut(
        &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
    );
    match &mut proof.searched_proof {
        EqualFactSearchedProof::ByClosedCalculation(p) => match &mut p.values {
            ClosedValuePair::Decimal { left, .. } => *left = "5".into(),
            _ => panic!("closed decimal extrema"),
        },
        EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::Calculation(
            EqualitySearchProofByCalculation::ClosedDecimal { left_normal, .. },
        )) => *left_normal = "5".into(),
        _ => panic!("original closed calculation"),
    }
    assert_eq!(
        compiler.compile_run(&run, "extrema").unwrap_err().route,
        "ClosedEquality/Values"
    );
}

#[test]
fn min_max_bound_rejects_a_rule_for_the_wrong_endpoint() {
    let (mut run, compiler) = super::execute("forall a, b R:\n    a <= max(a, b)\n");
    let universal = super::forall_proof_mut(&mut run.statement_results[0]);
    let proof = super::atomic_proof_mut(&mut universal.proved_then_facts[0].verify_result);
    proof.searched_proof = AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(OrderRule::MinLowerBound(
            MinLowerBoundProof,
        )),
    );
    assert_eq!(
        compiler.compile_run(&run, "extrema").unwrap_err().route,
        "MinMax/BoundConstructor"
    );
}

#[test]
fn min_max_monotonicity_rejects_swapped_or_missing_premises() {
    for replace_with_identity in [false, true] {
        let (mut run, compiler) = super::execute(
            "forall a, b, c, d R:\n    a <= c\n    b <= d\n    =>:\n        min(a, b) <= min(c, d)\n",
        );
        let universal = super::forall_proof_mut(&mut run.statement_results[0]);
        let proof = super::atomic_proof_mut(&mut universal.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
                OrderRule::MinWeakMonotone(p),
            ),
        ) = &mut proof.searched_proof
        else {
            panic!("recorded monotonicity rule")
        };
        if replace_with_identity {
            let AtomicFact::LessEqualFact(fact) = &proof.fact else {
                unreachable!()
            };
            let Obj::ArithmeticOperator(ArithmeticOperator::Min(m)) = &fact.left else {
                unreachable!()
            };
            p.left_order = WeakOrderArgumentProof::SameArgument((*m.left).clone());
        } else {
            std::mem::swap(&mut p.left_order, &mut p.right_order);
        }
        let error = compiler.compile_run(&run, "extrema").unwrap_err();
        assert_eq!(
            error.route,
            if replace_with_identity {
                "MinMax/FixedArgument"
            } else {
                "MinMax/OrderPremise"
            }
        );
    }
}

#[test]
fn min_max_does_not_verify_false_values_or_reversed_bounds() {
    for source in ["min(3, 5) = 5\n", "forall a, b R:\n    min(a, b) >= a\n"] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        let run = runtime.run_litex_code(source).unwrap();
        assert!(!run.success);
        assert!(super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "extrema")
            .is_err());
    }
}
