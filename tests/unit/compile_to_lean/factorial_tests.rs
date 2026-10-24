use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::IntegerOperatorObjWellDefinedProofByDef as IntegerWd;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::{less::LessFactSearchProofByBuiltinRule as Lt, less_equal::LessEqualFactSearchProofByBuiltinRule as Le};
use crate::prelude::*;

#[test]
fn factorial_examples_replay_original_results() {
    for source in [
        include_str!("../../../lean/examples/factorial_values/statement.lit"),
        include_str!("../../../lean/examples/factorial_identities/statement.lit"),
        include_str!("../../../lean/examples/factorial_order/statement.lit"),
        include_str!("../../../lean/examples/factorial_function/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "factorials").unwrap();
        assert!(output.contains("Litex.factorial"));
        assert_eq!(output, compiler.compile_run(&run, "factorials").unwrap());
    }
}

#[test]
fn factorial_wd_rejects_missing_child_missing_domain_and_wrong_carrier() {
    for fault in 0..3 {
        let (mut run, compiler) = super::execute("have n N\n$is_set(n!)\n");
        let atomic = super::atomic_proof_mut(
            &mut super::fact_statement_mut(&mut run.statement_results[1]).verify_result,
        );
        let ObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::IntegerOperator(IntegerWd::Factorial(p)),
            ..
        } = &mut atomic.well_defined_proof.well_defined_of_each_parameter[0]
        else {
            panic!("factorial WD")
        };
        match fault {
            0 => p.child_obj_well_defined.clear(),
            1 => p.requirement_fact_verified.clear(),
            _ => {
                let AtomicFact::InFact(member) =
                    &mut super::atomic_proof_mut(&mut p.requirement_fact_verified[0]).fact
                else {
                    panic!("natural requirement")
                };
                member.set = Obj::StandardSet(StandardSet::Z);
            }
        }
        assert!(compiler.compile_run(&run, "bad_factorial_wd").is_err());
    }
}

#[test]
fn factorial_recurrences_preserve_factor_order_and_both_equation_orientations() {
    for predecessor in [true, false] {
        for first in [true, false] {
            for reverse in [true, false] {
                let (domain, upper, coefficient, lower) = if predecessor {
                    ("N+", "n!", "n", "(n - 1)!")
                } else {
                    ("N", "(1 + n)!", "(n + 1)", "n!")
                };
                let product = if first {
                    format!("{coefficient} * {lower}")
                } else {
                    format!("{lower} * {coefficient}")
                };
                let equality = if reverse {
                    format!("{product} = {upper}")
                } else {
                    format!("{upper} = {product}")
                };
                let (run, compiler) =
                    super::execute(&format!("forall n {domain}:\n    {equality}\n"));
                assert!(compiler
                    .compile_run(&run, "recurrence")
                    .unwrap()
                    .contains("Litex.factorialStep"));
            }
        }
    }
}

#[test]
fn factorial_successor_requires_the_recorded_natural_premise() {
    for missing in [true, false] {
        let (mut run, compiler) = super::execute("forall n N:\n    (n + 1)! = (n + 1) * n!\n");
        let universal = super::forall_proof_mut(&mut run.statement_results[0]);
        let equality = super::equality_proof_mut(&mut universal.proved_then_facts[0].verify_result);
        let EqualFactSearchedProof::ByBuiltinRule(
            EqualitySearchProofByBuiltinRule::FactorialSuccessor(p),
        ) = &mut equality.searched_proof
        else {
            panic!("factorial successor")
        };
        if missing {
            p.proof_of_requirement_facts.clear();
        } else {
            let AtomicFact::InFact(member) =
                &mut super::atomic_proof_mut(&mut p.proof_of_requirement_facts[0]).fact
            else {
                panic!("natural premise")
            };
            member.set = Obj::StandardSet(StandardSet::Z);
        }
        assert_eq!(
            compiler.compile_run(&run, "bad_step").unwrap_err().route,
            if missing {
                "Factorial/StepRequirement"
            } else {
                "Factorial/StepDomain"
            }
        );
    }
}

#[test]
fn factorial_strict_order_keeps_the_positive_smaller_argument() {
    for fault in 0..3 {
        let (mut run, compiler) =
            super::execute("forall m N+, n N:\n    m < n\n    =>:\n        m! < n!\n");
        let universal = super::forall_proof_mut(&mut run.statement_results[0]);
        let atomic = super::atomic_proof_mut(&mut universal.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
                Lt::FactorialStrictMonotone(p),
            ),
        ) = &mut atomic.searched_proof
        else {
            panic!("strict factorial order")
        };
        if fault == 0 {
            let AtomicFact::InFact(member) =
                &mut super::atomic_proof_mut(&mut p.positive_smaller).fact
            else {
                panic!("positive domain")
            };
            member.set = Obj::StandardSet(StandardSet::N);
        } else if fault == 1 {
            let AtomicFact::LessFact(order) =
                &mut super::atomic_proof_mut(&mut p.argument_order).fact
            else {
                panic!("strict order")
            };
            std::mem::swap(&mut order.left, &mut order.right);
        } else {
            let order = super::atomic_proof_mut(&mut p.argument_order);
            let AtomicFact::LessFact(old) = &order.fact else {
                panic!("strict order")
            };
            order.fact = AtomicFact::LessEqualFact(LessEqualFact {
                fact_id: old.fact_id,
                left: old.left.clone(),
                right: old.right.clone(),
                line_file: old.line_file.clone(),
            });
        }
        assert!(compiler.compile_run(&run, "bad_factorial_order").is_err());
    }
}

#[test]
fn factorial_weak_order_rejects_reversed_source_arguments() {
    let (mut run, compiler) =
        super::execute("forall m, n N:\n    m <= n\n    =>:\n        m! <= n!\n");
    let universal = super::forall_proof_mut(&mut run.statement_results[0]);
    let atomic = super::atomic_proof_mut(&mut universal.proved_then_facts[0].verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(Le::FactorialMonotone(p)),
    ) = &mut atomic.searched_proof
    else {
        panic!("weak factorial order")
    };
    let AtomicFact::LessEqualFact(order) = &mut super::atomic_proof_mut(&mut p.argument_order).fact
    else {
        panic!("weak order")
    };
    std::mem::swap(&mut order.left, &mut order.right);
    assert_eq!(
        compiler
            .compile_run(&run, "bad_factorial_order")
            .unwrap_err()
            .route,
        "Factorial/OrderPremise"
    );
}

#[test]
fn integer_predecessor_replays_domains_and_strict_order() {
    for fault in [false, true] {
        let (mut run, compiler) =
            super::execute("forall a, b Z:\n    a < b\n    =>:\n        a <= b - 1\n");
        assert!(compiler
            .compile_run(&run, "integer_predecessor")
            .unwrap()
            .contains("Litex.integerPredecessorLe"));
        let universal = super::forall_proof_mut(&mut run.statement_results[0]);
        let atomic = super::atomic_proof_mut(&mut universal.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
                Le::IntegerPredecessorLe(p),
            ),
        ) = &mut atomic.searched_proof
        else {
            panic!("integer predecessor")
        };
        if fault {
            let AtomicFact::InFact(member) =
                &mut super::atomic_proof_mut(&mut p.right_in_z_proof).fact
            else {
                panic!("integer domain")
            };
            member.set = Obj::StandardSet(StandardSet::R);
        } else {
            let AtomicFact::LessFact(order) =
                &mut super::atomic_proof_mut(&mut p.strict_proof).fact
            else {
                panic!("strict order")
            };
            std::mem::swap(&mut order.left, &mut order.right);
        }
        assert!(compiler.compile_run(&run, "bad_predecessor").is_err());
    }
}

#[test]
fn factorial_reuses_existing_objects_and_checks_closed_values() {
    let (run, compiler) = super::execute("have n N\n$is_set(n! + 1)\n$is_set(n!)\n");
    let output = compiler.compile_run(&run, "factorial_reuse").unwrap();
    assert_eq!(output.matches("Litex.factorial ").count(), 1);
    let (mut run, compiler) = super::execute("5! = 120\n");
    let equality = super::equality_proof_mut(
        &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
    );
    let EqualFactSearchedProof::ByClosedCalculation(p) = &mut equality.searched_proof else {
        panic!("closed factorial")
    };
    let ClosedValuePair::Decimal { left, .. } = &mut p.values else {
        panic!("integer result")
    };
    *left = "24".into();
    assert_eq!(
        compiler
            .compile_run(&run, "forged_factorial")
            .unwrap_err()
            .route,
        "ClosedEquality/Values"
    );
}

#[test]
fn factorial_rejects_invalid_domains_and_the_zero_one_strict_boundary() {
    for source in [
        "$is_set((-1)!)",
        "$is_set((1 / 2)!)",
        "0! < 1!",
        "5! = 24",
        "have fn f(n N) N+ = n!\nf(-1) = 1",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime = Runtime::new(command);
        let run = runtime.run_litex_code(source).unwrap();
        assert!(!run.success, "{source}");
        assert!(super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "invalid_factorial")
            .is_err());
    }
}

#[test]
fn factorial_nonzero_accepts_both_orientations() {
    for goal in ["n! != 0", "0 != n!"] {
        let (run, compiler) = super::execute(&format!("forall n N:\n    {goal}\n"));
        assert!(compiler
            .compile_run(&run, "factorial_nonzero")
            .unwrap()
            .contains("Litex.factorialNonzero"));
    }
}

#[test]
fn refined_natural_membership_keeps_original_ordered_evidence() {
    for fault in 0..3 {
        let (mut run, compiler) = super::execute("forall n N+:\n    n - 1 $in N\n");
        let universal = super::forall_proof_mut(&mut run.statement_results[0]);
        let atomic = super::atomic_proof_mut(&mut universal.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RefinedNumericCarrier(p),
        ) = &mut atomic.searched_proof
        else {
            panic!("original integer/nonnegative refinement")
        };
        match fault {
            0 => {
                p.proof_of_requirement_facts.pop();
            }
            1 => p.requirement_facts.swap(0, 1),
            _ => {
                let AtomicFact::LessEqualFact(order) =
                    &mut super::atomic_proof_mut(&mut p.proof_of_requirement_facts[1]).fact
                else {
                    panic!("nonnegative requirement")
                };
                std::mem::swap(&mut order.left, &mut order.right);
            }
        }
        assert!(compiler.compile_run(&run, "forged_refinement").is_err());
    }
}
