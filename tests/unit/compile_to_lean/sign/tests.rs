use crate::prelude::*;

#[test]
fn sign_examples_preserve_integer_codomain_and_function_expansion() {
    for source in [
        include_str!("../../../../lean/examples/real_sign/statement.lit"),
        include_str!("../../../../lean/examples/shifted_sign_function/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "real_sign").unwrap();
        assert!(output.contains("Litex.signInZ"));
        assert!(output.contains("Litex.signDenoteReal"));
        assert!(output.contains("Litex.signOfPositive"));
        assert_eq!(output, compiler.compile_run(&run, "real_sign").unwrap());
    }
}

#[test]
fn sign_selected_rules_use_the_recorded_strict_order_in_both_orientations() {
    for (condition, value, law) in [
        ("0 < x", "1", "signOfPositive"),
        ("x < 0", "-1", "signOfNegative"),
        ("x < 0", "0 - 1", "signOfNegative"),
    ] {
        for reversed in [false, true] {
            let equality = if reversed {
                format!("{value} = sign(x)")
            } else {
                format!("sign(x) = {value}")
            };
            let (run, compiler) = super::execute(&format!(
                "forall x R:\n    {condition}\n    =>:\n        {equality}\n"
            ));
            let output = compiler.compile_run(&run, "sign_condition").unwrap();
            assert!(output.contains(&format!("Litex.{law}")), "{output}");
        }
    }
}

#[test]
fn sign_identity_rejects_missing_weakened_reversed_and_wrong_argument_premises() {
    for fault in ["missing", "weak", "reversed", "argument"] {
        let (mut run, compiler) =
            super::execute("forall x R:\n    0 < x\n    =>:\n        sign(x) = 1\n");
        let universal = super::forall_proof_mut(&mut run.statement_results[0]);
        let proof = super::equality_proof_mut(&mut universal.proved_then_facts[0].verify_result);
        let EqualFactSearchedProof::ByBuiltinRule(
            EqualitySearchProofByBuiltinRule::SignOfPositive(p),
        ) = &mut proof.searched_proof
        else {
            panic!("original sign rule")
        };
        if fault == "missing" {
            p.proof_of_requirement_facts.clear();
        } else {
            let requirement = super::atomic_proof_mut(&mut p.proof_of_requirement_facts[0]);
            let AtomicFact::LessFact(order) = &mut requirement.fact else {
                panic!("strict order")
            };
            match fault {
                "weak" => {
                    requirement.fact = AtomicFact::LessEqualFact(LessEqualFact {
                        fact_id: order.fact_id,
                        left: order.left.clone(),
                        right: order.right.clone(),
                        line_file: order.line_file.clone(),
                    })
                }
                "reversed" => std::mem::swap(&mut order.left, &mut order.right),
                _ => order.right = Obj::Literal(Literal::Number(Number::new("2".into()))),
            }
        }
        assert_eq!(
            compiler.compile_run(&run, "bad_sign").unwrap_err().route,
            if fault == "missing" {
                "Sign/IdentityRequirement"
            } else {
                "Sign/StrictOrder"
            }
        );
    }
}

#[test]
fn sign_wd_rejects_missing_or_wrong_child_evidence() {
    for missing in [false, true] {
        let (mut run, compiler) = super::execute("have x R\n$is_set(sign(x))\n");
        let fact = super::atomic_proof_mut(
            &mut super::fact_statement_mut(&mut run.statement_results[1]).verify_result,
        );
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::ArithmeticOperator(
                    ArithmeticOperatorObjWellDefinedProofByDef::Sign(wd),
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
            panic!("sign WD")
        };
        if missing {
            wd.requirement_fact_verified.clear();
        } else {
            let DetailedObjWellDefinedProof::ByDef { obj, .. } = (wd.child_obj_well_defined[0]
                .as_mut())
            .as_detailed_mut()
            .unwrap() else {
                panic!("identifier WD")
            };
            *obj = Obj::Literal(Literal::Number(Number::new("2".into())));
        }
        assert!(compiler.compile_run(&run, "bad_sign_wd").is_err());
    }
}

#[test]
fn sign_child_is_reused_after_an_enclosing_expression() {
    let (run, compiler) = super::execute("have x R\n$is_set(sign(x) + 1)\n$is_set(sign(x))\n");
    let output = compiler.compile_run(&run, "sign_reuse").unwrap();
    assert_eq!(output.matches("Litex.sign ").count(), 1, "{output}");
    assert!(output.contains(".val.left"));
}

#[test]
fn sign_rejects_a_changed_closed_calculation_value() {
    let (mut run, compiler) = super::execute("sign(4) = 1\n");
    let p = super::equality_proof_mut(
        &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
    );
    match &mut p.searched_proof {
        EqualFactSearchedProof::ByClosedCalculation(p) => match &mut p.values {
            ClosedValuePair::Decimal { left, .. } => *left = "0".into(),
            _ => panic!("decimal sign"),
        },
        EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::Calculation(
            EqualitySearchProofByCalculation::ClosedDecimal { left_normal, .. },
        )) => *left_normal = "0".into(),
        _ => panic!("original closed calculation"),
    }
    assert_eq!(
        compiler
            .compile_run(&run, "bad_sign_value")
            .unwrap_err()
            .route,
        "ClosedEquality/Values"
    );
}

#[test]
fn sign_does_not_accept_complex_only_domains_or_false_values() {
    for source in [
        "have x C\n$is_set(sign(x))\n",
        "sign(0) = 1\n",
        "forall x R:\n    0 <= x\n    =>:\n        sign(x) = 1\n",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        let run = runtime.run_litex_code(source).unwrap();
        assert!(!run.success);
        assert!(super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "false_sign")
            .is_err());
    }
}
