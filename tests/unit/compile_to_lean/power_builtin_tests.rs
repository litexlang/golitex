use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_elementary_arithmetic::ElementaryArithmeticProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::VerifyEqualitySuccess;
use crate::prelude::*;
const CASES: [(&str, &str); 6] = [
    (
        r#"forall n Z => 1^n=1
"#,
        "onePowerValue",
    ),
    (
        r#"forall n N+ => 0^n=0
"#,
        "zeroPositiveExponentPowerValue",
    ),
    (
        r#"forall a C,n Z:
    a!=0
    =>:
        a^(-n)=1/(a^n)
"#,
        "negativeIntegerPowerReciprocalValue",
    ),
    (
        r#"forall a R* => 1/a=a^(-1)
"#,
        "reciprocalNegativeOnePowerValue",
    ),
    (
        r#"forall a R,b R* => a/b=a*b^(-1)
"#,
        "quotientNegativeOnePowerValue",
    ),
    (
        r#"forall a,b C,n N => (a*b)^n=a^n*b^n
"#,
        "naturalPowerProductValue",
    ),
];
fn equality(run: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    let root = super::forall_proof_mut(&mut run.statement_results[0]);
    super::equality_proof_mut(&mut root.proved_then_facts[0].verify_result)
}
fn selected(
    proof: &mut VerifyEqualitySuccess,
    index: usize,
) -> &mut EqualitySearchProofByBuiltinRule {
    let EqualFactSearchedProof::ByBuiltinRule(rule) = &mut proof.searched_proof else {
        panic!("selected power builtin")
    };
    assert!(matches!(
        (&*rule, index),
        (EqualitySearchProofByBuiltinRule::OneToAnyPower(_), 0)
            | (
                EqualitySearchProofByBuiltinRule::ElementaryArithmetic(
                    ElementaryArithmeticProof::ZeroToPositiveRealPower { .. }
                ),
                1
            )
            | (
                EqualitySearchProofByBuiltinRule::NegativeIntegerPowerReciprocal(_),
                2
            )
            | (
                EqualitySearchProofByBuiltinRule::ReciprocalAsNegOnePower(_),
                3
            )
            | (
                EqualitySearchProofByBuiltinRule::QuotientAsMulNegOnePower(_),
                4
            )
            | (EqualitySearchProofByBuiltinRule::PowerOfProduct(_), 5)
    ));
    rule
}
#[test]
fn six_power_profiles_select_original_variants_and_generate_deterministically() {
    for (index, (source, law)) in CASES.into_iter().enumerate() {
        let (mut run, compiler) = super::execute(source);
        selected(equality(&mut run), index);
        let output = compiler
            .compile_run(&run, "power_builtin")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
        assert!(output.contains(&format!("Litex.{law}")));
        assert_eq!(output, compiler.compile_run(&run, "power_builtin").unwrap());
    }
}
#[test]
fn selected_power_rules_retain_both_equation_orientations() {
    for (index, (source, law)) in CASES.into_iter().enumerate() {
        let source = if let Some((prefix, last)) = source.trim_end().rsplit_once('\n') {
            let (left, right) = last.trim().split_once('=').unwrap();
            format!("{prefix}\n        {right}={left}\n")
        } else {
            let (prefix, body) = source.trim_end().split_once("=>").unwrap();
            let (left, right) = body.trim().split_once('=').unwrap();
            format!("{prefix}=>{right}={left}\n")
        };
        let (mut run, compiler) = super::execute(&source);
        selected(equality(&mut run), index);
        assert!(compiler
            .compile_run(&run, "reverse_power_builtin")
            .unwrap()
            .contains(&format!("Litex.{law}")));
    }
}
#[test]
fn original_power_children_cannot_be_deleted_swapped_or_retyped() {
    for (index, (source, _)) in CASES.into_iter().enumerate() {
        let (mut run, compiler) = super::execute(source);
        match selected(equality(&mut run), index) {
            EqualitySearchProofByBuiltinRule::OneToAnyPower(_) => continue,
            EqualitySearchProofByBuiltinRule::ElementaryArithmetic(
                ElementaryArithmeticProof::ZeroToPositiveRealPower { requirements },
            ) => {
                requirements.clear();
            }
            EqualitySearchProofByBuiltinRule::NegativeIntegerPowerReciprocal(p) => {
                std::mem::swap(&mut p.exponent_integer, &mut p.base_nonzero)
            }
            EqualitySearchProofByBuiltinRule::ReciprocalAsNegOnePower(p) => {
                p.proof_of_requirement_facts.clear();
            }
            EqualitySearchProofByBuiltinRule::QuotientAsMulNegOnePower(p) => {
                p.proof_of_requirement_facts.clear();
            }
            EqualitySearchProofByBuiltinRule::PowerOfProduct(p) => {
                p.proof_of_requirement_facts.swap(0, 2)
            }
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "malformed_power_child")
            .expect_err(
                "exact original power domain, integer/natural and nonzero evidence is mandatory",
            );
    }
}
#[test]
fn original_power_parent_wd_and_endpoints_are_required() {
    for (index, (source, _)) in CASES.into_iter().enumerate() {
        for change in ["wd", "endpoint"] {
            let (mut run, compiler) = super::execute(source);
            let p = equality(&mut run);
            selected(p, index);
            if change == "wd" {
                let wd = p.well_defined_proof.as_detailed_mut().unwrap();
                std::mem::swap(&mut wd.left, &mut wd.right);
            } else {
                p.fact.right = Obj::Literal(Literal::Number(Number::new("9".into())));
            }
            compiler
                .compile_run(&run, change)
                .expect_err("retain the exact two source constructors");
        }
    }
}
#[test]
fn zero_power_rule_does_not_accept_zero_exponent_or_omit_nonzero_assumptions() {
    for source in [
        "0^0=0\n",
        "forall a C,n Z => a^(-n)=1/(a^n)\n",
        "forall a R => 1/a=a^(-1)\n",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        assert!(
            !Runtime::new(command)
                .run_litex_code(source)
                .unwrap()
                .success,
            "{source}"
        );
    }
}

#[test]
fn positive_integer_power_cancellation_replays_exact_original_requirements_and_path() {
    let source = r#"forall a,b R+,n Z:
    n!=0
    a^n=b^n
    =>:
        a=b
"#;
    for change in [
        "unchanged",
        "missing",
        "swapped",
        "path",
        "future",
        "reverse_path",
    ] {
        let (mut run, compiler) = super::execute(source);
        let p = equality(&mut run);
        let future = p.fact.fact_id;
        let EqualFactSearchedProof::ByBuiltinRule(
            EqualitySearchProofByBuiltinRule::ElementaryArithmetic(
                ElementaryArithmeticProof::PositivePowerCancellation {
                    premise,
                    requirements,
                },
            ),
        ) = &mut p.searched_proof
        else {
            panic!("selected elementary positive-power cancellation")
        };
        assert_eq!(requirements.len(), 4);
        match change {
            "missing" => {
                requirements.pop();
            }
            "swapped" => requirements.swap(0, 2),
            "path" | "future" | "reverse_path" => {
                let EqualFactSearchedProof::ByEquivalenceClass(
                    EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
                ) = premise.as_mut()
                else {
                    panic!("original stored power equality path")
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
            assert!(result
                .unwrap()
                .contains("Litex.positiveIntegerPowerCancellationValue"))
        } else {
            result.expect_err("original positive carriers, nonzero integer exponent and prior exact equality path are required");
        }
    }
}
#[test]
fn nested_remainder_unit_uses_both_original_parent_integer_wd_certificates() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_scalar_extra::ScalarExtraEqualityProof as Extra;
    let source = r#"forall a Z,b Z* => (a%b)%1=a%1
"#;
    for change in ["unchanged", "wd", "modulus", "subject"] {
        let (mut run, compiler) = super::execute(source);
        let p = equality(&mut run);
        assert!(matches!(
            &p.searched_proof,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::ScalarExtra(
                Extra::NestedRemainderUnit(_)
            ))
        ));
        match change {
            "wd" => {
                let wd = p.well_defined_proof.as_detailed_mut().unwrap();
                std::mem::swap(&mut wd.left, &mut wd.right);
            }
            "modulus" | "subject" => {
                let Obj::IntegerOperator(IntegerOperator::Mod(rhs)) = &mut p.fact.right else {
                    panic!()
                };
                let replacement = Box::new(Obj::Literal(Literal::Number(Number::new("7".into()))));
                if change == "modulus" {
                    rhs.right = replacement
                } else {
                    rhs.left = replacement
                }
            }
            _ => {}
        }
        let result = compiler.compile_run(&run, change);
        if change == "unchanged" {
            assert!(result.unwrap().contains("Litex.remainderUnitValue"))
        } else {
            result.expect_err(
                "both original remainder constructors and unit moduli must be retained",
            );
        }
    }
}
#[test]
fn zero_positive_power_uses_shared_positive_natural_superset_replay() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::structural_membership_proof::StructuralMembershipReason;
    for change in ["unchanged", "carrier", "subject"] {
        let (mut run, compiler) = super::execute(CASES[1].0);
        let p = equality(&mut run);
        let EqualitySearchProofByBuiltinRule::ElementaryArithmetic(
            ElementaryArithmeticProof::ZeroToPositiveRealPower { requirements },
        ) = selected(p, 1)
        else {
            panic!()
        };
        let child = super::atomic_proof_mut(&mut requirements[0]);
        let AtomicExceptEqualityFactSearchedProof::ByStructuralMembership(proof) =
            &mut child.searched_proof
        else {
            panic!("original structural RPos evidence")
        };
        assert_eq!(proof.set, StandardSet::RPos);
        let StructuralMembershipReason::StandardSuperset(known) = &mut proof.reason else {
            panic!("original positive-natural inclusion")
        };
        assert_eq!(known.set, StandardSet::NPos);
        if change == "carrier" {
            known.set = StandardSet::N;
        } else if change == "subject" {
            known.element = Obj::Literal(Literal::Number(Number::new("7".into())));
        }
        let result = compiler.compile_run(&run, change);
        if change == "unchanged" {
            let output = result.unwrap();
            assert!(output.contains("Litex.inRPos_intro"));
            assert!(output.contains("Litex.inNPos_positive"));
        } else {
            result.expect_err(
                "a positive inclusion must retain both exact element and sign-bearing carrier",
            );
        }
    }
}
#[test]
fn zero_positive_real_source_remains_outside_supported_power_wd_profile() {
    let (run, compiler) = super::execute("forall r R+ => 0^r=0\n");
    compiler
        .compile_run(&run, "real_exponent_boundary")
        .expect_err("a real-only exponent cannot obtain a supported integer power constructor");
}
