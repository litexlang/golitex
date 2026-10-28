use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule as Rule;

#[test]
fn refined_closure_examples_replay_checked_operand_memberships() {
    for source in [
        include_str!("../../../lean/examples/refined_products/statement.lit"),
        include_str!("../../../lean/examples/nonzero_rational_reciprocal/statement.lit"),
        include_str!("../../../lean/examples/positive_scaling_functions/statement.lit"),
        include_str!("../../../lean/examples/nonzero_rational_product_theorem/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "refined_closure").unwrap();
        assert_eq!(
            output,
            compiler.compile_run(&run, "refined_closure").unwrap()
        );
        assert!(output.contains("InRPos") || output.contains("InQStar"));
    }
}

#[test]
fn refined_closure_consumes_all_four_selected_builtin_variants() {
    for (set, op, law) in [
        ("R+", "*", "mulInRPos"),
        ("R+", "/", "divInRPos"),
        ("Q*", "*", "mulInQStar"),
        ("Q*", "/", "divInQStar"),
    ] {
        let (mut run, compiler) = super::execute(&format!(
            "forall a {set}, b {set}:\n    a {op} b $in {set}\n"
        ));
        let body = super::forall_proof_mut(&mut run.statement_results[0]);
        let atomic = super::atomic_proof_mut(&mut body.proved_then_facts[0].verify_result);
        assert!(matches!(
            &atomic.searched_proof,
            AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
                AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
                    Rule::PositiveRealProduct(_)
                        | Rule::PositiveRealQuotient(_)
                        | Rule::NonzeroRationalProduct(_)
                        | Rule::NonzeroRationalQuotient(_)
                )
            )
        ));
        assert!(compiler
            .compile_run(&run, "selected_closure")
            .unwrap()
            .contains(&format!("Litex.{law}")));
    }
}

#[test]
fn refined_closure_rejects_changed_carriers_and_reordered_operands() {
    for (set, op) in [("R+", "*"), ("R+", "/"), ("Q*", "*"), ("Q*", "/")] {
        for swapped in [false, true] {
            let (mut run, compiler) = super::execute(&format!(
                "forall a {set}, b {set}:\n    a {op} b $in {set}\n"
            ));
            let body = super::forall_proof_mut(&mut run.statement_results[0]);
            let atomic = super::atomic_proof_mut(&mut body.proved_then_facts[0].verify_result);
            let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
                AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(rule),
            ) = &mut atomic.searched_proof
            else {
                panic!("builtin closure")
            };
            let (left, right) = match rule {
                Rule::PositiveRealProduct(p) => (&mut p.left_positive, &mut p.right_positive),
                Rule::PositiveRealQuotient(p) => {
                    (&mut p.numerator_positive, &mut p.denominator_positive)
                }
                Rule::NonzeroRationalProduct(p) => {
                    (&mut p.left_nonzero_rational, &mut p.right_nonzero_rational)
                }
                Rule::NonzeroRationalQuotient(p) => (
                    &mut p.numerator_nonzero_rational,
                    &mut p.denominator_nonzero_rational,
                ),
                _ => panic!("selected refined closure"),
            };
            if swapped {
                std::mem::swap(left, right);
            } else {
                let AtomicFact::InFact(member) = &mut super::atomic_proof_mut(left).fact else {
                    panic!("membership child")
                };
                member.set = Obj::StandardSet(if set == "R+" {
                    StandardSet::R
                } else {
                    StandardSet::Q
                });
            }
            assert!(compiler.compile_run(&run, "forged_closure").is_err());
        }
    }
}

#[test]
fn refined_quotient_still_requires_original_division_wd() {
    let (mut run, compiler) = super::execute("forall a Q*, b Q*:\n    a / b $in Q*\n");
    let body = super::forall_proof_mut(&mut run.statement_results[0]);
    let atomic = super::atomic_proof_mut(&mut body.proved_then_facts[0].verify_result);
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::ArithmeticOperator(
                ArithmeticOperatorObjWellDefinedProofByDef::Div(p),
            ),
        ..
    } = (&mut atomic
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .well_defined_of_each_parameter[0])
        .as_detailed_mut()
        .unwrap()
    else {
        panic!("division WD")
    };
    p.requirement_fact_verified.pop();
    assert!(compiler
        .compile_run(&run, "missing_division_guard")
        .is_err());
}

#[test]
fn refined_operations_reject_zero_and_wrong_sign() {
    for source in [
        "1 / 0 $in Q*",
        "0 * 2 $in Q*",
        "-2 * 3 $in R+",
        "-2 / 3 $in R+",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        let run = runtime.run_litex_code(source).unwrap();
        assert!(!run.success, "{source}");
        assert!(super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "invalid_refined_operation")
            .is_err());
    }
}
