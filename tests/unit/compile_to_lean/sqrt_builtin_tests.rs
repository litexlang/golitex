use crate::prelude::*;

#[test]
fn sqrt_square_replays_signed_and_nonnegative_contracts() {
    for (header, left, right, law) in [
        (
            "forall x R:\n",
            "sqrt(x^2)",
            "abs(x)",
            "sqrtOfSquareAbsolute",
        ),
        (
            "forall x R:\n    x >= 0\n    =>:\n",
            "sqrt(x^2)",
            "x",
            "sqrtOfNonnegativeSquare",
        ),
    ] {
        for reversed in [false, true] {
            let equality = if reversed {
                format!("{right} = {left}")
            } else {
                format!("{left} = {right}")
            };
            let indent = if header.contains("=>:") {
                "        "
            } else {
                "    "
            };
            let (run, compiler) = super::execute(&format!("{header}{indent}{equality}\n"));
            let output = compiler.compile_run(&run, "sqrt_square").unwrap();
            assert!(output.contains(&format!("Litex.{law}")));
        }
    }
}

#[test]
fn sqrt_product_and_quotient_replay_ordered_original_requirements() {
    for quotient in [false, true] {
        for commute in [false, true] {
            if quotient && commute {
                continue;
            }
            for reverse in [false, true] {
                let (operator, second_order, law) = if quotient {
                    ("/", ">", "sqrtQuotient")
                } else {
                    ("*", ">=", "sqrtProduct")
                };
                let left = format!("sqrt(x {operator} y)");
                let right = if commute {
                    "sqrt(y) * sqrt(x)".to_string()
                } else {
                    format!("sqrt(x) {operator} sqrt(y)")
                };
                let equality = if reverse {
                    format!("{right} = {left}")
                } else {
                    format!("{left} = {right}")
                };
                let source = format!("forall x R, y R:\n    x >= 0\n    y {second_order} 0\n    =>:\n        {equality}\n");
                let (mut run, compiler) = super::execute(&source);
                let output = compiler.compile_run(&run, "sqrt_binary").unwrap();
                assert!(output.contains(&format!("Litex.{law}")));
                let universal = super::forall_proof_mut(&mut run.statement_results[0]);
                let equality =
                    super::equality_proof_mut(&mut universal.proved_then_facts[0].verify_result);
                let requirements = match &mut equality.searched_proof {
                    EqualFactSearchedProof::ByBuiltinRule(
                        EqualitySearchProofByBuiltinRule::SqrtProduct(p),
                    ) => &mut p.proof_of_requirement_facts,
                    EqualFactSearchedProof::ByBuiltinRule(
                        EqualitySearchProofByBuiltinRule::SqrtQuotient(p),
                    ) => &mut p.proof_of_requirement_facts,
                    _ => panic!("selected square-root binary builtin"),
                };
                requirements.swap(0, 1);
                compiler
                    .compile_run(&run, "sqrt_reordered_children")
                    .expect_err("requirements cannot silently follow the target factor order");
            }
        }
    }
}

#[test]
fn sqrt_square_requires_its_recorded_nonnegative_child() {
    let source = "forall x R:\n    x >= 0\n    =>:\n        sqrt(x^2) = x\n";
    let (mut run, compiler) = super::execute(source);
    let universal = super::forall_proof_mut(&mut run.statement_results[0]);
    let equality = super::equality_proof_mut(&mut universal.proved_then_facts[0].verify_result);
    let requirements = match &mut equality.searched_proof {
        EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::ElementaryArithmetic(
            crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_elementary_arithmetic::ElementaryArithmeticProof::SqrtKnownSquare { requirements, .. }
        )) => requirements,
        _ => panic!("selected known-square rule"),
    };
    requirements.clear();
    compiler
        .compile_run(&run, "sqrt_missing_requirement")
        .expect_err("the selected proof is mandatory");
    let false_identity = "forall x R:\n    sqrt(x^2) = x\n";
    let command =
        parse_launch_command(&["-strict".into(), "-e".into(), false_identity.into()]).unwrap();
    assert!(
        !Runtime::new(command)
            .run_litex_code(false_identity)
            .unwrap()
            .success
    );
}
