use crate::prelude::*;

#[test]
fn imaginary_examples_replay_values_polynomials_and_function_proofs() {
    for source in [
        include_str!("../../../lean/examples/imaginary_unit_values/statement.lit"),
        include_str!("../../../lean/examples/complex_polynomial_identity/statement.lit"),
        include_str!("../../../lean/examples/complex_rotation/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "complex_numbers").unwrap();
        assert!(output.contains("Complex.I"));
        assert_eq!(
            output,
            compiler.compile_run(&run, "complex_numbers").unwrap()
        );
    }
}

#[test]
fn imaginary_closed_equality_rejects_changed_real_and_imaginary_certificates() {
    for imaginary in [false, true] {
        let (mut run, compiler) = super::execute("i * i = -1\n");
        let equality = super::equality_proof_mut(
            &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
        );
        let EqualFactSearchedProof::ByClosedCalculation(p) = &mut equality.searched_proof else {
            panic!("closed complex equality")
        };
        let ClosedValuePair::Complex {
            left_real,
            left_imaginary,
            ..
        } = &mut p.values
        else {
            panic!("exact complex coordinates")
        };
        if imaginary {
            *left_imaginary = EvalRational::new(1, 1).unwrap();
        } else {
            *left_real = EvalRational::new(1, 1).unwrap();
        }
        assert_eq!(
            compiler
                .compile_run(&run, "forged_complex")
                .unwrap_err()
                .route,
            "ClosedEquality/Values"
        );
    }
}

#[test]
fn imaginary_nonzero_rejects_equal_or_changed_coordinate_evidence() {
    let (mut run, compiler) = super::execute("i != 0\n");
    let atomic = super::atomic_proof_mut(
        &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
    );
    let AtomicExceptEqualityFactSearchedProof::ByClosedCalculation(
        ClosedAtomicExceptEqualityCalculationProof::NotEqual(p),
    ) = &mut atomic.searched_proof
    else {
        panic!("closed complex nonzero")
    };
    let ClosedValuePair::Complex { left_imaginary, .. } = &mut p.values else {
        panic!("exact complex coordinates")
    };
    *left_imaginary = EvalRational::new(0, 1).unwrap();
    assert_eq!(
        compiler
            .compile_run(&run, "forged_nonzero")
            .unwrap_err()
            .route,
        "ClosedNotEqual/Values"
    );
}

#[test]
fn imaginary_membership_checks_exact_coordinates() {
    let (mut run, compiler) = super::execute("i $in C\n");
    let atomic = super::atomic_proof_mut(
        &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
    );
    let AtomicExceptEqualityFactSearchedProof::ByClosedCalculation(
        ClosedAtomicExceptEqualityCalculationProof::In(
            ClosedMembershipCalculationProof::StandardSet {
                value: ClosedScalarValue::ExactComplex { imaginary, .. },
                ..
            },
        ),
    ) = &mut atomic.searched_proof
    else {
        panic!("closed imaginary membership")
    };
    *imaginary = EvalRational::new(0, 1).unwrap();
    assert_eq!(
        compiler
            .compile_run(&run, "forged_member")
            .unwrap_err()
            .route,
        "ClosedMembership/Value"
    );
}

#[test]
fn imaginary_division_still_requires_original_nonzero_wd() {
    let (mut run, compiler) = super::execute("i / i = 1\n");
    let equality = super::equality_proof_mut(
        &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
    );
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::ArithmeticOperator(
                ArithmeticOperatorObjWellDefinedProofByDef::Div(p),
            ),
        ..
    } = (&mut equality.well_defined_proof.as_detailed_mut().unwrap().left)
        .as_detailed_mut()
        .unwrap()
    else {
        panic!("division construction")
    };
    p.requirement_fact_verified.remove(0);
    assert_eq!(
        compiler
            .compile_run(&run, "missing_nonzero")
            .unwrap_err()
            .route,
        "WD/Arithmetic"
    );
}

#[test]
fn imaginary_invalid_carriers_equalities_and_division_reject() {
    for source in [
        "i $in R",
        "i < 0",
        "i * i = 1",
        "i * i != -1",
        "$is_set(i / 0)",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        let run = runtime.run_litex_code(source).unwrap();
        assert!(!run.success, "{source}");
        assert!(super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "invalid_complex")
            .is_err());
    }
}
