use crate::execute::execute_fact_stmt::structural_riemann_integral::{
    RiemannConstructorProof, StructuralRiemannIntegralProof,
};
use crate::prelude::*;

const BASIC_SOURCE: &str = r#"integral(fn(x R) R {(x+1)^2},0,1)=7/3
forall n N,a,b R:
    $has_riemann_integral(fn(x R) R {x^n},a,b,(b^(n+1)-a^(n+1))/(n+1))
"#;

const COEFFICIENT_SOURCE: &str = r#"forall c R*:
    integral(fn(x R) R {(x+1)/c},0,1)=3/(2*c)
    integral(fn(x R) R {x/c+1},0,1)=1/(2*c)+1
"#;

fn run_on_large_stack(f: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(f)
        .expect("spawn polynomial integral compiler test thread")
        .join()
        .expect("polynomial integral compiler test panicked");
}

#[test]
fn polynomial_integral_compiler_replays_normalization_and_integration() {
    run_on_large_stack(|| {
        for (source, name) in [
            (BASIC_SOURCE, "polynomial_integrals"),
            (COEFFICIENT_SOURCE, "polynomial_integral_coefficients"),
        ] {
            let (run, compiler) = super::execute(source);
            let output = compiler.compile_run(&run, name).unwrap();
            assert!(output.contains("riemannIntegralOfPolynomialFormula"));
            assert!(output.contains("_integral_normalization"));
            assert!(output.contains("variable [_functionSemantics : Litex.FunctionSemantics M]"));
            assert!(output.contains("set_option maxHeartbeats 1000000 in\ntheorem "));
            assert_eq!(output, compiler.compile_run(&run, name).unwrap());
        }
    });
}

fn polynomial_proof(run: &mut RunLitexCodeResult) -> &mut StructuralRiemannIntegralProof {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) =
        &mut run.statement_results[0]
    else {
        panic!("integral equality");
    };
    let equality = super::equality_proof_mut(&mut statement.verify_result);
    let EqualFactSearchedProof::ByBuiltinStrategy(
        EqualitySearchProofByBuiltinStrategy::RiemannIntegralValue(value),
    ) = &mut equality.searched_proof
    else {
        panic!("integral value strategy");
    };
    let candidate = super::atomic_proof_mut(&mut value.candidate);
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::StructuralRiemannIntegral(proof),
    ) = &mut candidate.searched_proof
    else {
        panic!("structural integral proof");
    };
    proof
}

#[test]
fn polynomial_integral_compiler_rejects_changed_evidence() {
    run_on_large_stack(|| {
        let single = "integral(fn(x R) R {(x+1)^2},0,1)=7/3";
        for mutation in 0..4 {
            let (mut run, compiler) = super::execute(single);
            let proof = polynomial_proof(&mut run);
            let wrong = Obj::Literal(Literal::Number(Number::new("99".into())));
            match mutation {
                0 => proof.lower = wrong,
                1 => proof.expression.integral = wrong,
                2 => {
                    let RiemannConstructorProof::Polynomial { normalized, .. } =
                        &mut proof.expression.constructor
                    else {
                        panic!("normalization evidence");
                    };
                    normalized.expression = wrong;
                }
                _ => {
                    let (mut donor_run, _) = super::execute(single);
                    let donor = polynomial_proof(&mut donor_run);
                    let RiemannConstructorProof::Polynomial { normalized, .. } =
                        &mut proof.expression.constructor
                    else {
                        panic!("normalization evidence");
                    };
                    std::mem::swap(
                        &mut normalized.constructor,
                        &mut donor.expression.constructor,
                    );
                }
            }
            compiler
                .compile_run(&run, "changed_integral_proof")
                .expect_err("the original subject and normalization must agree");
        }
    });
}
