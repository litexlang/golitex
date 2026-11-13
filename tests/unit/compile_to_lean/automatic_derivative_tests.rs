use crate::execute::execute_fact_stmt::pointwise_derivative::{
    DerivativeConclusionProof, DerivativeConstructorProof, PointInteriorProof,
    PointwiseDerivativeProof,
};
use crate::prelude::*;
const SQUARE: &str = r#"# Differentiate a square by the recorded finite expression tree, then select its value.
have fn auto_square(x R) R=x^2
$has_derivative_at(auto_square,3,6)
derivative(auto_square,3)=6
"#;

#[test]
fn automatic_derivative_replays_structural_rational_normalization() {
    let source = r#"have fn reciprocal(x R*) R=1/x
claim:
    ? forall p R*:
        $has_derivative_at(reciprocal,p,-1/(p^2))
    $has_derivative_at(reciprocal,p,-1/(p^2))
"#;
    let (run, compiler) = super::execute(source);
    let lean = compiler
        .compile_run(&run, "structural_derivative_rational_normalization")
        .expect("the existing guarded rational certificate must remain replayable");
    assert!(lean.contains("semanticDerivative"));
}

const DIRECT_VALUE: &str = "have fn square(x R) R=x*x\n$diff_at(square,3)\nderiv(square,3)=6\n";

#[test]
fn automatic_derivative_value_equality_replays_its_checked_candidate() {
    let (run, compiler) = super::execute(DIRECT_VALUE);
    let lean = compiler
        .compile_run(&run, "direct_derivative_value")
        .expect("direct derivative equality has a checked candidate");
    assert!(lean.contains("derivativeEqCandidate"));
}

#[test]
fn automatic_derivative_value_equality_rejects_a_changed_candidate() {
    let (mut run, compiler) = super::execute(DIRECT_VALUE);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) =
        &mut run.statement_results[2]
    else {
        panic!("derivative equality statement");
    };
    let equality = super::equality_proof_mut(&mut statement.verify_result);
    let EqualFactSearchedProof::ByBuiltinStrategy(
        EqualitySearchProofByBuiltinStrategy::DerivativeValue(proof),
    ) = &mut equality.searched_proof
    else {
        panic!("direct derivative value strategy");
    };
    let candidate = super::atomic_proof_mut(&mut proof.candidate);
    let AtomicFact::HasDerivativeAtFact(candidate) = &mut candidate.fact else {
        panic!("derivative candidate");
    };
    candidate.value = Obj::Literal(Literal::Number(Number::new("7".into())));
    compiler
        .compile_run(&run, "changed_direct_derivative_value")
        .expect_err("the candidate must match the original equality value");
}

#[test]
fn automatic_derivative_closed_power_index_compiles() {
    let source = include_str!(
        "../../../examples/proof_nodes/equal/by_builtin_rule/closed_exponent_polynomial_normalization.lit"
    );
    let (run, compiler) = super::execute(source);
    compiler
        .compile_run(&run, "closed_derivative_power_index")
        .expect("exact closed exponents retain their original checked expressions");
}
fn proof(run: &mut RunLitexCodeResult) -> &mut PointwiseDerivativeProof {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) =
        &mut run.statement_results[1]
    else {
        panic!("candidate statement");
    };
    let proof = super::atomic_proof_mut(&mut statement.verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PointwiseDerivative(proof),
    ) = &mut proof.searched_proof
    else {
        panic!("selected derivative tree");
    };
    proof
}
#[test]
fn automatic_derivative_requires_original_subject_and_open_domain() {
    for mutation in 0..3 {
        let (mut run, c) = super::execute(SQUARE);
        let p = proof(&mut run);
        match mutation {
            0 => p.point = Obj::Literal(Literal::Number(Number::new("2".into()))),
            1 => p.domain.domain = Obj::StandardSet(StandardSet::C),
            _ => {
                let PointInteriorProof::StandardOpen { set, .. } = &mut p.interior else {
                    panic!("standard real domain");
                };
                *set = StandardSet::Z;
            }
        }
        c.compile_run(&run, "changed_derivative_subject")
            .expect_err("original subject and classical open domain");
    }
}
#[test]
fn automatic_derivative_rejects_changed_point_value_or_formula() {
    for value in [true, false] {
        let (mut run, c) = super::execute(SQUARE);
        let p = proof(&mut run);
        let field = if value {
            &mut p.expression.value
        } else {
            &mut p.expression.derivative
        };
        *field = Obj::Literal(Literal::Number(Number::new("99".into())));
        c.compile_run(&run, "changed_derivative_expression")
            .expect_err("point substitution and selected formula");
    }
}
#[test]
fn automatic_power_requires_original_base_and_natural_exponent() {
    for base in [true, false] {
        let (mut run, c) = super::execute(SQUARE);
        let p = proof(&mut run);
        let DerivativeConstructorProof::NaturalPower {
            base: child,
            exponent_natural,
        } = &mut p.expression.constructor
        else {
            panic!("power rule");
        };
        if base {
            child.expression = Obj::Literal(Literal::Number(Number::new("9".into())));
        } else {
            let p = super::atomic_proof_mut(exponent_natural);
            let AtomicFact::InFact(f) = &mut p.fact else {
                panic!("exponent membership");
            };
            f.element = Obj::Literal(Literal::Number(Number::new("3".into())));
        }
        c.compile_run(&run, "changed_power_rule")
            .expect_err("exact recorded power children");
    }
}
#[test]
fn automatic_derivative_uses_its_checked_conclusion_equality() {
    let (mut run, c) = super::execute(SQUARE);
    let p = proof(&mut run);
    let DerivativeConclusionProof::Candidate(checked) = &mut p.conclusion else {
        panic!("candidate equality");
    };
    let p = super::equality_proof_mut(checked);
    p.fact.right = Obj::Literal(Literal::Number(Number::new("7".into())));
    c.compile_run(&run, "changed_derivative_conclusion")
        .expect_err("original result equality");
}
const GUARDED: &str = r#"# Differentiate on a positive guarded domain using its neighbourhood certificate.
$has_derivative_at(fn(x R: x > 0) R {x*x},2,4)
"#;
fn guarded(run: &mut RunLitexCodeResult) -> &mut PointwiseDerivativeProof {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) =
        &mut run.statement_results[0]
    else {
        panic!("guarded candidate");
    };
    let p = super::atomic_proof_mut(&mut statement.verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PointwiseDerivative(p),
    ) = &mut p.searched_proof
    else {
        panic!("selected pointwise derivative");
    };
    p
}
#[test]
fn automatic_derivative_guarded_domains_require_original_guards_and_point_facts() {
    for mutation in 0..4 {
        let (mut run, c) = super::execute(GUARDED);
        let p = guarded(&mut run);
        let PointInteriorProof::Guarded { guards, .. } = &mut p.interior else {
            panic!("guarded interior");
        };
        match mutation {
            0 => guards.clear(),
            1 => {
                guards[0].point_fact = EqualFact {
                    fact_id: FactId::new(u64::MAX),
                    left: p.point.clone(),
                    right: p.point.clone(),
                    line_file: None,
                }
                .into()
            }
            2 => guards[0].operands.clear(),
            _ => {
                let crate::execute::execute_fact_stmt::pointwise_derivative::InteriorOperandProof::Continuous(operand)=&mut guards[0].operands[0] else{panic!("continuity operand");};
                operand.value = Obj::Literal(Literal::Number(Number::new("99".into())));
            }
        }
        c.compile_run(&run, "changed_guard_certificate")
            .expect_err("exact guard, point substitution and ordered operands");
    }
}
#[test]
fn classical_derivative_requires_interior_even_when_relative_continuity_holds() {
    for source in [
        "have fn isolated(x {0}) R=x*x\n$is_continuous_at(isolated,0)\n$is_differentiable_at(isolated,0)",
        "$has_derivative_at(fn(x R: x >= 0) R {x*x},0,0)",
        "derivative(fn(x R) R {abs(x)},0)=0",
    ]{
        let mut runtime=Runtime::new(LaunchCommand::Eval{code:String::new(),session:false,strict:true,language:OutputLanguage::English});
        let run=runtime.run_litex_code(source).unwrap();
        assert!(!run.success,"{source}");
    }
}
