use crate::prelude::*;

#[test]
fn selected_transcendental_and_absolute_square_rules_compile() {
    for (source, law, variant) in [
        (
            r#"# The exponential of a sum is the product of the exponentials.
forall a,b R:
    exp(a+b)=exp(a)*exp(b)
"#,
            "exponentialSumValue",
            "exp",
        ),
        (
            r#"# The sine addition formula for two real arguments.
forall a,b R:
    sin(a+b)=sin(a)*cos(b)+cos(a)*sin(b)
"#,
            "sineAdditionComplex",
            "sin",
        ),
        (
            r#"# The cosine addition formula for two real arguments.
forall a,b R:
    cos(a+b)=cos(a)*cos(b)-sin(a)*sin(b)
"#,
            "cosineAdditionComplex",
            "cos",
        ),
        (
            r#"# The square of a real number is unchanged by absolute value.
forall a R:
    abs(a^2)=a^2
"#,
            "absoluteSquareValue",
            "abs",
        ),
    ] {
        let (mut run, compiler) = super::execute(source);
        let universal = super::forall_proof_mut(&mut run.statement_results[0]);
        let proof = super::equality_proof_mut(&mut universal.proved_then_facts[0].verify_result);
        assert!(matches!(
            (variant, &proof.searched_proof),
            (
                "exp",
                EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::ExpOfSum(
                    _
                ))
            ) | (
                "sin",
                EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::SinOfSum(
                    _
                ))
            ) | (
                "cos",
                EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::CosOfSum(
                    _
                ))
            ) | (
                "abs",
                EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::AbsSquare(
                    _
                ))
            )
        ));
        let output = compiler.compile_run(&run, "selected_addition").unwrap();
        assert!(output.contains(&format!("Litex.{law}")));
        if variant == "exp" {
            assert!(output.contains("variable [_setSemantics : Litex.SetSemantics M]"));
        }
        assert_eq!(
            output,
            compiler.compile_run(&run, "selected_addition").unwrap()
        );
    }
}

#[test]
fn addition_rules_preserve_source_permutations_and_equality_orientation() {
    for expression in [
        "exp(a+b)=exp(b)*exp(a)",
        "sin(a+b)=cos(a)*sin(b)+sin(a)*cos(b)",
        "sin(a+b)=sin(a)*cos(b)+sin(b)*cos(a)",
        "cos(a+b)=cos(b)*cos(a)-sin(a)*sin(b)",
        "exp(a)*exp(b)=exp(a+b)",
        "sin(a)*cos(b)+cos(a)*sin(b)=sin(a+b)",
        "cos(a)*cos(b)-sin(a)*sin(b)=cos(a+b)",
        "a^2=abs(a^2)",
    ] {
        let (run, compiler) = super::execute(&format!("forall a,b R:\n    {expression}\n"));
        compiler.compile_run(&run, "addition_permutations").unwrap();
    }
}

#[test]
fn sine_certificate_cannot_be_used_for_cosine() {
    let source="forall a,b R:\n    sin(a+b)=sin(a)*cos(b)+cos(a)*sin(b)\nforall a,b R:\n    cos(a+b)=cos(a)*cos(b)-sin(a)*sin(b)\n";
    let (mut run, compiler) = super::execute(source);
    let (first, second) = run.statement_results.split_at_mut(1);
    let first = super::forall_proof_mut(&mut first[0]);
    let second = super::forall_proof_mut(&mut second[0]);
    let first = super::equality_proof_mut(&mut first.proved_then_facts[0].verify_result);
    let second = super::equality_proof_mut(&mut second.proved_then_facts[0].verify_result);
    std::mem::swap(&mut first.searched_proof, &mut second.searched_proof);
    compiler
        .compile_run(&run, "wrong_addition_certificate")
        .expect_err("the exact selected operation is part of the certificate");
}

#[test]
fn absolute_square_requires_its_original_real_base_proof() {
    let source = "forall a,b R:\n    abs(a^2)=a^2\n    abs(b^2)=b^2\n";
    let (mut run, compiler) = super::execute(source);
    let universal = super::forall_proof_mut(&mut run.statement_results[0]);
    let (first, second) = universal.proved_then_facts.split_at_mut(1);
    let first = super::equality_proof_mut(&mut first[0].verify_result);
    let second = super::equality_proof_mut(&mut second[0].verify_result);
    let (
        EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::AbsSquare(a)),
        EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::AbsSquare(b)),
    ) = (&mut first.searched_proof, &mut second.searched_proof)
    else {
        panic!("original square certificates");
    };
    std::mem::swap(&mut a.base_real, &mut b.base_real);
    compiler
        .compile_run(&run, "wrong_square_base")
        .expect_err("base realness belongs to the exact original base");
}
