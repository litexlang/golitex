use crate::prelude::*;

#[test]
fn abs_builtin_routes_replay_both_orientations() {
    for (binders, left, right, law) in [
        ("x R", "abs(abs(x))", "abs(x)", "absIdempotent"),
        ("x R", "abs(-x)", "abs(x)", "absNegation"),
        ("x R", "abs(0 - x)", "abs(x)", "absNegation"),
        ("x R", "abs((-1) * x)", "abs(x)", "absNegation"),
        ("x R", "abs(x * (-1))", "abs(x)", "absNegation"),
        ("x R, y R", "abs(x * y)", "abs(x) * abs(y)", "absProduct"),
        ("x R, y R", "abs(y * x)", "abs(x) * abs(y)", "absProduct"),
        ("x R, y R", "abs(x * y)", "abs(y) * abs(x)", "absProduct"),
    ] {
        for reverse in [false, true] {
            let equality = if reverse {
                format!("{right} = {left}")
            } else {
                format!("{left} = {right}")
            };
            let (mut run, compiler) =
                super::execute(&format!("forall {binders}:\n    {equality}\n"));
            let universal = super::forall_proof_mut(&mut run.statement_results[0]);
            let selected =
                super::equality_proof_mut(&mut universal.proved_then_facts[0].verify_result);
            assert!(
                matches!(
                    selected.searched_proof,
                    EqualFactSearchedProof::ByBuiltinRule(
                        EqualitySearchProofByBuiltinRule::AbsAbsAbsorption(_)
                            | EqualitySearchProofByBuiltinRule::AbsOfNegation(_)
                            | EqualitySearchProofByBuiltinRule::AbsProduct(_)
                    )
                ),
                "{equality}"
            );
            let output = compiler.compile_run(&run, "abs_builtin").unwrap();
            assert!(output.contains(&format!("Litex.{law}")), "{equality}");
            assert_eq!(output, compiler.compile_run(&run, "abs_builtin").unwrap());
        }
    }
}

#[test]
fn abs_nonpositive_replays_its_exact_order_child() {
    for order in ["<=", "<"] {
        for reverse in [false, true] {
            let equality = if reverse {
                "0 - x = abs(x)"
            } else {
                "abs(x) = 0 - x"
            };
            let source = format!("forall x R:\n    x {order} 0\n    =>:\n        {equality}\n");
            let (mut run, compiler) = super::execute(&source);
            let output = compiler.compile_run(&run, "abs_nonpositive").unwrap();
            assert!(output.contains("Litex.absOfNonpositive"));
            let universal = super::forall_proof_mut(&mut run.statement_results[0]);
            let selected =
                super::equality_proof_mut(&mut universal.proved_then_facts[0].verify_result);
            let EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::AbsNonposEqualsNegation(p),
            ) = &mut selected.searched_proof
            else {
                panic!("selected nonpositive rule");
            };
            p.proof_of_requirement_facts.clear();
            compiler
                .compile_run(&run, "abs_missing_child")
                .expect_err("the recorded order proof is mandatory");
        }
    }
}

#[test]
fn abs_builtin_certificates_cannot_prove_another_equality() {
    for source in [
        "forall x R:\n    abs(abs(x)) = abs(x)\n",
        "forall x R:\n    abs(-x) = abs(x)\n",
        "forall x R, y R:\n    abs(x * y) = abs(x) * abs(y)\n",
    ] {
        let (mut original, _) = super::execute(source);
        let (mut target, compiler) = super::execute("forall x R:\n    x = x\n");
        let original = super::forall_proof_mut(&mut original.statement_results[0]);
        let target_proof = super::forall_proof_mut(&mut target.statement_results[0]);
        let original = super::equality_proof_mut(&mut original.proved_then_facts[0].verify_result);
        let target_proof =
            super::equality_proof_mut(&mut target_proof.proved_then_facts[0].verify_result);
        std::mem::swap(
            &mut original.searched_proof,
            &mut target_proof.searched_proof,
        );
        compiler
            .compile_run(&target, "abs_wrong_subject")
            .expect_err("a selected rule certifies only its own schema");
    }
}
