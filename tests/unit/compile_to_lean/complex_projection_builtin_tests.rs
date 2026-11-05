use crate::prelude::*;

#[test]
fn rectangular_projection_keeps_all_source_permutations() {
    for imaginary in [false, true] {
        for real_first in [false, true] {
            for unit_first in [false, true] {
                for reversed in [false, true] {
                    let scaled = if unit_first { "i * y" } else { "y * i" };
                    let input = if real_first {
                        format!("x + {scaled}")
                    } else {
                        format!("{scaled} + x")
                    };
                    let left = format!("{}({input})", if imaginary { "img" } else { "re" });
                    let right = if imaginary { "y" } else { "x" };
                    let equality = if reversed {
                        format!("{right} = {left}")
                    } else {
                        format!("{left} = {right}")
                    };
                    let (run, compiler) =
                        super::execute(&format!("forall x R, y R:\n    {equality}\n"));
                    assert!(compiler
                        .compile_run(&run, "rectangular_projection")
                        .unwrap()
                        .contains(if imaginary {
                            "Litex.imaginaryPartRectangularValue"
                        } else {
                            "Litex.realPartRectangularValue"
                        }));
                }
            }
        }
    }
}

#[test]
fn real_projection_requires_original_real_membership() {
    let source = r#"# Real-part projection fixes real numbers.
forall x R:
    re(x) = x
"#;
    let (mut run, compiler) = super::execute(source);
    let universal = super::forall_proof_mut(&mut run.statement_results[0]);
    let equality = super::equality_proof_mut(&mut universal.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::ReOfReal(p)) =
        &mut equality.searched_proof
    else {
        panic!("selected real projection");
    };
    p.proof_of_requirement_facts.clear();
    compiler
        .compile_run(&run, "missing_real_membership")
        .expect_err("WD alone does not supply the selected real premise");
    let false_identity = "forall z C:\n    img(z) = 0\n";
    let command =
        parse_launch_command(&["-strict".into(), "-e".into(), false_identity.into()]).unwrap();
    assert!(
        !Runtime::new(command)
            .run_litex_code(false_identity)
            .unwrap()
            .success
    );
}

#[test]
fn rectangular_projection_rejects_swapped_coefficient_proofs() {
    let source = r#"# The imaginary coordinate of a rectangular complex number is its imaginary coefficient.
forall x R, y R:
    img(x + y * i) = y
"#;
    let (mut run, compiler) = super::execute(source);
    let universal = super::forall_proof_mut(&mut run.statement_results[0]);
    let equality = super::equality_proof_mut(&mut universal.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::ImgOfRealPlusImagScaled(p),
    ) = &mut equality.searched_proof
    else {
        panic!("selected rectangular projection");
    };
    std::mem::swap(
        &mut p.real_coefficient_real,
        &mut p.imaginary_coefficient_real,
    );
    compiler
        .compile_run(&run, "wrong_coefficient_proofs")
        .expect_err("the original two real coefficients have distinct roles");
}
