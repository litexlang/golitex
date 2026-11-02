use crate::prelude::*;

#[test]
fn complex_projection_pairs_replay_the_selected_builtin() {
    for (source, law) in [
        (
            include_str!("../../../lean/examples/complex_real_projection/statement.lit"),
            "realPartOfRealValue",
        ),
        (
            include_str!("../../../lean/examples/complex_real_imaginary_zero/statement.lit"),
            "imaginaryPartOfRealValue",
        ),
        (
            include_str!(
                "../../../lean/examples/complex_rectangular_real_projection/statement.lit"
            ),
            "realPartRectangularValue",
        ),
        (
            include_str!(
                "../../../lean/examples/complex_rectangular_imaginary_projection/statement.lit"
            ),
            "imaginaryPartRectangularValue",
        ),
        (
            include_str!("../../../lean/examples/complex_product_real_projection/statement.lit"),
            "complexRealProduct",
        ),
        (
            include_str!(
                "../../../lean/examples/complex_product_imaginary_projection/statement.lit"
            ),
            "complexImaginaryProduct",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "complex_projection").unwrap();
        assert!(output.contains(&format!("Litex.{law}")));
        assert_eq!(
            output,
            compiler.compile_run(&run, "complex_projection").unwrap()
        );
    }
}

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
    let source = include_str!("../../../lean/examples/complex_real_projection/statement.lit");
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
    let source = include_str!(
        "../../../lean/examples/complex_rectangular_imaginary_projection/statement.lit"
    );
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
