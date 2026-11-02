use crate::prelude::*;

#[test]
fn elementary_minmax_pairs_replay_selected_certificates() {
    for (source, law) in [
        (
            include_str!("../../../lean/examples/minimum_associativity/statement.lit"),
            "minMaxAssociativeValue",
        ),
        (
            include_str!("../../../lean/examples/maximum_associativity/statement.lit"),
            "minMaxAssociativeValue",
        ),
        (
            include_str!("../../../lean/examples/minimum_maximum_sum/statement.lit"),
            "minMaxSumValue",
        ),
        (
            include_str!("../../../lean/examples/minimum_maximum_product/statement.lit"),
            "minMaxProductValue",
        ),
        (
            include_str!("../../../lean/examples/minimum_translation/statement.lit"),
            "minTranslationValue",
        ),
        (
            include_str!("../../../lean/examples/maximum_negation/statement.lit"),
            "maxNegationValue",
        ),
    ] {
        let (mut run, compiler) = super::execute(source);
        let universal = super::forall_proof_mut(&mut run.statement_results[0]);
        let equality = super::equality_proof_mut(&mut universal.proved_then_facts[0].verify_result);
        assert!(matches!(
            equality.searched_proof,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::ElementaryIdentity(_)
            )
        ));
        let output = compiler.compile_run(&run, "elementary_identity").unwrap();
        assert!(output.contains(&format!("Litex.{law}")));
        assert_eq!(
            output,
            compiler.compile_run(&run, "elementary_identity").unwrap()
        );
    }
}

#[test]
fn sorted_pair_rules_preserve_each_operand_and_orientation() {
    for product in [false, true] {
        for min_first in [false, true] {
            for reverse_args in [false, true] {
                for reversed in [false, true] {
                    let op = if product { "*" } else { "+" };
                    let left = if min_first {
                        format!("min(x,y) {op} max(x,y)")
                    } else {
                        format!("max(x,y) {op} min(x,y)")
                    };
                    let right = if reverse_args {
                        format!("y {op} x")
                    } else {
                        format!("x {op} y")
                    };
                    let equality = if reversed {
                        format!("{right} = {left}")
                    } else {
                        format!("{left} = {right}")
                    };
                    let (run, compiler) =
                        super::execute(&format!("forall x R, y R:\n    {equality}\n"));
                    assert!(compiler.compile_run(&run, "sorted_pair").unwrap().contains(
                        if product {
                            "Litex.minMaxProductValue"
                        } else {
                            "Litex.minMaxSumValue"
                        }
                    ));
                }
            }
        }
    }
}

#[test]
fn elementary_certificate_cannot_change_its_operation() {
    let source = include_str!("../../../lean/examples/minimum_associativity/statement.lit");
    let other = include_str!("../../../lean/examples/maximum_associativity/statement.lit");
    let (mut original, _) = super::execute(source);
    let (mut target, compiler) = super::execute(other);
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
        .compile_run(&target, "wrong_operation")
        .expect_err("minimum evidence is not maximum evidence");
}

#[test]
fn negation_does_not_preserve_maximum() {
    let source = "forall x R, y R:\n    max(-x,-y) = -max(x,y)\n";
    let command = parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
    assert!(
        !Runtime::new(command)
            .run_litex_code(source)
            .unwrap()
            .success
    );
}
