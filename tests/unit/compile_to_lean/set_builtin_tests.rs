use crate::prelude::*;

#[test]
fn selected_set_identity_pairs_replay_original_evidence() {
    for (source, law) in [
        (
            include_str!("../../../lean/examples/union_absorption_subset/statement.lit"),
            "unionOfSubsetRight",
        ),
        (
            include_str!("../../../lean/examples/relative_complement_recovery/statement.lit"),
            "setMinusRecovery",
        ),
        (
            include_str!("../../../lean/examples/union_complement_decomposition/statement.lit"),
            "unionSetMinusDecomposition",
        ),
        (
            include_str!("../../../lean/examples/relative_complement_intersection/statement.lit"),
            "setMinusOfIntersection",
        ),
        (
            include_str!("../../../lean/examples/empty_from_no_members/statement.lit"),
            "emptyOfNotNonempty",
        ),
        (
            include_str!("../../../lean/examples/power_set_intersection/statement.lit"),
            "powerSetIntersection",
        ),
        (
            include_str!("../../../lean/examples/power_set_empty/statement.lit"),
            "powerEmptyValue",
        ),
        (
            include_str!("../../../lean/examples/empty_family_union/statement.lit"),
            "familyUnionEmptyValue",
        ),
        (
            include_str!("../../../lean/examples/singleton_family_union/statement.lit"),
            "familyUnionSingletonValue",
        ),
        (
            include_str!("../../../lean/examples/power_set_family_union/statement.lit"),
            "familyUnionPowerValue",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "set_builtin").unwrap();
        assert!(output.contains(&format!("Litex.{law}")), "{law}");
        if matches!(law, "familyUnionSingletonValue" | "familyUnionPowerValue") {
            assert!(output.contains("variable [_setSemantics : Litex.SetSemantics M]"));
        }
        assert_eq!(output, compiler.compile_run(&run, "set_builtin").unwrap());
    }
}

#[test]
fn union_absorption_keeps_operand_order_and_equality_orientation() {
    for swapped in [false, true] {
        for reverse in [false, true] {
            let union = if swapped { "union(B,A)" } else { "union(A,B)" };
            let equality = if reverse {
                format!("B = {union}")
            } else {
                format!("{union} = B")
            };
            let (run, compiler) = super::execute(&format!(
                "forall A set, B set:\n    A $subset B\n    =>:\n        {equality}\n"
            ));
            let output = compiler.compile_run(&run, "subset_union").unwrap();
            assert!(output.contains(if swapped {
                "Litex.unionOfSubsetLeft"
            } else {
                "Litex.unionOfSubsetRight"
            }));
        }
    }
}

#[test]
fn set_identity_rules_require_the_original_premise() {
    for source in [
        include_str!("../../../lean/examples/union_absorption_subset/statement.lit"),
        include_str!("../../../lean/examples/relative_complement_recovery/statement.lit"),
        include_str!("../../../lean/examples/empty_from_no_members/statement.lit"),
    ] {
        let (mut run, compiler) = super::execute(source);
        let universal = super::forall_proof_mut(&mut run.statement_results[0]);
        let equality = super::equality_proof_mut(&mut universal.proved_then_facts[0].verify_result);
        let requirements = match &mut equality.searched_proof {
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::UnionAbsorptionFromSubset(p),
            ) => &mut p.proof_of_requirement_facts,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::SetMinusRecoversSubset(p),
            ) => &mut p.proof_of_requirement_facts,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::EmptySetFromNotNonempty(p),
            ) => &mut p.proof_of_requirement_facts,
            _ => panic!("selected set premise rule"),
        };
        requirements.clear();
        compiler
            .compile_run(&run, "missing_set_premise")
            .expect_err("true-looking target shapes do not replace premise evidence");
    }
}

#[test]
fn double_relative_complement_does_not_recover_an_arbitrary_set() {
    let source = "forall A set, B set:\n    set_minus(A,set_minus(A,B)) = B\n";
    let command = parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
    assert!(
        !Runtime::new(command)
            .run_litex_code(source)
            .unwrap()
            .success
    );
}
