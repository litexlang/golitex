use crate::prelude::*;

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
        r#"# A subset is absorbed by union with its containing set.
forall A set, B set:
    A $subset B
    =>:
        union(A,B) = B
"#,
        r#"# A subset is recovered by taking its relative complement twice inside the containing set.
forall A set, B set:
    B $subset A
    =>:
        set_minus(A,set_minus(A,B)) = B
"#,
        r#"# A set without a member is the empty set.
forall A set:
    not $is_nonempty_set(A)
    =>:
        A = {}
"#,
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
