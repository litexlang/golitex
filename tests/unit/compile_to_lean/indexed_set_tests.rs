use crate::prelude::*;

#[test]
fn closed_integer_range_enumeration_replays_literal_rule() {
    let (run, compiler) = super::execute(include_str!(
        "../../../lean/examples/closed_integer_range_enumeration/statement.lit"
    ));
    for statement in &run.statement_results {
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(result)) = statement else {
            panic!("fact")
        };
        let selected = &super::equality_proof(&result.verify_result).searched_proof;
        assert!(matches!(
            selected,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::ClosedRangeLiteralExpansion(_)
            )
        ));
    }
    compiler
        .compile_run(&run, "closed_integer_range_enumeration")
        .unwrap();
}

#[test]
fn closed_integer_range_enumeration_rejects_retagged_rule() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_equality_identities_wave13::ClosedRangeLiteralExpansionBuiltinRuleProof;
    let (mut run, compiler) = super::execute("1 = 1");
    let equality = super::equality_proof_mut(
        &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
    );
    equality.searched_proof = EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::ClosedRangeLiteralExpansion(
            ClosedRangeLiteralExpansionBuiltinRuleProof {},
        ),
    );
    assert!(compiler.compile_run(&run, "wrong_range_rule").is_err());
}

#[test]
fn new_set_object_examples_replay() {
    for source in [
        include_str!("../../../lean/examples/symmetric_difference_membership/statement.lit"),
        include_str!("../../../lean/examples/symmetric_difference_identities/statement.lit"),
        include_str!("../../../lean/examples/indexed_union_member/statement.lit"),
        include_str!("../../../lean/examples/indexed_intersection_member/statement.lit"),
        include_str!("../../../lean/examples/indexed_product_member/statement.lit"),
        include_str!("../../../lean/examples/family_intersection_member/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        compiler
            .compile_run(&run, "set_object_examples")
            .unwrap_or_else(|e| panic!("{source}\n{e:?}"));
    }
}

#[test]
fn family_intersection_retains_nonempty_wd_and_rejects_missing_evidence() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SetOperatorObjWellDefinedProofByDef as W;
    let (mut run, compiler) = super::execute("have F nonempty_set\n$is_set(family_intersect(F))");
    let proof = super::atomic_proof_mut(
        &mut super::fact_statement_mut(&mut run.statement_results[1]).verify_result,
    );
    let DetailedObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::SetOperator(W::FamilyIntersect(wd)),
        ..
    } = (&mut proof
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .well_defined_of_each_parameter[0])
        .as_detailed_mut()
        .unwrap()
    else {
        panic!("family intersection constructor WD");
    };
    assert_eq!(wd.child_obj_well_defined.len(), 1);
    assert_eq!(wd.requirement_fact_verified.len(), 1);
    assert!(matches!(
        super::super::helper::source_subject(&wd.requirement_fact_verified[0]).unwrap(),
        Fact::AtomicFact(AtomicFact::IsNonemptySetFact(_))
    ));
    wd.requirement_fact_verified.clear();
    assert!(compiler
        .compile_run(&run, "missing_family_nonempty")
        .is_err());
}

#[test]
fn indexed_set_wd_rejects_missing_and_reordered_requirements() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SetOperatorObjWellDefinedProofByDef as W;
    for name in ["index_union", "index_intersect", "index_cart"] {
        let (carrier, ret) = if name == "index_cart" {
            ("nonempty_set", "X")
        } else {
            ("set", "power_set(X)")
        };
        let source = format!(
            "have I nonempty_set\nhave X {carrier}\nhave A fn(k I) {ret}\n$is_set({name}(I,X,A))"
        );
        for reorder in [false, true] {
            let (mut run, compiler) = super::execute(&source);
            let proof = super::atomic_proof_mut(
                &mut super::fact_statement_mut(&mut run.statement_results[3]).verify_result,
            );
            let DetailedObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::SetOperator(wd),
                ..
            } = (&mut proof
                .well_defined_proof
                .as_detailed_mut()
                .unwrap()
                .well_defined_of_each_parameter[0])
                .as_detailed_mut()
                .unwrap()
            else {
                panic!("constructor WD")
            };
            let requirements = match wd {
                W::IndexUnion(p) => &mut p.requirement_fact_verified,
                W::IndexIntersect(p) => &mut p.requirement_fact_verified,
                W::IndexCart(p) => &mut p.requirement_fact_verified,
                _ => panic!(),
            };
            if reorder {
                requirements.swap(0, 1)
            } else {
                requirements.pop();
            }
            assert!(compiler.compile_run(&run, "bad_index_wd").is_err());
        }
    }
}

#[test]
fn new_set_objects_reject_empty_index_and_missing_membership_evidence() {
    for source in [
        "let family = fn(k {}) power_set(N) {{1}}\nlet U = index_union({},N,family)",
        "let family = fn(k {}) power_set(N) {{1}}\nlet U = index_intersect({},N,family)",
        "let family = fn(k {}) power_set(N) {{1}}\nlet U = index_cart({},power_set(N),family)",
        "forall A,B set,x A:\n    x $in set_diff(A,B)",
        "let invalid = family_intersect({})",
        "have F set\nlet invalid = family_intersect(F)",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        let run = runtime.run_litex_code(source).unwrap();
        assert!(!run.success, "{source}");
        assert!(super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "bad_set_source")
            .is_err());
    }
}
