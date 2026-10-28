use crate::prelude::*;

#[test]
fn hyperbolic_examples_compile_original_domains_values_rules_and_functions() {
    for source in [
        include_str!("../../../lean/examples/hyperbolic_domains/statement.lit"),
        include_str!("../../../lean/examples/hyperbolic_zero_values/statement.lit"),
        include_str!("../../../lean/examples/hyperbolic_definitions/statement.lit"),
        include_str!("../../../lean/examples/hyperbolic_parity/statement.lit"),
        include_str!("../../../lean/examples/hyperbolic_nonzero/statement.lit"),
        include_str!("../../../lean/examples/hyperbolic_function/statement.lit"),
        include_str!("../../../lean/examples/hyperbolic_identities/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        compiler.compile_run(&run, "hyperbolic_example").unwrap();
    }
}

#[test]
fn hyperbolic_wd_rejects_missing_or_wrong_nonzero_argument() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::HyperbolicOperatorObjWellDefinedProofByDef;
    for missing in [false, true] {
        let (mut run, compiler) = super::execute("$is_set(coth(1))");
        let atom = super::atomic_proof_mut(
            &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
        );
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::HyperbolicOperator(
                    HyperbolicOperatorObjWellDefinedProofByDef::Coth(wd),
                ),
            ..
        } = (&mut atom
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .well_defined_of_each_parameter[0])
            .as_detailed_mut()
            .unwrap()
        else {
            panic!("coth WD");
        };
        if missing {
            wd.requirement_fact_verified.pop();
        } else {
            let premise = super::atomic_proof_mut(&mut wd.requirement_fact_verified[1]);
            let AtomicFact::NotEqualFact(fact) = &mut premise.fact else {
                panic!("nonzero");
            };
            fact.left = Obj::Literal(Literal::Number(Number::new("2".into())));
        }
        assert!(compiler.compile_run(&run, "bad_hyperbolic_guard").is_err());
    }
}

#[test]
fn hyperbolic_definition_rejects_another_selected_rule() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_hyperbolic::{HyperbolicEqualityProof, CoshDefinitionProof};
    let (mut run, compiler) = super::execute("forall x R:\n    sinh(x) = (exp(x)-exp(-x))/2\n");
    let all = super::forall_proof_mut(&mut run.statement_results[0]);
    let equality = super::equality_proof_mut(&mut all.proved_then_facts[0].verify_result);
    assert!(matches!(
        equality.searched_proof,
        EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::Hyperbolic(_))
    ));
    equality.searched_proof =
        EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::Hyperbolic(
            HyperbolicEqualityProof::CoshDefinition(CoshDefinitionProof),
        ));
    assert!(compiler
        .compile_run(&run, "changed_hyperbolic_rule")
        .is_err());
}

#[test]
fn hyperbolic_identity_rejects_wrong_subject_and_selected_rule() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_hyperbolic::{HyperbolicEqualityProof, TanhSechSquareProof};
    for wrong_subject in [false, true] {
        let (mut run, compiler) = super::execute("forall x R:\n    cosh(x)^2 - sinh(x)^2 = 1\n");
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let equality = super::equality_proof_mut(&mut all.proved_then_facts[0].verify_result);
        assert!(matches!(
            equality.searched_proof,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::Hyperbolic(
                HyperbolicEqualityProof::HyperbolicPythagorean(_)
            ))
        ));
        if wrong_subject {
            equality.fact.right = Obj::Literal(Literal::Number(Number::new("2".into())));
        } else {
            equality.searched_proof = EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::Hyperbolic(
                    HyperbolicEqualityProof::TanhSechSquare(TanhSechSquareProof),
                ),
            );
        }
        assert!(compiler
            .compile_run(&run, "changed_hyperbolic_identity")
            .is_err());
    }
}
