use crate::prelude::*;

#[test]
fn six_selected_cardinality_rules_replay_their_own_certificates() {
    for (source, law, selected) in [
        (
            include_str!("../../../lean/examples/finite_set_zero_cardinality/statement.lit"),
            "emptyOfCardinalityZero",
            "zero",
        ),
        (
            include_str!("../../../lean/examples/finite_sets_equal_cardinality/statement.lit"),
            "sameOfFiniteSubsetCardinality",
            "equal",
        ),
        (
            include_str!("../../../lean/examples/finite_difference_cardinality/statement.lit"),
            "finiteCardinalityDifferenceValue",
            "minus",
        ),
        (
            include_str!("../../../lean/examples/finite_union_cardinality/statement.lit"),
            "finiteCardinalityUnionValue",
            "union",
        ),
        (
            include_str!("../../../lean/examples/finite_subset_cardinality_bound/statement.lit"),
            "finiteCardinalitySubsetLe",
            "le",
        ),
        (
            include_str!("../../../lean/examples/finite_proper_subset_cardinality/statement.lit"),
            "finiteCardinalityProperSubsetLt",
            "lt",
        ),
    ] {
        let (mut run, compiler) = super::execute(source);
        let universal = super::forall_proof_mut(&mut run.statement_results[0]);
        let actual = &mut universal.proved_then_facts[0].verify_result;
        let chosen = if matches!(selected, "le" | "lt") {
            let actual = super::atomic_proof_mut(actual);
            match (&actual.searched_proof,selected) {
                (AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less_equal::LessEqualFactSearchProofByBuiltinRule::FiniteSetSizeSubsetLe(_))),"le")=>true,
                (AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less::LessFactSearchProofByBuiltinRule::FiniteSetSizeProperSubsetLt(_))),"lt")=>true,
                _=>false,
            }
        } else {
            let actual = super::equality_proof_mut(actual);
            matches!(
                (&actual.searched_proof, selected),
                (
                    EqualFactSearchedProof::ByBuiltinRule(
                        EqualitySearchProofByBuiltinRule::EmptySetFromSizeZero(_)
                    ),
                    "zero"
                ) | (
                    EqualFactSearchedProof::ByBuiltinRule(
                        EqualitySearchProofByBuiltinRule::FiniteSetEqualFromSubsetSize(_)
                    ),
                    "equal"
                ) | (
                    EqualFactSearchedProof::ByBuiltinRule(
                        EqualitySearchProofByBuiltinRule::FiniteSetSizeSetMinus(_)
                    ),
                    "minus"
                ) | (
                    EqualFactSearchedProof::ByBuiltinRule(
                        EqualitySearchProofByBuiltinRule::FiniteSetSizeUnion(_)
                    ),
                    "union"
                )
            )
        };
        assert!(chosen, "{selected}");
        let output = compiler.compile_run(&run, "finite_cardinality").unwrap();
        assert!(output.contains(&format!("Litex.{law}")));
        if matches!(selected, "equal" | "lt") {
            assert!(output.contains("variable [_setSemantics : Litex.SetSemantics M]"));
        }
        assert_eq!(
            output,
            compiler.compile_run(&run, "finite_cardinality").unwrap()
        );
    }
}

#[test]
fn finite_union_cardinality_keeps_all_original_permutations() {
    for union in ["union(A,B)", "union(B,A)"] {
        for intersection in ["intersect(A,B)", "intersect(B,A)"] {
            for sum in [
                "finite_set_size(A)+finite_set_size(B)",
                "finite_set_size(B)+finite_set_size(A)",
            ] {
                for reversed in [false, true] {
                    let lhs = format!("finite_set_size({union})");
                    let rhs = format!("{sum}-finite_set_size({intersection})");
                    let eq = if reversed {
                        format!("{rhs}={lhs}")
                    } else {
                        format!("{lhs}={rhs}")
                    };
                    let (run, compiler) =
                        super::execute(&format!("forall A finite_set,B finite_set:\n    {eq}\n"));
                    assert!(compiler
                        .compile_run(&run, "union_permutations")
                        .unwrap()
                        .contains("Litex.finiteCardinalityUnionValue"));
                }
            }
        }
    }
}

#[test]
fn finite_cardinality_equalities_preserve_both_inclusion_and_equality_directions() {
    for inclusion in ["A $subset B", "B $subset A"] {
        for eq in ["A=B", "B=A"] {
            let source=format!("forall A finite_set,B finite_set:\n    {inclusion}\n    finite_set_size(A)=finite_set_size(B)\n    =>:\n        {eq}\n");
            let (run, compiler) = super::execute(&source);
            compiler
                .compile_run(&run, "finite_equality_orientations")
                .unwrap();
        }
    }
}

#[test]
fn cardinality_certificates_cannot_lose_or_exchange_distinct_premises() {
    for source in [
        include_str!("../../../lean/examples/finite_set_zero_cardinality/statement.lit"),
        include_str!("../../../lean/examples/finite_sets_equal_cardinality/statement.lit"),
    ] {
        let (mut run, compiler) = super::execute(source);
        let universal = super::forall_proof_mut(&mut run.statement_results[0]);
        let proof = super::equality_proof_mut(&mut universal.proved_then_facts[0].verify_result);
        match &mut proof.searched_proof {
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::EmptySetFromSizeZero(p),
            ) => p.proof_of_requirement_facts.clear(),
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::FiniteSetEqualFromSubsetSize(p),
            ) => std::mem::swap(&mut p.size_equal_proof, &mut p.subset_proof),
            _ => panic!("original finite-cardinality rule"),
        }
        compiler
            .compile_run(&run, "corrupted_cardinality_premise")
            .expect_err("the original zero/cardinality/inclusion evidence is mandatory");
    }
}

#[test]
fn finite_union_and_difference_wd_replay_original_operand_proofs() {
    for source in [
        include_str!("../../../lean/examples/finite_union_construction/statement.lit"),
        include_str!("../../../lean/examples/finite_difference_construction/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "finite_constructor_wd").unwrap();
        assert!(output.contains(if source.contains("union(") {
            "Litex.finiteUnionFromBoth"
        } else {
            "Litex.finiteDifferenceFromLeft"
        }));
    }
    for change in ["missing", "swapped"] {
        let (mut run, compiler) = super::execute(include_str!(
            "../../../lean/examples/finite_union_construction/statement.lit"
        ));
        let universal = super::forall_proof_mut(&mut run.statement_results[0]);
        let proof = super::atomic_proof_mut(&mut universal.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::UnionFiniteFromBoth(p),
        ) = &mut proof.searched_proof
        else {
            panic!("selected union-finite strategy");
        };
        if change == "missing" {
            p.proof_of_requirement_facts.pop();
        } else {
            p.proof_of_requirement_facts.swap(0, 1);
        }
        compiler
            .compile_run(&run, change)
            .expect_err("both original ordered finite operand certificates must be retained");
    }
}

#[test]
fn weak_finite_inclusion_does_not_prove_strict_or_equal_sets() {
    for source in [
        "forall A finite_set,B finite_set:\n    A $subset B\n    =>:\n        finite_set_size(A)<finite_set_size(B)\n",
        "forall A finite_set,B finite_set:\n    finite_set_size(A)=finite_set_size(B)\n    =>:\n        A=B\n",
        "forall A set,B finite_set:\n    $is_finite_set(set_minus(A,B))\n",
    ] {
        let command=parse_launch_command(&["-strict".into(),"-e".into(),source.into()]).unwrap();
        assert!(!Runtime::new(command).run_litex_code(source).unwrap().success);
    }
}
