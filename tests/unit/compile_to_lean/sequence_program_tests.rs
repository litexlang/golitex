use super::dense_order_theorem_tests::invocation;
use crate::execute::execute_by_stmt::TheoremDerivationProof;
use crate::prelude::*;

const SOURCES: [&str; 7] = [
    r#"# Replay the recorded source completeness proof for this sequence law.
thm sequence_builtin_monotone_bounded_above_draft:
    ? forall a seq(R):
        $is_seq_nondecreasing(a)
        $is_seq_bounded_above(a)
        =>:
            exist L R st {$has_seq_limit(a,L)}
    release thm sequence_monotone_bounded_above(a)
"#,
    r#"# Replay the recorded source completeness proof for this sequence law.
thm sequence_builtin_monotone_bounded_below_draft:
    ? forall a seq(R):
        $is_seq_nonincreasing(a)
        $is_seq_bounded_below(a)
        =>:
            exist L R st {$has_seq_limit(a,L)}
    release thm sequence_monotone_bounded_below(a)
"#,
    r#"# Replay the recorded source completeness proof for this sequence law.
thm sequence_builtin_cauchy_bounded_draft:
    ? forall a seq(R):
        $is_seq_cauchy(a)
        =>:
            $is_seq_bounded(a)
    release thm sequence_cauchy_bounded(a)
"#,
    r#"# Replay the recorded source completeness proof for this sequence law.
thm sequence_builtin_cauchy_convergent_draft:
    ? forall a seq(R):
        $is_seq_cauchy(a)
        =>:
            $is_seq_convergent(a)
    release thm sequence_cauchy_convergent(a)
"#,
    r#"# Replay the recorded source completeness proof for this sequence law.
thm sequence_builtin_convergent_bounded_draft:
    ? forall a seq(R):
        $is_seq_convergent(a)
        =>:
            $is_seq_bounded(a)
    release thm sequence_convergent_bounded(a)
"#,
    r#"# Retain the original bounded-sequence extremal-existence source program.
thm sequence_builtin_limsup_bounded_exists_draft:
    ? forall a seq(R),bound R+:
        forall k N+:
            abs(a(k))<=bound
        =>:
            exist L R st {$has_seq_limsup(a,L)}
    release thm seq_limsup_bounded_exists(a,bound)
"#,
    r#"# Retain the original bounded-sequence extremal-existence source program.
thm sequence_builtin_liminf_bounded_exists_draft:
    ? forall a seq(R),bound R+:
        forall k N+:
            abs(a(k))<=bound
        =>:
            exist L R st {$has_seq_liminf(a,L)}
    release thm seq_liminf_bounded_exists(a,bound)
"#,
];

#[test]
fn sequence_program_local_predicates_follow_the_original_declaration_prefix() {
    use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
    let (mut run, compiler) = super::execute(SOURCES[5]);
    let derivation = &invocation(&mut run).theorem_derivation;
    let (_, steps, _, _) =
        crate::compile_to_lean::compile_builtin_sequence_program::program_parts(derivation)
            .expect("original extremal-existence program");
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
        crate::execute::ExecDefPropStmtResult::Success(declaration),
    )) = &steps[0]
    else {
        panic!("original leading local predicate");
    };
    let name = AtomicName::Plain {
        name: declaration.statement.name.clone(),
    };
    let before = SourcePosition::new(None, SourceOwner::Derivation(derivation), 0);
    assert!(before.visible_prop(&name, &compiler.runtime).is_err());
    let after = SourcePosition {
        before: 1,
        ..before
    };
    let (actual, producer, index) = after.visible_prop(&name, &compiler.runtime).unwrap();
    assert!(std::ptr::eq(actual, declaration));
    assert_eq!((producer.before, index), (0, 0));
    let premature = SourcePosition::new(Some(&before), SourceOwner::Derivation(derivation), 1);
    assert!(premature.visible_prop(&name, &compiler.runtime).is_err());
    let (index, selected) = steps
        .iter()
        .enumerate()
        .find_map(|(index, step)| match step {
            ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByForallExistUnique(
                crate::execute::ExecHaveFnByForallExistUniqueStmtResult::Success(proof),
            )) => Some((index, proof)),
            _ => None,
        })
        .expect("original local selected-function declaration");
    let id = selected.statement.name.id;
    let pending = SourcePosition {
        before: index,
        ..before
    };
    assert!(pending.visible_selected_function(&id).is_err());
    let published = SourcePosition {
        before: index + 1,
        ..before
    };
    let (actual, producer) = published.visible_selected_function(&id).unwrap();
    assert!(std::ptr::eq(actual, selected));
    assert_eq!(producer.before, index);
    let premature = SourcePosition::new(
        Some(&pending),
        SourceOwner::Derivation(derivation),
        index + 1,
    );
    assert!(premature.visible_selected_function(&id).is_err());
    let closed = SourcePosition::new(None, SourceOwner::Run(&run), run.statement_results.len());
    assert!(closed.visible_prop(&name, &compiler.runtime).is_err());
    assert!(closed.visible_selected_function(&id).is_err());
}

#[test]
fn positive_natural_lower_bound_keeps_direction_carrier_and_original_citation() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::greater_equal::GreaterEqualFactSearchProofByBuiltinRule;
    let (mut run, compiler) = super::execute("have n N+\nn>=1\n");
    let lean = compiler
        .compile_run(&run, "positive_natural_lower_bound")
        .unwrap();
    assert!(lean.contains("Litex.integerSuccessorLowerBound"));
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) =
        &mut run.statement_results[1]
    else {
        panic!("original bound");
    };
    let proof = super::atomic_proof_mut(&mut statement.verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(
            GreaterEqualFactSearchProofByBuiltinRule::FromKnownInPositiveNatural(bound),
        ),
    ) = &mut proof.searched_proof
    else {
        panic!("original positive-natural rule");
    };
    let original = bound.premise_proof.fact.clone();
    let AtomicFact::InFact(member) = &mut bound.premise_proof.fact else {
        panic!("original membership");
    };
    member.set = Obj::StandardSet(StandardSet::N);
    assert!(compiler.compile_run(&run, "wrong_natural_carrier").is_err());
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) =
        &mut run.statement_results[1]
    else {
        unreachable!()
    };
    let proof = super::atomic_proof_mut(&mut statement.verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(
            GreaterEqualFactSearchProofByBuiltinRule::FromKnownInPositiveNatural(bound),
        ),
    ) = &mut proof.searched_proof
    else {
        unreachable!()
    };
    bound.premise_proof.fact = original;
    let AtomicFact::GreaterEqualFact(goal) = &mut proof.fact else {
        unreachable!()
    };
    goal.right = super::number_object("2");
    assert!(compiler
        .compile_run(&run, "wrong_positive_natural_boundary")
        .is_err());
}

#[test]
fn sequence_program_monotone_bounded_replays_original_source_completeness() {
    let (run, compiler) = super::execute(SOURCES[0]);
    let lean = compiler
        .compile_run(&run, "monotone_bounded_completeness")
        .expect("the Native-checked completeness program retains its original scoped evidence");
    assert!(!lean.contains("sorry") && !lean.contains("admit"));
}

#[test]
fn sequence_program_rejects_missing_stages_and_native_substitution() {
    for source in SOURCES {
        let (mut run, compiler) = super::execute(source);
        let proof = invocation(&mut run).dom_proofs.pop().unwrap();
        assert!(compiler.compile_run(&run, "missing_proof").is_err());
        invocation(&mut run).dom_proofs.push(proof);

        let store = invocation(&mut run).dom_stores.pop().unwrap();
        assert!(compiler.compile_run(&run, "missing_store").is_err());
        invocation(&mut run).dom_stores.push(store);

        let formation = std::mem::take(&mut invocation(&mut run).conclusions_wd);
        assert!(compiler.compile_run(&run, "missing_formation").is_err());
        invocation(&mut run).conclusions_wd = formation;

        let derivation = std::mem::replace(
            &mut invocation(&mut run).theorem_derivation,
            TheoremDerivationProof::NativeSchema,
        );
        assert!(compiler.compile_run(&run, "native_substitution").is_err());
        invocation(&mut run).theorem_derivation = derivation;

        let requirement = invocation(&mut run)
            .builtin
            .as_mut()
            .unwrap()
            .requirements
            .pop()
            .unwrap();
        assert!(compiler.compile_run(&run, "missing_requirement").is_err());
        invocation(&mut run)
            .builtin
            .as_mut()
            .unwrap()
            .requirements
            .push(requirement);
    }
}
