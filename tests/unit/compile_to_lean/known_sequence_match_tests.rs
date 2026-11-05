use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    DetailedForallConclusionArgMatchProof, SearchProofByKnownForallFact,
};
use crate::prelude::*;

fn equality(run: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) =
        run.statement_results.last_mut().unwrap()
    else {
        panic!("original fact")
    };
    let result = match &mut statement.verify_result {
        VerifyFactResult::ForallFact(proof) => {
            let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(proof)) =
                proof.as_mut()
            else {
                panic!("original local forall")
            };
            &mut proof.proved_then_facts.last_mut().unwrap().verify_result
        }
        result => result,
    };
    super::equality_proof_mut(result)
}
fn application(run: &mut RunLitexCodeResult) -> &mut SearchProofByKnownForallFact {
    let EqualFactSearchedProof::ByKnownForallFact(proof) = &mut equality(run).searched_proof else {
        panic!("original known forall")
    };
    proof
}
fn matched(run: &mut RunLitexCodeResult) -> &mut DetailedForallConclusionArgMatchProof {
    application(run).as_detailed_mut().unwrap().arg_match_proofs[0]
        .as_detailed_mut()
        .unwrap()
}
fn reject(
    run: &RunLitexCodeResult,
    compiler: &crate::compile_to_lean::LitexToLeanCompiler,
    name: &str,
) {
    assert!(
        super::compile_run(run, compiler, name).is_err(),
        "changed original evidence accepted: {name}"
    );
}
#[test]
fn known_sequence_matches_original_single_carrier_child() {
    let (mut run, compiler) = super::execute(SOURCE);
    let DetailedForallConclusionArgMatchProof::ByStructure {
        pattern,
        goal_arg,
        child_matches,
    } = matched(&mut run)
    else {
        panic!("original sequence constructor match")
    };
    assert!(matches!(pattern, Obj::SetFormer(SetFormer::SeqSet(_))));
    assert!(matches!(goal_arg, Obj::SetFormer(SetFormer::SeqSet(_))));
    assert_eq!(child_matches.len(), 1);
    let output = super::compile_run(&run, &compiler, "known_sequence").unwrap();
    assert_eq!(
        output,
        super::compile_run(&run, &compiler, "known_sequence").unwrap()
    );
}
#[test]
fn known_sequence_requires_both_captured_constructor_subjects() {
    for pattern_side in [false, true] {
        let (mut run, compiler) = super::execute(SOURCE);
        let DetailedForallConclusionArgMatchProof::ByStructure {
            pattern, goal_arg, ..
        } = matched(&mut run)
        else {
            panic!()
        };
        if pattern_side {
            *pattern = Obj::StandardSet(StandardSet::R);
        } else {
            *goal_arg = Obj::StandardSet(StandardSet::R);
        }
        reject(&run, &compiler, "constructor_subject");
    }
}
#[test]
fn known_sequence_requires_exactly_one_original_carrier_child() {
    for duplicate in [false, true] {
        let (mut run, compiler) = super::execute(SOURCE);
        let (mut donor, _) = super::execute(SOURCE);
        let DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } =
            matched(&mut donor)
        else {
            panic!()
        };
        let original_child = child_matches.pop().unwrap();
        let DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } =
            matched(&mut run)
        else {
            panic!()
        };
        if duplicate {
            child_matches.push(original_child);
        } else {
            child_matches.clear();
        }
        reject(&run, &compiler, "carrier_child_count");
    }
}
#[test]
fn known_sequence_preserves_the_original_endpoint_match_order() {
    let (mut run, compiler) = super::execute(SOURCE);
    application(&mut run)
        .as_detailed_mut()
        .unwrap()
        .arg_match_proofs
        .swap(0, 1);
    reject(&run, &compiler, "endpoint_match_order");
}
#[test]
fn known_sequence_retains_original_bound_parameter_identity() {
    let (mut run, compiler) = super::execute(SOURCE);
    let DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } =
        matched(&mut run)
    else {
        panic!()
    };
    let DetailedForallConclusionArgMatchProof::BoundParam { param_id, .. } =
        child_matches[0].as_detailed_mut().unwrap()
    else {
        panic!()
    };
    *param_id = IdentifierId::new(u64::MAX);
    reject(&run, &compiler, "bound_identity");
}
#[test]
fn known_sequence_retains_each_child_pattern_and_goal() {
    for pattern_side in [false, true] {
        let (mut run, compiler) = super::execute(SOURCE);
        let DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } =
            matched(&mut run)
        else {
            panic!()
        };
        let DetailedForallConclusionArgMatchProof::BoundParam {
            pattern, goal_arg, ..
        } = child_matches[0].as_detailed_mut().unwrap()
        else {
            panic!()
        };
        if pattern_side {
            *pattern = Obj::StandardSet(StandardSet::C);
        } else {
            *goal_arg = Obj::StandardSet(StandardSet::C);
        }
        reject(&run, &compiler, "child_subject");
    }
}
#[test]
fn known_sequence_does_not_replace_the_original_substitution() {
    let (mut run, compiler) = super::execute(SOURCE);
    application(&mut run)
        .as_detailed_mut()
        .unwrap()
        .forall_parameters_match_what_args[0] = Obj::StandardSet(StandardSet::C);
    reject(&run, &compiler, "substitution");
}
#[test]
fn known_sequence_needs_its_original_set_requirement() {
    let (mut run, compiler) = super::execute(SOURCE);
    application(&mut run)
        .as_detailed_mut()
        .unwrap()
        .instantiation_requirements
        .as_detailed_mut()
        .unwrap()
        .param_type_requirements
        .clear();
    reject(&run, &compiler, "set_requirement_count");
}
#[test]
fn known_sequence_keeps_the_original_set_requirement_subject() {
    let (mut run, compiler) = super::execute(SOURCE);
    let requirements = application(&mut run)
        .as_detailed_mut()
        .unwrap()
        .instantiation_requirements
        .as_detailed_mut()
        .unwrap();
    let proof = super::atomic_proof_mut(&mut requirements.param_type_requirements[0].proof);
    let AtomicFact::IsSetFact(fact) = &mut proof.fact else {
        panic!()
    };
    fact.set = Obj::StandardSet(StandardSet::C);
    reject(&run, &compiler, "set_requirement_subject");
}
#[test]
fn known_sequence_needs_an_exact_prior_theorem_citation() {
    for missing in [false, true] {
        let (mut run, compiler) = super::execute(SOURCE);
        let target = equality(&mut run).fact.fact_id;
        application(&mut run)
            .as_detailed_mut()
            .unwrap()
            .cite
            .fact_id = if missing {
            FactId::new(u64::MAX)
        } else {
            target
        };
        reject(&run, &compiler, "theorem_citation");
    }
}
#[test]
fn known_sequence_cannot_use_a_sibling_private_theorem() {
    let private = "forall replay36_private R:\n    forall replay36_private_A set:\n        seq(replay36_private_A)=fn(replay36_private_k N+) replay36_private_A\n    =>:\n        replay36_private=replay36_private\n";
    let (mut run, compiler) = super::execute(&format!("{private}\n{SOURCE}"));
    super::compile_run(&run, &compiler, "private_scope_baseline").unwrap();
    let first = super::forall_proof_mut(&mut run.statement_results[0]);
    let StoreFactResult::ForallFact(store) = &first.assumed_dom_facts[0].store_and_infer.store
    else {
        panic!("original closed private premise")
    };
    let foreign = store.fact_id;
    application(&mut run)
        .as_detailed_mut()
        .unwrap()
        .cite
        .fact_id = foreign;
    reject(&run, &compiler, "private_theorem");
}
#[test]
fn known_sequence_keeps_both_original_endpoint_wd() {
    let (mut run, compiler) = super::execute(SOURCE);
    let wd = equality(&mut run)
        .well_defined_proof
        .as_detailed_mut()
        .unwrap();
    std::mem::swap(&mut wd.left, &mut wd.right);
    reject(&run, &compiler, "endpoint_wd");
}
#[test]
fn known_sequence_cannot_change_the_checked_goal_carrier() {
    let (mut run, compiler) = super::execute(SOURCE);
    let Obj::SetFormer(SetFormer::SeqSet(sequence)) = &mut equality(&mut run).fact.left else {
        panic!()
    };
    sequence.set = Box::new(Obj::StandardSet(StandardSet::C));
    reject(&run, &compiler, "goal_carrier");
}
#[test]
fn known_sequence_keeps_the_original_signature_alpha_certificate() {
    let (mut run, compiler) = super::execute(SOURCE);
    let proof = application(&mut run).as_detailed_mut().unwrap();
    let DetailedForallConclusionArgMatchProof::NonParamEqual {
        pattern_after_subst,
        ..
    } = proof.arg_match_proofs[1].as_detailed_mut().unwrap()
    else {
        panic!("original signature equality")
    };
    *pattern_after_subst = Obj::StandardSet(StandardSet::C);
    reject(&run, &compiler, "signature_certificate");
}
#[test]
fn known_sequence_keeps_guard_equality_and_positive_natural_indices() {
    for source in [
        SOURCE.replace("replay36_i N+", "replay36_i N"),
        GUARDED.replace("replay36_gw>0", "replay36_gw>1"),
    ] {
        let command =
            parse_launch_command(&["-strict".to_string(), "-e".to_string(), source.clone()])
                .unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        assert!(!runtime.run_litex_code(&source).unwrap().success);
    }
}

const SOURCE: &str = "# Sequence-space equality is reused at an alpha-renamed function-space carrier.\n# Before: the same source verified, but its second fact could not compile.\n# forall replay36_A set:\n#     seq(replay36_A)=fn(replay36_k N+) replay36_A\n# seq(fn(replay36_v R) R)=fn(replay36_i N+) fn(replay36_w R) R\n# Former compiler result: CompoundKnown/StructureConstructor.\n# Now: replay the original single carrier match and original scoped formation.\n# Sequence spaces are function spaces on the positive natural indices.\nforall replay36_A set:\n    seq(replay36_A)=fn(replay36_k N+) replay36_A\nseq(fn(replay36_v R) R)=fn(replay36_i N+) fn(replay36_w R) R\n# Boundary: changing the right carrier guard remains unproved.\n# Evidence: litex -lean -strict -f corpus case known_sequence_real\n# Evidence: known_sequence_match_tests rejects damaged evidence and scope escapes.\n";
const GUARDED: &str = "# Sequence spaces are function spaces on the positive natural indices.\nforall replay36_A set:\n    seq(replay36_A)=fn(replay36_k N+) replay36_A\nseq(fn(replay36_gv R:replay36_gv>0) R)=fn(replay36_gi N+) fn(replay36_gw R:replay36_gw>0) R\n";
