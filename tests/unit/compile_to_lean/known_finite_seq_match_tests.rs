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
fn known_finite_sequence_matches_original_carrier_and_length_children() {
    let (mut run, compiler) = super::execute(SOURCE);
    let DetailedForallConclusionArgMatchProof::ByStructure {
        pattern,
        goal_arg,
        child_matches,
    } = matched(&mut run)
    else {
        panic!("original constructor match")
    };
    assert!(matches!(
        pattern,
        Obj::SetFormer(SetFormer::FiniteSeqSet(_))
    ));
    assert!(matches!(
        goal_arg,
        Obj::SetFormer(SetFormer::FiniteSeqSet(_))
    ));
    assert_eq!(child_matches.len(), 2);
    let output = super::compile_run(&run, &compiler, "known_finite_sequence").unwrap();
    assert_eq!(
        output,
        super::compile_run(&run, &compiler, "known_finite_sequence").unwrap()
    );
}
#[test]
fn known_finite_sequence_replays_actual_alpha_domains_and_nested_carriers() {
    for source in ALL {
        let (run, compiler) = super::execute(source);
        let output = super::compile_run(&run, &compiler, "known_finite_sequence_profiles").unwrap();
        assert_eq!(
            output,
            super::compile_run(&run, &compiler, "known_finite_sequence_profiles").unwrap()
        );
    }
}
#[test]
fn known_finite_sequence_requires_both_captured_constructor_subjects() {
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
fn known_finite_sequence_requires_exactly_two_original_children() {
    for count in [0, 1] {
        let (mut run, compiler) = super::execute(SOURCE);
        let DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } =
            matched(&mut run)
        else {
            panic!()
        };
        child_matches.truncate(count);
        reject(&run, &compiler, "children_count");
    }
}
#[test]
fn known_finite_sequence_cannot_swap_carrier_and_length_children() {
    let (mut run, compiler) = super::execute(SOURCE);
    let DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } =
        matched(&mut run)
    else {
        panic!()
    };
    child_matches.swap(0, 1);
    reject(&run, &compiler, "children_order");
}
#[test]
fn known_finite_sequence_retains_original_bound_parameter_identity() {
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
fn known_finite_sequence_retains_each_child_pattern_and_goal() {
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
fn known_finite_sequence_does_not_replace_the_original_substitution() {
    let (mut run, compiler) = super::execute(SOURCE);
    application(&mut run)
        .as_detailed_mut()
        .unwrap()
        .forall_parameters_match_what_args[0] = Obj::StandardSet(StandardSet::C);
    reject(&run, &compiler, "substitution");
}
#[test]
fn known_finite_sequence_needs_original_set_and_natural_requirements() {
    for count in [0, 1] {
        let (mut run, compiler) = super::execute(SOURCE);
        application(&mut run)
            .as_detailed_mut()
            .unwrap()
            .instantiation_requirements
            .as_detailed_mut()
            .unwrap()
            .param_type_requirements
            .truncate(count);
        reject(&run, &compiler, "requirement_count");
    }
}
#[test]
fn known_finite_sequence_needs_the_original_natural_requirement_subject() {
    let (mut run, compiler) = super::execute(SOURCE);
    let requirements = application(&mut run)
        .as_detailed_mut()
        .unwrap()
        .instantiation_requirements
        .as_detailed_mut()
        .unwrap();
    let proof = super::atomic_proof_mut(&mut requirements.param_type_requirements[1].proof);
    let AtomicFact::InFact(fact) = &mut proof.fact else {
        panic!()
    };
    fact.set = Obj::StandardSet(StandardSet::Z);
    reject(&run, &compiler, "natural_subject");
}
#[test]
fn known_finite_sequence_needs_an_exact_prior_theorem_citation() {
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
fn known_finite_sequence_cannot_use_a_sibling_private_theorem() {
    let private="forall replay35_private R:\n    forall replay35_private_A set,replay35_private_n N:\n        finite_seq(replay35_private_A,replay35_private_n)=fn(replay35_private_k closed_range(1,replay35_private_n)) replay35_private_A\n    =>:\n        replay35_private=replay35_private\n";
    let (mut run, compiler) = super::execute(&format!("{private}\n{SOURCE}"));
    super::compile_run(&run, &compiler, "private_scope_baseline").unwrap();
    let first = super::forall_proof_mut(&mut run.statement_results[0]);
    let StoreFactResult::ForallFact(store) = &first.assumed_dom_facts[0].store_and_infer.store
    else {
        panic!("original private universal premise")
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
fn known_finite_sequence_keeps_both_original_endpoint_wd() {
    let (mut run, compiler) = super::execute(SOURCE);
    let wd = equality(&mut run)
        .well_defined_proof
        .as_detailed_mut()
        .unwrap();
    std::mem::swap(&mut wd.left, &mut wd.right);
    reject(&run, &compiler, "endpoint_wd");
}
#[test]
fn known_finite_sequence_cannot_change_the_checked_goal_length() {
    let (mut run, compiler) = super::execute(SOURCE);
    let Obj::SetFormer(SetFormer::FiniteSeqSet(sequence)) = &mut equality(&mut run).fact.left
    else {
        panic!()
    };
    sequence.n = Box::new(Obj::Literal(Literal::Number(Number::new("3".into()))));
    reject(&run, &compiler, "goal_length");
}
#[test]
fn known_finite_sequence_keeps_the_original_signature_alpha_certificate() {
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
fn known_finite_sequence_does_not_accept_a_changed_guard_or_nonnatural_length() {
    for source in [
        SOURCE.replace(",2)", ",-1)").replace("(1,2)", "(1,-1)"),
        GUARDED.replace("replay35_gw>0", "replay35_gw>1"),
    ] {
        let command =
            parse_launch_command(&["-strict".to_string(), "-e".to_string(), source.clone()])
                .unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        assert!(!runtime.run_litex_code(&source).unwrap().success);
    }
}

const SOURCE: &str = "# A finite sequence space theorem is instantiated at an alpha-renamed function-space carrier.\nforall replay35_A set,replay35_n N:\n    finite_seq(replay35_A,replay35_n)=fn(replay35_k closed_range(1,replay35_n)) replay35_A\nfinite_seq(fn(replay35_v R) R,2)=fn(replay35_i closed_range(1,2)) fn(replay35_w R) R\n";
const GUARDED: &str = "# A finite sequence space theorem is instantiated at an alpha-renamed function-space carrier.\nforall replay35_A set,replay35_n N:\n    finite_seq(replay35_A,replay35_n)=fn(replay35_k closed_range(1,replay35_n)) replay35_A\nfinite_seq(fn(replay35_gv R:replay35_gv>0) R,2)=fn(replay35_gi closed_range(1,2)) fn(replay35_gw R:replay35_gw>0) R\n";
const ALL: &[&str] = &[
"# A finite sequence space theorem is instantiated at an alpha-renamed function-space carrier.\nforall replay35_A set,replay35_n N:\n    finite_seq(replay35_A,replay35_n)=fn(replay35_k closed_range(1,replay35_n)) replay35_A\nfinite_seq(fn(replay35_v R) R,2)=fn(replay35_i closed_range(1,2)) fn(replay35_w R) R\n",
"# A finite sequence space theorem is instantiated at an alpha-renamed function-space carrier.\nforall replay35_A set,replay35_n N:\n    finite_seq(replay35_A,replay35_n)=fn(replay35_k closed_range(1,replay35_n)) replay35_A\nfinite_seq(fn(replay35_cv C) C,3)=fn(replay35_ci closed_range(1,3)) fn(replay35_cw C) C\n",
"# A finite sequence space theorem is instantiated at an alpha-renamed function-space carrier.\nforall replay35_A set,replay35_n N:\n    finite_seq(replay35_A,replay35_n)=fn(replay35_k closed_range(1,replay35_n)) replay35_A\nfinite_seq(fn(replay35_zv R) R,0)=fn(replay35_zi closed_range(1,0)) fn(replay35_zw R) R\n",
"# A finite sequence space theorem is instantiated at an alpha-renamed function-space carrier.\nforall replay35_A set,replay35_n N:\n    finite_seq(replay35_A,replay35_n)=fn(replay35_k closed_range(1,replay35_n)) replay35_A\nfinite_seq(fn(replay35_ev {}) C,1)=fn(replay35_ei closed_range(1,1)) fn(replay35_ew {}) C\n",
"# A finite sequence space theorem is instantiated at an alpha-renamed function-space carrier.\nforall replay35_A set,replay35_n N:\n    finite_seq(replay35_A,replay35_n)=fn(replay35_k closed_range(1,replay35_n)) replay35_A\nfinite_seq(fn(replay35_gv R:replay35_gv>0) R,2)=fn(replay35_gi closed_range(1,2)) fn(replay35_gw R:replay35_gw>0) R\n",
"# A finite sequence space theorem is instantiated at an alpha-renamed function-space carrier.\nforall replay35_A set,replay35_n N:\n    finite_seq(replay35_A,replay35_n)=fn(replay35_k closed_range(1,replay35_n)) replay35_A\nfinite_seq(fn(replay35_mv R,replay35_mu C) C,2)=fn(replay35_mi closed_range(1,2)) fn(replay35_mw R,replay35_mt C) C\n",
"# A finite sequence space theorem is instantiated at an alpha-renamed function-space carrier.\nforall replay35_A set,replay35_n N:\n    finite_seq(replay35_A,replay35_n)=fn(replay35_k closed_range(1,replay35_n)) replay35_A\nfinite_seq(fn(replay35_iv closed_range(1,2)) R,2)=fn(replay35_ii closed_range(1,2)) fn(replay35_iw closed_range(1,2)) R\n",
"# A finite sequence space theorem is instantiated at an alpha-renamed function-space carrier.\nforall replay35_A set,replay35_n N:\n    finite_seq(replay35_A,replay35_n)=fn(replay35_k closed_range(1,replay35_n)) replay35_A\nfinite_seq(fn(replay35_nv R) fn(replay35_nu C) C,2)=fn(replay35_ni closed_range(1,2)) fn(replay35_nw R) fn(replay35_nt C) C\n",
"# A finite sequence space theorem is instantiated at an alpha-renamed function-space carrier.\nforall replay35_A set,replay35_n N:\n    finite_seq(replay35_A,replay35_n)=fn(replay35_k closed_range(1,replay35_n)) replay35_A\nfinite_seq(finite_seq(fn(replay35_fv R) R,2),3)=fn(replay35_fi closed_range(1,3)) finite_seq(fn(replay35_fw R) R,2)\n",
"# A finite sequence space theorem is instantiated at an alpha-renamed function-space carrier.\nforall replay35_A set,replay35_n N:\n    finite_seq(replay35_A,replay35_n)=fn(replay35_k closed_range(1,replay35_n)) replay35_A\nforall replay35_h fn(replay35_t R) N,replay35_a R:\n    replay35_h(replay35_a) $in N\n    finite_seq(fn(replay35_rv R) R,replay35_h(replay35_a))=fn(replay35_ri closed_range(1,replay35_h(replay35_a))) fn(replay35_rw R) R\n",
];
