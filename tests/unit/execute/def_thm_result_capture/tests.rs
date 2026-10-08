use crate::execute::execute_by_stmt::{
    ExecByStmtResult, ExecByThmStmtResult, ExecReleaseThmStmtResult, ResolvedTheoremCallee,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::EqualFactSearchedProofByEquivalenceClass;
use crate::execute::{
    ExecDefThmBodyProof, ExecDefThmStmtResult, ExecDefThmStmtSuccess, ExecDefinitionStmtResult,
    ExecReleaseAndExpandStmtResult,
};
use crate::prelude::*;

fn runtime(strict: bool) -> Runtime {
    let mut arguments = vec!["-e".to_string(), String::new()];
    if strict {
        arguments.push("-strict".to_string());
    }
    Runtime::new(parse_launch_command(&arguments).expect("test launch command"))
}

fn theorem(result: &ExecStmtResult) -> &ExecDefThmStmtSuccess {
    match result {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
            ExecDefThmStmtResult::Success(p),
        )) => p,
        _ => panic!("successful theorem declaration"),
    }
}

#[test]
fn non_forall_keeps_original_named_declaration_and_single_conclusion() {
    let mut rt = runtime(true);
    let run = rt.run_litex_code("thm named_self:\n    ? 1 = 1\n").unwrap();
    assert!(run.success && run.session_error.is_none());
    let proof = theorem(&run.statement_results[0]);
    assert_eq!(proof.statement.name.as_str(), "named_self");
    assert_eq!(
        &proof.statement,
        rt.def_thm_visible_in_stack("named_self").unwrap()
    );
    match &proof.body {
        ExecDefThmBodyProof::NonForall(body) => {
            assert!(body.proof_steps.is_empty());
            let conclusion = match &body.conclusion_proof {
                VerifyFactResult::Equality(result) => match result.as_ref() {
                    VerifyEqualityResult::Success(p) => {
                        Fact::AtomicFact(AtomicFact::EqualFact(p.fact.clone()))
                    }
                    _ => panic!("successful conclusion"),
                },
                _ => panic!("atomic equality conclusion"),
            };
            assert_eq!(conclusion, proof.statement.fact);
        }
        _ => panic!("direct theorem must not pretend to introduce forall binders"),
    }
    assert_eq!(
        proof.stored.primary_fact_id(),
        proof.statement.fact.fact_id()
    );
    let normal =
        crate::json_output::project_stmt_normal(&run.statement_results[0], &rt).stringify();
    let detailed =
        crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt).stringify();
    assert!(normal.contains("thm named_self"));
    assert!(detailed.contains("non_forall") && detailed.contains("conclusion_proof"));
}

#[test]
fn forall_retains_actual_binder_producers_and_ordered_domain_wd_stores() {
    let mut rt = runtime(true);
    let source = "thm guarded_identity:\n    ? forall x R, y R:\n        x != 0\n        y != 0\n        =>:\n            x = x\n    x = x\n";
    let run = rt.run_litex_code(source).unwrap();
    assert!(run.success && run.session_error.is_none());
    let proof = theorem(&run.statement_results[0]);
    let source_forall = match &proof.statement.fact {
        Fact::ForallFact(p) => p,
        _ => panic!("forall source"),
    };
    let body = match &proof.body {
        ExecDefThmBodyProof::Forall(p) => p,
        _ => panic!("forall success captures its stages"),
    };
    assert_eq!(body.introduced_params.param_type_well_defined.len(), 2);
    assert_eq!(
        body.introduced_params.defined_params.stored_fact_ids.len(),
        2
    );
    for (id, parameter) in body
        .introduced_params
        .defined_params
        .stored_fact_ids
        .iter()
        .zip(
            source_forall
                .typed_parameters
                .groups
                .iter()
                .flat_map(|g| g.params.iter()),
        )
    {
        let fact = proof.local_env.facts.facts_by_id.get(id).unwrap();
        match fact {
            Fact::AtomicFact(AtomicFact::InFact(member)) => {
                assert_eq!(
                    member.element.ir(),
                    Obj::Identifier(IdentifierObj::from_bound_name(parameter)).ir()
                );
                assert_eq!(member.set, Obj::StandardSet(StandardSet::R));
            }
            _ => panic!("actual introduced member fact"),
        }
    }
    assert_eq!(body.assumed_dom_facts.len(), source_forall.dom_facts.len());
    for (captured, dom) in body.assumed_dom_facts.iter().zip(&source_forall.dom_facts) {
        assert_eq!(captured.store_and_infer.primary_fact_id(), dom.fact_id());
        assert_eq!(
            proof.local_env.facts.facts_by_id.get(&dom.fact_id()),
            Some(dom)
        );
        assert!(matches!(
            &captured.well_defined,
            FactWellDefinedProof::AtomicExceptEquality(_)
        ));
    }
    assert_eq!(body.proof_steps.len(), 1);
    assert!(!body.proof_steps[0].is_failed());
    assert_eq!(body.conclusion_proofs.len(), 1);
    let detail =
        crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt).stringify();
    assert!(detail.contains("introduced_params") && detail.contains("assumed_dom_facts"));
}

#[test]
fn by_thm_captures_resolved_declaration_and_actual_selected_fact_producer() {
    let mut rt = runtime(true);
    let run = rt.run_litex_code("thm two_results:\n    ? forall x R:\n        x = x\n        x + 0 = x\nby thm two_results(2) => 2 = 2\n").unwrap();
    assert!(run.success && run.session_error.is_none());
    let declaration = theorem(&run.statement_results[0]);
    let applied = match &run.statement_results[1] {
        ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(p))) => p,
        _ => panic!("successful explicit theorem use"),
    };
    match &applied.callee {
        ResolvedTheoremCallee::UserTheorem(stmt) => assert_eq!(stmt, &declaration.statement),
        _ => panic!("the actually resolved user theorem"),
    }
    assert!(applied.builtin.is_none());
    assert_eq!(applied.returned_conclusions.len(), 2);
    let selected = match &applied.selected_proof {
        VerifyFactResult::Equality(p) => match p.as_ref() {
            VerifyEqualityResult::Success(p) => p,
            _ => panic!("selected equality success"),
        },
        _ => panic!("selected equality"),
    };
    match &selected.searched_proof {
        EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::AlphaEndpoints(p),
        ) => {
            let returned = &applied.returned_conclusions[0];
            assert_eq!(p.cited.fact_id, returned.primary_fact_id());
            assert!(returned
                .atomic_components()
                .iter()
                .any(|(id, atomic)| *id == p.cited.fact_id
                    && atomic == &AtomicFact::EqualFact(p.cited.clone())));
            assert_eq!(
                applied.local_env.facts.facts_by_id.get(&p.cited.fact_id),
                Some(&Fact::AtomicFact(AtomicFact::EqualFact(p.cited.clone())))
            );
        }
        _ => panic!("selection cites a returned fact instead of re-proving the target"),
    }
    let detail =
        crate::json_output::project_stmt_detailed(&run.statement_results[1], &rt).stringify();
    assert!(detail.contains("returned_conclusions") && detail.contains("user_theorem"));
}

#[test]
fn capture_does_not_publish_failed_theorems_or_relax_strict_selection() {
    let mut rt = runtime(true);
    let valid = rt.run_litex_code("thm kept:\n    ? 1 = 1\n").unwrap();
    assert!(valid.success);
    let failed = rt.run_litex_code("thm retryable:\n    ? 1 = 2\n").unwrap();
    assert!(!failed.success && failed.session_error.is_none());
    assert!(rt.def_thm_visible_in_stack("retryable").is_none());
    assert!(rt.def_thm_visible_in_stack("kept").is_some());
    assert!(
        rt.run_litex_code("thm retryable:\n    ? 1 = 1\n")
            .unwrap()
            .success
    );
    assert!(
        rt.run_litex_code("thm reflexive:\n    ? forall x R:\n        x = x\n")
            .unwrap()
            .success
    );
    let unrelated = rt.run_litex_code("by thm reflexive(2) => 1 = 1\n").unwrap();
    assert!(!unrelated.success && unrelated.session_error.is_none());
    assert!(matches!(
        &unrelated.statement_results[0],
        ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Failed(_)))
    ));
    assert!(
        rt.run_litex_code("by thm reflexive(2) => 2 = 2\n")
            .unwrap()
            .success
    );
}

#[test]
fn existing_builtin_and_axiom_callees_remain_explicit_and_distinct() {
    let mut rt = runtime(true);
    let builtin = rt
        .run_litex_code("release thm subset_of_finite_set_is_finite({1}, {1, 2})\n")
        .unwrap();
    assert!(builtin.success && builtin.session_error.is_none());
    match &builtin.statement_results[0] {
        ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
            ExecReleaseThmStmtResult::Success(p),
        )) => {
            assert!(matches!(&p.callee, ResolvedTheoremCallee::Builtin));
            assert!(p.builtin.is_some());
        }
        _ => panic!("existing builtin release"),
    }
    let mut nonstrict = runtime(false);
    let axiom = nonstrict.run_litex_code("axiom declared_identity:\n    ? forall x R:\n        x = x\nby thm declared_identity(1) => 1 = 1\n").unwrap();
    assert!(axiom.success && axiom.session_error.is_none());
    match &axiom.statement_results[1] {
        ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(p))) => {
            assert!(matches!(&p.callee, ResolvedTheoremCallee::UserAxiom(_)));
            assert!(p.builtin.is_none());
        }
        _ => panic!("existing axiom application stays marked axiomatic"),
    }
}
