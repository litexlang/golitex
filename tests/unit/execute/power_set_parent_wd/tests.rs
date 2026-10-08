use super::*;
use crate::ast::stmt::{ProofBlockStmt, Stmt};
use crate::execute::exec_stmt_result::ExecStmtResult;
use crate::execute::execute_by_stmt::{ExecByDefStmtResult, ExecByStmtResult};
use crate::execute::execute_fact_stmt::{VerifyAtomicFactWellDefinedResult, VerifyStateLevel};
use crate::launch_command::{LaunchCommand, OutputLanguage};

const SOURCE: &str = "claim:\n    ? forall X, Y set, f fn(arg X) Y, K power_set(X):\n        fn_range(fn(point K) Y {f(point)}) $in power_set(Y)\n    by def:\n        ? fn_range(fn(point K) Y {f(point)}) $subset Y\n    fn_range(fn(point K) Y {f(point)}) $in power_set(Y)\n";

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

#[test]
fn power_set_restricted_image_premise_reuses_parent_objects_at_original_ceiling() {
    let mut rt = runtime();
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize(SOURCE, rt.current_file.clone())
        .unwrap();
    let mut stmts = rt.parse(&tokens).unwrap();
    let Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(claim)) = stmts.remove(0) else {
        panic!("claim")
    };
    let Fact::ForallFact(context) = claim.fact else {
        panic!("universal context")
    };
    rt.run_in_local_env_and_take_env(|rt| {
        assert!(rt
            .introduce_typed_parameters(&context.typed_parameters, VerifyState::top_level())?
            .is_ok());
        // Real explicit proof entry; no trusted setup or branch executor bypass.
        let first = rt.exec_stmt(&claim.proof[0])?;
        assert!(matches!(
            first,
            ExecStmtResult::By(ExecByStmtResult::Def(ExecByDefStmtResult::Success(_)))
        ));
        let Stmt::Fact(Fact::AtomicFact(AtomicFact::InFact(goal))) = &claim.proof[1] else {
            panic!("membership")
        };
        assert!(
            matches!(
                rt.verify_atomic_fact_well_definedness(
                    &AtomicFact::InFact(goal.clone()),
                    VerifyState::top_level()
                )?,
                VerifyAtomicFactWellDefinedResult::Success(_)
            ),
            "parent WD succeeds"
        );
        let Obj::SetOperator(SetOperator::PowerSet(power)) = &goal.set else {
            panic!("power set")
        };
        let subset = AtomicFact::SubsetFact(SubsetFact {
            fact_id: rt.global_ids.allocate_fact_id(),
            left: goal.element.clone(),
            right: power.set.as_ref().clone(),
            line_file: None,
        });
        let child = VerifyState::top_level()
            .for_premises(VerifyStateLevel::BuiltinRule)
            .unwrap();
        assert_eq!(child.level(), VerifyStateLevel::KnownSpecialProperty);
        let known = rt.lookup_known_atomic_fact(&subset);
        eprintln!("power set: known subset matches={}", known.is_some());
        assert!(
            known.is_some(),
            "the real by-def subset was stored and alpha matches"
        );
        let old = rt.verify_builtin_rule_premise(&Fact::AtomicFact(subset.clone()), child)?;
        eprintln!(
            "power set: full lower premise failed={}, WD failed={}",
            old.is_failed(),
            old.is_wd_failed()
        );
        let truth = rt.search_atomic_except_equality_fact_proof(&subset, child)?;
        eprintln!(
            "power set: unchanged lower truth succeeds={}",
            truth.is_some()
        );
        assert!(
            truth.is_some(),
            "same permission succeeds without repeating parent objects' WD"
        );
        let proof = rt.power_set_membership_proof(goal, child)?;
        let Some(InFactSearchProofByBuiltinRule::PowerSetMembership(proof)) = proof else {
            panic!("parent-valid power membership must consume existing subset truth")
        };
        let PowerSetMembershipSubsetProof::KnownSubset(known_subset) = proof.subset_proof else {
            panic!("actual stored subset route")
        };
        assert_eq!(
            known_subset.cite_fact_id(),
            known.as_ref().map(|proof| proof.cite_fact_id)
        );
        let AtomicFact::SubsetFact(cited_goal) = known_subset.fact else {
            panic!("subset evidence")
        };
        assert_eq!(cited_goal.left, goal.element);
        assert_eq!(cited_goal.right, *power.set);
        Ok(())
    })
    .unwrap();
    let run = runtime().run_litex_code(SOURCE).unwrap();
    assert!(
        run.success && run.session_error.is_none(),
        "actual public proof must pass"
    );
}

#[test]
fn power_set_parent_wd_maintained_tracer_and_detailed_citation_pass() {
    let mut rt = runtime();
    let run = rt.run_litex_code(include_str!("../../../../examples/proof_nodes/atomic/by_builtin_rule/in_power_set_from_restricted_image.lit")).unwrap();
    assert!(run.success && run.session_error.is_none());
    let detail =
        crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt).stringify();
    for field in [
        "PowerSetMembership",
        "by_known_subset",
        "cite_fact_id",
        "parent_wd_arguments",
        "compound_obj",
    ] {
        assert!(detail.contains(field), "{field} missing: {detail}");
    }
}

#[test]
fn power_set_parent_wd_known_route_requires_the_exact_positive_subset() {
    for premise in [
        "",
        "        S $subset X\n",
        "        T $subset Y\n",
        "        not S $subset Y\n",
    ] {
        let mut rt = runtime();
        let source = format!("claim:\n    ? forall S, T, X, Y set:\n{premise}{}S $in power_set(Y)\n    S $in power_set(Y)\n", if premise.is_empty() { "        " } else { "        =>:\n            " });
        let run = rt.run_litex_code(&source).unwrap();
        assert!(
            !run.success && run.session_error.is_none(),
            "missing exact positive subset: {source}"
        );
        assert!(
            rt.run_litex_code("1=1\n").unwrap().success,
            "failed locals discard"
        );
    }
}

#[test]
fn power_set_parent_wd_keeps_stored_equality_citation_and_permission_policy() {
    let source = "claim:\n    ? forall S, Y set:\n        S $subset Y\n        =>:\n            S $in power_set(Y)\n    let renamed = S\n    renamed $in power_set(Y)\n    S $in power_set(Y)\n";
    let mut rt = runtime();
    let run = rt.run_litex_code(source).unwrap();
    assert!(run.success && run.session_error.is_none());
    let detail =
        crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt).stringify();
    assert!(
        detail.contains("by_equivalence_class") && detail.contains("by_known_subset"),
        "stored endpoint transport retained: {detail}"
    );
    // Below BuiltinRule this conversion cannot introduce a new rule route.
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize(source, rt.current_file.clone())
        .unwrap();
    let mut statements = rt.parse(&tokens).unwrap();
    let Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(claim)) = statements.remove(0) else {
        panic!("claim")
    };
    let Fact::ForallFact(context) = claim.fact else {
        panic!("context")
    };
    rt.run_in_local_env_and_take_env(|rt| {
        assert!(rt
            .introduce_typed_parameters(&context.typed_parameters, VerifyState::top_level())?
            .is_ok());
        for dom in &context.dom_facts {
            rt.store_fact_and_infer(dom, VerifyState::top_level())?;
        }
        let goal: Fact = context.then_facts[0].clone().into();
        for level in [
            VerifyStateLevel::Direct,
            VerifyStateLevel::KnownSpecialProperty,
        ] {
            assert!(
                rt.verify_fact(&goal, VerifyState::new(level))?.is_failed(),
                "cannot raise caller ceiling"
            );
        }
        assert!(!rt
            .verify_fact(&goal, VerifyState::new(VerifyStateLevel::BuiltinRule))?
            .is_failed());
        Ok(())
    })
    .unwrap();
}

#[test]
fn power_set_parent_wd_rejects_unmet_function_domains() {
    for carrier in ["R+", "R"] {
        let mut rt = runtime();
        let source = format!("claim:\n    ? forall f fn(arg R+) R, K power_set({carrier}):\n        fn_range(fn(point K) R {{f(point)}}) $in power_set(R)\n    by def:\n        ? fn_range(fn(point K) R {{f(point)}}) $subset R\n    fn_range(fn(point K) R {{f(point)}}) $in power_set(R)\n");
        let run = rt.run_litex_code(&source).unwrap();
        assert!(run.session_error.is_none());
        assert_eq!(
            run.success,
            carrier == "R+",
            "only a compatible restricted domain verifies"
        );
        if carrier == "R" {
            let detail = crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt)
                .stringify();
            assert!(
                detail.contains("well_defined"),
                "parent WD remains required: {detail}"
            );
        }
    }
}
