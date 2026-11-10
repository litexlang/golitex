use super::*;
use crate::execute::execute_by_stmt::{ExecByContraStmtResult, ExecByStmtResult};
use crate::execute::execute_proof_block_stmt::{
    ExecClaimStmtResult, ExecProofBlockStmtResult, ExecSketchStmtResult,
};

fn checked(source: &str) -> (RunLitexCodeResult, LitexToLeanCompiler) {
    let mut runtime = Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: source.to_owned(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    );
    let run = runtime.run_litex_code(source).unwrap();
    assert!(
        run.success,
        "{}",
        crate::json_output::emit_run_normal(&run, &runtime, "round2", None)
    );
    (run, LitexToLeanCompiler::new(runtime))
}

#[test]
fn round2_cited_atomic_formation_follows_actual_local_proof_scopes() {
    for source in [
        "sketch:\n    have local_x R = 1\n    local_x > 0\n",
        "claim:\n    ? 1 = 1\n    1 > 0\n    1 = 1\n",
        "thm local_id:\n    ? 1 = 1\n    1 > 0\n    1 = 1\n",
        "by contra:\n    ? 1 = 1\n    1 > 0\n    impossible 1 = 1\n",
    ] {
        let (run, compiler) = checked(source);
        let owner = match &run.statement_results[0] {
            ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Sketch(
                ExecSketchStmtResult::Success(p),
            )) => SourceOwner::Sketch(p),
            ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(
                ExecClaimStmtResult::Success(p),
            )) => SourceOwner::Claim(p),
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
                ExecDefThmStmtResult::Success(p),
            )) => SourceOwner::Named(p),
            ExecStmtResult::By(ExecByStmtResult::Contra(ExecByContraStmtResult::Success(p))) => {
                SourceOwner::Contra(p)
            }
            _ => panic!("expected a local proof owner"),
        };
        let (steps, head) = match owner {
            SourceOwner::Claim(p) => claim_steps(p),
            SourceOwner::Named(p) => named_steps(p),
            _ => local_steps(owner).unwrap(),
        };
        let (index, id) = steps
            .iter()
            .enumerate()
            .find_map(|(index, step)| {
                let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = step else {
                    return None;
                };
                let StoreFactResult::AtomicFact(stored) = &p.store_and_infer_result.store else {
                    return None;
                };
                matches!(&stored.fact, AtomicFact::GreaterFact(_))
                    .then_some((index, p.store_and_infer_result.primary_fact_id()))
            })
            .expect("original positive atomic statement");
        let root = SourcePosition::new(None, SourceOwner::Run(&run), 0);
        let after = SourcePosition::new(Some(&root), owner, head + index + 1);
        let observed = compiler
            .with_cited_atomic_formation(id, &after, &mut |fact, _, prior| {
                assert_eq!(fact.fact_id(), id);
                // The callback enters the selected statement's atomic-WD
                // scope at stage zero. Its parent retains the source index.
                assert_eq!(prior.before, 0);
                assert!(matches!(prior.owner, SourceOwner::AtomicVerify(proof)
                    if proof.fact.fact_id() == id));
                Ok(prior.parent.expect("original statement position").before)
            })
            .expect("the prior local statement owns its exact atomic formation");
        assert_eq!(observed, head + index);

        let before = SourcePosition::new(Some(&root), owner, head + index);
        assert!(
            compiler
                .with_cited_atomic_formation(id, &before, &mut |_, _, _| Ok(()))
                .is_err(),
            "future local facts remain invisible"
        );
        let outside = SourcePosition::new(None, SourceOwner::Run(&run), 1);
        assert!(
            compiler
                .with_cited_atomic_formation(id, &outside, &mut |_, _, _| Ok(()))
                .is_err(),
            "local formations must not escape their proof scope"
        );
    }
}

#[test]
fn round2_existing_local_induction_enumeration_and_struct_bridges_are_preserved() {
    for (source, marker) in [
        ("sketch:\n    by induc k from 0:\n        ? k = k\n        ? from k = 0:\n            0 = 0\n        ? induc:\n            k + 1 = k + 1\n", "Litex.semanticObject"),
        ("sketch:\n    by for:\n        ? forall n range(0,3):\n            n*n <= 4\n        n*n <= 4\n", "Litex.semanticObject"),
        ("sketch:\n    struct LocalPair:\n        x R\n        y R\n    forall p &LocalPair:\n        p.x $in R\n", "let struct_local_i"),
        ("thm local_regularity:\n    ? 1=1\n    release regularity_axiom({1})\n    1=1\n", "Litex.RegularitySemantics M"),
    ] {
        let (run, compiler) = checked(source);
        let lean = compiler.compile_run(&run, "round2_local_contracts").unwrap();
        assert!(lean.contains(marker), "{source}\nmissing {marker}");
        assert!(!lean.contains("sorry"));
    }
}

#[test]
fn round2_local_continuity_reuses_its_original_atomic_formation() {
    // Keep the regression self-contained. The optional lean/examples corpus is ignored.
    let source = r#"# The sum of two continuous real functions is continuous at the chosen point.
thm local_continuity_sum:
    ? forall f,g,h,k fn(x R) R, p R:
        $is_continuous_at(f,p)
        $is_continuous_at(g,p)
        forall x R:
            h(x)=f(x)+g(x)
        forall x R:
            k(x)=h(x)+h(x)
        =>:
            $is_continuous_at(k,p)
    claim:
        ? $is_continuous_at(k,p)
        by thm fn_continuous_at_add(f,g,h,p) => $is_continuous_at(h,p)
        by thm fn_continuous_at_add(h,h,k,p) => $is_continuous_at(k,p)
    $is_continuous_at(k,p)
"#;
    let (run, compiler) = checked(source);
    let lean = compiler.compile_run(&run, "local_continuity_sum").unwrap();
    assert!(lean.to_lowercase().contains("continuous"));
    assert!(!lean.contains("sorry"));
}

#[test]
fn round2_nested_regularity_releases_keep_their_semantics_dependency() {
    for source in [
        "by contra:\n    ? 1 = 1\n    release regularity_axiom({1})\n    impossible 1 = 1\n",
        "by for:\n    ? forall n range(0,2):\n        n = n\n    release regularity_axiom({1})\n    n = n\n",
        "sketch:\n    by induc k from 0:\n        ? k = k\n        ? from k = 0:\n            release regularity_axiom({1})\n            0 = 0\n        ? induc:\n            k + 1 = k + 1\n",
    ] {
        let (run, compiler) = checked(source);
        let lean = compiler.compile_run(&run, "round2_nested_regularity").unwrap();
        assert!(lean.contains("Litex.RegularitySemantics M"), "{source}");
        assert!(lean.contains("Litex.SetSemantics M"), "{source}");
        assert!(lean.contains("Litex.regularity"));
    }
}
