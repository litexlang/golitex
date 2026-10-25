use crate::compile_to_lean::LitexToLeanCompiler;
use crate::prelude::*;

fn execute(source: &str) -> (RunLitexCodeResult, LitexToLeanCompiler) {
    let mut runtime = Runtime::new(parse_launch_command(&["-e".into(), source.into()]).unwrap());
    let run = runtime.run_litex_code(source).unwrap();
    assert!(run.success, "source must be accepted");
    (run, LitexToLeanCompiler::new(runtime))
}

#[test]
fn trust_is_an_explicit_hypothesis() {
    let (run, compiler) = execute("have a R\ntrust a > 0\na >= 0\n");
    let lean = compiler.compile_run(&run, "assumed_positive").unwrap();
    assert!(lean.contains("variable (h_"));
    assert!(!lean.contains("axiom ") && !lean.contains("sorry"));
    assert_eq!(
        lean,
        compiler.compile_run(&run, "assumed_positive").unwrap()
    );
}

#[test]
fn trust_requires_all_original_formation_stages() {
    let (mut run, compiler) = execute("have a R\ntrust a > 0\na >= 0\n");
    let ExecStmtResult::Trust(
        crate::execute::execute_unsafe_stmt::ExecTrustBoundaryStmtResult::TrustStmt(
            crate::execute::execute_unsafe_stmt::ExecTrustStmtResult::Success(p),
        ),
    ) = &mut run.statement_results[1]
    else {
        panic!()
    };
    p.facts_well_defined.clear();
    assert!(compiler.compile_run(&run, "missing_wd").is_err());
}

#[test]
fn user_axiom_is_an_explicit_hypothesis() {
    let (run, compiler) = execute("abstract_prop marked(x)\naxiom all_marked:\n    ? forall x R:\n        $marked(x)\n$marked(0)\n");
    let lean = compiler.compile_run(&run, "assumed_property").unwrap();
    assert!(lean.contains("variable (h_"));
    assert!(!lean.contains("axiom ") && !lean.contains("sorry"));
}

#[test]
fn user_axiom_can_be_called_and_released() {
    let (run, compiler) = execute("abstract_prop marked(x)\naxiom all_marked:\n    ? forall x R:\n        $marked(x)\nrelease thm all_marked(0)\nby thm all_marked(1) => $marked(1)\n");
    let lean = compiler.compile_run(&run, "assumed_calls").unwrap();
    assert!(!lean.contains("axiom ") && !lean.contains("sorry"));
}

#[test]
fn regularity_replays_its_nonempty_and_formation_proofs() {
    let (run, compiler) =
        super::execute("release regularity_axiom({1})\nexist x {1} st {intersect(x, {1}) = {}}\n");
    let lean = compiler.compile_run(&run, "regularity").unwrap();
    assert!(lean.contains("Litex.regularity") && lean.contains("Litex.RegularitySemantics M"));
}

const REPLACEMENT: &str = "prop identity_relation(x, y set):\n    y = x\nforall x {1, 2}, y, z set:\n    $identity_relation(x, y)\n    $identity_relation(x, z)\n    =>:\n        y = z\nhave by replacement_axiom: Image from prop identity_relation, set {1, 2}\n$is_set(Image)\n";

#[test]
fn replacement_replays_the_recorded_uniqueness() {
    let (run, compiler) = super::execute(REPLACEMENT);
    let lean = compiler.compile_run(&run, "replacement").unwrap();
    assert!(lean.contains("Litex.replacement") && lean.contains("Litex.IndexedUnionSemantics M"));
    assert!(!lean.contains("axiom ") && !lean.contains("sorry"));
}

#[test]
fn replacement_rejects_a_missing_uniqueness_citation() {
    let (mut run, compiler) = super::execute(REPLACEMENT);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::HaveByReplacementAxiom(
            crate::execute::ExecHaveByReplacementAxiomStmtResult::Success(p),
        ),
    )) = &mut run.statement_results[2]
    else {
        panic!()
    };
    p.uniqueness_fact_id = FactId::new(999_999);
    assert!(compiler.compile_run(&run, "missing_unique").is_err());
}

const CHOICE: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/lean/examples/nonempty_family_choice/statement.lit"
));
const ZORN: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/lean/examples/poset_maximal_element/statement.lit"
));

#[test]
fn choice_replays_the_original_release_block() {
    let (run, compiler) = super::execute(CHOICE);
    let lean = compiler.compile_run(&run, "family_choice").unwrap();
    assert!(
        lean.contains("Litex.choiceForIdentity") && lean.contains("Litex.IndexedUnionSemantics M")
    );
    assert_eq!(lean, compiler.compile_run(&run, "family_choice").unwrap());
    assert!(!lean.contains("axiom ") && !lean.contains("sorry"));
}

#[test]
fn zorn_replays_the_original_poset_obligations() {
    let (run, compiler) = super::execute(ZORN);
    let lean = compiler.compile_run(&run, "poset_maximal").unwrap();
    assert!(lean.contains("Litex.zornMaximal"));
    assert_eq!(lean, compiler.compile_run(&run, "poset_maximal").unwrap());
    assert!(!lean.contains("axiom ") && !lean.contains("sorry"));
}

#[test]
fn local_trust_is_not_silently_hoisted() {
    let (run, compiler) = execute("claim:\n    ? 1 = 2\n    trust 1 = 2\n");
    assert!(compiler.compile_run(&run, "unclosed_assumption").is_err());
}

fn choice_release_mut(
    run: &mut RunLitexCodeResult,
) -> &mut crate::execute::execute_by_stmt::ExecReleaseAxiomOfChoiceStmtSuccess {
    let ExecStmtResult::ProofBlock(
        crate::execute::execute_proof_block_stmt::ExecProofBlockStmtResult::Claim(
            crate::execute::execute_proof_block_stmt::ExecClaimStmtResult::Success(claim),
        ),
    ) = &mut run.statement_results[0]
    else {
        panic!("claim")
    };
    let crate::execute::execute_proof_block_stmt::ExecClaimBodyProof::Forall(body) =
        &mut claim.body
    else {
        panic!("forall")
    };
    let ExecStmtResult::ReleaseAndExpand(
        crate::execute::ExecReleaseAndExpandStmtResult::AxiomOfChoice(
            crate::execute::execute_by_stmt::ExecReleaseAxiomOfChoiceStmtResult::Success(release),
        ),
    ) = &mut body.proof_steps[0]
    else {
        panic!("choice")
    };
    release
}

#[test]
fn choice_rejects_a_missing_original_obligation_store() {
    let (mut run, compiler) = super::execute(CHOICE);
    choice_release_mut(&mut run).obligations[0].stored = Err("missing retained store".into());
    assert_eq!(
        compiler
            .compile_run(&run, "missing_store")
            .unwrap_err()
            .route,
        "Choice/ObligationStore"
    );
}

#[test]
fn choice_rejects_reordered_obligation_evidence() {
    let (mut run, compiler) = super::execute(CHOICE);
    choice_release_mut(&mut run).obligations.swap(0, 1);
    assert_eq!(
        compiler
            .compile_run(&run, "reordered_obligations")
            .unwrap_err()
            .route,
        "Choice/SethoodSubject"
    );
}

#[test]
fn zorn_rejects_reordered_poset_obligations() {
    let (mut run, compiler) = super::execute(ZORN);
    let ExecStmtResult::ProofBlock(
        crate::execute::execute_proof_block_stmt::ExecProofBlockStmtResult::Claim(
            crate::execute::execute_proof_block_stmt::ExecClaimStmtResult::Success(claim),
        ),
    ) = &mut run.statement_results[4]
    else {
        panic!("claim")
    };
    let crate::execute::execute_proof_block_stmt::ExecClaimBodyProof::Forall(body) =
        &mut claim.body
    else {
        panic!("forall")
    };
    let ExecStmtResult::ReleaseAndExpand(
        crate::execute::ExecReleaseAndExpandStmtResult::ZornLemma(
            crate::execute::execute_by_stmt::ExecReleaseZornLemmaStmtResult::Success(release),
        ),
    ) = &mut body.proof_steps[0]
    else {
        panic!("Zorn")
    };
    release.obligations.swap(1, 2);
    assert_eq!(
        compiler
            .compile_run(&run, "reordered_poset")
            .unwrap_err()
            .route,
        "Zorn/ObligationSubject"
    );
}
