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
fn local_trust_requires_an_explicit_closed_assumption() {
    let (run, compiler) = execute("claim:\n    ? 1 = 2\n    trust 1 = 2\n");
    let lean = compiler.compile_run(&run, "closed_assumption").unwrap();
    assert!(lean.contains("variable (h_"));
    assert!(!lean.contains("axiom ") && !lean.contains("sorry"));
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

#[test]
fn trust_have_replays_nonzero_guard_and_parameter_inferences() {
    let (run, compiler) = execute("trust have denominator R:\n    denominator != 0\n1 / denominator = 1 / denominator\ndenominator $in C\n");
    let lean = compiler.compile_run(&run, "assumed_denominator").unwrap();
    assert!(lean.contains("variable {_Host_i"));
    assert!(lean.contains("Litex.div"));
    assert!(!lean.contains("axiom ") && !lean.contains("sorry"));
    assert_eq!(
        lean,
        compiler.compile_run(&run, "assumed_denominator").unwrap()
    );
}

#[test]
fn trust_have_can_introduce_dependent_set_members() {
    let (run, compiler) = execute("trust have A set, a A\na $in A\n$is_set(a)\n");
    compiler.compile_run(&run, "assumed_member").unwrap();
}

#[test]
fn trust_have_requires_parameter_and_body_evidence() {
    let (mut run, compiler) = execute("trust have a R:\n    a > 0\na >= 0\n");
    let ExecStmtResult::Trust(crate::execute::ExecTrustBoundaryStmtResult::TrustHaveStmt(
        crate::execute::ExecTrustHaveStmtResult::Success(p),
    )) = &mut run.statement_results[0]
    else {
        panic!()
    };
    p.param_type_well_defined.clear();
    assert!(compiler.compile_run(&run, "missing_parameter_wd").is_err());
}

#[test]
fn local_trust_closes_real_parameter_and_is_citable_later() {
    let (run, compiler) =
        execute("claim:\n    ? forall x R:\n        x >= 0\n    trust x > 0\n0 >= 0\n");
    let lean = compiler.compile_run(&run, "closed_positive").unwrap();
    assert!(lean.contains("variable (h_") && lean.contains("(∀"));
}

#[test]
fn template_alias_replays_body_and_definition_publication() {
    let (run, compiler) = super::execute(
        r"template<S set>:
    have carrier_copy set = S
\carrier_copy<R> = R
",
    );
    let lean = compiler.compile_run(&run, "carrier_copy").unwrap();
    assert!(lean.contains("noncomputable def _template_i"));
    assert!(!lean.contains("axiom ") && !lean.contains("sorry"));
}

#[test]
fn template_alias_replays_argument_and_nonzero_checks() {
    let (run, compiler) = super::execute(
        r"template<x R, y R: y != 0,>:
    have quotient R = x / y
\quotient<6, 2> = 3
",
    );
    compiler.compile_run(&run, "guarded_quotient").unwrap();
}

#[test]
fn template_alias_requires_the_original_publication_link() {
    let (mut run, compiler) = super::execute(
        r"template<S set>:
    have carrier_copy set = S
\carrier_copy<R> = R
",
    );
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(
        crate::execute::ExecDefTemplateStmtResult::Success(p),
    )) = &mut run.statement_results[0]
    else {
        panic!()
    };
    p.definition_facts[0].source_fact_id = FactId::new(999_999);
    assert!(compiler
        .compile_run(&run, "missing_template_source")
        .is_err());
}

#[test]
fn local_assumption_rejects_an_uncaptured_witness_closure() {
    let (run, compiler) = execute("sketch:\n    have x R\n    trust x > 0\n");
    assert!(compiler.compile_run(&run, "local_witness").is_err());
}

#[test]
fn local_assumption_rejects_missing_original_body_wd() {
    let (mut run, compiler) = execute("claim:\n    ? 1 = 2\n    trust 1 = 2\n");
    let ExecStmtResult::ProofBlock(
        crate::execute::execute_proof_block_stmt::ExecProofBlockStmtResult::Claim(
            crate::execute::execute_proof_block_stmt::ExecClaimStmtResult::Success(p),
        ),
    ) = &mut run.statement_results[0]
    else {
        panic!()
    };
    let crate::execute::execute_proof_block_stmt::ExecClaimBodyProof::NonForall(b) = &mut p.body
    else {
        panic!()
    };
    let ExecStmtResult::Trust(crate::execute::ExecTrustBoundaryStmtResult::TrustStmt(
        crate::execute::ExecTrustStmtResult::Success(p),
    )) = &mut b.proof_steps[0]
    else {
        panic!()
    };
    p.facts_well_defined.clear();
    assert!(compiler.compile_run(&run, "missing_local_wd").is_err());
}

#[test]
fn template_instance_rejects_missing_nonzero_obligation() {
    let (mut run, compiler) = super::execute(include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/lean/examples/template_guarded_quotient/statement.lit"
    )));
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(fact)) = &mut run.statement_results[1]
    else {
        panic!()
    };
    let VerifyFactResult::Equality(result) = &mut fact.verify_result else {
        panic!()
    };
    let VerifyEqualityResult::Success(p) = result.as_mut() else {
        panic!()
    };
    let ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::InstantiatedTemplateObj(p),
        ..
    } = &mut p.well_defined_proof.left
    else {
        panic!()
    };
    p.requirement_fact_verified.pop();
    assert!(compiler
        .compile_run(&run, "missing_template_guard")
        .is_err());
}

#[test]
fn template_function_body_remains_an_explicit_boundary() {
    let (run, compiler) = super::execute("template<S set>:\n    have fn f(x R) R = x\n");
    assert_eq!(
        compiler
            .compile_run(&run, "template_function")
            .unwrap_err()
            .route,
        "Template/Body"
    );
}

#[test]
fn local_quantified_trust_remains_an_explicit_boundary() {
    let (run, compiler) = execute("claim:\n    ? forall x R:\n        x = 0\n    trust:\n        forall y R:\n            y = 0\n");
    assert!(compiler
        .compile_run(&run, "local_quantified_trust")
        .is_err());
}
