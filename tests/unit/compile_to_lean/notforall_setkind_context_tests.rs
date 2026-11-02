use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedFactSearchedProof;
use crate::execute::execute_fact_stmt::verify_not_forall_fact::*;
use crate::execute::execute_witness_stmt::*;
use crate::prelude::*;
use crate::store_fact_and_infer::InferResult;

const SOURCES66: &[(&str, &str)] = &[
    (
        "nonempty_set_counterexample",
        include_str!("../../../lean/examples/notforall_setkind_nonempty_set_counterexample/statement.lit"),
    ),
    (
        "finite_set_counterexample",
        include_str!("../../../lean/examples/notforall_setkind_finite_set_counterexample/statement.lit"),
    ),
    (
        "finite_set_dependent_counterexample",
        include_str!("../../../lean/examples/notforall_setkind_finite_set_dependent_counterexample/statement.lit"),
    ),
    (
        "nonempty_set_dependent_counterexample",
        include_str!("../../../lean/examples/notforall_setkind_nonempty_set_dependent_counterexample/statement.lit"),
    ),
    (
        "nonempty_set_premise_inferred_witness",
        include_str!("../../../lean/examples/notforall_setkind_nonempty_set_premise_inferred_witness/statement.lit"),
    ),
    (
        "finite_set_premise_inferred_witness",
        include_str!("../../../lean/examples/notforall_setkind_finite_set_premise_inferred_witness/statement.lit"),
    ),
];

fn statement(run: &RunLitexCodeResult) -> &ExecFactStmtSuccessResult {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = &run.statement_results[1] else {
        panic!()
    };
    p
}
fn statement_mut(run: &mut RunLitexCodeResult) -> &mut ExecFactStmtSuccessResult {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = &mut run.statement_results[1] else {
        panic!()
    };
    p
}
fn negative(run: &RunLitexCodeResult) -> &VerifyNotForallFactSuccess {
    let VerifyFactResult::NotForall(p) = &statement(run).verify_result else {
        panic!()
    };
    let VerifyNotForallFactResult::Success(p) = p.as_ref() else {
        panic!()
    };
    p
}
fn negative_mut(run: &mut RunLitexCodeResult) -> &mut VerifyNotForallFactSuccess {
    let VerifyFactResult::NotForall(p) = &mut statement_mut(run).verify_result else {
        panic!()
    };
    let VerifyNotForallFactResult::Success(p) = p.as_mut() else {
        panic!()
    };
    p
}
fn plain(f: &ExistShapedFact) -> &PlainExistFact {
    let ExistShapedFact::Exist(p) = f else {
        panic!()
    };
    p
}
fn child(result: &VerifyFactResult) -> &VerifyPlainExistFactSuccess {
    let VerifyFactResult::ExistShapedFact(p) = result else {
        panic!()
    };
    let VerifyExistShapedFactResult::PlainExistFact(VerifyPlainExistFactResult::Success(p)) =
        p.as_ref()
    else {
        panic!()
    };
    p
}
fn child_mut(result: &mut VerifyFactResult) -> &mut VerifyPlainExistFactSuccess {
    let VerifyFactResult::ExistShapedFact(p) = result else {
        panic!()
    };
    let VerifyExistShapedFactResult::PlainExistFact(VerifyPlainExistFactResult::Success(p)) =
        p.as_mut()
    else {
        panic!()
    };
    p
}
fn witness(run: &RunLitexCodeResult) -> &ExecWitnessExistFactStmtSuccessResult {
    let ExecStmtResult::Witness(ExecWitnessStmtResult::WitnessExistFact(
        ExecWitnessExistFactStmtResult::Success(p),
    )) = &run.statement_results[0]
    else {
        panic!()
    };
    p
}
fn reject(run: &RunLitexCodeResult, compiler: &crate::compile_to_lean::LitexToLeanCompiler) {
    compiler
        .compile_run(run, "SetKind66ChangedEvidence")
        .expect_err("changed kind, WD, citation or inference must fail closed");
}

#[test]
fn notforall_setkind_original_counterexamples_retain_exact_kinds_and_dependent_carriers() {
    for (name, source) in SOURCES66.iter().take(4) {
        let (run, compiler) = super::execute(source);
        let p = negative(&run);
        let derived = plain(&p.derived_exist);
        let checked = child(&p.prove_derived_exist);
        assert_eq!(derived.typed_parameters, p.fact.typed_parameters);
        assert_eq!(checked.fact, p.derived_exist);
        assert_ne!(derived.fact_id, p.fact.fact_id);
        assert_eq!(
            derived.typed_parameters.groups.len(),
            if name.contains("dependent") { 2 } else { 1 }
        );
        let ExistShapedFactSearchedProof::ByKnownExistShapedFact(cite) = &checked.searched_proof
        else {
            panic!("actual known witness route")
        };
        let StoreFactResult::ExistShapedFact(original) =
            &witness(&run).store_and_infer_result.store
        else {
            panic!()
        };
        assert_eq!(cite.cite_fact_id, original.fact.plain().fact_id);
        assert!(crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::plain_exist_facts_alpha_equal(original.fact.plain(), derived));
        let introduced = &checked
            .well_defined_proof
            .as_detailed()
            .unwrap()
            .introduced_params;
        let exact = &introduced.param_type_well_defined[0];
        let nonempty = name.starts_with("nonempty");
        assert!(matches!(
            (nonempty, exact),
            (true, ParamTypeWellDefinedProof::NonemptySet)
                | (false, ParamTypeWellDefinedProof::FiniteSet)
        ));
        let parent = SourcePosition::new(None, SourceOwner::Run(&run), 1);
        let proposition = compiler
            .canonical_forall_proposition(&p.fact, &parent)
            .unwrap();
        assert!(proposition.contains(if nonempty {
            "Litex.IsNonempty"
        } else {
            "Litex.IsFiniteSet"
        }));
        let output = compiler.compile_run(&run, "SetKind66Original").unwrap();
        assert!(output.contains("_counterexample"));
        assert!(!output.contains("sorry"));
        eprintln!(
            "ORIGINAL66 {name} notforall:{} derived:{} cite:{} binders:{}",
            p.fact.fact_id.value(),
            derived.fact_id.value(),
            cite.cite_fact_id.value(),
            derived.typed_parameters.ordered_param_ids().len()
        );
    }
}

#[test]
fn notforall_setkind_premises_publish_the_actual_inferred_counterexample_without_proof_steps() {
    for (name, source) in SOURCES66.iter().skip(4) {
        let (run, compiler) = super::execute(source);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
            ExecDefThmStmtResult::Success(p),
        )) = &run.statement_results[0]
        else {
            panic!()
        };
        let ExecDefThmBodyProof::Forall(body) = &p.body else {
            panic!()
        };
        assert!(body.proof_steps.is_empty());
        assert_eq!(body.conclusion_proofs.len(), 1);
        let Fact::ForallFact(f) = &p.statement.fact else {
            panic!()
        };
        let Fact::NotForall(n) = &f.dom_facts[0] else {
            panic!()
        };
        let Some(InferResult::NotForall(infer)) = &body.assumed_dom_facts[0].store_and_infer.infer
        else {
            panic!()
        };
        let StoreFactResult::ExistShapedFact(stored) = &infer.derived_exist.store else {
            panic!()
        };
        assert_eq!(n.typed_parameters, plain(&stored.fact).typed_parameters);
        let ExistShapedFactSearchedProof::ByKnownExistShapedFact(cite) =
            &child(&body.conclusion_proofs[0]).searched_proof
        else {
            panic!()
        };
        assert_eq!(cite.cite_fact_id, stored.fact.plain().fact_id);
        let outer = SourcePosition::new(None, SourceOwner::Run(&run), 1);
        assert!(compiler
            .cited_fact_reference(cite.cite_fact_id, &outer)
            .is_err());
        compiler.compile_run(&run, "SetKind66Premise").unwrap();
        eprintln!(
            "ORIGINAL66 {name} actual_inferred_cite:{} proof_steps:0",
            cite.cite_fact_id.value()
        );
    }
}

#[test]
fn notforall_setkind_derived_formation_and_witness_locals_remain_private() {
    for (_, source) in SOURCES66.iter().take(4) {
        let (run, compiler) = super::execute(source);
        let p = negative(&run);
        let c = child(&p.prove_derived_exist);
        let before = SourcePosition::new(None, SourceOwner::Run(&run), 1);
        let after = SourcePosition {
            before: 2,
            ..before
        };
        let Some(InferResult::NotForall(infer)) = &statement(&run).store_and_infer_result.infer
        else {
            panic!()
        };
        let StoreFactResult::ExistShapedFact(stored) = &infer.derived_exist.store else {
            panic!()
        };
        assert!(compiler
            .cited_fact_reference(stored.fact.plain().fact_id, &before)
            .is_err());
        assert!(compiler
            .cited_fact_reference(stored.fact.plain().fact_id, &after)
            .is_ok());
        assert!(compiler
            .cited_fact_reference(plain(&p.derived_exist).fact_id, &after)
            .is_err());
        for local in &c
            .well_defined_proof
            .as_detailed()
            .unwrap()
            .introduced_params
            .defined_params
            .store_and_infer_results
        {
            assert!(compiler
                .cited_fact_reference(local.primary_fact_id(), &after)
                .is_err());
        }
        for local in &witness(&run).witness_equalities {
            assert!(compiler
                .cited_fact_reference(local.primary_fact_id(), &after)
                .is_err());
        }
    }
}

#[test]
fn notforall_setkind_rejects_a_widened_or_other_quantifier_kind() {
    for (_, source) in SOURCES66.iter().take(4) {
        for replacement in [
            ParamType::Obj(Obj::StandardSet(StandardSet::R)),
            ParamType::Set(crate::ast::param::Set {}),
        ] {
            let (mut run, compiler) = super::execute(source);
            negative_mut(&mut run).fact.typed_parameters.groups[0].param_type = replacement;
            reject(&run, &compiler);
        }
    }
}

#[test]
fn notforall_setkind_requires_exact_counterexample_formation_kind() {
    for (name, source) in SOURCES66.iter().take(4) {
        for replacement in [
            ParamTypeWellDefinedProof::Set,
            if name.starts_with("nonempty") {
                ParamTypeWellDefinedProof::FiniteSet
            } else {
                ParamTypeWellDefinedProof::NonemptySet
            },
        ] {
            let (mut run, compiler) = super::execute(source);
            child_mut(&mut negative_mut(&mut run).prove_derived_exist)
                .well_defined_proof
                .as_detailed_mut()
                .unwrap()
                .introduced_params
                .param_type_well_defined[0] = replacement;
            reject(&run, &compiler);
        }
    }
}

#[test]
fn notforall_setkind_rejects_missing_or_reordered_parameter_introductions() {
    for (_, source) in SOURCES66.iter().take(4) {
        let (mut run, compiler) = super::execute(source);
        child_mut(&mut negative_mut(&mut run).prove_derived_exist)
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .introduced_params
            .defined_params
            .stored_fact_ids
            .clear();
        reject(&run, &compiler);
    }
    for (_, source) in SOURCES66.iter().skip(2).take(2) {
        let (mut run, compiler) = super::execute(source);
        child_mut(&mut negative_mut(&mut run).prove_derived_exist)
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .introduced_params
            .defined_params
            .store_and_infer_results
            .swap(0, 1);
        reject(&run, &compiler);
    }
}

#[test]
fn notforall_setkind_rejects_unknown_self_and_private_counterexample_citations() {
    for (_, source) in SOURCES66.iter().take(4) {
        for change in 0..3 {
            let (mut run, compiler) = super::execute(source);
            let p = negative(&run);
            let wrong = match change {
                0 => FactId::new(u64::MAX),
                1 => p.fact.fact_id,
                _ => child(&p.prove_derived_exist)
                    .well_defined_proof
                    .as_detailed()
                    .unwrap()
                    .introduced_params
                    .defined_params
                    .store_and_infer_results[0]
                    .primary_fact_id(),
            };
            let ExistShapedFactSearchedProof::ByKnownExistShapedFact(cite) =
                &mut child_mut(&mut negative_mut(&mut run).prove_derived_exist).searched_proof
            else {
                panic!()
            };
            cite.cite_fact_id = wrong;
            reject(&run, &compiler);
        }
    }
}

#[test]
fn notforall_setkind_requires_its_published_inference() {
    for (_, source) in SOURCES66.iter().take(4) {
        let (mut run, compiler) = super::execute(source);
        statement_mut(&mut run).store_and_infer_result.infer = None;
        reject(&run, &compiler);
    }
}
