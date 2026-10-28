use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::{
    ExecHaveFnByForallExistUniqueStmtResult, ExecHaveFnByForallExistUniqueStmtSuccessResult,
};
use crate::prelude::*;

const COPY: &str = include_str!("../../../lean/examples/selected_identity_function/statement.lit");
const RECIPROCAL: &str =
    include_str!("../../../lean/examples/selected_reciprocal_function/statement.lit");

#[test]
fn selected_function_replays_unique_source_and_published_call_property() {
    for source in [
        COPY,
        RECIPROCAL,
        include_str!("../../../lean/examples/selected_sum_function/statement.lit"),
        include_str!("../../../lean/examples/selected_set_identity_function/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "selected_function").unwrap();
        assert!(output.contains("Litex.selectedFn "));
        assert!(output.contains("Litex.existsUniqueValueOfObjects"));
        assert!(output.contains("Litex.selectedFn_call_spec"));
        assert!(output.contains("Litex.selectedFn_unique"));
        assert!(!output.contains("sorry"));
        assert_eq!(
            output,
            compiler.compile_run(&run, "selected_function").unwrap()
        );
    }
}

fn selected(run: &mut RunLitexCodeResult) -> &mut ExecHaveFnByForallExistUniqueStmtSuccessResult {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByForallExistUnique(
        ExecHaveFnByForallExistUniqueStmtResult::Success(p),
    )) = &mut run.statement_results[1]
    else {
        panic!("selected function")
    };
    p
}

#[test]
fn selected_function_rejects_changed_source_signature_or_published_facts() {
    for mutation in 0..8 {
        let (mut run, compiler) = super::execute(RECIPROCAL);
        let p = selected(&mut run);
        match mutation {
            0 => p.property_forall_fact_id = p.membership_fact_id,
            1 => {
                p.stored_fact_ids.pop();
            }
            2 => p.statement.forall.dom_facts.clear(),
            3 => {
                let StoreFactResult::AtomicFact(s) = &mut p.membership.store else {
                    panic!()
                };
                let AtomicFact::InFact(s) = &mut s.fact else {
                    panic!()
                };
                s.element = Obj::StandardSet(StandardSet::R);
            }
            4 => {
                let StoreFactResult::ForallFact(s) = &mut p.property.store else {
                    panic!()
                };
                s.fact.then_facts.clear();
            }
            5 => {
                let StoreFactResult::ForallFact(s) = &mut p.uniqueness.store else {
                    panic!()
                };
                let id = s.fact.typed_parameters.groups[0].params[0].id;
                s.fact.typed_parameters.groups.last_mut().unwrap().params[0].id = id;
            }
            6 => {
                let FactWellDefinedProof::ForallFact(wd) = &mut p.property_well_defined else {
                    panic!()
                };
                wd.as_detailed_mut()
                    .unwrap()
                    .introduced_params
                    .defined_params
                    .store_and_infer_results
                    .clear();
            }
            7 => {
                let VerifyFactResult::ForallFact(result) = &mut p.source_forall else {
                    panic!()
                };
                let VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(
                    source,
                )) = result.as_mut()
                else {
                    panic!("known forall route")
                };
                source.cite_fact_id = p.property_forall_fact_id;
            }
            _ => unreachable!(),
        }
        assert!(
            compiler.compile_run(&run, "corrupt_selected").is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn selected_function_publication_order_keeps_hypothetical_wd_local() {
    let (mut run, compiler) = super::execute(RECIPROCAL);
    let p = selected(&mut run);
    let name = p.statement.name.id;
    let published = [
        (3, p.membership_fact_id),
        (5, p.property_forall_fact_id),
        (6, p.uniqueness_forall_fact_id),
    ];
    let FactWellDefinedProof::ForallFact(wd) = &p.property_well_defined else {
        panic!()
    };
    let local_ids: Vec<_> = wd
        .detailed_ref()
        .introduced_params
        .defined_params
        .store_and_infer_results
        .iter()
        .map(|s| s.primary_fact_id())
        .collect();
    let before = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    let after = SourcePosition::new(None, SourceOwner::Run(&run), 2);
    assert!(before.visible_selected_function(&name).is_err());
    assert!(after.visible_selected_function(&name).is_ok());
    for (stage, id) in published {
        assert!(compiler.cited_fact_reference(id, &before).is_err());
        assert!(compiler.cited_fact_reference(id, &after).is_ok());
        for cursor in [stage - 1, stage] {
            let at = SourcePosition::new(
                Some(&before),
                SourceOwner::Statement(&run.statement_results[1]),
                cursor,
            );
            assert_eq!(
                compiler.cited_fact_reference(id, &at).is_ok(),
                cursor == stage
            );
        }
    }
    for id in local_ids {
        assert!(compiler.cited_fact_reference(id, &after).is_err());
    }
}

#[test]
fn unique_forall_alpha_matching_preserves_carriers_and_free_inputs() {
    let (mut run, _) = super::execute(COPY);
    let p = selected(&mut run);
    let ExistOrAndChainAtomicFact::ExistUniqueFact(source) = &p.statement.forall.then_facts[0]
    else {
        panic!()
    };
    let new_id = p.statement.name.id;
    let old_id = source.typed_parameters.groups[0].params[0].id;
    let mut renamed = source.clone();
    renamed.typed_parameters.groups[0].params[0].id = new_id;
    let QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(eq)) = &mut renamed.facts[0] else {
        panic!()
    };
    let Obj::Identifier(IdentifierObj::Plain { id, .. }) = &mut eq.left else {
        panic!()
    };
    assert_eq!(*id, old_id);
    *id = new_id;
    let original = Fact::ExistUniqueFact(source.clone());
    assert!(super::super::helper::instantiated_fact_matches(
        &original,
        &Fact::ExistUniqueFact(renamed.clone()),
        &Default::default()
    ));
    let input = &p.statement.forall.typed_parameters.groups[0].params[0];
    let mut captured_input = renamed.clone();
    captured_input.typed_parameters.groups[0].params[0].id = input.id;
    let QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(eq)) = &mut captured_input.facts[0]
    else {
        panic!()
    };
    eq.left = Obj::Identifier(IdentifierObj::from_bound_name(input));
    let substitution = std::collections::HashMap::from([(input.id, eq.left.clone())]);
    assert!(!super::super::helper::instantiated_fact_matches(
        &original,
        &Fact::ExistUniqueFact(captured_input),
        &substitution,
    ));
    let mut wrong_carrier = renamed.clone();
    wrong_carrier.typed_parameters.groups[0].param_type =
        ParamType::Obj(Obj::StandardSet(StandardSet::C));
    assert!(!super::super::helper::instantiated_fact_matches(
        &original,
        &Fact::ExistUniqueFact(wrong_carrier),
        &Default::default()
    ));
    let QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(eq)) = &mut renamed.facts[0] else {
        panic!()
    };
    eq.right = eq.left.clone();
    assert!(!super::super::helper::instantiated_fact_matches(
        &original,
        &Fact::ExistUniqueFact(renamed),
        &Default::default()
    ));
}

#[test]
fn selected_function_requires_uniqueness_and_call_domain() {
    for source in [
        "thm ordinary_copy:\n    ? forall seed R:\n        exist value R st {value = seed}\n    witness exist value R st {value = seed} from seed\nhave fn f by exist!:\n    ? forall x R:\n        exist! y R st {y = x}\n".to_string(),
        format!("{RECIPROCAL}selected(0) = 0\n"),
    ] {
        let mut runtime = Runtime::new_with_result_detail(LaunchCommand::Eval { code: String::new(), session: false, strict: true, language: OutputLanguage::English }, crate::result_detail::OutputDetail::Detailed);
        let result = runtime.run_litex_code(&source).unwrap();
        assert!(!result.success);
        assert!(matches!(&result.statement_results[0], ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(ExecDefThmStmtResult::Success(_)))));
    }
}
