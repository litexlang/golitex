use super::source_position::{SourceOwner, SourcePosition};
use super::LitexToLeanCompiler;
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferEqualFactPositiveRealPowerResult, InferEqualFactResult, InferResult,
};

const SOURCE: &str = "forall a R+, n N:\n    a^(n+0)=a^n\n    =>:\n        a^n $in R+\n";

fn checked() -> (RunLitexCodeResult, LitexToLeanCompiler) {
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(), session: false, strict: true, language: OutputLanguage::English,
    });
    let result = runtime.run_litex_code(SOURCE).expect("actual source run");
    assert!(result.success && result.session_error.is_none());
    (result, LitexToLeanCompiler::new(runtime))
}

fn original(
    result: &RunLitexCodeResult,
) -> (&VerifyForallFactSuccess, &[InferEqualFactResult], usize, &InferEqualFactPositiveRealPowerResult) {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) = &result.statement_results[0]
    else { panic!("original forall statement") };
    let VerifyFactResult::ForallFact(proof) = &statement.verify_result
    else { panic!("original forall proof") };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(proof)) = proof.as_ref()
    else { panic!("original local introduction") };
    let Some(InferResult::AtomicFact(InferAtomicFactResult::EqualFact(rules))) =
        &proof.assumed_dom_facts[0].store_and_infer.infer
    else { panic!("original equality infer group") };
    let (index, power) = rules.iter().enumerate().find_map(|(index, rule)| {
        if let InferEqualFactResult::PositiveRealPower(power) = rule { Some((index, power)) } else { None }
    }).expect("the selected equality really infers positive-power membership");
    assert_eq!(power.transports.len(), 2, "both source power sides have actual retained transports");
    (proof, rules, index, power)
}

#[test]
fn positive_power_cursor_blocks_own_and_later_stores_in_the_completed_source_environment() {
    let (result, compiler) = checked();
    let (forall, rules, index, power) = original(&result);
    let run = SourcePosition::new(None, SourceOwner::Run(&result), 0);
    let header = SourcePosition::new(Some(&run), SourceOwner::Forall(forall), usize::MAX);
    let equality = SourcePosition::new(Some(&header), SourceOwner::EqualityInferences(rules), index);
    let group = SourcePosition::new(Some(&equality), SourceOwner::PositivePowerInferences(power), 0);
    let first = SourcePosition::new(Some(&group), SourceOwner::PositivePowerTransport(&power.transports[0]), 0);
    let own = power.transports[0].derived.primary_fact_id();
    let later = power.transports[1].derived.primary_fact_id();
    assert!(forall.local_env.facts.facts_by_id.contains_key(&own));
    assert!(forall.local_env.facts.facts_by_id.contains_key(&later));
    for stage in 0..=2 {
        let pending = SourcePosition { before: stage, ..first };
        assert_eq!(pending.visible_fact(own, &compiler.runtime).unwrap_err().route, "Inference/FutureProducer");
        assert_eq!(pending.visible_fact(later, &compiler.runtime).unwrap_err().route, "Inference/FutureProducer");
    }
    let complete = SourcePosition { before: 3, ..first };
    assert_eq!(complete.visible_fact(own, &compiler.runtime).unwrap().1, format!("h_{}", own.value()));
    assert_eq!(complete.visible_fact(later, &compiler.runtime).unwrap_err().route, "Inference/FutureProducer");
}

#[test]
fn positive_power_cursor_preserves_the_previous_transport_inside_the_next_original_proof() {
    let (result, compiler) = checked();
    let (forall, rules, index, power) = original(&result);
    let run = SourcePosition::new(None, SourceOwner::Run(&result), 0);
    let header = SourcePosition::new(Some(&run), SourceOwner::Forall(forall), usize::MAX);
    let equality = SourcePosition::new(Some(&header), SourceOwner::EqualityInferences(rules), index);
    let group = SourcePosition::new(Some(&equality), SourceOwner::PositivePowerInferences(power), 1);
    let second = SourcePosition::new(Some(&group), SourceOwner::PositivePowerTransport(&power.transports[1]), 0);
    let prior = power.transports[0].derived.primary_fact_id();
    let own = power.transports[1].derived.primary_fact_id();
    assert_eq!(second.visible_fact(prior, &compiler.runtime).unwrap().1, format!("h_{}", prior.value()));
    assert_eq!(second.visible_fact(own, &compiler.runtime).unwrap_err().route, "Inference/FutureProducer");
    let completed_rule = SourcePosition { before: index + 1, ..equality };
    for transport in &power.transports {
        assert!(completed_rule.visible_fact(transport.derived.primary_fact_id(), &compiler.runtime).is_ok());
    }
}

#[test]
fn positive_power_detailed_projection_retains_ordered_original_proofs_and_stores() {
    let (result, compiler) = checked();
    let (_, _, _, power) = original(&result);
    let json = crate::json_output::project_run_detailed(&result, &compiler.runtime, "eval", None);
    let statement = &json.as_object().unwrap().get("statement_results").unwrap().as_array().unwrap()[0];
    let verify = statement.as_object().unwrap().get("verify").unwrap();
    let domain = &verify.as_object().unwrap().get("assumed_dom_facts").unwrap().as_array().unwrap()[0];
    let store = domain.as_object().unwrap().get("store_and_infer").unwrap();
    let rules = store.as_object().unwrap().get("positive_real_power_rules").unwrap().as_array().unwrap();
    assert_eq!(rules.len(), 1);
    let transports = rules[0].as_object().unwrap().get("transports").unwrap().as_array().unwrap();
    assert_eq!(transports.len(), power.transports.len());
    for (projected, original) in transports.iter().zip(&power.transports) {
        let projected = projected.as_object().unwrap();
        assert_eq!(projected.get("power").unwrap().as_str().unwrap(), original.power.readable_string());
        assert!(projected.get("positivity").is_some());
        assert!(projected.get("exponent_real").is_some());
        let source = projected.get("source").unwrap().as_object().unwrap();
        assert_eq!(source.get("fact_id").unwrap().as_str().unwrap(), original.source_fact_id.to_string());
        assert!(projected.get("derived").is_some());
    }
}
