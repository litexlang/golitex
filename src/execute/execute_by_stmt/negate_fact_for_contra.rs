use crate::ast::fact::{
    negate_atomic_fact, ExistOrAndChainAtomicFact, Fact, ForallFact, NotForallFact,
    QuantifierFreeFact,
};
use crate::instantiate::quantifier_free_fact_to_fact;
use crate::runtime::Runtime;

pub(super) fn negate_fact_for_contra(runtime: &mut Runtime, fact: &Fact) -> Result<Fact, String> {
    match fact {
        Fact::AtomicFact(atomic) => {
            let neg = negate_atomic_fact(atomic, runtime.global_ids.allocate_fact_id())
                .ok_or_else(|| "by contra: cannot negate this atomic fact".to_string())?;
            Ok(neg.into())
        }
        Fact::ExistFact(plain) => {
            let mut negated = plain.clone();
            negated.fact_id = runtime.global_ids.allocate_fact_id();
            Ok(Fact::NotExistFact(negated))
        }
        Fact::NotExistFact(plain) => {
            let mut negated = plain.clone();
            negated.fact_id = runtime.global_ids.allocate_fact_id();
            Ok(Fact::ExistFact(negated))
        }
        Fact::AndFact(a) => negate_qf(runtime, QuantifierFreeFact::AndFact(a.clone())),
        Fact::OrFact(o) => negate_qf(runtime, QuantifierFreeFact::OrFact(o.clone())),
        Fact::ChainFact(c) => negate_qf(runtime, QuantifierFreeFact::ChainFact(c.clone())),
        Fact::ForallFact(forall) => {
            let mut dom_facts = Vec::new();
            for dom in &forall.dom_facts {
                dom_facts.push(as_quantifier_free(dom).ok_or_else(|| {
                    "by contra: existing NotForall cannot represent a quantified domain fact"
                        .to_string()
                })?);
            }
            let mut then_facts = Vec::new();
            for then in &forall.then_facts {
                then_facts.push(as_quantifier_free(&then.clone().into()).ok_or_else(|| {
                    "by contra: existing NotForall cannot represent an existential conclusion"
                        .to_string()
                })?);
            }
            Ok(Fact::NotForall(NotForallFact {
                fact_id: runtime.global_ids.allocate_fact_id(),
                typed_parameters: forall.typed_parameters.clone(),
                dom_facts,
                then_facts,
                line_file: forall.line_file.clone(),
            }))
        }
        Fact::NotForall(not_forall) => {
            let then_facts = not_forall
                .then_facts
                .iter()
                .map(|f| match f {
                    QuantifierFreeFact::AtomicFact(a) => {
                        ExistOrAndChainAtomicFact::AtomicFact(a.clone())
                    }
                    QuantifierFreeFact::AndFact(a) => ExistOrAndChainAtomicFact::AndFact(a.clone()),
                    QuantifierFreeFact::ChainFact(c) => {
                        ExistOrAndChainAtomicFact::ChainFact(c.clone())
                    }
                    QuantifierFreeFact::OrFact(o) => ExistOrAndChainAtomicFact::OrFact(o.clone()),
                })
                .collect();
            Ok(Fact::ForallFact(ForallFact {
                fact_id: runtime.global_ids.allocate_fact_id(),
                typed_parameters: not_forall.typed_parameters.clone(),
                dom_facts: not_forall
                    .dom_facts
                    .iter()
                    .cloned()
                    .map(quantifier_free_fact_to_fact)
                    .collect(),
                then_facts,
                line_file: not_forall.line_file.clone(),
            }))
        }
        Fact::ExistUniqueFact(plain) => {
            super::negate_unique_exist::negate_unique_exist(runtime, plain)
        }
        Fact::ForallFactWithIff(iff) => super::negate_forall_iff::negate_forall_iff(runtime, iff),
    }
}

fn negate_qf(runtime: &mut Runtime, fact: QuantifierFreeFact) -> Result<Fact, String> {
    let line_file = match &fact {
        QuantifierFreeFact::AndFact(a) => a.line_file.clone(),
        QuantifierFreeFact::OrFact(o) => o.line_file.clone(),
        QuantifierFreeFact::ChainFact(c) => c.line_file.clone(),
        QuantifierFreeFact::AtomicFact(_) => None,
    };
    let negated = runtime
        .negate_quantifier_free_conjunction(&[fact], line_file)
        .map_err(|e| format!("by contra: cannot construct classified negation: {e:?}"))?
        .ok_or_else(|| "by contra: cannot negate this quantifier-free shape".to_string())?;
    Ok(quantifier_free_fact_to_fact(negated))
}

pub(super) fn as_quantifier_free(fact: &Fact) -> Option<QuantifierFreeFact> {
    match fact {
        Fact::AtomicFact(a) => Some(QuantifierFreeFact::AtomicFact(a.clone())),
        Fact::AndFact(a) => Some(QuantifierFreeFact::AndFact(a.clone())),
        Fact::OrFact(o) => Some(QuantifierFreeFact::OrFact(o.clone())),
        Fact::ChainFact(c) => Some(QuantifierFreeFact::ChainFact(c.clone())),
        _ => None,
    }
}

#[cfg(test)]
#[path = "../../../tests/unit/execute/contra_classified_negation/tests.rs"]
mod classified_negation_tests;
