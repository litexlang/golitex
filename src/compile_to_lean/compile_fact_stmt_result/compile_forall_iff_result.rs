use crate::compile_to_lean::helper::{conjunction_proposition, source_subject};
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

/// The source sugar is the conjunction of its two complete universal directions.
/// Only their outer IDs differ between verification and storage.
pub(in crate::compile_to_lean) fn validate_iff_direction(
    source: &ForallFactWithIff,
    direction: &ForallFact,
    forward: bool,
) -> Result<(), LeanCompileError> {
    let common = &source.forall_fact;
    let (premises, conclusions) = if forward {
        (&common.then_facts, &source.iff_facts)
    } else {
        (&source.iff_facts, &common.then_facts)
    };
    let expected_dom: Vec<Fact> = common
        .dom_facts
        .iter()
        .cloned()
        .chain(premises.iter().cloned().map(Fact::from))
        .collect();
    if direction.typed_parameters != common.typed_parameters
        || direction.dom_facts != expected_dom
        || &direction.then_facts != conclusions
        || premises.is_empty()
        || conclusions.is_empty()
    {
        return Err(LeanCompileError::new("ForallIff/Direction",
            "An iff direction must preserve the original binders, shared premises and ordered sides."));
    }
    Ok(())
}

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_forall_iff_formation(
        &self,
        fact: &ForallFactWithIff,
        proof: &crate::execute::execute_fact_stmt::verify_forall_fact_with_iff::ForallFactWithIffWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if proof.detailed_ref().then.len() != fact.forall_fact.then_facts.len()
            || proof.detailed_ref().iff.len() != fact.iff_facts.len()
            || proof.detailed_ref().then.is_empty()
            || proof.detailed_ref().iff.is_empty()
        {
            return Err(LeanCompileError::unsupported("ForallIff/FormationArity"));
        }
        let scope = SourcePosition::new(Some(position), SourceOwner::ForallIffWD(fact, proof), 0);
        let (head, _, definitions) = self.compile_forall_head(
            &fact.forall_fact,
            &proof.detailed_ref().introduced_params,
            &proof.detailed_ref().assumed_dom_facts,
            &scope,
        )?;
        let formed = SourcePosition {
            before: fact
                .forall_fact
                .typed_parameters
                .groups
                .iter()
                .map(|g| g.params.len())
                .sum::<usize>()
                + proof.detailed_ref().assumed_dom_facts.len(),
            ..scope
        };
        let mut sides = Vec::new();
        for (clauses, wds) in [
            (&fact.forall_fact.then_facts, &proof.detailed_ref().then),
            (&fact.iff_facts, &proof.detailed_ref().iff),
        ] {
            let mut propositions = Vec::new();
            let mut binders = Vec::new();
            for (clause, wd) in clauses.iter().zip(wds) {
                let source: Fact = clause.clone().into();
                let proposition = self.compile_formed_fact_proposition(wd, &source, &formed)?;
                let proposition = self.scope_proposition(proposition, &definitions);
                binders.push(format!("(h_{} : {proposition})", source.fact_id().value()));
                propositions.push(proposition);
            }
            sides.push((binders.join(" "), conjunction_proposition(propositions)?));
        }
        conjunction_proposition(vec![
            format!("∀ {} {}, {}", head.join(" "), sides[0].0, sides[1].1),
            format!("∀ {} {}, {}", head.join(" "), sides[1].0, sides[0].1),
        ])
    }

    pub(in crate::compile_to_lean) fn compile_verify_forall_iff(
        &self,
        result: &VerifyForallFactWithIffResult,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let VerifyForallFactWithIffResult::Success(proof) = result else {
            return Err(LeanCompileError::unsupported("ForallIff/Failed"));
        };
        let mut compiled = Vec::new();
        let mut ids = Vec::new();
        for (forward, result) in [
            (true, &proof.then_implies_iff),
            (false, &proof.iff_implies_then),
        ] {
            let Fact::ForallFact(direction) = source_subject(result)? else {
                return Err(LeanCompileError::unsupported("ForallIff/DirectionFamily"));
            };
            validate_iff_direction(&proof.fact, &direction, forward)?;
            if direction.fact_id == proof.fact.fact_id || ids.contains(&direction.fact_id) {
                return Err(LeanCompileError::unsupported("ForallIff/DirectionIdentity"));
            }
            ids.push(direction.fact_id);
            compiled.push(self.compile_verify(result, position)?);
        }
        Ok((
            conjunction_proposition(compiled.iter().map(|p| p.0.clone()).collect())?,
            format!("⟨{}, {}⟩", compiled[0].1, compiled[1].1),
        ))
    }

    pub(in crate::compile_to_lean) fn compile_iff_stored_directions(
        &self,
        store: &StoreFactAndInferResult,
        source: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        self.validate_store(&store.store, source)?;
        let StoreFactResult::ForallFactWithIff(stored) = &store.store else {
            return Err(LeanCompileError::unsupported("ForallIff/StoreFamily"));
        };
        if !matches!(
            &store.infer,
            None | Some(crate::store_fact_and_infer::InferResult::ForallFactWithIff(
                _
            ))
        ) {
            return Err(LeanCompileError::unsupported("ForallIff/InferFamily"));
        }
        [&stored.forward, &stored.reverse]
            .into_iter()
            .enumerate()
            .map(|(index, direction)| {
                let fact = Fact::ForallFact(direction.fact.clone());
                if self.resolve_fact(direction.fact_id, position)? != fact {
                    return Err(LeanCompileError::unsupported("ForallIff/StoreIdentity"));
                }
                // The checked conjunction determines this projection's entire type,
                // including its original WD-dependent binders. Do not rerender it.
                let side = if index == 0 { "p" } else { "q" };
                let proposition = format!(
                    "((fun {{p q : Prop}} (_ : p ∧ q) => {side}) {})",
                    compiled.1
                );
                self.emit_internal_fact(
                    &fact,
                    &(proposition, format!("({}).{}", compiled.1, index + 1)),
                    position,
                )
            })
            .collect()
    }
}
