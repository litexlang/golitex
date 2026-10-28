use crate::compile_to_lean::compile_by_stmt_result::compile_classified_negation::validate_negated_conjunction;
use crate::compile_to_lean::helper::{conjunction_proposition, source_subject};
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_not_forall_fact::{
    VerifyNotForallFactResult, VerifyNotForallFactSuccess,
};
use crate::prelude::*;
use crate::store_fact_and_infer::InferResult;
use std::collections::HashMap;

// A fixed propositional bridge for the validated De Morgan route. It never
// searches for a source proof or changes the recorded existential witness.
const NEGATION_LAWS: &str = "not_forall, Classical.not_imp, not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc, exists_prop";

fn validate_counterexample<'a>(
    source: &NotForallFact,
    derived: &'a ExistShapedFact,
) -> Result<&'a PlainExistFact, LeanCompileError> {
    let ExistShapedFact::Exist(derived) = derived else {
        return Err(LeanCompileError::unsupported(
            "NotForall/CounterexampleFamily",
        ));
    };
    if source.typed_parameters != derived.typed_parameters
        || derived.facts.len() <= source.dom_facts.len()
        || derived.facts[..source.dom_facts.len()] != source.dom_facts
        || source.fact_id == derived.fact_id
    {
        return Err(LeanCompileError::new(
            "NotForall/CounterexampleSubject",
            "The counterexample must retain the original binders and exact ordered domain facts.",
        ));
    }
    validate_negated_conjunction(&source.then_facts, &derived.facts[source.dom_facts.len()..])?;
    Ok(derived)
}

fn checked_counterexample(
    proof: &VerifyNotForallFactSuccess,
) -> Result<&VerifyPlainExistFactSuccess, LeanCompileError> {
    validate_counterexample(&proof.fact, &proof.derived_exist)?;
    if source_subject(&proof.prove_derived_exist)?
        != crate::ast::fact::exist_shaped_fact_to_fact(&proof.derived_exist)
    {
        return Err(LeanCompileError::unsupported(
            "NotForall/VerificationSubject",
        ));
    }
    let VerifyFactResult::ExistShapedFact(child) = &proof.prove_derived_exist else {
        return Err(LeanCompileError::unsupported(
            "NotForall/VerificationFamily",
        ));
    };
    let VerifyExistShapedFactResult::PlainExistFact(VerifyPlainExistFactResult::Success(child)) =
        child.as_ref()
    else {
        return Err(LeanCompileError::unsupported(
            "NotForall/CounterexampleFailed",
        ));
    };
    Ok(child)
}

impl LitexToLeanCompiler {
    /// Logical quantification uses the same semantic objects as plain exist.
    /// The denotation layer is proof-independent; WD is checked by the recorded
    /// counterexample result before this proposition is exported.
    pub(in crate::compile_to_lean) fn not_forall_proposition(
        &self,
        source: &NotForallFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        Ok(format!(
            "¬ ({})",
            self.canonical_forall_proposition(source, position)?
        ))
    }

    pub(in crate::compile_to_lean) fn canonical_forall_proposition(
        &self,
        source: &NotForallFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let mut bindings = HashMap::new();
        let mut parameters = Vec::new();
        for group in &source.typed_parameters.groups {
            for parameter in &group.params {
                let name = format!("_value_i{}", parameter.id.value());
                let denotation = format!("(Litex.denote {name})");
                let member = match &group.param_type {
                    ParamType::Obj(carrier) => format!(
                        "M.mem {denotation} {}",
                        self.compile_function_raw_expression_bound(carrier, position, &bindings)?
                    ),
                    ParamType::Set(_) => format!("M.isSet {denotation}"),
                    _ => return Err(LeanCompileError::unsupported("NotForall/ParameterKind")),
                };
                if bindings.insert(parameter.id, denotation).is_some() {
                    return Err(LeanCompileError::unsupported("NotForall/ParameterIdentity"));
                }
                parameters.push((name, member));
            }
        }
        if parameters.is_empty() {
            return Err(LeanCompileError::unsupported("NotForall/EmptyParameters"));
        }
        let mut meaning =
            self.not_forall_raw_conjunction(&source.then_facts, position, &bindings)?;
        for domain in source.dom_facts.iter().rev() {
            let domain = crate::instantiate::quantifier_free_fact_to_fact(domain.clone());
            meaning = format!(
                "({}) → ({meaning})",
                self.compile_function_raw_predicate(&domain, position, &bindings)?
            );
        }
        for (name, member) in parameters.into_iter().rev() {
            meaning = format!("∀ ({name} : Litex.Obj (M := M) M.Value), ({member}) → ({meaning})");
        }
        Ok(meaning)
    }

    pub(in crate::compile_to_lean) fn compile_not_forall_wd(
        &self,
        fact: &NotForallFact,
        proof: &crate::execute::execute_fact_stmt::verify_not_forall_fact::NotForallFactWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<(), LeanCompileError> {
        let scope = SourcePosition::new(Some(position), SourceOwner::NotForallWD(fact, proof), 0);
        let domains = fact
            .dom_facts
            .iter()
            .cloned()
            .map(crate::instantiate::quantifier_free_fact_to_fact)
            .collect::<Vec<_>>();
        self.compile_quantified_head(
            &fact.typed_parameters,
            &domains,
            &proof.detailed_ref().introduced_params,
            &proof.detailed_ref().assumed_dom_facts,
            &scope,
        )?;
        if fact.then_facts.len() != proof.detailed_ref().then.len() {
            return Err(LeanCompileError::unsupported(
                "NotForall/ThenFormationArity",
            ));
        }
        let head = fact.typed_parameters.ordered_param_ids().len() + domains.len();
        for (index, (clause, wd)) in fact
            .then_facts
            .iter()
            .zip(&proof.detailed_ref().then)
            .enumerate()
        {
            let clause = crate::instantiate::quantifier_free_fact_to_fact(clause.clone());
            self.compile_fact_wd(
                wd,
                &clause,
                &SourcePosition {
                    before: head + index,
                    ..scope
                },
            )?;
        }
        Ok(())
    }

    fn not_forall_raw_conjunction(
        &self,
        clauses: &[QuantifierFreeFact],
        position: &SourcePosition<'_>,
        bindings: &HashMap<IdentifierId, String>,
    ) -> Result<String, LeanCompileError> {
        conjunction_proposition(
            clauses
                .iter()
                .map(|clause| {
                    self.compile_function_raw_predicate(
                        &crate::instantiate::quantifier_free_fact_to_fact(clause.clone()),
                        position,
                        bindings,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?,
        )
    }

    pub(in crate::compile_to_lean) fn compile_not_forall_result(
        &self,
        result: &VerifyNotForallFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let VerifyNotForallFactResult::Success(proof) = result else {
            return Err(LeanCompileError::unsupported("NotForall/Failed"));
        };
        let child = checked_counterexample(proof)?;
        let fact = child.fact.plain();
        let counterexample = self.compile_verify(&proof.prove_derived_exist, position)?;
        let mut names = Vec::new();
        let mut arguments = Vec::new();
        let mut bindings = HashMap::new();
        for (parameter, store) in fact
            .typed_parameters
            .groups
            .iter()
            .flat_map(|group| &group.params)
            .zip(
                &child
                    .well_defined_proof
                    .detailed_ref()
                    .introduced_params
                    .defined_params
                    .store_and_infer_results,
            )
        {
            let name = format!("_value_i{}", parameter.id.value());
            bindings.insert(parameter.id, format!("(Litex.denote {name})"));
            names.push(name.clone());
            arguments.push(name);
            let member = format!("h_{}", store.primary_fact_id().value());
            names.push(member.clone());
            arguments.push(member);
        }
        let body_names: Vec<_> = fact
            .facts
            .iter()
            .map(|clause| {
                format!(
                    "h_{}",
                    crate::instantiate::quantifier_free_fact_to_fact(clause.clone())
                        .fact_id()
                        .value()
                )
            })
            .collect();
        names.extend(body_names.iter().cloned());
        arguments.extend(body_names[..proof.fact.dom_facts.len()].iter().cloned());
        let positive =
            self.not_forall_raw_conjunction(&proof.fact.then_facts, position, &bindings)?;
        let negative = self.not_forall_raw_conjunction(
            &fact.facts[proof.fact.dom_facts.len()..],
            position,
            &bindings,
        )?;
        let negative_names = &body_names[proof.fact.dom_facts.len()..];
        let evidence = if negative_names.len() == 1 {
            negative_names[0].clone()
        } else {
            format!("⟨{}⟩", negative_names.join(", "))
        };
        let term = format!("(by\n  classical\n  intro _universal\n  have _counterexample : {} := {}\n  rcases _counterexample with ⟨{}⟩\n  have _positive : {positive} := _universal {}\n  have _negative : {negative} := {evidence}\n  have _refute : ¬ ({positive}) := by\n    simpa only [{NEGATION_LAWS}] using _negative\n  exact _refute _positive)", counterexample.0, counterexample.1, names.join(", "), arguments.join(" "));
        Ok((self.not_forall_proposition(&proof.fact, position)?, term))
    }

    pub(in crate::compile_to_lean) fn compile_not_forall_inference(
        &self,
        store: &StoreFactAndInferResult,
        source: &NotForallFact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let Some(InferResult::NotForall(infer)) = &store.infer else {
            return Err(LeanCompileError::unsupported("NotForall/InferenceCapture"));
        };
        let StoreFactResult::ExistShapedFact(stored) = &infer.derived_exist.store else {
            return Err(LeanCompileError::unsupported("NotForall/InferenceFamily"));
        };
        validate_counterexample(source, &stored.fact)?;
        let mut cursor = Some(position);
        let mut original = None;
        while let Some(current) = cursor {
            if let SourceOwner::Statement(ExecStmtResult::Fact(ExecFactStmtResult::Success(
                statement,
            ))) = current.owner
            {
                if let VerifyFactResult::NotForall(result) = &statement.verify_result {
                    if let VerifyNotForallFactResult::Success(proof) = result.as_ref() {
                        if &proof.fact == source {
                            original = Some(proof);
                            break;
                        }
                    }
                }
            }
            cursor = current.parent;
        }
        let inferred = crate::ast::fact::exist_shaped_fact_to_fact(&stored.fact);
        self.validate_store(&infer.derived_exist.store, &inferred)?;
        let raw =
            self.compile_exist_raw_predicate(stored.fact.plain(), position, &HashMap::new())?;
        let proposition = if let Some(original) = original {
            let child = checked_counterexample(original)?;
            self.compile_exist_formation(child.fact.plain(), &child.well_defined_proof, position)?
        } else {
            // Assumptions have NotForall WD, not a fabricated existential
            // verification. The exact De Morgan store has this raw meaning.
            raw.clone()
        };
        let term = format!("(by\n  classical\n  have _counterexample : {raw} := by\n    simpa only [{NEGATION_LAWS}] using {}\n  exact _counterexample)", compiled.1);
        Ok(vec![self.emit_internal_fact(
            &inferred,
            &(proposition, term),
            position,
        )?])
    }
}
