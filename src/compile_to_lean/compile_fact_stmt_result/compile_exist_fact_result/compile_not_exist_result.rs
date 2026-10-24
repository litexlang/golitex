use crate::compile_to_lean::compile_by_stmt_result::compile_classified_negation::quantifier_free_terms;
use crate::compile_to_lean::helper::{conjunction_proposition, instantiated_fact_matches, instantiated_object_matches};
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::plain_exist_facts_alpha_equal;
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::{ExistShapedFactSearchedProof, VerifyNotExistFactResult};
use crate::prelude::*;
use crate::store_fact_and_infer::{InferNotExistFactResult, InferResult};
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_verify_not_exist_result(
        &self,
        result: &VerifyNotExistFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let VerifyNotExistFactResult::Success(proof) = result else {
            return Err(LeanCompileError::unsupported("NotExist/Failed"));
        };
        let ExistShapedFact::NotExist(fact) = &proof.fact else {
            return Err(LeanCompileError::unsupported("NotExist/Family"));
        };
        let proposition = format!(
            "¬ ({})",
            self.compile_exist_formation(fact, &proof.well_defined_proof, position)?
        );
        if let ExistShapedFactSearchedProof::ByKnownForallFact(known) = &proof.searched_proof {
            let evidence = self.compile_exist_known_forall(
                &proof.fact,
                &proof.well_defined_proof,
                known,
                position,
            )?;
            return Ok((proposition, evidence));
        }
        let ExistShapedFactSearchedProof::ByKnownExistShapedFact(known) = &proof.searched_proof
        else {
            return Err(LeanCompileError::unsupported("NotExist/ProofRoute"));
        };
        let registered = self.cited_fact_reference(known.cite_fact_id, position)?;
        let Fact::NotExistFact(source) = registered.0 else {
            return Err(LeanCompileError::unsupported("NotExist/CitationFamily"));
        };
        if source.fact_id != known.cite_fact_id || !plain_exist_facts_alpha_equal(source, fact) {
            return Err(LeanCompileError::unsupported("NotExist/CitationSubject"));
        }
        Ok((proposition, registered.1))
    }

    /// The source inference records a renamed forall, but performs no second
    /// WD verification. Prove that exact logical consequence from the negative
    /// existential, using denotations of arbitrary host objects as witnesses.
    pub(in crate::compile_to_lean) fn compile_not_exist_inference(
        &self,
        store: &StoreFactAndInferResult,
        source: &PlainExistFact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let Some(InferResult::NotExistFact(infer)) = &store.infer else {
            return Err(LeanCompileError::unsupported("NotExist/InferenceCapture"));
        };
        let expected = negated_atoms(source)?;
        let InferNotExistFactResult::DemorganForall(infer) = infer else {
            if expected.is_some() {
                return Err(LeanCompileError::unsupported("NotExist/MissingInference"));
            }
            return Ok(Vec::new());
        };
        let expected =
            expected.ok_or_else(|| LeanCompileError::unsupported("NotExist/InferenceDomain"))?;
        let StoreFactResult::ForallFact(stored) = &infer.derived.store else {
            return Err(LeanCompileError::unsupported("NotExist/InferenceFamily"));
        };
        let target = &stored.fact;
        if !target.dom_facts.is_empty()
            || target.then_facts.len() != 1
            || target.typed_parameters.groups.len() != source.typed_parameters.groups.len()
        {
            return Err(LeanCompileError::unsupported("NotExist/InferenceShape"));
        }
        let mut substitution = HashMap::new();
        let mut bindings = HashMap::new();
        let mut old_bindings = HashMap::new();
        let mut binders = Vec::new();
        let mut introductions = Vec::new();
        let mut witnesses = Vec::new();
        let mut fresh = std::collections::HashSet::new();
        for (old, new) in source
            .typed_parameters
            .groups
            .iter()
            .zip(&target.typed_parameters.groups)
        {
            if old.params.len() != new.params.len()
                || !match (&old.param_type, &new.param_type) {
                    (ParamType::Obj(a), ParamType::Obj(b)) => {
                        instantiated_object_matches(a, b, &substitution)
                    }
                    (ParamType::Set(_), ParamType::Set(_)) => true,
                    _ => false,
                }
            {
                return Err(LeanCompileError::unsupported("NotExist/InferenceCarrier"));
            }
            for (old, parameter) in old.params.iter().zip(&new.params) {
                if !fresh.insert(parameter.id)
                    || source
                        .typed_parameters
                        .ordered_param_ids()
                        .contains(&parameter.id)
                {
                    return Err(LeanCompileError::unsupported("NotExist/InferenceIdentity"));
                }
                let id = parameter.id.value();
                let name = format!("_value_i{id}");
                let denotation = format!("(Litex.denote {name})");
                let member = match &new.param_type {
                    ParamType::Obj(carrier) => format!(
                        "M.mem {denotation} {}",
                        self.compile_function_raw_expression_bound(carrier, position, &bindings)?
                    ),
                    ParamType::Set(_) => format!("M.isSet {denotation}"),
                    _ => {
                        return Err(LeanCompileError::unsupported(
                            "NotExist/InferenceParameterKind",
                        ))
                    }
                };
                binders.push(format!("{{_Host_i{id} : Type _}} [_rep_i{id} : Litex.Representation M _Host_i{id}] ({name} : Litex.Obj (M := M) _Host_i{id})"));
                binders.push(format!("(_membership_i{id} : {member})"));
                introductions.extend([
                    format!("_Host_i{id}"),
                    format!("_rep_i{id}"),
                    name.clone(),
                    format!("_membership_i{id}"),
                ]);
                witnesses.extend([
                    format!("Litex.semanticObject {denotation} (Litex.isSet {name})"),
                    format!("_membership_i{id}"),
                ]);
                substitution.insert(
                    old.id,
                    Obj::Identifier(IdentifierObj::from_bound_name(parameter)),
                );
                old_bindings.insert(old.id, denotation.clone());
                bindings.insert(parameter.id, denotation);
            }
        }
        let conclusion: Fact = target.then_facts[0].clone().into();
        let terms = quantifier_free_terms(&conclusion)?;
        if terms.len() != expected.len()
            || terms.iter().zip(&expected).any(|(term, old)| {
                term.len() != 1
                    || !instantiated_fact_matches(
                        &Fact::AtomicFact(old.clone()),
                        &Fact::AtomicFact(term[0].clone()),
                        &substitution,
                    )
            })
        {
            return Err(LeanCompileError::unsupported("NotExist/InferenceNegation"));
        }
        let fact = Fact::ForallFact(target.clone());
        self.validate_store(&infer.derived.store, &fact)?;
        let conclusion = self.compile_function_raw_predicate(&conclusion, position, &bindings)?;
        let body = conjunction_proposition(
            source
                .facts
                .iter()
                .map(|clause| {
                    self.compile_function_raw_predicate(
                        &crate::instantiate::quantifier_free_fact_to_fact(clause.clone()),
                        position,
                        &old_bindings,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?,
        )?;
        let names: Vec<_> = source
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
        let raw = self.compile_exist_raw_predicate(source, position, &HashMap::new())?;
        let split = if names.len() == 1 {
            format!("have {} := _candidate", names[0])
        } else {
            format!("rcases _candidate with ⟨{}⟩", names.join(", "))
        };
        witnesses.extend(names);
        let proof = format!("(by\n  classical\n  intro {}\n  have _excluded : ¬ ({raw}) := {}\n  have _no_body : ¬ ({body}) := by\n    intro _candidate\n    {split}\n    apply _excluded\n    exact ⟨{}⟩\n  simpa only [not_and_or, not_or, not_not, and_assoc, or_assoc] using _no_body)", introductions.join(" "),compiled.1,witnesses.join(", "));
        let proposition = format!("∀ {}, {conclusion}", binders.join(" "));
        Ok(vec![self.emit_internal_fact(
            &fact,
            &(proposition, proof),
            position,
        )?])
    }
}

fn negated_atoms(source: &PlainExistFact) -> Result<Option<Vec<AtomicFact>>, LeanCompileError> {
    if source.typed_parameters.ordered_param_ids().is_empty() || source.facts.is_empty() {
        return Ok(None);
    }
    let mut atoms = Vec::new();
    for clause in &source.facts {
        if matches!(clause, QuantifierFreeFact::OrFact(_)) {
            return Ok(None);
        }
        let clauses = quantifier_free_terms(&crate::instantiate::quantifier_free_fact_to_fact(
            clause.clone(),
        ))?;
        for clause in clauses {
            for atom in clause {
                let Some(negative) = crate::ast::fact::negate_atomic_fact(&atom, atom.fact_id())
                else {
                    return Ok(None);
                };
                atoms.push(negative);
            }
        }
    }
    Ok(Some(atoms))
}
