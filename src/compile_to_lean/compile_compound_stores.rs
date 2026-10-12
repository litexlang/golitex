use crate::compile_to_lean::compile_compound_fact::chain_edge;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferFactResult};

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_compound_stores(
        &self,
        store: &StoreFactAndInferResult,
        source: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        self.validate_store(&store.store, source)?;
        let mut declarations = Vec::new();
        let components = match (&store.store, &store.infer, source) {
            (
                StoreFactResult::AndFact(stored),
                Some(InferFactResult::AndFact(inferred)),
                Fact::AndFact(source),
            ) => {
                if stored.components.len() != source.facts.len()
                    || inferred.components.len() != source.facts.len()
                    || source.facts.is_empty()
                {
                    return Err(LeanCompileError::unsupported("And/StoreArity"));
                }
                let mut components = Vec::new();
                for (index, component) in stored.components.iter().enumerate() {
                    if component.component_index != index
                        || component.fact_id != component.fact.fact_id()
                        || component.fact != source.facts[index]
                    {
                        return Err(LeanCompileError::new(
                            "And/StoreSubject",
                            "A stored component has another source index, subject or identity.",
                        ));
                    }
                    components.push((component.fact_id, component.fact.clone()));
                }
                components
            }
            (
                StoreFactResult::ChainFact(stored),
                Some(InferFactResult::ChainFact(inferred)),
                Fact::ChainFact(source),
            ) => {
                if stored.adjacent.len() != source.prop_names.len()
                    || inferred.adjacent_infers.len() != source.prop_names.len()
                    || source.prop_names.is_empty()
                {
                    return Err(LeanCompileError::unsupported("Chain/StoreArity"));
                }
                let mut components = Vec::new();
                for (index, component) in stored.adjacent.iter().enumerate() {
                    if component.edge_index != index
                        || component.fact_id != component.fact.fact_id()
                        || component.fact != chain_edge(source, index, component.fact_id)?
                    {
                        return Err(LeanCompileError::new("Chain/StoreSubject", "A stored edge has another source index, subject, orientation or identity."));
                    }
                    components.push((component.fact_id, component.fact.clone()));
                }
                components
            }
            _ => return Err(LeanCompileError::unsupported("Compound/StoreFamily")),
        };
        for (index, (id, atomic)) in components.iter().enumerate() {
            let fact = Fact::AtomicFact(atomic.clone());
            if self.resolve_fact(*id, position)? != fact {
                return Err(LeanCompileError::new(
                    "Compound/StoreIdentity",
                    "The stored projection differs from the exact registered source FactId.",
                ));
            }
            let projection = (
                self.fact_proposition(&fact, position)?,
                conjunction_projection(&compiled.1, index, components.len()),
            );
            declarations.push(self.emit_internal_fact(&fact, &projection, position));
        }
        let group = SourcePosition::new(Some(position), SourceOwner::CompoundInference(store), 0);
        match &store.infer {
            Some(InferFactResult::AndFact(inferred)) => {
                for (index, infer) in inferred.components.iter().enumerate() {
                    let fact = Fact::AtomicFact(components[index].1.clone());
                    let prior = SourcePosition {
                        before: index,
                        ..group
                    };
                    let name = format!("h_{}", fact.fact_id().value());
                    let reference = if prior.is_local() {
                        name
                    } else {
                        self.context_application(&name, &prior)
                    };
                    let seed = (self.fact_proposition(&fact, &prior)?, reference);
                    let current = SourcePosition::new(
                        Some(&prior),
                        SourceOwner::AtomicInference(&fact, infer),
                        0,
                    );
                    declarations
                        .extend(self.compile_atomic_inferences(infer, &fact, &seed, &current)?);
                }
            }
            Some(InferFactResult::ChainFact(inferred)) => {
                for (index, captured) in inferred.adjacent_infers.iter().enumerate() {
                    let Fact::AtomicFact(atomic) = &captured.fact else {
                        return Err(LeanCompileError::unsupported("Chain/InferenceSeedFamily"));
                    };
                    if captured.edge_index != index
                        || *atomic != chain_edge(&inferred_chain(store)?, index, atomic.fact_id())?
                    {
                        return Err(LeanCompileError::new(
                            "Chain/InferenceSeed",
                            "An inference seed differs from its captured original adjacent edge.",
                        ));
                    }
                    let prior = SourcePosition {
                        before: index,
                        ..group
                    };
                    let name = format!("h_{}", components[index].0.value());
                    let reference = if prior.is_local() {
                        name
                    } else {
                        self.context_application(&name, &prior)
                    };
                    let seed = (self.fact_proposition(&captured.fact, &prior)?, reference);
                    declarations.push(self.emit_internal_fact(&captured.fact, &seed, &prior));
                    let name = format!("h_{}", captured.fact.fact_id().value());
                    let reference = if prior.is_local() {
                        name
                    } else {
                        self.context_application(&name, &prior)
                    };
                    let seed = (seed.0, reference);
                    let current = SourcePosition::new(
                        Some(&prior),
                        SourceOwner::AtomicInference(&captured.fact, &captured.infer),
                        0,
                    );
                    declarations.extend(self.compile_atomic_inferences(
                        &captured.infer,
                        &captured.fact,
                        &seed,
                        &current,
                    )?);
                }
                declarations.extend(self.compile_chain_closures(store, &group)?);
            }
            _ => unreachable!("the original compound family was checked"),
        }
        Ok(declarations)
    }

    // Index projections are part of storage, including for a derived And/Chain.
    pub(in crate::compile_to_lean) fn compile_stored_projections(
        &self,
        store: &StoreFactResult,
        source: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        if !matches!(source, Fact::AndFact(_) | Fact::ChainFact(_)) {
            return Ok(Vec::new());
        }
        self.validate_store(store, source)?;
        let components = store.atomic_components();
        let expected = match source {
            Fact::AndFact(fact) => fact.facts.len(),
            Fact::ChainFact(fact) => fact.prop_names.len(),
            _ => unreachable!(),
        };
        if components.len() != expected || expected == 0 {
            return Err(LeanCompileError::unsupported("Compound/StoreArity"));
        }
        let mut declarations = Vec::new();
        for (index, (id, atomic)) in components.iter().enumerate() {
            let expected_atomic = match source {
                Fact::AndFact(fact) => fact.facts[index].clone(),
                Fact::ChainFact(fact) => chain_edge(fact, index, *id)?,
                _ => unreachable!(),
            };
            if *atomic != expected_atomic || *id != atomic.fact_id() {
                return Err(LeanCompileError::unsupported("Compound/StoreSubject"));
            }
            let fact = Fact::AtomicFact(atomic.clone());
            if self.resolve_fact(*id, position)? != fact {
                return Err(LeanCompileError::unsupported("Compound/StoreIdentity"));
            }
            let projection = (
                self.fact_proposition(&fact, position)?,
                conjunction_projection(&compiled.1, index, components.len()),
            );
            declarations.push(self.emit_internal_fact(&fact, &projection, position));
        }
        Ok(declarations)
    }

    pub(in crate::compile_to_lean) fn compile_atomic_inferences(
        &self,
        infer: &InferAtomicFactResult,
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        match (infer, seed) {
            (
                InferAtomicFactResult::EqualFact(rules),
                Fact::AtomicFact(AtomicFact::EqualFact(source)),
            ) => self.compile_equality_inference_rules(rules, source, compiled, position),
            (InferAtomicFactResult::ExceptEquality(rules), Fact::AtomicFact(atomic))
                if !matches!(atomic, AtomicFact::EqualFact(_)) =>
            {
                let mut declarations =
                    self.compile_prop_inference_rules(rules, seed, compiled, position)?;
                declarations
                    .extend(self.compile_order_bound_inferences(rules, seed, compiled, position)?);
                if matches!(seed, Fact::AtomicFact(AtomicFact::InFact(member)) if member.set == Obj::StandardSet(StandardSet::N))
                {
                    for rule in rules {
                        if let crate::store_fact_and_infer::InferAtomicExceptEqualityResult::InFactSignedStandardSetSign(sign) = rule {
                            declarations.extend(self.compile_natural_sign_inference(sign, seed, compiled, position)?);
                        }
                    }
                }
                Ok(declarations)
            }
            _ => Err(LeanCompileError::unsupported(
                "Compound/AtomicInferenceFamily",
            )),
        }
    }
}

fn inferred_chain(store: &StoreFactAndInferResult) -> Result<ChainFact, LeanCompileError> {
    match &store.store {
        StoreFactResult::ChainFact(stored) => Ok(stored.fact.clone()),
        _ => Err(LeanCompileError::unsupported("Chain/StoreFamily")),
    }
}
