use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_verify_forall_result(
        &self,
        result: &VerifyForallFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        match result {
            VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(proof)) => {
                self.compile_forall(proof, position)
            }
            VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(proof)) => {
                self.compile_known_forall(proof, position)
            }
            VerifyForallFactResult::Success(VerifyForallFactProof::ByEmptyParameterDomain(
                proof,
            )) => self.compile_empty_parameter_domain(proof, position),
            VerifyForallFactResult::Failed(_) => Err(LeanCompileError::new(
                "Forall/Failed",
                "Failed verification is not proof evidence.",
            )),
        }
    }

    pub(in crate::compile_to_lean) fn compile_known_forall(
        &self,
        proof: &VerifyKnownForallFactProof,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let resolved = self.resolve_fact(proof.cite_fact_id, position)?;
        let source = match &resolved {
            Fact::ForallFact(source) if source.fact_id == proof.cite_fact_id => source,
            _ => {
                return Err(LeanCompileError::new(
                    "KnownForall/Citation",
                    "The whole-proposition citation is not this source forall identity.",
                ))
            }
        };
        let registered = self.cited_fact_reference(proof.cite_fact_id, position)?;
        if *registered.0 != resolved {
            return Err(LeanCompileError::new(
                "KnownForall/Producer",
                "The source forall differs from its active compiled producer.",
            ));
        }
        let source_parameters: Vec<_> = source
            .typed_parameters
            .groups
            .iter()
            .flat_map(|group| group.params.iter().map(|param| (param, &group.param_type)))
            .collect();
        let target_parameters: Vec<_> = proof
            .fact
            .typed_parameters
            .groups
            .iter()
            .flat_map(|group| group.params.iter().map(|param| (param, &group.param_type)))
            .collect();
        if source_parameters.len() != target_parameters.len()
            || proof.parameter_renamings.len() != source_parameters.len()
            || source.dom_facts.len() != proof.fact.dom_facts.len()
            || source.then_facts.len() != proof.fact.then_facts.len()
            || source.then_facts.is_empty()
        {
            return Err(LeanCompileError::new(
                "KnownForall/Arity",
                "Whole-forall reuse has different ordered parameter, premise or conclusion arity.",
            ));
        }
        let mut substitution = HashMap::new();
        let mut targets = std::collections::HashSet::new();
        for (((source, _), (target, _)), renaming) in source_parameters
            .iter()
            .zip(&target_parameters)
            .zip(&proof.parameter_renamings)
        {
            if renaming.source != source.id
                || renaming.target != target.id
                || substitution
                    .insert(
                        source.id,
                        Obj::Identifier(IdentifierObj::from_bound_name(target)),
                    )
                    .is_some()
                || !targets.insert(target.id)
            {
                return Err(LeanCompileError::new(
                    "KnownForall/Renaming",
                    "The recorded renaming must be the exact ordered bijection of declared binders.",
                ));
            }
        }
        for ((_, source), (_, target)) in source_parameters.iter().zip(&target_parameters) {
            match (source, target) {
                (ParamType::Set(_), ParamType::Set(_))
                | (ParamType::NonemptySet(_), ParamType::NonemptySet(_))
                | (ParamType::FiniteSet(_), ParamType::FiniteSet(_)) => {}
                (ParamType::Obj(source), ParamType::Obj(target))
                    if instantiated_object_matches(source, target, &substitution) => {}
                (ParamType::Obj(_), ParamType::Obj(_)) => {
                    return Err(LeanCompileError::new(
                        "KnownForall/Carrier",
                        "A parameter carrier changes under the recorded renaming.",
                    ))
                }
                _ => return Err(LeanCompileError::unsupported("KnownForall/ParameterKind")),
            }
        }
        for (source, target) in source.dom_facts.iter().zip(&proof.fact.dom_facts) {
            if !instantiated_fact_matches(source, target, &substitution) {
                return Err(LeanCompileError::new(
                    "KnownForall/Domain",
                    "A domain proposition changes under the recorded exact renaming.",
                ));
            }
        }
        for (source, target) in source.then_facts.iter().zip(&proof.fact.then_facts) {
            if !instantiated_fact_matches(
                &source.clone().into(),
                &target.clone().into(),
                &substitution,
            ) {
                return Err(LeanCompileError::new(
                    "KnownForall/Conclusion",
                    "A conclusion or free reference changes under the recorded exact renaming.",
                ));
            }
        }
        let source_position = SourcePosition {
            parent: Some(position),
            owner: SourceOwner::KnownForall(proof),
            before: 0,
        };
        let compiled = self.compile_known_forall_body(proof, &registered, &source_position);
        compiled
    }

    pub(in crate::compile_to_lean) fn compile_known_forall_body(
        &self,
        proof: &VerifyKnownForallFactProof,
        registered: &(&Fact, String),
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let (binders, introductions, definitions) = self.compile_forall_head(
            &proof.fact,
            &proof.well_defined.detailed_ref().introduced_params,
            &proof.well_defined.detailed_ref().assumed_dom_facts,
            position,
        )?;
        let formed = SourcePosition {
            before: proof
                .fact
                .typed_parameters
                .groups
                .iter()
                .map(|g| g.params.len())
                .sum::<usize>()
                + proof.fact.dom_facts.len(),
            ..*position
        };
        let position = &formed;
        if proof.well_defined.detailed_ref().then.len() != proof.fact.then_facts.len() {
            return Err(LeanCompileError::new(
                "KnownForall/ConclusionWD",
                "The recorded whole-proposition WD omits or adds a conclusion stage.",
            ));
        }
        let mut propositions = Vec::new();
        for (index, (source, wd)) in proof
            .fact
            .then_facts
            .iter()
            .zip(&proof.well_defined.detailed_ref().then)
            .enumerate()
        {
            let fact: Fact = source.clone().into();
            let then_position = SourcePosition {
                before: position.before + index,
                ..*position
            };
            self.compile_fact_wd(wd, &fact, &then_position)?;
            let formed = SourcePosition {
                parent: Some(&then_position),
                owner: SourceOwner::FactWD(wd),
                before: usize::MAX,
            };
            propositions.push(self.fact_proposition(&fact, &formed)?);
        }
        let mut arguments = Vec::new();
        let mut offset = 0;
        let ids = &proof
            .well_defined
            .detailed_ref()
            .introduced_params
            .defined_params
            .store_and_infer_results;
        for group in &proof.fact.typed_parameters.groups {
            for parameter in &group.params {
                let object = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
                let value = self.compile_object_reference(&object, position)?;
                arguments.push(format!(
                    "(Litex.semanticObject (Litex.denote {value}) (Litex.isSet {value}))"
                ));
                arguments.push(
                    self.cited_fact_reference(ids[offset].primary_fact_id(), position)?
                        .1
                        .clone(),
                );
                offset += 1;
            }
        }
        for domain in &proof.fact.dom_facts {
            let registered = self.cited_fact_reference(domain.fact_id(), position)?;
            if *registered.0 != *domain {
                return Err(LeanCompileError::new(
                    "KnownForall/DomainProducer",
                    "A domain hypothesis differs from the current scoped source requirement.",
                ));
            }
            arguments.push(registered.1.clone());
        }
        let application = if arguments.is_empty() {
            registered.1.clone()
        } else {
            format!("({} {})", registered.1, arguments.join(" "))
        };
        let mut conclusion = propositions.pop().expect("validated nonempty conclusions");
        while let Some(left) = propositions.pop() {
            conclusion = format!("(({left}) ∧ ({conclusion}))");
        }
        let conclusion = self.scope_proposition(conclusion, &definitions);
        let proposition = if binders.is_empty() {
            conclusion
        } else {
            format!("∀ {}, {conclusion}", binders.join(" "))
        };
        let introduction = if introductions.is_empty() {
            String::new()
        } else {
            format!("  intro {}\n", introductions.join(" "))
        };
        Ok((
            proposition,
            format!(
                "(by\n{introduction}{}  exact {application}\n)",
                if definitions.is_empty() {
                    String::new()
                } else {
                    format!("  {}\n", definitions.join("\n").replace('\n', "\n  "))
                }
            ),
        ))
    }

    pub(in crate::compile_to_lean) fn compile_forall(
        &self,
        proof: &VerifyForallFactSuccess,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let source_position = SourcePosition {
            parent: Some(position),
            owner: SourceOwner::Forall(proof),
            before: 0,
        };
        let compiled = self.compile_forall_body(proof, &source_position);
        compiled
    }

    pub(in crate::compile_to_lean) fn compile_forall_head(
        &self,
        fact: &ForallFact,
        introduced: &IntroduceTypedParametersResult,
        assumed: &[AssumeDomFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, Vec<String>, Vec<String>), LeanCompileError> {
        self.compile_quantified_head(
            &fact.typed_parameters,
            &fact.dom_facts,
            introduced,
            assumed,
            position,
        )
    }

    pub(in crate::compile_to_lean) fn compile_quantified_head(
        &self,
        parameters: &TypedParameterList,
        domains: &[Fact],
        introduced: &IntroduceTypedParametersResult,
        assumed: &[AssumeDomFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, Vec<String>, Vec<String>), LeanCompileError> {
        let groups = &parameters.groups;
        let parameters = groups
            .iter()
            .flat_map(|group| &group.params)
            .collect::<Vec<_>>();
        if parameters.iter().enumerate().any(|(index, parameter)| {
            parameters[..index]
                .iter()
                .any(|earlier| earlier.id == parameter.id)
        }) {
            return Err(LeanCompileError::new(
                "Parameters/Identity",
                "Duplicate source parameter identity.",
            ));
        }
        if introduced.param_type_well_defined.len() != groups.len() {
            return Err(LeanCompileError::new(
                "Forall/Parameters",
                "Parameter evidence does not match the supported plain groups.",
            ));
        }
        let expected_count: usize = groups.iter().map(|group| group.params.len()).sum();
        self.validate_parameter_store_capture(&introduced.defined_params)?;
        let stores = &introduced.defined_params.store_and_infer_results;
        if stores.len() != expected_count {
            return Err(LeanCompileError::new(
                "Forall/ParameterStores",
                "Parameter introduction needs its actual ordered stores.",
            ));
        }
        let mut binders = Vec::new();
        let mut introductions = Vec::new();
        let mut definitions = Vec::new();
        let mut offset = 0;
        for (group, wd) in groups.iter().zip(&introduced.param_type_well_defined) {
            let group_position = SourcePosition {
                before: offset,
                ..*position
            };
            let position = &group_position;
            if matches!(
                &group.param_type,
                ParamType::Set(_) | ParamType::NonemptySet(_) | ParamType::FiniteSet(_)
            ) {
                if !matches!(
                    (&group.param_type, wd),
                    (ParamType::Set(_), ParamTypeWellDefinedProof::Set)
                        | (
                            ParamType::FiniteSet(_),
                            ParamTypeWellDefinedProof::FiniteSet
                        )
                        | (
                            ParamType::NonemptySet(_),
                            ParamTypeWellDefinedProof::NonemptySet
                        )
                ) {
                    return Err(LeanCompileError::new(
                        "Forall/SetKindWD",
                        "A set-kind binder requires evidence for its exact declared kind.",
                    ));
                }
                for parameter in &group.params {
                    let introduced = SourcePosition {
                        before: offset + 1,
                        ..*position
                    };
                    let (new_binders, new_arguments) = self.introduce_set_kind_parameter(
                        parameter,
                        &group.param_type,
                        &stores[offset],
                        &introduced,
                    )?;
                    binders.extend(new_binders);
                    introductions.extend(new_arguments);
                    offset += 1;
                }
                continue;
            }
            let set = match &group.param_type {
                ParamType::Obj(set) => set,
                ParamType::Set(_) | ParamType::NonemptySet(_) | ParamType::FiniteSet(_) => {
                    return Err(LeanCompileError::unsupported("Forall/ParameterKind"))
                }
            };
            match wd {
                ParamTypeWellDefinedProof::Obj(wd) => {
                    ensure_object(set, wd)?;
                    self.compile_wd(wd, position)?;
                }
                ParamTypeWellDefinedProof::Set
                | ParamTypeWellDefinedProof::NonemptySet
                | ParamTypeWellDefinedProof::FiniteSet => {
                    return Err(LeanCompileError::unsupported("Forall/ParameterKindWD"))
                }
            }
            for parameter in &group.params {
                let parameter_position = SourcePosition {
                    before: offset + 1,
                    ..*position
                };
                let carrier_position = SourcePosition {
                    parent: Some(&parameter_position),
                    owner: SourceOwner::ParamTypeWD(wd),
                    before: 1,
                };
                let (new_binders, new_arguments) = self.introduce_member_parameter(
                    parameter,
                    set,
                    &stores[offset],
                    &carrier_position,
                )?;
                binders.extend(new_binders);
                introductions.extend(new_arguments);
                let fact =
                    self.resolve_fact(stores[offset].primary_fact_id(), &parameter_position)?;
                let member = (
                    self.fact_proposition(&fact, &carrier_position)?,
                    format!("h_{}", stores[offset].primary_fact_id().value()),
                );
                // Parameters and their inferences precede automatic opening.
                let unopened = SourcePosition::new(
                    Some(&carrier_position),
                    SourceOwner::StructLayers(
                        introduced
                            .auto_opened_struct_layers
                            .as_deref()
                            .unwrap_or(&[]),
                    ),
                    0,
                );
                definitions.extend(self.compile_parameter_inferences(
                    &stores[offset],
                    &fact,
                    &member,
                    &unopened,
                )?);
                offset += 1;
            }
        }
        let complete = SourcePosition {
            before: expected_count,
            ..*position
        };
        definitions.extend(self.compile_auto_struct_layers(
            groups,
            stores,
            introduced.auto_opened_struct_layers.as_deref(),
            &complete,
        )?);
        if assumed.len() != domains.len() {
            return Err(LeanCompileError::new(
                "Forall/Domain",
                "Domain evidence has the wrong arity.",
            ));
        }
        for (index, (fact, assumed)) in domains.iter().zip(assumed).enumerate() {
            let domain_position = SourcePosition {
                before: expected_count + index,
                ..*position
            };
            let position = &domain_position;
            // A quantified hypothesis is a proposition over semantic objects,
            // rather than one fixed host universe. Calls instantiate it using
            // the source argument's unchanged denotation.
            let proposition = match (fact, &assumed.well_defined) {
                (Fact::ForallFact(fact), FactWellDefinedProof::ForallFact(wd)) => {
                    self.compile_canonical_forall_formation(fact, wd, position)?
                }
                _ => self.compile_formed_fact_proposition(&assumed.well_defined, fact, position)?,
            };
            self.validate_store(&assumed.store_and_infer.store, fact)?;
            let hypothesis = format!("h_{}", fact.fact_id().value());
            // A premise's construction can use parameter/earlier-premise
            // inferences. Close its type before adding this premise's own
            // producers; declarations in the conclusion scope are too late.
            let closed = self.scope_proposition(proposition.clone(), &definitions);
            binders.push(format!("({hypothesis} : {closed})"));
            introductions.push(hypothesis.clone());
            let complete = SourcePosition {
                before: expected_count + index + 1,
                ..*position
            };
            definitions.extend(self.compile_stored_inferences(
                &assumed.store_and_infer,
                fact,
                &(proposition, hypothesis),
                &complete,
            )?);
        }
        Ok((binders, introductions, definitions))
    }

    pub(in crate::compile_to_lean) fn compile_forall_body(
        &self,
        proof: &VerifyForallFactSuccess,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let (binders, introductions, definitions) = self.compile_forall_head(
            &proof.fact,
            &proof.introduced_params,
            &proof.assumed_dom_facts,
            position,
        )?;
        if proof.proved_then_facts.len() != proof.fact.then_facts.len()
            || proof.proved_then_facts.is_empty()
        {
            return Err(LeanCompileError::new(
                "Forall/Then",
                "Conclusion evidence has the wrong arity.",
            ));
        }
        let mut conclusions = Vec::new();
        let mut definitions = definitions;
        let head_count = proof
            .fact
            .typed_parameters
            .groups
            .iter()
            .map(|g| g.params.len())
            .sum::<usize>()
            + proof.fact.dom_facts.len();
        for (index, (fact, proved)) in proof
            .fact
            .then_facts
            .iter()
            .zip(&proof.proved_then_facts)
            .enumerate()
        {
            let then_position = SourcePosition {
                before: head_count + index,
                ..*position
            };
            let position = &then_position;
            let expected = match fact {
                ExistOrAndChainAtomicFact::AtomicFact(atomic) => Fact::AtomicFact(atomic.clone()),
                ExistOrAndChainAtomicFact::AndFact(and) => Fact::AndFact(and.clone()),
                ExistOrAndChainAtomicFact::ChainFact(chain) => Fact::ChainFact(chain.clone()),
                ExistOrAndChainAtomicFact::OrFact(or) => Fact::OrFact(or.clone()),
                ExistOrAndChainAtomicFact::ExistFact(exist) => Fact::ExistFact(exist.clone()),
                ExistOrAndChainAtomicFact::NotExistFact(exist) => Fact::NotExistFact(exist.clone()),
                ExistOrAndChainAtomicFact::ExistUniqueFact(fact) => {
                    Fact::ExistUniqueFact(fact.clone())
                }
            };
            if source_subject(&proved.verify_result)? != expected {
                return Err(LeanCompileError::new(
                    "Forall/Then",
                    "Verified conclusion differs from the source conclusion.",
                ));
            }
            self.validate_store(&proved.store_and_infer.store, &expected)?;

            definitions.extend(self.compile_formed_subjects(
                &proved.verify_result,
                &proved.store_and_infer,
                position,
                true,
            )?);
            let formed = SourcePosition::new(
                Some(position),
                SourceOwner::FormedSubjects(&proved.verify_result, &proved.store_and_infer),
                0,
            );
            let compiled = self.compile_verify(&proved.verify_result, &formed)?;
            definitions.push(self.emit_internal_fact(&expected, &compiled, position)?);
            let complete = SourcePosition {
                before: head_count + index + 1,
                ..*position
            };
            definitions.extend(self.compile_stored_inferences(
                &proved.store_and_infer,
                &expected,
                &(
                    compiled.0.clone(),
                    format!("h_{}", expected.fact_id().value()),
                ),
                &complete,
            )?);
            conclusions.push((compiled.0, format!("h_{}", expected.fact_id().value())));
        }
        let mut conclusion = conclusions.pop().expect("nonempty conclusions");
        while let Some(left) = conclusions.pop() {
            conclusion.0 = format!("(({}) ∧ ({}))", left.0, conclusion.0);
            conclusion.1 = format!("(And.intro {} {})", left.1, conclusion.1);
        }
        let closed_proposition = self.scope_proposition(conclusion.0, &definitions);
        let proposition = if binders.is_empty() {
            closed_proposition
        } else {
            format!("∀ {}, {}", binders.join(" "), closed_proposition)
        };
        let intro = if introductions.is_empty() {
            String::new()
        } else {
            format!("  intro {}\n", introductions.join(" "))
        };
        Ok((
            proposition,
            format!(
                "(by\n{intro}{}  exact {}\n)",
                if definitions.is_empty() {
                    String::new()
                } else {
                    format!("  {}\n", definitions.join("\n").replace('\n', "\n  "))
                },
                conclusion.1
            ),
        ))
    }

    pub(in crate::compile_to_lean) fn compile_forall_wd(
        &self,
        fact: &ForallFact,
        proof: &ForallFactWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<(), LeanCompileError> {
        let scope = SourcePosition::new(Some(position), SourceOwner::ForallWD(fact, proof), 0);
        self.compile_forall_head(
            fact,
            &proof.detailed_ref().introduced_params,
            &proof.detailed_ref().assumed_dom_facts,
            &scope,
        )?;
        if proof.detailed_ref().then.len() != fact.then_facts.len() {
            return Err(LeanCompileError::unsupported("WD/ForallThenArity"));
        }
        let head = fact.typed_parameters.ordered_param_ids().len() + fact.dom_facts.len();
        for (index, (clause, wd)) in fact
            .then_facts
            .iter()
            .zip(&proof.detailed_ref().then)
            .enumerate()
        {
            self.compile_fact_wd(
                wd,
                &clause.clone().into(),
                &SourcePosition {
                    before: head + index,
                    ..scope
                },
            )?;
        }
        Ok(())
    }

    pub(in crate::compile_to_lean) fn compile_forall_formation(
        &self,
        fact: &ForallFact,
        proof: &ForallFactWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let source_position = SourcePosition {
            parent: Some(position),
            owner: SourceOwner::ForallWD(fact, proof),
            before: 0,
        };
        let compiled = self.compile_forall_wd_body(fact, proof, &source_position, false);
        compiled
    }

    pub(in crate::compile_to_lean) fn compile_canonical_forall_formation(
        &self,
        fact: &ForallFact,
        proof: &ForallFactWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let scope = SourcePosition::new(Some(position), SourceOwner::ForallWD(fact, proof), 0);
        self.compile_forall_wd_body(fact, proof, &scope, true)
    }

    fn compile_forall_wd_body(
        &self,
        fact: &ForallFact,
        proof: &ForallFactWellDefinedProof,
        position: &SourcePosition<'_>,
        canonical: bool,
    ) -> Result<String, LeanCompileError> {
        // Reuse the same binder/domain replay, but emit no declaration or
        // truth proof. In particular, then-WD never assumes a conclusion.
        let (binders, _, definitions) = if canonical {
            self.compile_canonical_forall_head(fact, proof, position)?
        } else {
            self.compile_forall_head(
                fact,
                &proof.detailed_ref().introduced_params,
                &proof.detailed_ref().assumed_dom_facts,
                position,
            )?
        };
        let formed = SourcePosition {
            before: fact
                .typed_parameters
                .groups
                .iter()
                .map(|g| g.params.len())
                .sum::<usize>()
                + fact.dom_facts.len(),
            ..*position
        };
        let position = &formed;
        if proof.detailed_ref().then.len() != fact.then_facts.len() {
            return Err(LeanCompileError::new(
                "WD/ForallThenArity",
                "Quantified conclusion WD has the wrong ordered stage arity.",
            ));
        }
        let mut conclusions = Vec::new();
        for (index, (fact, wd)) in fact
            .then_facts
            .iter()
            .zip(&proof.detailed_ref().then)
            .enumerate()
        {
            let fact: Fact = fact.clone().into();
            let prior = SourcePosition {
                before: position.before + index,
                ..*position
            };
            conclusions.push(self.compile_formed_fact_proposition(wd, &fact, &prior)?);
        }
        let conclusion =
            self.scope_proposition(conjunction_proposition(conclusions)?, &definitions);
        Ok(if binders.is_empty() {
            conclusion
        } else {
            format!("∀ {}, {conclusion}", binders.join(" "))
        })
    }

    // Endpoints have already been certified by the owning verify/argument stage.
    // Reuse the exact selected search route, never another proof of its target.
}
