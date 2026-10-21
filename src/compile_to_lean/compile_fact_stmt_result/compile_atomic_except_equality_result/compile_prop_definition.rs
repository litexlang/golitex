use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::{
    AtomicExceptEqualityFactSearchProofByDefinition, BuiltinPropDefinitionProof, UserDefinedPropDefinitionProof,
};
use crate::execute::ExecDefPropStmtSuccessResult;
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferNormalAtomicFactResult, InferAtomicFactResult, InferResult,
};
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_prop_definition(
        &self,
        goal: &AtomicFact,
        proof: &AtomicExceptEqualityFactSearchProofByDefinition,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match (goal, proof) {
            (
                AtomicFact::NormalAtomicFact(normal),
                AtomicExceptEqualityFactSearchProofByDefinition::UserDefinedProp(proof),
            ) => self.compile_user_prop_fold(normal, proof, position),
            (_, AtomicExceptEqualityFactSearchProofByDefinition::UserDefinedProp(_)) => {
                Err(LeanCompileError::new(
                    "Prop/FoldFamily",
                    "Concrete predicate folding has another source predicate family.",
                ))
            }
            (
                AtomicFact::SubsetFact(fact),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::Subset(proof),
                ),
            ) => self.compile_subset_definition(
                fact,
                &proof.requirement_facts,
                &proof.proof_of_requirement_facts,
                position,
            ),
            (_, AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(_)) => {
                Err(LeanCompileError::unsupported("Prop/BuiltinDefinition"))
            }
        }
    }

    fn compile_user_prop_fold(
        &self,
        normal: &NormalAtomicFact,
        proof: &UserDefinedPropDefinitionProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (declaration, _, _) = position.visible_prop(&normal.predicate)?;
        let substitution = self.prop_argument_substitution(declaration, normal)?;
        let parameters = declaration
            .statement
            .typed_parameters
            .groups
            .iter()
            .flat_map(|group| {
                group
                    .params
                    .iter()
                    .map(|parameter| (parameter, &group.param_type))
            })
            .collect::<Vec<_>>();
        let expected_count = parameters.len() + declaration.statement.iff_facts.len();
        if declaration.statement.iff_facts.is_empty()
            || proof.requirement_facts.len() != expected_count
            || proof.proof_of_requirement_facts.len() != expected_count
        {
            return Err(LeanCompileError::new(
                "Prop/FoldArity",
                "The selected definition proof omits or adds an ordered domain/body requirement.",
            ));
        }
        let mut witnesses = Vec::new();
        for (index, (requirement, checked)) in proof
            .requirement_facts
            .iter()
            .zip(&proof.proof_of_requirement_facts)
            .enumerate()
        {
            if index < parameters.len() {
                let (_, param_type) = parameters[index];
                let set = match param_type {
                    ParamType::Obj(set) => set,
                    _ => return Err(LeanCompileError::unsupported("Prop/FoldParameterKind")),
                };
                match requirement {
                    Fact::AtomicFact(AtomicFact::InFact(member))
                        if member.element.ir() == normal.body[index].ir()
                            && instantiated_object_matches(set, &member.set, &substitution) => {}
                    _ => {
                        return Err(LeanCompileError::new(
                            "Prop/FoldDomain",
                            "A selected definition requirement proves another argument or carrier.",
                        ))
                    }
                }
            } else if !instantiated_fact_matches(
                &declaration.statement.iff_facts[index - parameters.len()],
                requirement,
                &substitution,
            ) {
                return Err(LeanCompileError::new("Prop/FoldBody", "A selected definition requirement differs from its instantiated defining clause."));
            }
            if source_subject(checked)? != *requirement {
                return Err(LeanCompileError::new("Prop/FoldRequirementSubject", "A definition requirement and its actual proof have different source subjects or IDs."));
            }
            let prior = SourcePosition {
                parent: Some(position),
                owner: SourceOwner::PropRequirements(proof),
                before: index,
            };
            witnesses.push(self.compile_verify(checked, &prior)?.1);
        }
        let mut proof = witnesses
            .pop()
            .expect("validated nonempty definition requirements");
        for witness in witnesses.into_iter().rev() {
            proof = format!("(Exists.intro {witness} {proof})");
        }
        Ok(proof)
    }

    pub(in crate::compile_to_lean) fn compile_normal_atomic_proposition(
        &self,
        normal: &NormalAtomicFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (declaration, declaration_position, index) =
            position.visible_prop(&normal.predicate)?;
        self.prop_argument_substitution(declaration, normal)?;
        let mut arguments = Vec::new();
        for object in &normal.body {
            arguments.push(self.compile_object_reference(object, position)?);
        }
        let predicate =
            self.context_application(&format!("prop_{}", index + 1), &declaration_position);
        Ok(if arguments.is_empty() {
            predicate
        } else {
            format!("({predicate} {})", arguments.join(" "))
        })
    }

    pub(in crate::compile_to_lean) fn validate_prop_predicate_signature(
        &self,
        signature: &PredicateSignatureWellDefinedProof,
        fact: &AtomicFact,
        position: &SourcePosition<'_>,
    ) -> Result<(), LeanCompileError> {
        let negative_view;
        let (normal, predicate, arity) = match (fact, signature) {
            (
                AtomicFact::NormalAtomicFact(normal),
                PredicateSignatureWellDefinedProof::Prop { predicate, arity },
            ) => (normal, predicate, arity),
            (
                AtomicFact::NotNormalAtomicFact(normal),
                PredicateSignatureWellDefinedProof::Prop { predicate, arity },
            ) => {
                negative_view = NormalAtomicFact {
                    fact_id: normal.fact_id,
                    predicate: normal.predicate.clone(),
                    body: normal.body.clone(),
                    line_file: normal.line_file.clone(),
                };
                (&negative_view, predicate, arity)
            }
            _ => {
                return Err(LeanCompileError::new(
                    "Prop/SignatureFamily",
                    "The concrete predicate signature has another source family.",
                ))
            }
        };
        if predicate != &normal.predicate || *arity != normal.body.len() {
            return Err(LeanCompileError::new(
                "Prop/Signature",
                "The recorded predicate identity or arity differs from its occurrence.",
            ));
        }
        let (declaration, _, _) = position.visible_prop(predicate)?;
        self.prop_argument_substitution(declaration, normal)?;
        Ok(())
    }

    pub(in crate::compile_to_lean) fn prop_argument_substitution(
        &self,
        declaration: &ExecDefPropStmtSuccessResult,
        normal: &NormalAtomicFact,
    ) -> Result<HashMap<IdentifierId, Obj>, LeanCompileError> {
        if !matches!(&normal.predicate, AtomicName::Plain { name } if name == &declaration.statement.name)
        {
            return Err(LeanCompileError::new(
                "Prop/Identity",
                "The predicate occurrence does not name this prior concrete declaration.",
            ));
        }
        let parameters = declaration
            .statement
            .typed_parameters
            .groups
            .iter()
            .flat_map(|group| &group.params)
            .collect::<Vec<_>>();
        if parameters.len() != normal.body.len() {
            return Err(LeanCompileError::new(
                "Prop/Arguments",
                "The concrete predicate has another argument arity.",
            ));
        }
        let mut substitution = HashMap::new();
        for (parameter, argument) in parameters.iter().zip(&normal.body) {
            if substitution
                .insert(parameter.id, argument.clone())
                .is_some()
            {
                return Err(LeanCompileError::new(
                    "Prop/ParameterIdentity",
                    "The concrete declaration repeats a parameter identity.",
                ));
            }
        }
        Ok(substitution)
    }

    pub(in crate::compile_to_lean) fn compile_prop_inferences(
        &self,
        store: &StoreFactAndInferResult,
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        if !matches!(seed, Fact::AtomicFact(AtomicFact::NormalAtomicFact(_))) {
            return Ok(Vec::new());
        }
        self.validate_store(&store.store, seed)?;
        let rules = match &store.infer {
            Some(InferResult::AtomicFact(InferAtomicFactResult::NormalAtomicFact(rules))) => rules,
            _ => {
                return Err(LeanCompileError::new(
                    "Prop/InferFamily",
                    "The stored predicate has another inference family.",
                ))
            }
        };
        let scope = SourcePosition {
            parent: Some(position),
            owner: SourceOwner::PropInference(store),
            before: 0,
        };
        self.compile_prop_inference_rules(rules, seed, compiled, &scope)
    }

    pub(in crate::compile_to_lean) fn compile_prop_inference_rules(
        &self,
        rules: &[InferNormalAtomicFactResult],
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let normal = match seed {
            Fact::AtomicFact(AtomicFact::NormalAtomicFact(normal)) => normal,
            _ => return Ok(Vec::new()),
        };
        let (declaration, _, _) = position.visible_prop(&normal.predicate)?;
        let substitution = self.prop_argument_substitution(declaration, normal)?;
        let parameters = declaration
            .statement
            .typed_parameters
            .groups
            .iter()
            .flat_map(|group| {
                group
                    .params
                    .iter()
                    .map(|parameter| (parameter, &group.param_type))
            })
            .collect::<Vec<_>>();
        let witness_ids = declaration
            .defined_params
            .store_and_infer_results
            .iter()
            .map(|stored| stored.primary_fact_id())
            .chain(declaration.statement.iff_facts.iter().map(Fact::fact_id))
            .collect::<Vec<_>>();
        let mut declarations = Vec::new();
        let mut seen_members = false;
        let mut seen_body = false;
        let mut completed = 0;
        for rule in rules {
            let (derived, body) = match rule {
                InferNormalAtomicFactResult::ParamTypes(proof) => {
                    if seen_members || seen_body || proof.derived.len() != parameters.len() {
                        return Err(LeanCompileError::new("Prop/InferDomainOrder", "Predicate domain projections have another original arity or stage order."));
                    }
                    seen_members = true;
                    (&proof.derived, false)
                }
                InferNormalAtomicFactResult::ExpandDefinition(proof) => {
                    if seen_body
                        || (!parameters.is_empty() && !seen_members)
                        || proof.derived.len() != declaration.statement.iff_facts.len()
                    {
                        return Err(LeanCompileError::new("Prop/InferBodyOrder", "Predicate body projections have another original arity or stage order."));
                    }
                    seen_body = true;
                    (&proof.derived, true)
                }
            };
            for (index, derived) in derived.iter().enumerate() {
                let fact = match &derived.store {
                    StoreFactResult::AtomicFact(fact) => Fact::AtomicFact(fact.fact.clone()),
                    StoreFactResult::AndFact(fact) => Fact::AndFact(fact.fact.clone()),
                    StoreFactResult::ChainFact(fact) => Fact::ChainFact(fact.fact.clone()),
                    StoreFactResult::ExistShapedFact(stored) => match &stored.fact {
                        ExistShapedFact::Exist(fact) => Fact::ExistFact(fact.clone()),
                        _ => return Err(LeanCompileError::unsupported("Prop/InferExistFamily")),
                    },
                    _ => return Err(LeanCompileError::unsupported("Prop/InferCompoundClause")),
                };
                let witness_index = if body {
                    parameters.len() + index
                } else {
                    index
                };
                if body {
                    if !instantiated_fact_matches(
                        &declaration.statement.iff_facts[index],
                        &fact,
                        &substitution,
                    ) {
                        return Err(LeanCompileError::new("Prop/InferBodySubject", "An inferred predicate body differs from its exact instantiated defining clause."));
                    }
                } else {
                    let set = match parameters[index].1 {
                        ParamType::Obj(set) => set,
                        _ => return Err(LeanCompileError::unsupported("Prop/InferParameterKind")),
                    };
                    match &fact {
                        Fact::AtomicFact(AtomicFact::InFact(member))
                            if member.element.ir() == normal.body[index].ir()
                                && instantiated_object_matches(set, &member.set, &substitution) => {}
                        _ => return Err(LeanCompileError::new("Prop/InferDomainSubject", "An inferred predicate domain differs from its actual argument or carrier.")),
                    }
                }
                let prior = SourcePosition {
                    before: completed,
                    ..*position
                };
                if self.resolve_fact(derived.store.primary_fact_id(), &prior)? != fact {
                    return Err(LeanCompileError::new(
                        "Prop/InferIdentity",
                        "The captured derived store differs from its exact source fact ID.",
                    ));
                }
                self.validate_store(&derived.store, &fact)?;
                if position.is_local() && matches!(fact, Fact::AtomicFact(_) | Fact::ExistFact(_)) {
                    // The checked predicate already determines this projection's
                    // type, including constructors certified in its declaration.
                    // Do not demand a second, instantiated WD run just to print it.
                    let mut projection = format!("(show {} from {})", compiled.0, compiled.1);
                    for _ in 0..witness_index {
                        projection = format!("(Classical.choose_spec {projection})");
                    }
                    if witness_index + 1 < witness_ids.len() {
                        projection = format!("(Classical.choose {projection})");
                    }
                    declarations.push(format!(
                        "have h_{} :=\n  {}",
                        fact.fact_id().value(),
                        projection.replace('\n', "\n  ")
                    ));
                    completed += 1;
                    continue;
                }
                let formed = SourcePosition {
                    parent: Some(&prior),
                    owner: SourceOwner::InferredStore(&derived.store),
                    before: usize::MAX,
                };
                let names = witness_ids
                    .iter()
                    .map(|id| format!("h_{}", id.value()))
                    .collect::<Vec<_>>();
                let proof = if names.len() == 1 {
                    compiled.1.clone()
                } else {
                    format!(
                        "(by rcases {} with ⟨{}⟩; exact {})",
                        compiled.1,
                        names.join(", "),
                        names[witness_index]
                    )
                };
                let proposition = if matches!(fact, Fact::ExistFact(_)) {
                    self.compile_prop_clause_instance(normal, index, &compiled.1, &formed)?
                } else {
                    self.fact_proposition(&fact, &formed)?
                };
                let member = (proposition, proof);
                declarations.push(self.emit_internal_fact(&fact, &member, position)?);
                declarations.extend(self.compile_stored_projections(
                    &derived.store,
                    &fact,
                    &member,
                    &formed,
                )?);
                completed += 1;
            }
        }
        Ok(declarations)
    }
}
