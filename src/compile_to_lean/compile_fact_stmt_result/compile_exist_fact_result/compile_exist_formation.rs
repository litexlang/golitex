use crate::compile_to_lean::helper::ensure_object;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedFactWellDefinedProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    /// A source existential quantifies over semantic objects. Each original
    /// membership/guard proof is bound before a later constructor may consume it.
    pub(in crate::compile_to_lean) fn compile_exist_formation(
        &self,
        fact: &PlainExistFact,
        proof: &ExistShapedFactWellDefinedProof,
        parent: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let scope = SourcePosition::new(Some(parent), SourceOwner::ExistWD(fact, proof), 0);
        let groups = &fact.typed_parameters.groups;
        let count: usize = groups.iter().map(|group| group.params.len()).sum();
        let stores = &proof
            .detailed_ref()
            .introduced_params
            .defined_params
            .store_and_infer_results;
        if count == 0
            || stores.len() != count
            || proof
                .detailed_ref()
                .introduced_params
                .param_type_well_defined
                .len()
                != groups.len()
            || proof.detailed_ref().assumed_body_facts.len() != fact.facts.len()
        {
            return Err(LeanCompileError::new(
                "Exist/FormationStages",
                "Existential formation needs its ordered binders and every original body stage.",
            ));
        }
        self.validate_parameter_store_capture(
            &proof.detailed_ref().introduced_params.defined_params,
        )?;
        let mut ids = std::collections::HashSet::new();
        let mut parameters = Vec::new();
        let mut offset = 0;
        for (group, formation) in groups.iter().zip(
            &proof
                .detailed_ref()
                .introduced_params
                .param_type_well_defined,
        ) {
            let prior = SourcePosition {
                before: offset,
                ..scope
            };
            match (&group.param_type, formation) {
                (ParamType::Obj(carrier), ParamTypeWellDefinedProof::Obj(checked)) => {
                    ensure_object(carrier, checked)?;
                    self.compile_wd(checked, &prior)?;
                }
                (ParamType::Set(_), ParamTypeWellDefinedProof::Set) => {}
                _ => return Err(LeanCompileError::unsupported("Exist/ParameterKind")),
            }
            for parameter in &group.params {
                if !ids.insert(parameter.id) {
                    return Err(LeanCompileError::new(
                        "Exist/ParameterIdentity",
                        "Existential parameters repeat a source identity.",
                    ));
                }
                let introduced = SourcePosition {
                    before: offset + 1,
                    ..scope
                };
                let formed =
                    SourcePosition::new(Some(&introduced), SourceOwner::ParamTypeWD(formation), 1);
                let store = &stores[offset];
                let member = self.resolve_fact(store.primary_fact_id(), &introduced)?;
                let object = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
                let matching = match (&group.param_type, &member) {
                    (ParamType::Obj(carrier), Fact::AtomicFact(AtomicFact::InFact(member))) => {
                        member.element.ir() == object.ir() && member.set.ir() == carrier.ir()
                    }
                    (ParamType::Set(_), Fact::AtomicFact(AtomicFact::IsSetFact(member))) => {
                        member.set.ir() == object.ir()
                    }
                    _ => false,
                };
                if !matching {
                    return Err(LeanCompileError::new(
                        "Exist/ParameterSubject",
                        "The original membership names another binder or carrier.",
                    ));
                }
                self.validate_store(&store.store, &member)?;
                let compiled = (
                    self.fact_proposition(&member, &formed)?,
                    format!("h_{}", member.fact_id().value()),
                );
                let derived =
                    self.compile_parameter_inferences(store, &member, &compiled, &introduced)?;
                parameters.push((parameter.id, compiled, derived));
                offset += 1;
            }
        }
        let mut clauses = Vec::new();
        for (index, (source, captured)) in fact
            .facts
            .iter()
            .zip(&proof.detailed_ref().assumed_body_facts)
            .enumerate()
        {
            let source = crate::instantiate::quantifier_free_fact_to_fact(source.clone());
            let prior = SourcePosition {
                before: count + index,
                ..scope
            };
            self.compile_fact_wd(&captured.well_defined, &source, &prior)?;
            self.validate_store(&captured.store_and_infer.store, &source)?;
            let formed = SourcePosition::new(
                Some(&prior),
                SourceOwner::FactWD(&captured.well_defined),
                usize::MAX,
            );
            let compiled = (
                self.fact_proposition(&source, &formed)?,
                format!("h_{}", source.fact_id().value()),
            );
            let completed = SourcePosition {
                before: count + index + 1,
                ..scope
            };
            let derived = self.compile_stored_inferences(
                &captured.store_and_infer,
                &source,
                &compiled,
                &completed,
            )?;
            clauses.push((compiled, derived));
        }
        let mut meaning = match clauses.pop() {
            Some((last, _)) => last.0,
            None => "True".to_string(),
        };
        for ((clause, name), derived) in clauses.into_iter().rev() {
            meaning = format!(
                "∃ ({name} : {clause}), {}",
                self.scope_proposition(meaning, &derived)
            );
        }
        for (id, (member, name), derived) in parameters.into_iter().rev() {
            meaning = format!(
                "∃ (_value_i{} : Litex.Obj (M := M) M.Value), ∃ ({name} : {member}), {}",
                id.value(),
                self.scope_proposition(meaning, &derived),
            );
        }
        Ok(meaning)
    }

    pub(in crate::compile_to_lean) fn exist_proposition(
        &self,
        fact: &PlainExistFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let mut current = Some(position);
        while let Some(cursor) = current {
            match cursor.owner {
                SourceOwner::FactWD(FactWellDefinedProof::ExistFact(proof)) => {
                    return self.compile_exist_formation(fact, proof, position);
                }
                SourceOwner::ExistWD(source, proof) if source == fact => {
                    return self.compile_exist_formation(fact, proof, position);
                }
                SourceOwner::Verify(VerifyFactResult::ExistShapedFact(result)) => {
                    if let VerifyExistShapedFactResult::ExistUniqueFact(
                        VerifyExistUniqueFactResult::Success(proof),
                    ) = result.as_ref()
                    {
                        if proof.fact.plain() == fact {
                            return self.compile_exist_formation(
                                fact,
                                &proof.well_defined_proof,
                                position,
                            );
                        }
                    }
                    if let VerifyExistShapedFactResult::NotExistFact(
                        crate::execute::execute_fact_stmt::verify_exist_shaped_fact::VerifyNotExistFactResult::Success(proof),
                    ) = result.as_ref() {
                        if proof.fact.plain() == fact {
                            return self.compile_exist_formation(fact, &proof.well_defined_proof, position);
                        }
                    }
                    if let VerifyExistShapedFactResult::PlainExistFact(
                        VerifyPlainExistFactResult::Success(proof),
                    ) = result.as_ref()
                    {
                        if proof.fact.plain() == fact {
                            return self.compile_exist_formation(
                                fact,
                                &proof.well_defined_proof,
                                position,
                            );
                        }
                    }
                }
                _ => {}
            }
            current = cursor.parent;
        }
        Err(LeanCompileError::new(
            "Exist/FormationProducer",
            "An existential proposition needs its original ordered formation result.",
        ))
    }
}

impl LitexToLeanCompiler {
    /// The same canonical existential shape in the raw function/predicate
    /// interpretation. Source formation is checked by its owned result path.
    pub(in crate::compile_to_lean) fn compile_exist_raw_predicate(
        &self,
        fact: &PlainExistFact,
        position: &SourcePosition<'_>,
        bindings: &std::collections::HashMap<IdentifierId, String>,
    ) -> Result<String, LeanCompileError> {
        let mut local = bindings.clone();
        let mut parameters = Vec::new();
        for group in &fact.typed_parameters.groups {
            for parameter in &group.params {
                let name = format!("_value_i{}", parameter.id.value());
                let denotation = format!("(Litex.denote {name})");
                let member = match &group.param_type {
                    ParamType::Obj(carrier) => format!(
                        "M.mem {denotation} {}",
                        self.compile_function_raw_expression_bound(carrier, position, &local)?,
                    ),
                    ParamType::Set(_) => format!("M.isSet {denotation}"),
                    _ => return Err(LeanCompileError::unsupported("Exist/RawParameterKind")),
                };
                if local.insert(parameter.id, denotation).is_some() {
                    return Err(LeanCompileError::new(
                        "Exist/RawParameterIdentity",
                        "The existential binder collides with an enclosing source identity.",
                    ));
                }
                parameters.push((name, member));
            }
        }
        let mut clauses = Vec::new();
        for source in &fact.facts {
            let source = crate::instantiate::quantifier_free_fact_to_fact(source.clone());
            clauses.push((
                source.fact_id(),
                self.compile_function_raw_predicate(&source, position, &local)?,
            ));
        }
        let mut meaning = clauses
            .pop()
            .map(|(_, body)| body)
            .unwrap_or_else(|| "True".into());
        for (id, clause) in clauses.into_iter().rev() {
            meaning = format!("∃ (h_{} : {clause}), {meaning}", id.value());
        }
        for (name, member) in parameters.into_iter().rev() {
            meaning =
                format!("∃ ({name} : Litex.Obj (M := M) M.Value), ∃ (_ : {member}), {meaning}");
        }
        Ok(format!("({meaning})"))
    }
}
