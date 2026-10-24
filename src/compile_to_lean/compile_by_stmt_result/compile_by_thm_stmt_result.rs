use crate::ast::stmt::TheoremCall;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_by_thm_result(
        &self,
        result: &ExecByThmStmtResult,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        match result {
            ExecByThmStmtResult::Success(proof) => {
                let compiled = self.compile_by_theorem(proof, position)?;
                self.compile_completed_fact_statement(
                    &source_subject(&proof.selected_proof)?,
                    compiled,
                    &proof.stored,
                    position,
                    index,
                    local,
                )
            }
            ExecByThmStmtResult::Failed(_) => Err(LeanCompileError::new(
                "ByThm/Failed",
                "Failed invocation is not proof evidence.",
            )),
        }
    }

    pub(in crate::compile_to_lean) fn compile_by_theorem(
        &self,
        proof: &ExecByThmStmtSuccess,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let source_position = SourcePosition {
            parent: Some(position),
            owner: SourceOwner::Call(proof),
            before: 0,
        };
        let compiled = if matches!(proof.callee, ResolvedTheoremCallee::Builtin) {
            let (definitions, application, facts) = self.compile_builtin_membership_theorem(
                &proof.call,
                proof.builtin.as_ref(),
                &proof.theorem_derivation,
                &proof.type_proofs,
                &proof.type_stores,
                proof.function_domain.as_ref(),
                &proof.dom_proofs,
                &proof.dom_stores,
                &proof.conclusions_wd,
                &source_position,
            )?;
            self.compile_by_theorem_selection(
                proof,
                definitions,
                application,
                facts,
                &source_position,
            )?
        } else {
            let declaration = match &proof.callee {
                ResolvedTheoremCallee::UserTheorem(declaration) => declaration,
                _ => return Err(LeanCompileError::unsupported("ByThm/Callee")),
            };
            let source_name = match &proof.call.name {
                AtomicName::Plain { name } => name,
                _ => return Err(LeanCompileError::unsupported("ByThm/QualifiedCallee")),
            };
            let (registered, declaration_position, _) = position.visible_theorem(source_name)?;
            if registered != declaration
                || source_name != &declaration.name
                || proof.builtin.is_some()
                || proof.function_domain.is_some()
            {
                return Err(LeanCompileError::new(
                    "ByThm/Callee",
                    "The resolved declaration differs from the cited compiled theorem.",
                ));
            }
            let (definitions, application, returned_facts) = self.compile_user_theorem_instance(
                &proof.call,
                &proof.type_proofs,
                &proof.type_stores,
                &proof.dom_proofs,
                &proof.dom_stores,
                &proof.conclusions_wd,
                &proof.returned_conclusions,
                registered,
                &declaration_position,
                &source_position,
            )?;
            self.compile_by_theorem_selection(
                proof,
                definitions,
                application,
                returned_facts,
                &source_position,
            )?
        };
        let selected = source_subject(&proof.selected_proof)?;
        self.compile_fact_wd(&proof.selected_wd, &selected, position)?;
        self.validate_store(&proof.stored.store, &selected)?;
        Ok(compiled)
    }

    fn compile_by_theorem_selection(
        &self,
        proof: &ExecByThmStmtSuccess,
        mut definitions: Vec<String>,
        application: String,
        returned_facts: Vec<Fact>,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let conclusions_count = returned_facts.len();
        if conclusions_count != proof.returned_conclusions.len()
            || conclusions_count != proof.conclusions_wd.len()
        {
            return Err(LeanCompileError::unsupported("ByThm/ReturnStages"));
        }
        let return_head =
            proof.type_proofs.len() + proof.dom_proofs.len() + proof.conclusions_wd.len();
        for (index, (fact, stored)) in returned_facts
            .iter()
            .zip(&proof.returned_conclusions)
            .enumerate()
        {
            self.validate_store(&stored.store, fact)?;
            let prior = SourcePosition {
                before: return_head + index,
                ..*position
            };
            let captured_formation = SourcePosition::new(
                Some(&prior),
                SourceOwner::FactWD(&proof.conclusions_wd[index]),
                usize::MAX,
            );
            let compiled = (
                self.fact_proposition(fact, &captured_formation)?,
                conjunction_projection(&application, index, conclusions_count),
            );
            definitions.push(self.emit_internal_fact(fact, &compiled, &prior)?);
            let published = SourcePosition {
                before: return_head + index + 1,
                ..*position
            };
            let reference = (compiled.0, format!("h_{}", fact.fact_id().value()));
            // These projections and inferred producers remain local to this
            // invocation. Selection below admits only the direct source atoms.
            definitions
                .extend(self.compile_stored_inferences(stored, fact, &reference, &published)?);
        }
        let returned_ids: Vec<_> = proof
            .returned_conclusions
            .iter()
            .flat_map(|store| {
                store
                    .store
                    .atomic_components()
                    .into_iter()
                    .map(|(id, _)| id)
            })
            .collect();
        let allowed = match &proof.selected_proof {
            VerifyFactResult::Equality(result) => match result.as_ref() {
                VerifyEqualityResult::Success(selected) => match &selected.searched_proof {
                    EqualFactSearchedProof::ByEquivalenceClass(
                        EqualFactSearchedProofByEquivalenceClass::AlphaEndpoints(p),
                    ) => !p.reversed && returned_ids.contains(&p.cited.fact_id),
                    _ => false,
                },
                _ => false,
            },
            VerifyFactResult::AtomicExceptEquality(result) => match result.as_ref() {
                VerifyAtomicExceptEqualityFactResult::Success(selected) => {
                    match &selected.searched_proof {
                        AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(p) => {
                            returned_ids.contains(&p.cite_fact_id)
                                && p.why_parameters_of_known_fact_are_equal_to_givens
                                    .iter()
                                    .all(|proof| {
                                        matches!(proof, EqualFactSearchedProof::ByTheyAreTheSame(_))
                                    })
                        }
                        _ => false,
                    }
                }
                _ => false,
            },
            _ => false,
        };
        if !allowed {
            return Err(LeanCompileError::new(
                "ByThm/SelectionProvenance",
                "The selection does not directly cite an unreversed atomic component returned by this invocation.",
            ));
        }
        let selection_position = SourcePosition {
            before: proof.type_proofs.len()
                + proof.dom_proofs.len()
                + proof.conclusions_wd.len()
                + proof.returned_conclusions.len(),
            ..*position
        };
        let selected = self.compile_verify(&proof.selected_proof, &selection_position)?;
        Ok((
            self.scope_proposition(selected.0, &definitions),
            format!(
                "(by\n  {}\n  exact {}\n)",
                definitions.join("\n").replace('\n', "\n  "),
                selected.1
            ),
        ))
    }
    pub(in crate::compile_to_lean) fn compile_user_theorem_instance(
        &self,
        call: &TheoremCall,
        type_proofs: &[VerifyFactResult],
        type_stores: &[StoreFactAndInferResult],
        dom_proofs: &[VerifyFactResult],
        dom_stores: &[StoreFactAndInferResult],
        conclusions_wd: &[FactWellDefinedProof],
        returned_conclusions: &[StoreFactAndInferResult],
        registered: &DefThmStmt,
        declaration_position: &SourcePosition<'_>,
        position: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, String, Vec<Fact>), LeanCompileError> {
        let mut substitution = HashMap::new();
        if type_proofs.len() != type_stores.len() {
            return Err(LeanCompileError::new(
                "ByThm/TypeStoreStages",
                "The actual ordered type proofs and stores have different stage counts.",
            ));
        }
        let mut application_arguments = Vec::new();
        let mut definitions = Vec::new();
        let (domains, conclusions) = match (&registered.fact, &call.arguments) {
            (Fact::ForallFact(fact), TheoremCallArguments::Parenthesized(args)) => {
                let parameters: Vec<_> = fact
                    .typed_parameters
                    .groups
                    .iter()
                    .flat_map(|group| &group.params)
                    .collect();
                if args.len() != parameters.len() || type_proofs.len() != parameters.len() {
                    return Err(LeanCompileError::new(
                        "ByThm/Arguments",
                        "The invocation has different arguments or type-proof arity.",
                    ));
                }
                for (parameter, arg) in parameters.iter().zip(args) {
                    substitution.insert(parameter.id, arg.clone());
                }
                let mut offset = 0;
                for group in &fact.typed_parameters.groups {
                    for _ in &group.params {
                        let arg = &args[offset];
                        let type_position = SourcePosition {
                            before: offset,
                            ..*position
                        };
                        let member = self.compile_verify(&type_proofs[offset], &type_position)?;
                        match (&group.param_type, &source_subject(&type_proofs[offset])?) {
                            (ParamType::Obj(set), Fact::AtomicFact(AtomicFact::InFact(f)))
                                if f.element.ir() == arg.ir()
                                    && instantiated_object_matches(set, &f.set, &substitution) => {}
                            (ParamType::Set(_), Fact::AtomicFact(AtomicFact::IsSetFact(f)))
                                if f.set.ir() == arg.ir() => {}
                            _ => {
                                return Err(LeanCompileError::new(
                                    "ByThm/TypeProof",
                                    "The recorded parameter proof has another subject or domain kind.",
                                ));
                            }
                        }
                        application_arguments.push(self.compile_object_reference(
                            arg,
                            &SourcePosition {
                                before: offset + 1,
                                ..*position
                            },
                        )?);
                        let subject = source_subject(&type_proofs[offset])?;
                        definitions.push(self.emit_internal_fact(
                            &subject,
                            &member,
                            &type_position,
                        )?);
                        application_arguments.push(format!("h_{}", subject.fact_id().value()));
                        self.validate_store(&type_stores[offset].store, &subject)?;
                        let published = SourcePosition {
                            before: offset + 1,
                            ..*position
                        };
                        definitions.extend(self.compile_stored_inferences(
                            &type_stores[offset],
                            &subject,
                            &(member.0, format!("h_{}", subject.fact_id().value())),
                            &published,
                        )?);

                        offset += 1;
                    }
                }
                let conclusions = fact
                    .then_facts
                    .iter()
                    .map(|fact| match fact {
                        ExistOrAndChainAtomicFact::AtomicFact(atomic) => {
                            Ok(Fact::AtomicFact(atomic.clone()))
                        }
                        ExistOrAndChainAtomicFact::AndFact(fact) => Ok(Fact::AndFact(fact.clone())),
                        ExistOrAndChainAtomicFact::ChainFact(fact) => {
                            Ok(Fact::ChainFact(fact.clone()))
                        }
                        ExistOrAndChainAtomicFact::ExistFact(fact) => {
                            Ok(Fact::ExistFact(fact.clone()))
                        }
                        ExistOrAndChainAtomicFact::NotExistFact(fact) => {
                            Ok(Fact::NotExistFact(fact.clone()))
                        }
                        ExistOrAndChainAtomicFact::ExistUniqueFact(fact) => {
                            Ok(Fact::ExistUniqueFact(fact.clone()))
                        }
                        _ => Err(LeanCompileError::unsupported("ByThm/CompoundConclusion")),
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                (fact.dom_facts.iter().collect::<Vec<_>>(), conclusions)
            }
            (
                Fact::AtomicFact(_)
                | Fact::AndFact(_)
                | Fact::ChainFact(_)
                | Fact::ExistFact(_)
                | Fact::NotExistFact(_)
                | Fact::ExistUniqueFact(_)
                | Fact::NotForall(_),
                TheoremCallArguments::Bare,
            ) if type_proofs.is_empty() => (Vec::new(), vec![registered.fact.clone()]),
            _ => return Err(LeanCompileError::unsupported("ByThm/CallShape")),
        };
        if domains.len() != dom_proofs.len()
            || domains.len() != dom_stores.len()
            || conclusions.len() != returned_conclusions.len()
            || conclusions.len() != conclusions_wd.len()
            || conclusions.is_empty()
        {
            return Err(LeanCompileError::new(
                "ByThm/Stages",
                "The invocation has different premise, returned-store or WD stages.",
            ));
        }
        for (index, ((domain, result), stored)) in
            domains.iter().zip(dom_proofs).zip(dom_stores).enumerate()
        {
            let domain_position = SourcePosition {
                before: type_proofs.len() + index,
                ..*position
            };
            let compiled = self.compile_verify(result, &domain_position)?;
            if !instantiated_fact_matches(domain, &source_subject(result)?, &substitution) {
                return Err(LeanCompileError::new(
                    "ByThm/Domain",
                    "A premise proves another instantiated source requirement.",
                ));
            }
            let subject = source_subject(result)?;
            self.validate_store(&stored.store, &subject)?;
            definitions.push(self.emit_internal_fact(&subject, &compiled, &domain_position)?);
            application_arguments.push(format!("h_{}", subject.fact_id().value()));
            let published = SourcePosition {
                before: type_proofs.len() + index + 1,
                ..*position
            };
            let reference = (compiled.0, format!("h_{}", subject.fact_id().value()));
            definitions
                .extend(self.compile_stored_inferences(stored, &subject, &reference, &published)?);
        }
        let name = format!("h_{}", registered.fact.fact_id().value());
        let reference = if declaration_position.is_local() {
            name
        } else {
            self.context_application(&name, declaration_position)
        };
        let application = if application_arguments.is_empty() {
            reference
        } else {
            format!("({} {})", reference, application_arguments.join(" "))
        };
        let mut returned_facts = Vec::new();
        // The runtime forms every conclusion before publishing any returned
        // package. Later formation cannot cite an earlier returned truth.
        for (index, ((expected, stored), wd)) in conclusions
            .iter()
            .zip(returned_conclusions)
            .zip(conclusions_wd)
            .enumerate()
        {
            let fact = match &stored.store {
                StoreFactResult::NotForallFact(stored) => Fact::NotForall(stored.fact.clone()),
                StoreFactResult::AtomicFact(stored) => Fact::AtomicFact(stored.fact.clone()),
                StoreFactResult::AndFact(stored) => Fact::AndFact(stored.fact.clone()),
                StoreFactResult::ChainFact(stored) => Fact::ChainFact(stored.fact.clone()),
                StoreFactResult::ExistShapedFact(stored) => match &stored.fact {
                    ExistShapedFact::Exist(fact) => Fact::ExistFact(fact.clone()),
                    ExistShapedFact::NotExist(fact) => Fact::NotExistFact(fact.clone()),
                    ExistShapedFact::ExistUnique(fact) => Fact::ExistUniqueFact(fact.clone()),
                },
                _ => return Err(LeanCompileError::unsupported("ByThm/ReturnedPackage")),
            };
            self.validate_store(&stored.store, &fact)?;
            if !instantiated_fact_matches(expected, &fact, &substitution) {
                return Err(LeanCompileError::new(
                    "ByThm/ReturnedSubject",
                    "The returned producer differs from this theorem instance.",
                ));
            }
            let formation = SourcePosition {
                before: type_proofs.len() + dom_proofs.len() + index,
                ..*position
            };
            self.compile_fact_wd(wd, &fact, &formation)?;
            returned_facts.push(fact);
        }
        Ok((definitions, application, returned_facts))
    }
}
