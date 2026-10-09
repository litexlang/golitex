use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use std::collections::HashMap;

impl<'a> LitexToLeanCompiler<'a> {
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
                Ok(self.emit_fact(
                    &source_subject(&proof.selected_proof)?,
                    compiled,
                    index,
                    local,
                    position,
                ))
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
        let declaration = match &proof.callee {
            ResolvedTheoremCallee::UserTheorem(declaration) => declaration,
            _ => return Err(LeanCompileError::unsupported("ByThm/Callee")),
        };
        let source_name = match &proof.call.name {
            AtomicName::Plain { name } => name,
            _ => return Err(LeanCompileError::unsupported("ByThm/QualifiedCallee")),
        };
        let (registered, declaration_position, declaration_index) =
            position.visible_theorem(source_name)?;
        let declaration_index = declaration_index + 1;
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
        let source_position = SourcePosition {
            parent: Some(position),
            owner: SourceOwner::Call(proof),
            before: 0,
        };
        let compiled = self.compile_by_theorem_body(
            proof,
            registered,
            &declaration_position,
            declaration_index,
            &source_position,
        );
        let compiled = compiled?;
        self.validate_store(&proof.stored, &source_subject(&proof.selected_proof)?)?;
        Ok(compiled)
    }

    pub(in crate::compile_to_lean) fn compile_by_theorem_body(
        &self,
        proof: &ExecByThmStmtSuccess,
        registered: &DefThmStmt,
        declaration_position: &SourcePosition<'_>,
        declaration_index: usize,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let mut substitution = HashMap::new();
        let mut application_arguments = Vec::new();
        let mut definitions = Vec::new();
        let (domains, conclusions) = match (&registered.fact, &proof.call.arguments) {
            (Fact::ForallFact(fact), TheoremCallArguments::Parenthesized(args)) => {
                let parameters: Vec<_> = fact
                    .typed_parameters
                    .groups
                    .iter()
                    .flat_map(|group| &group.params)
                    .collect();
                if args.len() != parameters.len() || proof.type_proofs.len() != parameters.len() {
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
                    let set = match &group.param_type {
                        ParamType::Obj(set) => set,
                        _ => return Err(LeanCompileError::unsupported("ByThm/ParameterKind")),
                    };
                    for _ in &group.params {
                        let arg = &args[offset];
                        let type_position = SourcePosition {
                            before: offset,
                            ..*position
                        };
                        let member =
                            self.compile_verify(&proof.type_proofs[offset], &type_position)?;
                        match &source_subject(&proof.type_proofs[offset])? {
                            Fact::AtomicFact(AtomicFact::InFact(f))
                                if f.element.ir() == arg.ir()
                                    && instantiated_object_matches(set, &f.set, &substitution) => {}
                            _ => {
                                return Err(LeanCompileError::new(
                                    "ByThm/TypeProof",
                                    "The membership proves another parameter or carrier.",
                                ))
                            }
                        }
                        application_arguments.push(self.compile_object_reference(
                            arg,
                            &SourcePosition {
                                before: offset + 1,
                                ..*position
                            },
                        )?);
                        let subject = source_subject(&proof.type_proofs[offset])?;
                        definitions.push(self.emit_internal_fact(
                            &subject,
                            &member,
                            &type_position,
                        ));
                        application_arguments.push(format!("_fact_f{}", subject.fact_id().value()));

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
                        _ => Err(LeanCompileError::unsupported("ByThm/CompoundConclusion")),
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                (fact.dom_facts.iter().collect::<Vec<_>>(), conclusions)
            }
            (Fact::AtomicFact(_), TheoremCallArguments::Bare) if proof.type_proofs.is_empty() => {
                (Vec::new(), vec![registered.fact.clone()])
            }
            _ => return Err(LeanCompileError::unsupported("ByThm/CallShape")),
        };
        if domains.len() != proof.dom_proofs.len()
            || conclusions.len() != proof.returned_conclusions.len()
            || conclusions.len() != proof.conclusions_wd.len()
            || conclusions.is_empty()
        {
            return Err(LeanCompileError::new(
                "ByThm/Stages",
                "The invocation has different premise, returned-store or WD stages.",
            ));
        }
        for (index, (domain, result)) in domains.iter().zip(&proof.dom_proofs).enumerate() {
            let domain_position = SourcePosition {
                before: proof.type_proofs.len() + index,
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
            definitions.push(self.emit_internal_fact(&subject, &compiled, &domain_position));
            application_arguments.push(format!("_fact_f{}", subject.fact_id().value()));
        }
        let application = if application_arguments.is_empty() {
            self.context_application(
                &format!("named_thm_{declaration_index}"),
                declaration_position,
            )
        } else {
            format!(
                "({} {})",
                self.context_application(
                    &format!("named_thm_{declaration_index}"),
                    declaration_position
                ),
                application_arguments.join(" ")
            )
        };
        for (index, ((expected, stored), wd)) in conclusions
            .iter()
            .zip(&proof.returned_conclusions)
            .zip(&proof.conclusions_wd)
            .enumerate()
        {
            let fact = match &stored.store {
                StoreFactResult::AtomicFact(stored) => Fact::AtomicFact(stored.fact.clone()),
                _ => return Err(LeanCompileError::unsupported("ByThm/ReturnedPackage")),
            };
            self.validate_store(stored, &fact)?;
            if !instantiated_fact_matches(expected, &fact, &substitution) {
                return Err(LeanCompileError::new(
                    "ByThm/ReturnedSubject",
                    "The returned producer differs from this theorem instance.",
                ));
            }
            let conclusion_position = SourcePosition {
                before: proof.type_proofs.len() + proof.dom_proofs.len() + index,
                ..*position
            };
            self.compile_fact_wd(wd, &fact, &conclusion_position)?;
            let formed = SourcePosition {
                before: proof.type_proofs.len() + proof.dom_proofs.len() + index + 1,
                ..*position
            };
            let compiled = (
                self.fact_proposition(&fact, &formed)?,
                conjunction_projection(&application, index, conclusions.len()),
            );
            definitions.push(self.emit_internal_fact(&fact, &compiled, &formed));
        }
        let returned_ids: Vec<_> = proof
            .returned_conclusions
            .iter()
            .map(StoreFactAndInferResult::primary_fact_id)
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
            return Err(LeanCompileError::new("ByThm/SelectionProvenance", "The selection does not directly cite an unreversed atom returned by this invocation."));
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
}
