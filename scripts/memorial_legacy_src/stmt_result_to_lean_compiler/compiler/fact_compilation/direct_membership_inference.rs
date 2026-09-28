//! Direct numeric, set-builder, and list-set membership inference.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// `Combine`: publish a directly constructed standard numeric membership
    /// proof, then consume its typed sign/nonzero inference Results. Closed
    /// evaluation has a stricter dedicated path above; this route covers
    /// symbolic closure and primitive constant rules.
    pub(in super::super) fn compile_direct_standard_numeric_membership_with_inference(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<bool, String> {
        let Some(verified) = result.verification() else {
            return Ok(false);
        };
        let source_fact = result.fact();
        let Ok((_, set)) = membership_parts(&source_fact) else {
            return Ok(false);
        };
        if !matches!(set, Obj::StandardSet(_)) || result.store.infers.rule_applications.is_empty() {
            return Ok(false);
        }
        let Some(proof) = self.construct_lean_proof_from_direct_fact_result(verified)? else {
            return Ok(false);
        };
        validate_atomic_fact_well_definedness_result(&verified.checked, &source_fact)?;
        let source_fact_id = result
            .store
            .fact_id
            .ok_or_else(|| "stored standard numeric membership has no FactId".to_string())?;
        let proposition = render_fact(&source_fact, &self.environment_stack)?;
        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {theorem_name} : {proposition} := by\n  exact {proof}"
        ));
        self.environment_stack
            .fact_names
            .insert(source_fact_id, theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(source_fact_id, source_fact.clone());
        self.next_fact_name_index += 1;
        self.compile_standard_numeric_membership_infer_result_as_top_level_declarations(
            &source_fact,
            source_fact_id,
            &result.store.infers,
            "standard numeric membership inference",
        )?;
        Ok(true)
    }

    /// `Combine`: publish membership in one literal set builder, then publish
    /// the exact base-membership and predicate projections named by its typed
    /// infer Results. Every projection cites the source statement's FactId;
    /// the compiler never rediscovers these consequences from proposition
    /// shape or a store-reason string.
    pub(in super::super) fn compile_direct_set_builder_membership_with_inference(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<bool, String> {
        let Some(verified) = result.verification() else {
            return Ok(false);
        };
        let source_fact = result.fact();
        let Ok((_, source_set)) = membership_parts(&source_fact) else {
            return Ok(false);
        };
        let Obj::SetBuilder(_) = source_set else {
            return Ok(false);
        };
        if result.store.infers.rule_applications.is_empty() {
            return Ok(false);
        }
        let Some(source_proof) = self.construct_lean_proof_from_direct_fact_result(verified)?
        else {
            return Ok(false);
        };
        validate_atomic_fact_well_definedness_result(&verified.checked, &source_fact)?;
        let source_fact_id = result
            .store
            .fact_id
            .ok_or_else(|| "stored set-builder membership has no FactId".to_string())?;
        let source_proposition = render_fact(&source_fact, &self.environment_stack)?;
        let source_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {source_name} : {source_proposition} := by\n  exact {source_proof}"
        ));
        self.environment_stack
            .fact_names
            .insert(source_fact_id, source_name.clone());
        self.environment_stack
            .fact_propositions
            .insert(source_fact_id, source_fact.clone());
        self.next_fact_name_index += 1;

        self.compile_set_builder_membership_infer_result_as_top_level_declarations(
            &source_fact,
            source_fact_id,
            &source_name,
            &result.store.infers,
        )?;
        Ok(true)
    }

    pub(in super::super) fn compile_set_builder_membership_infer_result_as_top_level_declarations(
        &mut self,
        source_fact: &Fact,
        source_fact_id: FactId,
        source_name: &str,
        infers: &SuccessInferResult,
    ) -> Result<(), String> {
        let (source_element, source_set) = membership_parts(source_fact)?;
        let Obj::SetBuilder(builder) = source_set else {
            return Err("set-builder inference source retained a non-builder set".into());
        };
        resolve_fact_citation(&source_fact_id, source_fact, &self.environment_stack)?;
        let expected_application_count = builder.facts.len() + 1;
        if infers.rule_applications.len() != expected_application_count {
            return Err(format!(
                "set-builder membership retained {} typed projections instead of {expected_application_count}",
                infers.rule_applications.len()
            ));
        }
        for (application_index, application) in infers.rule_applications.iter().enumerate() {
            let [premise] = application.premises.as_slice() else {
                return Err(format!(
                    "set-builder projection {application_index} must cite one source premise"
                ));
            };
            if premise.fact_id != Some(source_fact_id)
                || premise.fact.to_string() != source_fact.to_string()
            {
                return Err(format!(
                    "set-builder projection {application_index} does not cite the exact source FactId"
                ));
            }
            let [conclusion] = application.conclusions.as_slice() else {
                return Err(format!(
                    "set-builder projection {application_index} must retain one conclusion"
                ));
            };
            let conclusion_fact_id = conclusion.fact_id.ok_or_else(|| {
                format!("set-builder projection {application_index} has no conclusion FactId")
            })?;
            if conclusion_fact_id == source_fact_id
                || !infer_result_retains_fact_id(infers, &conclusion.fact, conclusion_fact_id)
            {
                return Err(format!(
                    "set-builder projection {application_index} disagrees with its ordered store effect"
                ));
            }

            let proof = match &application.rule {
                InferRule::SetBuilderBaseMembershipProjection if application_index == 0 => {
                    let (element, set) = membership_parts(&conclusion.fact)?;
                    if obj_equality_key(element) != obj_equality_key(source_element)
                        || obj_equality_key(set) != obj_equality_key(builder.param_set.as_ref())
                    {
                        return Err(
                            "set-builder base projection changed its element or base set".into(),
                        );
                    }
                    format!("Litex.Rules.inBaseOfInSetBuilder ({source_name})")
                }
                InferRule::SetBuilderPredicateProjection { clause_index }
                    if application_index == *clause_index + 1
                        && *clause_index < builder.facts.len() =>
                {
                    render_set_builder_predicate_projection_from_fact_and_proof(
                        &conclusion.fact,
                        *clause_index,
                        &source_fact,
                        &source_name,
                        &self.environment_stack,
                    )?
                }
                _ => {
                    return Err(format!(
                        "set-builder projection {application_index} changed its typed rule or clause order"
                    ));
                }
            };
            let proposition =
                if let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = &conclusion.fact {
                    let left = render_obj(&equality.left, &self.environment_stack)?;
                    let right = render_obj(&equality.right, &self.environment_stack)?;
                    if left == right {
                        render_fact(&conclusion.fact, &self.environment_stack)?
                    } else {
                        render_no_observation_equality_alternatives_fact(
                            &conclusion.fact,
                            &self.environment_stack,
                        )?
                    }
                } else {
                    render_fact(&conclusion.fact, &self.environment_stack)?
                };
            let theorem_name = format!("__fact{}", self.next_fact_name_index);
            self.declarations.push(format!(
                "theorem {theorem_name} : {proposition} := by\n  exact {proof}"
            ));
            self.environment_stack
                .fact_names
                .insert(conclusion_fact_id, theorem_name);
            self.environment_stack
                .fact_propositions
                .insert(conclusion_fact_id, conclusion.fact.clone());
            self.next_fact_name_index += 1;
        }
        Ok(())
    }

    /// `Combine`: publish the selected list-set membership proof and then
    /// publish the exact ordered equality alternatives returned by inference.
    /// Both layers cite frozen FactIds; the compiler never reconstructs this
    /// rule from a store-reason string.
    pub(in super::super) fn compile_direct_list_set_membership_with_inference(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<bool, String> {
        let Some(verified) = result.verification() else {
            return Ok(false);
        };
        let source_fact = result.fact();
        let Ok((_, source_set)) = membership_parts(&source_fact) else {
            return Ok(false);
        };
        let Obj::ListSet(list_set) = source_set else {
            return Ok(false);
        };
        let matching_applications = result
            .store
            .infers
            .rule_applications
            .iter()
            .filter(|application| {
                matches!(
                    application.rule,
                    InferRule::ListSetMembershipImpliesEqualityAlternatives(_)
                )
            })
            .collect::<Vec<_>>();
        if matching_applications.is_empty() {
            return Ok(false);
        }
        let [application] = matching_applications.as_slice() else {
            return Err("list-set membership retained more than one alternatives inference".into());
        };
        if result.store.infers.rule_applications.len() != 1 {
            return Err("list-set membership retained unrelated top-level inference rules".into());
        }
        let InferRule::ListSetMembershipImpliesEqualityAlternatives(rule) = &application.rule
        else {
            unreachable!("matching list-set inference filtered above")
        };
        if rule.element_count == 0 || rule.element_count != list_set.list.len() {
            return Err("list-set alternatives rule changed its nonempty source arity".into());
        }
        let source_fact_id = result
            .store
            .fact_id
            .ok_or_else(|| "stored list-set membership has no FactId".to_string())?;
        let [premise] = application.premises.as_slice() else {
            return Err("list-set alternatives inference must cite one membership premise".into());
        };
        if premise.fact_id != Some(source_fact_id)
            || premise.fact.to_string() != source_fact.to_string()
        {
            return Err("list-set alternatives inference changed its source FactId".into());
        }
        let [conclusion] = application.conclusions.as_slice() else {
            return Err("list-set alternatives inference must retain one conclusion".into());
        };
        let conclusion_fact_id = conclusion
            .fact_id
            .ok_or_else(|| "list-set alternatives conclusion has no FactId".to_string())?;
        if !infer_result_retains_fact_id(&result.store.infers, &conclusion.fact, conclusion_fact_id)
        {
            return Err(
                "list-set alternatives conclusion disagrees with its flattened store effect".into(),
            );
        }
        if !conclusion.infers.rule_applications.is_empty()
            || conclusion.infers.store_fact_outputs.iter().any(|output| {
                output.fact_id != Some(conclusion_fact_id)
                    || output.itself_and_why_itself_is_stored.0.to_string()
                        != conclusion.fact.to_string()
                    || !output.inferred_facts.is_empty()
                    || !output.inferred_fact_ids.is_empty()
            })
        {
            return Err(
                "list-set alternatives conclusion retained unsupported recursive effects".into(),
            );
        }

        let Some(source_proof) = self.construct_lean_proof_from_direct_fact_result(verified)?
        else {
            return Ok(false);
        };
        validate_atomic_fact_well_definedness_result(&verified.checked, &source_fact)?;
        let source_proposition = render_fact(&source_fact, &self.environment_stack)?;
        let source_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {source_name} : {source_proposition} := by\n  exact {source_proof}"
        ));
        self.environment_stack
            .fact_names
            .insert(source_fact_id, source_name.clone());
        self.environment_stack
            .fact_propositions
            .insert(source_fact_id, source_fact.clone());
        self.next_fact_name_index += 1;

        let conclusion_proof = render_list_set_membership_elimination_from_fact_and_proof(
            &conclusion.fact,
            &source_fact,
            &source_name,
            &self.environment_stack,
        )?;
        let conclusion_proposition = render_no_observation_equality_alternatives_fact(
            &conclusion.fact,
            &self.environment_stack,
        )?;
        let conclusion_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {conclusion_name} : {conclusion_proposition} := by\n  exact {conclusion_proof}"
        ));
        self.environment_stack
            .fact_names
            .insert(conclusion_fact_id, conclusion_name);
        self.environment_stack
            .fact_propositions
            .insert(conclusion_fact_id, conclusion.fact.clone());
        self.environment_stack
            .fact_lean_propositions
            .insert(conclusion_fact_id, conclusion_proposition);
        self.next_fact_name_index += 1;
        validate_flattened_inferred_fact_ids_are_visible(
            &result.store.infers,
            &self.environment_stack,
            "list-set membership inference",
        )?;
        Ok(true)
    }
}
