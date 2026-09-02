//! Set-builder and function-set membership.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// Recover the explicit carrier witness owned by a checked set-builder
    /// membership, including the common case where the user names that
    /// set-builder with a transparent local definition. The outer
    /// transformation Result is replayed before its source is inspected, so
    /// this never unfolds an ambient definition merely because its text
    /// happens to match.
    pub(in super::super) fn construct_lean_exact_set_builder_value_from_fact_result(
        &mut self,
        result: &SuccessFactProofNode,
    ) -> Result<Option<(String, String)>, String> {
        match result.proof() {
            SuccessFactProofResult::BuiltinRule(builtin)
            | SuccessFactProofResult::BuiltinStrategy(builtin) => {
                let Some(BuiltinRuleEvidence::SetBuilderMembership(evidence)) =
                    builtin.evidence.typed()
                else {
                    return Ok(None);
                };
                self.construct_lean_exact_set_builder_value_from_result(
                    &result.fact(),
                    evidence,
                    &builtin.subgoals,
                )
            }
            SuccessFactProofResult::Transform(transformation) => {
                let FactTransformationRule::TransparentDefinitionReduction(evidence) =
                    &transformation.rule
                else {
                    return Ok(None);
                };
                let source = transformation.source.as_ref();
                self.construct_lean_transparent_definition_reduction_from_result(
                    &source.fact(),
                    &result.fact(),
                    "True.intro".to_string(),
                    evidence,
                    0,
                )?;
                self.construct_lean_exact_set_builder_value_from_fact_result(source)
            }
            SuccessFactProofResult::Reuse(reuse) => {
                let source = reuse.source.as_ref();
                if source.fact().to_string() != result.fact().to_string() {
                    return Err(
                        "reused set-builder membership changed its exact proposition".into(),
                    );
                }
                self.construct_lean_exact_set_builder_value_from_fact_result(source)
            }
            SuccessFactProofResult::CombinedProofs(combined) => {
                let Some(primary) = combined.primary.as_deref() else {
                    return Ok(None);
                };
                if primary.fact().to_string() != result.fact().to_string() {
                    return Err(
                        "combined set-builder membership changed its primary proposition".into(),
                    );
                }
                self.construct_lean_exact_set_builder_value_from_fact_result(primary)
            }
            _ => Ok(None),
        }
    }

    /// Compile the same ordered children as ordinary set-builder membership,
    /// but retain the canonical exact carrier value for a typed object
    /// definition.  Returning `None` means the checked membership is valid
    /// but does not expose a definitionally coherent exact representation.
    pub(in super::super) fn construct_lean_exact_set_builder_value_from_result(
        &mut self,
        target: &Fact,
        evidence: &SetBuilderMembershipBuiltinRuleEvidence,
        subgoals: &[VerifyFactResult],
    ) -> Result<Option<(String, String)>, String> {
        if evidence.expected_target.to_string() != target.to_string() {
            return Err("set-builder membership evidence changed its target".into());
        }
        if subgoals.len() != evidence.expected_premises.len() {
            return Err("set-builder membership lost an ordered child Result".into());
        }
        let mut compiled_children = Vec::with_capacity(subgoals.len());
        for (index, (child, expected)) in subgoals
            .iter()
            .zip(evidence.expected_premises.iter())
            .enumerate()
        {
            let child = child
                .verified()
                .ok_or_else(|| format!("set-builder child {index} is not factual"))?;
            if child.fact().to_string() != expected.to_string() {
                return Err(format!(
                    "set-builder child {index} changed its proposition"
                ));
            }
            let Some(proof) = self.construct_lean_proof_from_direct_fact_result(child)? else {
                return Ok(None);
            };
            compiled_children.push((expected.clone(), proof));
        }
        render_exact_set_builder_value_from_fact_and_proofs(
            target,
            &compiled_children,
            &self.environment_stack,
        )
    }

    /// `Combine`: consume the base-membership child followed by every checked
    /// set-builder predicate child in source order. The representative used by
    /// Lean is introduced only inside the resulting proof term; the caller's
    /// compiler environment is unchanged.
    pub(in super::super) fn construct_lean_set_builder_membership_from_result(
        &mut self,
        target: &Fact,
        evidence: &SetBuilderMembershipBuiltinRuleEvidence,
        subgoals: &[VerifyFactResult],
    ) -> Result<Option<String>, String> {
        if evidence.expected_target.to_string() != target.to_string() {
            return Err("set-builder membership evidence changed its target".into());
        }
        if subgoals.len() != evidence.expected_premises.len() {
            return Err("set-builder membership lost an ordered child Result".into());
        }
        let mut compiled_children = Vec::with_capacity(subgoals.len());
        for (index, (child, expected)) in subgoals
            .iter()
            .zip(evidence.expected_premises.iter())
            .enumerate()
        {
            let child = child
                .verified()
                .ok_or_else(|| format!("set-builder child {index} is not factual"))?;
            if child.fact().to_string() != expected.to_string() {
                return Err(format!(
                    "set-builder child {index} changed its proposition"
                ));
            }
            let Some(proof) = self.construct_lean_proof_from_direct_fact_result(child)? else {
                return Ok(None);
            };
            compiled_children.push((expected.clone(), proof));
        }
        Ok(Some(render_set_builder_membership_from_fact_and_proofs(
            target,
            &compiled_children,
            &self.environment_stack,
        )?))
    }

    /// `Wrap`: validate the exact pointwise forall child retained by the
    /// verifier, then package the compiler-constructed function value in the
    /// exact Lean carrier of its function set. The pointwise child is not
    /// discarded: its recursive `ForallProof` shape must agree with the
    /// evidence. The final `In.own` is possible only because rendering the
    /// function value already consumes its Result-owned WD/body evidence and
    /// constructs a value of that exact carrier.
    pub(in super::super) fn construct_lean_function_set_membership_from_result(
        &mut self,
        target: &Fact,
        evidence: &FunctionSetMembershipBuiltinRuleEvidence,
        subgoals: &[VerifyFactResult],
    ) -> Result<Option<String>, String> {
        if evidence.expected_target.to_string() != target.to_string() {
            return Err("function-set membership evidence changed its target".into());
        }
        let Fact::AtomicFact(AtomicFact::InFact(target_membership)) = target else {
            return Err("function-set membership evidence targets a non-membership".into());
        };
        if !matches!(&target_membership.set, Obj::FnSet(_)) {
            return Err("function-set membership evidence retained a non-function set".into());
        }
        let [pointwise_result] = subgoals else {
            return Err(
                "function-set membership evidence requires one pointwise forall child Result"
                    .into(),
            );
        };
        let pointwise_result = pointwise_result
            .verified()
            .ok_or_else(|| "function-set membership pointwise child is not factual".to_string())?;
        if pointwise_result.fact().to_string() != evidence.expected_pointwise.to_string() {
            return Err("function-set membership changed its pointwise proposition".into());
        }
        let Fact::ForallFact(expected_pointwise) = &evidence.expected_pointwise else {
            return Err(
                "function-set membership retained a non-forall pointwise proposition".into(),
            );
        };
        let SuccessFactProofResult::ForallProof(pointwise_proof) = pointwise_result.proof() else {
            return Err(
                "function-set membership pointwise child lost its ForallProof Result".into(),
            );
        };
        if pointwise_proof.forall_fact.to_string() != expected_pointwise.to_string()
            || pointwise_proof.proves.len() != expected_pointwise.then_facts.len()
        {
            return Err(
                "function-set membership pointwise ForallProof changed its binder or conclusions"
                    .into(),
            );
        }

        let rendered_function = render_obj(&target_membership.element, &self.environment_stack)?;
        let rendered_function_set = render_obj(&target_membership.set, &self.environment_stack)?;
        let rendered_target = render_fact(target, &self.environment_stack)?;
        let expected_rendered_target =
            format!("Litex.In {rendered_function} {rendered_function_set}");
        if rendered_target != expected_rendered_target {
            return Err("function-set membership changed its rendered target".into());
        }
        Ok(Some(format!(
            "Litex.In.own {rendered_function_set} {rendered_function}"
        )))
    }
}
