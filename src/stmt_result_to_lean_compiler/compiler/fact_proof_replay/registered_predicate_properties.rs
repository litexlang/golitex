//! Registered symmetric and antisymmetric predicate proofs.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// `Wrap`: compile the exact reordered predicate child retained by the
    /// verifier, then replay the registered permutation theorem until the
    /// requested target ordering is reached. Repeating the theorem matters for
    /// non-involutive permutations: the Runtime checks `P(target)`, while a
    /// theorem registered as `source -> P(source)` may need more than one
    /// application to return from that premise to `target`.
    pub(in super::super) fn construct_lean_registered_symmetric_predicate_from_result(
        &mut self,
        target: &Fact,
        evidence: &RegisteredSymmetricPredicateBuiltinRuleEvidence,
        subgoals: &[VerifyFactResult],
    ) -> Result<Option<String>, String> {
        if evidence.expected_target.to_string() != target.to_string() {
            return Err("registered symmetric-predicate evidence changed its target".into());
        }
        let Fact::AtomicFact(target_atomic @ AtomicFact::NormalAtomicFact(target_predicate)) =
            target
        else {
            return Err(
                "registered symmetric-predicate evidence targets a non-user predicate".into(),
            );
        };
        if target_predicate.predicate.to_string() != evidence.predicate_name
            || target_predicate.body.len() < 2
        {
            return Err(
                "registered symmetric-predicate evidence changed its predicate or arity".into(),
            );
        }
        let expected_alternate_from_gather: Fact = target_atomic
            .symmetric_reordered_args(&evidence.gather)
            .ok_or_else(|| {
                "registered symmetric-predicate evidence retained an invalid permutation"
                    .to_string()
            })?
            .into();
        if expected_alternate_from_gather.to_string() != evidence.expected_alternate.to_string() {
            return Err(
                "registered symmetric-predicate evidence changed its reordered premise".into(),
            );
        }
        let [alternate_result] = subgoals else {
            return Err(
                "registered symmetric-predicate proof requires exactly one child Result".into(),
            );
        };
        let alternate_result = alternate_result
            .verified()
            .ok_or_else(|| "registered symmetric-predicate child is not factual".to_string())?;
        if alternate_result.fact().to_string() != evidence.expected_alternate.to_string() {
            return Err("registered symmetric-predicate child changed its fact".into());
        }

        let bindings = self
            .environment_stack
            .registered_symmetric_predicate_theorem_bindings
            .get(&evidence.predicate_name)
            .ok_or_else(|| {
                format!(
                    "registered symmetry theorem for `{}` is not visible in this compiler environment",
                    evidence.predicate_name
                )
            })?;
        let mut selected_binding = None;
        for binding in bindings.iter().rev() {
            let binding_gather = registered_symmetric_predicate_gather(
                &binding.forall_fact,
                &evidence.predicate_name,
            )?;
            if binding_gather == evidence.gather {
                selected_binding = Some(binding.clone());
                break;
            }
        }
        let binding = selected_binding.ok_or_else(|| {
            format!(
                "registered symmetry theorem for `{}` does not own permutation {:?}",
                evidence.predicate_name, evidence.gather
            )
        })?;

        render_fact(target, &self.environment_stack)?;
        let Some(mut proof) =
            self.construct_lean_proof_from_direct_fact_result(alternate_result)?
        else {
            return Ok(None);
        };
        let mut current = evidence.expected_alternate.clone();
        let mut visited = HashSet::new();
        visited.insert(current.to_string());
        loop {
            let (next, parameter_arguments) =
                instantiate_registered_symmetric_predicate_transition(
                    &binding.forall_fact,
                    &evidence.predicate_name,
                    &current,
                )?;
            let mut theorem_application = binding.theorem_name.clone();
            for argument in parameter_arguments {
                theorem_application.push(' ');
                theorem_application.push_str(&render_obj(&argument, &self.environment_stack)?);
            }
            theorem_application.push_str(&format!(" ({proof})"));
            proof = theorem_application;
            if next.to_string() == target.to_string() {
                return Ok(Some(proof));
            }
            if !visited.insert(next.to_string()) {
                return Err(
                    "registered symmetric-predicate permutation cycled without reaching its target"
                        .into(),
                );
            }
            current = next;
        }
    }

    /// `Combine`: compile the two ordered predicate-premise children and apply
    /// the exact antisymmetry theorem currently visible in the compiler
    /// environment created by an earlier registration Result.
    pub(in super::super) fn construct_lean_registered_antisymmetric_predicate_from_result(
        &mut self,
        target: &Fact,
        evidence: &RegisteredAntisymmetricPredicateBuiltinRuleEvidence,
        subgoals: &[VerifyFactResult],
    ) -> Result<Option<String>, String> {
        if evidence.expected_target.to_string() != target.to_string() {
            return Err("registered antisymmetric-predicate evidence changed its target".into());
        }
        let binding = self
            .environment_stack
            .registered_antisymmetric_predicate_theorem_bindings
            .get(&evidence.predicate_name)
            .cloned()
            .ok_or_else(|| {
                format!(
                    "registered antisymmetry theorem for `{}` is not visible in this compiler environment",
                    evidence.predicate_name
                )
            })?;
        let (parameter_arguments, expected_premises) =
            instantiate_registered_antisymmetric_predicate_application(
                &binding.forall_fact,
                &evidence.predicate_name,
                target,
            )?;
        if subgoals.len() != expected_premises.len() {
            return Err(
                "registered antisymmetric-predicate proof lost an ordered child Result".into(),
            );
        }
        let mut premise_proofs = Vec::with_capacity(subgoals.len());
        for (index, (subgoal, expected)) in
            subgoals.iter().zip(expected_premises.iter()).enumerate()
        {
            let subgoal = subgoal.verified().ok_or_else(|| {
                format!("registered antisymmetric-predicate child {index} is not factual")
            })?;
            if subgoal.fact().to_string() != expected.to_string() {
                return Err(format!(
                    "registered antisymmetric-predicate child {index} changed its fact"
                ));
            }
            let Some(proof) = self.construct_lean_proof_from_direct_fact_result(subgoal)? else {
                return Ok(None);
            };
            premise_proofs.push(proof);
        }

        render_fact(target, &self.environment_stack)?;
        let mut theorem_application = binding.theorem_name;
        for argument in parameter_arguments {
            theorem_application.push(' ');
            theorem_application.push_str(&render_obj(&argument, &self.environment_stack)?);
        }
        for proof in premise_proofs {
            theorem_application.push_str(&format!(" ({proof})"));
        }
        Ok(Some(theorem_application))
    }
}
