//! Native equality proof construction and retention.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// Construct a native equality under the exact object WD view owned by
    /// the statement Result. Function applications inside arithmetic
    /// equalities need the same occurrence/codomain certificates as their
    /// ordinary semantic proof.
    pub(in super::super) fn construct_lean_native_equality_proof_from_direct_fact_result_using_its_well_definedness(
        &mut self,
        result: &VerifiedFactResult,
    ) -> Result<Option<String>, String> {
        self.with_verified_fact_well_definedness_context(result, |compiler| {
            compiler.construct_lean_native_equality_proof_from_direct_fact_result(result)
        })
    }

    /// Construct native Lean equality only for Result rules whose reviewed
    /// consumer proves the exact rendered `=` before wrapping it in
    /// `Litex.Same`.  Returning `None` is intentional: semantic equality is
    /// heterogeneous, so an arbitrary successful `Same` proof is not an
    /// admissible rewrite certificate for native order propositions.
    pub(in super::super) fn construct_lean_native_equality_proof_from_direct_fact_result(
        &mut self,
        result: &VerifiedFactResult,
    ) -> Result<Option<String>, String> {
        let target = result.fact();
        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = &target else {
            return Ok(None);
        };
        let (SuccessFactProofResult::BuiltinRule(builtin)
        | SuccessFactProofResult::BuiltinStrategy(builtin)) = result.proof()
        else {
            return Ok(None);
        };

        match builtin.evidence.typed() {
            Some(BuiltinRuleEvidence::ObjectReflexivity(evidence)) => {
                if !builtin.subgoals.is_empty()
                    || evidence.expected_target.to_string() != target.to_string()
                    || obj_equality_key(&equality.left) != obj_equality_key(&equality.right)
                {
                    return Err("native object-reflexivity evidence changed its target".into());
                }
                render_obj(&equality.left, &self.environment_stack)?;
                render_obj(&equality.right, &self.environment_stack)?;
                Ok(Some("by rfl".into()))
            }
            Some(BuiltinRuleEvidence::RationalNormalization(evidence)) => {
                if !builtin.subgoals.is_empty()
                    || evidence.expected_target.to_string() != target.to_string()
                    || obj_equality_key(&equality.left)
                        != obj_equality_key(&evidence.left_evaluation.expression)
                    || obj_equality_key(&equality.right)
                        != obj_equality_key(&evidence.right_evaluation.expression)
                {
                    return Err("native rational-normalization evidence changed its target".into());
                }
                validate_success_evaluate_obj_result(&evidence.left_evaluation)?;
                validate_success_evaluate_obj_result(&evidence.right_evaluation)?;
                if evidence.left_evaluation.value.normalized_value
                    != evidence.right_evaluation.value.normalized_value
                {
                    return Err(
                        "native rational-normalization evidence retained unequal normal forms"
                            .into(),
                    );
                }
                render_fact(&target, &self.environment_stack)?;
                Ok(Some(
                    "by norm_num [Litex.abs, Litex.min, Litex.max, Litex.tupleDim, Litex.TupleShape.dimension]"
                        .into(),
                ))
            }
            Some(BuiltinRuleEvidence::IntegralPolynomialNormalization(evidence)) => {
                self.construct_lean_integral_polynomial_normalization_from_result(
                    &target,
                    evidence,
                    &builtin.subgoals,
                )?
                .ok_or_else(|| {
                    "integral-polynomial equality lost its native proof constructor".to_string()
                })?;
                let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = &target else {
                    unreachable!()
                };
                let left = render_numeric_obj(&equality.left, &self.environment_stack)?;
                let right = render_numeric_obj(&equality.right, &self.environment_stack)?;
                Ok(Some(format!(
                    "by\n  show {left} = {right}\n  norm_cast <;> ring_nf"
                )))
            }
            Some(BuiltinRuleEvidence::ComplexAlgebraicNormalization(evidence)) => {
                validate_complex_algebraic_normalization_builtin_rule_evidence(&target, evidence)?;
                self.construct_lean_native_algebraic_normalization_from_result(
                    &target,
                    &evidence.expected_nonzero_premises,
                    &builtin.subgoals,
                )
                .map(Some)
            }
            Some(BuiltinRuleEvidence::RationalAlgebraicNormalization(evidence)) => {
                validate_rational_algebraic_normalization_builtin_rule_evidence(&target, evidence)?;
                self.construct_lean_native_algebraic_normalization_from_result(
                    &target,
                    &evidence.expected_nonzero_premises,
                    &builtin.subgoals,
                )
                .map(Some)
            }
            Some(BuiltinRuleEvidence::AbsoluteValue(AbsoluteValueBuiltinRule::Product)) => {
                self.construct_lean_absolute_value_from_result(
                    &target,
                    AbsoluteValueBuiltinRule::Product,
                    &builtin.subgoals,
                )?
                .ok_or_else(|| {
                    "absolute-value product lost its semantic proof constructor".to_string()
                })?;
                Ok(Some("by simp [Litex.abs]".into()))
            }
            _ => Ok(None),
        }
    }

    pub(in super::super) fn retain_native_equality_proof_in_current_environment(
        &mut self,
        fact_id: FactId,
        fact: &Fact,
        proof_expression: String,
    ) -> Result<(), String> {
        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = fact else {
            return Err(format!(
                "native equality proof `{fact_id}` was attached to non-equality `{fact}`"
            ));
        };
        // Native equality certificates are consumed by `rw` inside the
        // compiler's exact numeric target representation.  A source symbol
        // such as an `R+` epsilon is not definitionally its selected
        // `In.rep`; retain the rendered numeric endpoints, while the ordinary
        // Litex proof continues to use heterogeneous `Same` bridges.
        let rendered_left = render_numeric_obj(&equality.left, &self.environment_stack)?;
        let rendered_right = render_numeric_obj(&equality.right, &self.environment_stack)?;
        if let Some(existing) = self.environment_stack.native_equality_proofs.get(&fact_id) {
            if existing.fact.to_string() != fact.to_string()
                || existing.rendered_left != rendered_left
                || existing.rendered_right != rendered_right
                || existing.proof_expression != proof_expression
            {
                return Err(format!(
                    "native equality FactId `{fact_id}` was rebound to another certificate"
                ));
            }
            return Ok(());
        }
        self.environment_stack.native_equality_proofs.insert(
            fact_id,
            NativeEqualityProofBinding {
                fact: fact.clone(),
                rendered_left,
                rendered_right,
                proof_expression,
            },
        );
        Ok(())
    }
}
