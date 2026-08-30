//! Rational, complex, and native algebraic normalization proofs.

use super::super::*;

pub(in super::super) fn fact_proof_is_not_equal_from_strict_order(
    proof: &SuccessFactProofResult,
) -> bool {
    match proof {
        SuccessFactProofResult::BuiltinRule(builtin) => matches!(
            builtin.evidence.typed(),
            Some(BuiltinRuleEvidence::NotEqualFromStrictOrder)
        ),
        SuccessFactProofResult::Reuse(reuse) => {
            fact_proof_is_not_equal_from_strict_order(reuse.source.proof())
        }
        _ => false,
    }
}
impl StmtResultToLeanCompiler {
    pub(in super::super) fn compile_rational_normalization_fact_result(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<bool, String> {
        let SuccessFactProofResult::BuiltinRule(builtin) = result.proof() else {
            return Ok(false);
        };
        let Some(BuiltinRuleEvidence::RationalNormalization(evidence)) = builtin.evidence.typed()
        else {
            return Ok(false);
        };
        if fact_result_contains_inferred_facts(result) {
            return Ok(false);
        }
        if !builtin.subgoals.is_empty() {
            return Err("rational normalization gained unexpected proof children".into());
        }
        let source_fact = result.fact();
        if evidence.expected_target.to_string() != source_fact.to_string() {
            return Err("rational-normalization evidence changed its target".into());
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = &source_fact else {
            return Err("rational-normalization evidence targets a non-equality fact".into());
        };
        if obj_equality_key(&equality.left)
            != obj_equality_key(&evidence.left_evaluation.expression)
            || obj_equality_key(&equality.right)
                != obj_equality_key(&evidence.right_evaluation.expression)
        {
            return Err("rational-normalization evidence changed an equality endpoint".into());
        }
        validate_success_evaluate_obj_result(&evidence.left_evaluation)?;
        validate_success_evaluate_obj_result(&evidence.right_evaluation)?;
        if evidence.left_evaluation.value.normalized_value
            != evidence.right_evaluation.value.normalized_value
        {
            return Err("rational-normalization evidence retained unequal normal forms".into());
        }
        validate_atomic_fact_well_definedness_result(&result.well_definedness, &source_fact)?;
        self.render_object_using_well_definedness_from_fact_result(result, &equality.left)?;
        self.render_object_using_well_definedness_from_fact_result(result, &equality.right)?;
        self.compile_stored_fact_without_inference(
            result,
            "Litex.Same.ofEq (by norm_num [Litex.abs, Litex.min, Litex.max, Litex.tupleDim, Litex.TupleShape.dimension])"
                .to_string(),
        )?;
        Ok(true)
    }

    pub(in super::super) fn compile_complex_algebraic_normalization_fact_result(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<bool, String> {
        let SuccessFactProofResult::BuiltinRule(builtin) = result.proof() else {
            return Ok(false);
        };
        let Some(BuiltinRuleEvidence::ComplexAlgebraicNormalization(evidence)) =
            builtin.evidence.typed()
        else {
            return Ok(false);
        };
        if fact_result_contains_inferred_facts(result) {
            return Ok(false);
        }
        let source_fact = result.fact();
        let Some(proof) = self.construct_lean_complex_algebraic_normalization_from_result(
            &source_fact,
            evidence,
            &builtin.subgoals,
        )?
        else {
            return Ok(false);
        };
        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = &source_fact else {
            unreachable!();
        };
        validate_atomic_fact_well_definedness_result(&result.well_definedness, &source_fact)?;
        self.render_object_using_well_definedness_from_fact_result(result, &equality.left)?;
        self.render_object_using_well_definedness_from_fact_result(result, &equality.right)?;
        self.compile_stored_fact_without_inference(result, proof)?;
        Ok(true)
    }

    pub(in super::super) fn compile_rational_algebraic_normalization_fact_result(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<bool, String> {
        let SuccessFactProofResult::BuiltinRule(builtin) = result.proof() else {
            return Ok(false);
        };
        let Some(BuiltinRuleEvidence::RationalAlgebraicNormalization(evidence)) =
            builtin.evidence.typed()
        else {
            return Ok(false);
        };
        if fact_result_contains_inferred_facts(result) {
            return Ok(false);
        }
        let source_fact = result.fact();
        let Some(proof) = self.construct_lean_rational_algebraic_normalization_from_result(
            &source_fact,
            evidence,
            &builtin.subgoals,
        )?
        else {
            return Ok(false);
        };
        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = &source_fact else {
            unreachable!();
        };
        validate_atomic_fact_well_definedness_result(&result.well_definedness, &source_fact)?;
        self.render_object_using_well_definedness_from_fact_result(result, &equality.left)?;
        self.render_object_using_well_definedness_from_fact_result(result, &equality.right)?;
        self.compile_stored_fact_without_inference(result, proof)?;
        Ok(true)
    }

    /// Compile the exact nonzero child Results retained by complex calculate,
    /// bridge each semantic `!= 0` proof to native Complex nonzero, and feed
    /// only those named proofs to the fixed field/ring adapter.
    pub(in super::super) fn construct_lean_complex_algebraic_normalization_from_result(
        &mut self,
        target: &Fact,
        evidence: &ComplexAlgebraicNormalizationBuiltinRuleEvidence,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        validate_complex_algebraic_normalization_builtin_rule_evidence(target, evidence)?;
        self.construct_lean_algebraic_normalization_from_result(
            target,
            &evidence.expected_nonzero_premises,
            subgoals,
        )
    }

    pub(in super::super) fn construct_lean_rational_algebraic_normalization_from_result(
        &mut self,
        target: &Fact,
        evidence: &RationalAlgebraicNormalizationBuiltinRuleEvidence,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        validate_rational_algebraic_normalization_builtin_rule_evidence(target, evidence)?;
        self.construct_lean_algebraic_normalization_from_result(
            target,
            &evidence.expected_nonzero_premises,
            subgoals,
        )
    }

    pub(in super::super) fn construct_lean_algebraic_normalization_from_result(
        &mut self,
        target: &Fact,
        expected_nonzero_premises: &[Fact],
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        let native = self.construct_lean_native_algebraic_normalization_from_result(
            target,
            expected_nonzero_premises,
            subgoals,
        )?;
        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = target else {
            unreachable!("algebraic normalization validator requires equality")
        };
        let source_to_numeric = |object: &Obj| -> Result<(String, String, String), String> {
            let source = render_obj(object, &self.environment_stack)?;
            let numeric = render_numeric_obj(object, &self.environment_stack)?;
            if source == numeric {
                return Ok((
                    source.clone(),
                    numeric,
                    format!("Litex.Same.refl ({source})"),
                ));
            }
            let LeanTargetObjectRepresentation::Symbol { symbol_id, .. } =
                LeanTargetObjectRepresentation::lower(object)?
            else {
                return Err(format!(
                    "algebraic normalization changed non-symbol endpoint `{source}` to `{numeric}` without a structural Same bridge"
                ));
            };
            let bridge = self
                .environment_stack
                .numeric_representation_equalities
                .get(&symbol_id)
                .cloned()
                .ok_or_else(|| {
                    format!(
                        "algebraic normalization endpoint `{source}` has no exact numeric Same bridge"
                    )
                })?;
            Ok((source, numeric, bridge))
        };
        let (_source_left, numeric_left, left_bridge) = source_to_numeric(&equality.left)?;
        let (_source_right, numeric_right, right_bridge) = source_to_numeric(&equality.right)?;
        let native = format!("(show {numeric_left} = {numeric_right} from {native})");
        Ok(Some(format!(
            "Litex.Same.trans ({left_bridge}) (Litex.Same.trans (Litex.Same.ofEq ({native})) (Litex.Same.symm ({right_bridge})))"
        )))
    }

    pub(in super::super) fn construct_lean_native_algebraic_normalization_from_result(
        &mut self,
        target: &Fact,
        expected_nonzero_premises: &[Fact],
        subgoals: &[StmtResult],
    ) -> Result<String, String> {
        let Fact::AtomicFact(AtomicFact::EqualFact(_)) = target else {
            unreachable!("complex normalization validator requires an equality")
        };
        if subgoals.len() != expected_nonzero_premises.len() {
            return Err(
                "complex-algebraic-normalization proof lost an ordered nonzero child Result".into(),
            );
        }

        let mut declarations = Vec::with_capacity(subgoals.len());
        let mut native_nonzero_names = Vec::with_capacity(subgoals.len());
        for (index, (expected, subgoal)) in expected_nonzero_premises
            .iter()
            .zip(subgoals.iter())
            .enumerate()
        {
            let subgoal = subgoal
                .factual_success()
                .ok_or_else(|| format!("complex nonzero child {index} is not a factual Result"))?;
            if subgoal.fact().to_string() != expected.to_string()
                || subgoal.store.fact.to_string() != expected.to_string()
            {
                return Err(format!(
                    "complex nonzero child {index} changed its exact premise"
                ));
            }
            let Fact::AtomicFact(AtomicFact::NotEqualFact(nonzero)) = expected else {
                return Err(format!(
                    "complex nonzero premise {index} is not a disequality"
                ));
            };
            if !matches!(
                &nonzero.right,
                Obj::Number(number) if number.normalized_value == "0"
            ) {
                return Err(format!(
                    "complex nonzero premise {index} changed its zero endpoint"
                ));
            }
            let left = render_numeric_obj(&nonzero.left, &self.environment_stack)?;
            let right = render_numeric_obj(&nonzero.right, &self.environment_stack)?;
            let semantic_proposition = render_fact(expected, &self.environment_stack)?;
            let name = format!("__calculate_nonzero{}", index + 1);
            let native_proof = match self.construct_lean_proof_from_direct_fact_result(subgoal) {
                Ok(Some(semantic_proof)) => format!(
                    "by\n    intro __native_eq\n    exact (show {semantic_proposition} from {semantic_proof}) (Litex.Same.ofEq __native_eq)"
                ),
                Ok(None) => {
                    // A few closed native constants still have legacy
                    // label-only nonzero Results. The target is independently
                    // checked here by Lean; symbolic premises never use this
                    // fallback because `norm_num` cannot manufacture them.
                    "by\n    norm_num [Complex.I_mul_I]".to_string()
                }
                Err(_error)
                    if fact_proof_is_not_equal_from_strict_order(subgoal.proof()) =>
                {
                    self.construct_native_nonzero_from_strict_order_result(
                        subgoal,
                        &nonzero.left,
                    )?
                }
                Err(error) => return Err(error),
            };
            declarations.push(format!(
                "  have {name} : {left} ≠ {right} := {native_proof}"
            ));
            native_nonzero_names.push(name);
        }

        let mut proof = "by\n".to_string();
        if !declarations.is_empty() {
            proof.push_str(&declarations.join("\n"));
            proof.push('\n');
        }
        if native_nonzero_names.is_empty() {
            proof.push_str("  ring_nf <;> norm_num [Complex.I_mul_I] <;> ring");
        } else {
            proof.push_str(&format!(
                "  field_simp [{}] <;> ring_nf <;> norm_num [Complex.I_mul_I] <;> ring",
                native_nonzero_names.join(", ")
            ));
        }
        Ok(format!("({proof})"))
    }

    pub(in super::super) fn construct_native_nonzero_from_strict_order_result(
        &mut self,
        result: &SuccessFactStmtResult,
        expected_object: &Obj,
    ) -> Result<String, String> {
        let mut proof = result.proof();
        while let SuccessFactProofResult::Reuse(reuse) = proof {
            proof = reuse.source.proof();
        }
        let SuccessFactProofResult::BuiltinRule(builtin) = proof else {
            return Err("strict-order nonzero Result changed its proof kind".into());
        };
        if !matches!(
            builtin.evidence.typed(),
            Some(BuiltinRuleEvidence::NotEqualFromStrictOrder)
        ) {
            return Err("native nonzero extraction requires strict-order evidence".into());
        }
        let mut selected = None;
        for child in &builtin.subgoals {
            let Some(child) = child.factual_success() else {
                return Err("strict-order nonzero evidence retained a non-factual child".into());
            };
            if let Ok((left, right, true)) = order_relation_parts(&child.fact()) {
                let endpoints_match = (is_literal_zero(left)
                    && obj_equality_key(right) == obj_equality_key(expected_object))
                    || (obj_equality_key(left) == obj_equality_key(expected_object)
                        && is_literal_zero(right));
                if endpoints_match {
                    if selected.is_some() {
                        return Err(
                            "strict-order nonzero evidence retained multiple matching orders"
                                .into(),
                        );
                    }
                    selected = Some(child);
                    continue;
                }
            }
            let child_fact = child.fact();
            let Ok((_, set)) = membership_parts(&child_fact) else {
                return Err(
                    "strict-order nonzero evidence retained an unrelated child fact".into(),
                );
            };
            if !matches!(set, Obj::StandardSet(StandardSet::R)) {
                return Err(
                    "strict-order nonzero evidence changed its real-carrier premise".into(),
                );
            }
        }
        let selected = selected.ok_or_else(|| {
            "strict-order nonzero evidence lost its strict-order child".to_string()
        })?;
        // Consume the retained strict-order child as authority for this
        // nonzero obligation, but prove the exact target term in Lean's
        // native real representation. This avoids treating Litex's
        // representative-owning `Positive` wrapper as definitionally equal
        // to a `Litex.Lt` proposition.
        self.construct_lean_proof_from_direct_fact_result(selected)?
            .ok_or_else(|| {
                "strict-order nonzero child has no direct Lean proof constructor".to_string()
            })?;
        let native_real = render_real_target_object_representation(
            &LeanTargetObjectRepresentation::lower(expected_object)?,
            &self.environment_stack,
        )?;
        Ok(format!(
            "by\n    intro __native_eq\n    have __native_re := congrArg Complex.re __native_eq\n    simp [Litex.abs, ← Complex.ofReal_add, ← Complex.ofReal_sub, ← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs] at __native_re\n    have __native_nonzero : ({native_real} : ℝ) ≠ 0 := by positivity\n    exact __native_nonzero __native_re"
        ))
    }
}
