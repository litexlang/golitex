//! Tuple equality shape inference.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// `Combine`: publish the two exact consequences retained when equality
    /// exposes a literal tuple shape. The current Lean representation can
    /// replay this rule when the selected target is the same concrete tuple;
    /// other heterogeneous transports remain fail-closed until the Lean ABI
    /// has an explicit tuple-shape transport theorem.
    pub(in super::super) fn compile_tuple_equality_shape_infer_result(
        &mut self,
        source_fact: &Fact,
        source_fact_id: FactId,
        infers: &SuccessInferResult,
    ) -> Result<(), String> {
        validate_typed_infer_result_identity_completeness(
            infers,
            "tuple-equality shape inference",
        )?;
        let [application] = infers.rule_applications.as_slice() else {
            return Err("tuple equality must retain exactly one typed shape inference".into());
        };
        let InferRule::TupleEqualityWithKnownTupleImpliesTupleShape(rule) = &application.rule
        else {
            return Err("object reflexivity retained a non-tuple inference rule".into());
        };
        let [premise] = application.premises.as_slice() else {
            return Err("tuple-shape inference must cite one equality premise".into());
        };
        if premise.fact_id != Some(source_fact_id)
            || premise.fact.to_string() != source_fact.to_string()
        {
            return Err("tuple-shape inference changed its source equality FactId".into());
        }
        let equality_proof =
            resolve_fact_citation(&source_fact_id, source_fact, &self.environment_stack)?;
        if equality_proof.is_empty() {
            return Err("tuple-shape inference resolved an empty equality proof".into());
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = source_fact else {
            return Err("tuple-shape inference source is not equality".into());
        };
        let (known_object, target_object) = match rule.known_side {
            KnownTupleEqualitySide::Left => (&equality.left, &equality.right),
            KnownTupleEqualitySide::Right => (&equality.right, &equality.left),
        };
        let Obj::Tuple(known_tuple) = known_object else {
            return Err("tuple-shape inference selected a non-tuple known side".into());
        };
        if known_tuple.args.len() != rule.tuple_length || rule.tuple_length < 2 {
            return Err("tuple-shape inference changed its retained tuple length".into());
        }
        if obj_equality_key(known_object) != obj_equality_key(target_object) {
            return Err(
                "tuple-shape inference requires an explicit Lean transport theorem for a distinct target object"
                    .into(),
            );
        }

        let expected_tuple_fact: Fact =
            IsTupleFact::new(target_object.clone(), equality.line_file.clone()).into();
        let expected_dimension_fact: Fact = EqualFact::new(
            TupleDim::new(target_object.clone()).into(),
            Number::new(rule.tuple_length.to_string()).into(),
            equality.line_file.clone(),
        )
        .into();
        let expected = [
            (expected_tuple_fact, "⟨inferInstance⟩".to_string()),
            (
                expected_dimension_fact,
                "Litex.Same.ofEq (by norm_num [Litex.tupleDim, Litex.TupleShape.dimension])"
                    .to_string(),
            ),
        ];
        if application.conclusions.len() != expected.len() {
            return Err("tuple-shape inference changed its two-conclusion contract".into());
        }

        for (conclusion, (expected_fact, proof)) in
            application.conclusions.iter().zip(expected.into_iter())
        {
            if conclusion.fact.to_string() != expected_fact.to_string() {
                return Err("tuple-shape inference changed an ordered conclusion".into());
            }
            let fact_id = conclusion
                .fact_id
                .ok_or_else(|| "tuple-shape conclusion has no FactId".to_string())?;
            let recursively_stored = conclusion.infers.store_fact_outputs.iter().any(|output| {
                output.fact_id == Some(fact_id)
                    && output.itself_and_why_itself_is_stored.0.to_string()
                        == conclusion.fact.to_string()
            });
            if !recursively_stored {
                return Err("tuple-shape conclusion lost its recursive store Result".into());
            }
            let advertised = infers.store_fact_outputs.iter().any(|output| {
                output
                    .inferred_facts
                    .iter()
                    .zip(output.inferred_fact_ids.iter())
                    .any(|(fact, id)| {
                        fact.to_string() == conclusion.fact.to_string() && *id == Some(fact_id)
                    })
                    || (output.fact_id == Some(fact_id)
                        && output.itself_and_why_itself_is_stored.0.to_string()
                            == conclusion.fact.to_string())
            });
            if !advertised {
                return Err("tuple-shape conclusion is absent from ordered store effects".into());
            }
            let proposition = render_fact(&conclusion.fact, &self.environment_stack)?;
            let theorem_name = format!("__fact{}", self.next_fact_name_index);
            self.declarations.push(format!(
                "theorem {theorem_name} : {proposition} := by\n  exact {proof}"
            ));
            self.environment_stack
                .fact_names
                .insert(fact_id, theorem_name);
            self.environment_stack
                .fact_propositions
                .insert(fact_id, conclusion.fact.clone());
            self.next_fact_name_index += 1;
        }
        validate_flattened_inferred_fact_ids_are_visible(
            infers,
            &self.environment_stack,
            "tuple-equality shape inference",
        )
    }
}
