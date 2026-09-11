//! Literal Cartesian membership inference declarations.

use super::super::*;

impl StmtResultToLeanCompiler {
    pub(in super::super) fn compile_literal_cartesian_membership_infer_result_as_top_level_declarations(
        &mut self,
        requirement_check: &VerifiedFactResult,
        source_fact: &Fact,
        source_fact_id: FactId,
        infers: &SuccessInferResult,
    ) -> Result<(), String> {
        let SuccessFactProofResult::BuiltinRule(builtin) = requirement_check.proof() else {
            return Err("literal cart membership lost its builtin proof Result".into());
        };
        let Some(BuiltinRuleEvidence::TupleCartesianMembership(evidence)) =
            builtin.evidence.typed()
        else {
            return Err("literal cart membership lost its typed coordinate evidence".into());
        };
        let Some(coordinate_proofs) = self
            .construct_lean_tuple_cartesian_coordinate_proofs_from_result(
                evidence,
                &builtin.subgoals,
            )?
        else {
            return Err("literal cart membership coordinate proof has no direct consumer".into());
        };
        let Fact::AtomicFact(AtomicFact::InFact(source_membership)) = source_fact else {
            return Err("literal cart inference source is not membership".into());
        };
        let (Obj::Tuple(tuple), Obj::Cart(cart)) =
            (&source_membership.element, &source_membership.set)
        else {
            return Err("literal cart inference source retained nonliteral operands".into());
        };
        let coordinate_count = tuple.args.len();
        if coordinate_count != cart.args.len()
            || coordinate_count != coordinate_proofs.len()
            || infers.rule_applications.len() != coordinate_count + 2
        {
            return Err("literal cart inference changed its projection arity".into());
        }

        for (application_index, application) in infers.rule_applications.iter().enumerate() {
            let [premise] = application.premises.as_slice() else {
                return Err(format!(
                    "literal cart projection {application_index} must cite one premise"
                ));
            };
            if premise.fact_id != Some(source_fact_id)
                || premise.fact.to_string() != source_fact.to_string()
            {
                return Err(format!(
                    "literal cart projection {application_index} changed its source FactId"
                ));
            }
            let [conclusion] = application.conclusions.as_slice() else {
                return Err(format!(
                    "literal cart projection {application_index} must retain one conclusion"
                ));
            };
            let conclusion_fact_id = conclusion.fact_id.ok_or_else(|| {
                format!("literal cart projection {application_index} has no FactId")
            })?;
            let (expected_fact, expected_projection, proof) =
                if application_index == 0 {
                    let rendered_tuple =
                        render_obj(&source_membership.element, &self.environment_stack)?;
                    (
                        Fact::from(self.runtime.new_is_tuple_fact(
                            source_membership.element.clone(),
                            default_line_file(),
                        )),
                        CartesianMembershipProjectionKind::TupleShape,
                        format!("Litex.tupleShape_isTuple {rendered_tuple}"),
                    )
                } else if application_index == 1 {
                    (
                    Fact::from(self.runtime.new_equal_fact(
                        TupleDim::new(source_membership.element.clone()).into(),
                        Number::new(coordinate_count.to_string()).into(),
                        default_line_file(),
                    )),
                    CartesianMembershipProjectionKind::TupleDimension,
                    "Litex.Same.ofEq (by norm_num [Litex.tupleDim, Litex.TupleShape.dimension])"
                        .to_string(),
                )
                } else {
                    let coordinate_index = application_index - 2;
                    (
                        evidence.expected_coordinate_memberships[coordinate_index].clone(),
                        CartesianMembershipProjectionKind::Coordinate {
                            index: coordinate_index,
                        },
                        coordinate_proofs[coordinate_index].clone(),
                    )
                };
            let InferRule::CartesianMembershipProjection(rule) = &application.rule else {
                return Err(format!(
                    "literal cart projection {application_index} lost its typed rule"
                ));
            };
            if rule.coordinate_count != coordinate_count
                || rule.projection != expected_projection
                || conclusion.fact.to_string() != expected_fact.to_string()
            {
                return Err(format!(
                    "literal cart projection {application_index} changed its typed target"
                ));
            }

            if self
                .environment_stack
                .fact_propositions
                .contains_key(&conclusion_fact_id)
            {
                resolve_fact_citation(
                    &conclusion_fact_id,
                    &conclusion.fact,
                    &self.environment_stack,
                )?;
                continue;
            }
            if !infer_result_retains_fact_id(infers, &conclusion.fact, conclusion_fact_id) {
                return Err(format!(
                    "literal cart projection {application_index} is absent from its flattened store effects"
                ));
            }
            let proposition = render_fact(&conclusion.fact, &self.environment_stack)?;
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
        validate_flattened_inferred_fact_ids_are_visible(
            infers,
            &self.environment_stack,
            "literal cart membership inference",
        )
    }
}
