//! Integer-range sum pointwise order.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// `Combine`: preserve the verifier-owned pointwise binder as a compiled
    /// local theorem, then feed it to the reviewed native `Z`-sum monotonicity
    /// adapter. Endpoint equality Results are checked and rendered too. The
    /// first compiler tranche intentionally accepts only structurally
    /// identical endpoints and exact unary `Z -> Z` sums; semantic endpoint
    /// transport requires a separate reviewed `Same` elimination route.
    pub(in super::super) fn construct_lean_integer_range_sum_pointwise_order_from_result(
        &mut self,
        target: &Fact,
        evidence: &IntegerRangeSumPointwiseOrderBuiltinRuleEvidence,
        subgoals: &[VerifyFactResult],
    ) -> Result<Option<String>, String> {
        if evidence.expected_target.to_string() != target.to_string() {
            return Err("integer-range sum order evidence changed its target".into());
        }
        let Fact::AtomicFact(AtomicFact::LessEqualFact(order)) = target else {
            return Err("integer-range sum order evidence targets a non-order fact".into());
        };
        let (Obj::Sum(left_sum), Obj::Sum(right_sum)) = (&order.left, &order.right) else {
            return Err("integer-range sum order evidence retained non-sum operands".into());
        };
        if obj_equality_key(left_sum.start.as_ref()) != obj_equality_key(right_sum.start.as_ref())
            || obj_equality_key(left_sum.end.as_ref()) != obj_equality_key(right_sum.end.as_ref())
        {
            return Err(
                "integer-range sum compiler currently requires structurally identical endpoints"
                    .into(),
            );
        }
        let [start_result, end_result, pointwise_result] = subgoals else {
            return Err(
                "integer-range sum order evidence requires start, end, and pointwise children"
                    .into(),
            );
        };
        let expected = [
            &evidence.expected_start_equality,
            &evidence.expected_end_equality,
            &evidence.expected_pointwise,
        ];
        let factual_children = [start_result, end_result, pointwise_result]
            .into_iter()
            .zip(expected)
            .enumerate()
            .map(|(index, (result, expected))| {
                let child = result.verified().ok_or_else(|| {
                    format!("integer-range sum order child {index} is not factual")
                })?;
                if child.fact().to_string() != expected.to_string() {
                    return Err(format!(
                        "integer-range sum order child {index} changed its proposition"
                    ));
                }
                Ok(child)
            })
            .collect::<Result<Vec<_>, String>>()?;
        let start_proof = self
            .construct_lean_proof_from_direct_fact_result_using_its_well_definedness(
                factual_children[0],
            )?
            .ok_or_else(|| {
                "integer-range sum start equality has no direct proof consumer".to_string()
            })?;
        let end_proof = self
            .construct_lean_proof_from_direct_fact_result_using_its_well_definedness(
                factual_children[1],
            )?
            .ok_or_else(|| {
                "integer-range sum end equality has no direct proof consumer".to_string()
            })?;

        let Fact::ForallFact(pointwise_forall) = &evidence.expected_pointwise else {
            return Err("integer-range sum pointwise child is not a forall fact".into());
        };
        let pointwise_parameters = pointwise_forall
            .typed_parameters
            .collect_param_bindings_with_types();
        if !matches!(
            pointwise_parameters.as_slice(),
            [(_, ParamType::Obj(Obj::StandardSet(StandardSet::Z)))]
        ) || pointwise_forall.dom_facts.len() != 2
            || pointwise_forall.then_facts.len() != 1
        {
            return Err(
                "integer-range sum compiler requires one Z binder, two range premises, and one conclusion"
                    .into(),
            );
        }
        let pointwise_declaration_index = self.next_fact_name_index;
        if !self.compile_direct_forall_verify_result(factual_children[2])? {
            return Err(
                "integer-range sum pointwise ForallProof has no direct compiler consumer".into(),
            );
        }
        if self.next_fact_name_index != pointwise_declaration_index + 1 {
            return Err(
                "integer-range sum pointwise Result published an unexpected theorem count".into(),
            );
        }
        let pointwise_theorem = format!("__fact{pointwise_declaration_index}");

        let left_function = LeanTargetObjectRepresentation::lower(left_sum.func.as_ref())?;
        let right_function = LeanTargetObjectRepresentation::lower(right_sum.func.as_ref())?;
        let (left_function, _) =
            render_exact_unary_integer_function(&left_function, &self.environment_stack)?;
        let (right_function, _) =
            render_exact_unary_integer_function(&right_function, &self.environment_stack)?;
        let start = render_integer_obj(left_sum.start.as_ref(), &self.environment_stack)?;
        let end = render_integer_obj(left_sum.end.as_ref(), &self.environment_stack)?;
        let start_proposition =
            render_fact(&evidence.expected_start_equality, &self.environment_stack)?;
        let end_proposition =
            render_fact(&evidence.expected_end_equality, &self.environment_stack)?;

        Ok(Some(format!(
            "(by\n  have __sum_start_equal : {start_proposition} := {start_proof}\n  have __sum_end_equal : {end_proposition} := {end_proof}\n  exact Litex.Rules.integerRangeSumLeOwn {start} {end} {left_function} {right_function} (fun __index __lower __upper => by\n    simpa only [Litex.Fn.callOwn] using ({pointwise_theorem} __index (by simpa using __lower) (by simpa using __upper)))\n)"
        )))
    }
}
