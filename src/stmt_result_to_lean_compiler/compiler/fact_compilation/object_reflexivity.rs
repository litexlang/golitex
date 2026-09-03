//! Object reflexivity fact compilation.

use super::super::*;

impl StmtResultToLeanCompiler {
    pub(in super::super) fn compile_object_reflexivity_fact_result(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<bool, String> {
        let Some(verified) = result.verification() else {
            return Ok(false);
        };
        let SuccessFactProofResult::BuiltinRule(builtin) = verified.proof() else {
            return Ok(false);
        };
        let Some(BuiltinRuleEvidence::ObjectReflexivity(evidence)) = builtin.evidence.typed()
        else {
            return Ok(false);
        };
        if !builtin.subgoals.is_empty() {
            return Err("object reflexivity gained unexpected proof children".into());
        }
        let source_fact = result.fact();
        if evidence.expected_target.to_string() != source_fact.to_string() {
            return Err("object-reflexivity evidence changed its target".into());
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = &source_fact else {
            return Err("object-reflexivity evidence targets a non-equality fact".into());
        };
        if obj_equality_key(&equality.left) != obj_equality_key(&equality.right) {
            return Err("object-reflexivity evidence changed its equality endpoints".into());
        }
        validate_atomic_fact_well_definedness_result(&verified.checked, &source_fact)?;
        let proof = format!(
            "Litex.Same.refl {}",
            self.render_object_using_well_definedness_from_fact_result(verified, &equality.left)
                .map_err(|error| format!("rendering reflexive object: {error}"))?
        );
        if !fact_result_contains_inferred_facts(result) {
            self.compile_stored_fact_without_inference(result, proof)
                .map_err(|error| format!("publishing zero-inference reflexivity: {error}"))?;
            return Ok(true);
        }

        let source_fact_id = result
            .store
            .fact_id
            .ok_or_else(|| "object-reflexivity source has no FactId".to_string())?;
        let source_output = result
            .store
            .infers
            .store_fact_outputs
            .iter()
            .find(|output| {
                output.fact_id == Some(source_fact_id)
                    && output.itself_and_why_itself_is_stored.0.to_string()
                        == source_fact.to_string()
            })
            .ok_or_else(|| {
                "object-reflexivity typed inference lost its source store output".to_string()
            })?;
        if source_output.inferred_facts.len() != source_output.inferred_fact_ids.len() {
            return Err("object-reflexivity source store changed its inferred FactId arity".into());
        }
        let proposition = render_fact(&source_fact, &self.environment_stack)
            .map_err(|error| format!("rendering inferred reflexivity proposition: {error}"))?;
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
        self.compile_tuple_equality_shape_infer_result(
            &source_fact,
            source_fact_id,
            &result.store.infers,
        )?;
        Ok(true)
    }
}
