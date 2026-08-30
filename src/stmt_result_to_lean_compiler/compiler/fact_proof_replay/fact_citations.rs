//! Stored fact citations and equality transport.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// `Wrap`: cite the exact source FactId, then apply the verifier-retained
    /// equality edges in their recorded order. The Result owns both the
    /// orientation and the equality FactId of every edge; the compiler does
    /// not search the current environment for a proposition-shaped match.
    pub(in super::super) fn construct_lean_fact_citation_with_equality_transport_from_result(
        &self,
        target: &Fact,
        cited_statement: &Stmt,
        source_fact_id: Option<FactId>,
        equality_transport: Option<&EqualityTransportEvidence>,
    ) -> Result<Option<String>, String> {
        let Stmt::Fact(source_fact) = cited_statement else {
            return Ok(None);
        };
        let Some(source_fact_id) = source_fact_id else {
            return Ok(None);
        };
        let mut proof =
            resolve_fact_citation(&source_fact_id, source_fact, &self.environment_stack)?;
        if equality_transport_has_no_steps(equality_transport) {
            if facts_are_comparison_notation_duals(source_fact, target)
                && render_fact(source_fact, &self.environment_stack)?
                    == render_fact(target, &self.environment_stack)?
            {
                return Ok(Some(proof));
            }
            return Ok(Some(resolve_fact_citation(
                &source_fact_id,
                target,
                &self.environment_stack,
            )?));
        }

        let (source_element, source_set) = membership_parts(source_fact)?;
        let mut current_element = source_element.clone();
        let (target_element, target_set) = membership_parts(target)?;
        if obj_equality_key(source_set) != obj_equality_key(target_set) {
            return Err("equality transport changed the membership set".into());
        }
        let rendered_set = render_obj(target_set, &self.environment_stack)?;
        for (step_index, step) in equality_transport
            .expect("nonempty transport checked above")
            .steps
            .iter()
            .enumerate()
        {
            if obj_equality_key(&current_element) != obj_equality_key(&step.from) {
                return Err(format!(
                    "equality transport step {step_index} does not start at the current membership element"
                ));
            }
            let left_key = obj_equality_key(&step.equality.left);
            let right_key = obj_equality_key(&step.equality.right);
            let from_key = obj_equality_key(&step.from);
            let to_key = obj_equality_key(&step.to);
            let direction = if from_key == left_key && to_key == right_key {
                "mp"
            } else if from_key == right_key && to_key == left_key {
                "mpr"
            } else {
                return Err(format!(
                    "equality transport step {step_index} is not oriented by its retained equality"
                ));
            };
            let equality_fact: Fact = AtomicFact::EqualFact(step.equality.clone()).into();
            let equality_fact_id = step.equality_fact_id;
            let equality_proof =
                resolve_fact_citation(&equality_fact_id, &equality_fact, &self.environment_stack)?;
            proof =
                format!("(Litex.In.congr ({equality_proof}) {rendered_set}).{direction} ({proof})");
            current_element = step.to.clone();
        }
        if obj_equality_key(&current_element) != obj_equality_key(target_element) {
            return Err("equality transport did not end at the target membership element".into());
        }
        Ok(Some(proof))
    }

    pub(in super::super) fn construct_lean_stored_fact_citation_proof_from_result(
        &self,
        target: &Fact,
        citation: &SuccessStoredFactCitationProofResult,
    ) -> Result<Option<String>, String> {
        self.construct_lean_fact_citation_with_equality_transport_from_result(
            target,
            &citation.source_fact.clone().into_stmt(),
            Some(citation.source_fact_id),
            None,
        )
    }
}
