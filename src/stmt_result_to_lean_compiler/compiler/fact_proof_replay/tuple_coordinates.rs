//! Tuple Cartesian coordinate proofs.

use super::super::*;

impl StmtResultToLeanCompiler {
    pub(in super::super) fn construct_lean_tuple_cartesian_coordinate_proofs_from_result(
        &mut self,
        evidence: &TupleCartesianMembershipBuiltinRuleEvidence,
        subgoals: &[VerifyFactResult],
    ) -> Result<Option<Vec<String>>, String> {
        let [child] = subgoals else {
            return Err(
                "tuple/cart membership requires one retained coordinate-premise Result".into(),
            );
        };
        let child = child
            .verified()
            .ok_or_else(|| "tuple/cart coordinate premise is not factual".to_string())?;
        let child_fact = child.fact();
        let components = conjunction_components(&child_fact)?;
        if components.len() != evidence.expected_coordinate_memberships.len()
            || components
                .iter()
                .zip(evidence.expected_coordinate_memberships.iter())
                .any(|(retained, expected)| retained.to_string() != expected.to_string())
        {
            return Err("tuple/cart coordinate child changed its ordered conjunction".into());
        }
        let Some(conjunction_proof) =
            self.construct_lean_proof_from_direct_fact_result_using_its_well_definedness(child)?
        else {
            return Ok(None);
        };
        let conjunction_type =
            self.render_fact_using_well_definedness_result(&child.checked, &child_fact)?;
        let typed_conjunction_proof = format!("({conjunction_proof} : {conjunction_type})");
        let mut coordinate_proofs = Vec::with_capacity(components.len());
        for index in 0..components.len() {
            coordinate_proofs.push(conjunction_projection(
                &typed_conjunction_proof,
                index,
                components.len(),
            )?);
        }
        Ok(Some(coordinate_proofs))
    }
}
