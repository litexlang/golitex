//! Tuple Cartesian membership.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// `Combine`: validate the literal tuple/cart arity and exact ordered
    /// coordinate memberships retained by the verifier, then fold their
    /// proofs into the target's typed `HCons`/`cartCons` spine.
    pub(in super::super) fn construct_lean_tuple_cartesian_membership_from_result(
        &mut self,
        target: &Fact,
        evidence: &TupleCartesianMembershipBuiltinRuleEvidence,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        if evidence.expected_target.to_string() != target.to_string() {
            return Err("tuple/cart membership evidence changed its target".into());
        }
        let Fact::AtomicFact(AtomicFact::InFact(membership)) = target else {
            return Err("tuple/cart membership evidence targets a non-membership".into());
        };
        let (Obj::Tuple(tuple), Obj::Cart(cart)) = (&membership.element, &membership.set) else {
            return Err("tuple/cart membership evidence retained nonliteral operands".into());
        };
        if tuple.args.len() != cart.args.len()
            || tuple.args.len() != evidence.expected_coordinate_memberships.len()
            || tuple.args.len() < 2
        {
            return Err("tuple/cart membership evidence changed its coordinate arity".into());
        }
        for (index, ((element, set), expected)) in tuple
            .args
            .iter()
            .zip(cart.args.iter())
            .zip(evidence.expected_coordinate_memberships.iter())
            .enumerate()
        {
            let Fact::AtomicFact(AtomicFact::InFact(expected_membership)) = expected else {
                return Err(format!(
                    "tuple/cart coordinate {index} retained a non-membership premise"
                ));
            };
            if obj_equality_key(element.as_ref()) != obj_equality_key(&expected_membership.element)
                || obj_equality_key(set.as_ref()) != obj_equality_key(&expected_membership.set)
            {
                return Err(format!(
                    "tuple/cart coordinate {index} changed its element or factor"
                ));
            }
        }

        let Some(coordinate_proofs) =
            self.construct_lean_tuple_cartesian_coordinate_proofs_from_result(evidence, subgoals)?
        else {
            return Ok(None);
        };
        let mut proof = "Litex.Rules.inCartNil".to_string();
        for coordinate_proof in coordinate_proofs.iter().rev() {
            proof = format!("Litex.Rules.inCartCons ({coordinate_proof}) ({proof})");
        }
        Ok(Some(proof))
    }
}
