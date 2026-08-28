//! Tuple reconstruction from Cartesian membership.

use crate::prelude::*;
use crate::verification::verify_equality_by_builtin_rules::objs_match_for_pattern;

impl Runtime {
    // A member of a literal Cartesian product is the tuple of its own
    // coordinates. This is intentionally narrower than general tuple
    // extensionality: it uses one exact known cart-membership fact and only
    // accepts the canonical projection list `(p[1], ..., p[n])`.
    pub(super) fn try_verify_tuple_reconstruction_from_known_cart_membership(
        &mut self,
        equal_fact: &EqualFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let (target, tuple) = match (left, right) {
            (target, Obj::Tuple(tuple)) if !matches!(target, Obj::Tuple(_)) => (target, tuple),
            (Obj::Tuple(tuple), target) if !matches!(target, Obj::Tuple(_)) => (target, tuple),
            _ => return Ok(None),
        };

        for (index, component) in tuple.args.iter().enumerate() {
            let expected: Obj =
                ObjAtIndex::new(target.clone(), Number::new((index + 1).to_string()).into()).into();
            if !objs_match_for_pattern(component.as_ref(), &expected) {
                return Ok(None);
            }
        }

        for owner_set in self.known_sets_containing_obj(target) {
            let Obj::Cart(cart) = &owner_set else {
                continue;
            };
            if cart.args.len() != tuple.args.len() {
                continue;
            }
            let membership: AtomicFact =
                InFact::new(target.clone(), owner_set, line_file.clone()).into();
            let membership_result =
                self.verify_non_equational_atomic_fact_with_known_atomic_facts(&membership)?;
            if !membership_result.is_success() {
                continue;
            }
            return Ok(Some(
                SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    equal_fact.clone().into(),
                    "tuple reconstruction from known Cartesian-product membership".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryVerifyTupleReconstructionFromKnownCartMembership),
                    vec![membership_result],
                )
                .into(),
            ));
        }

        Ok(None)
    }
}
