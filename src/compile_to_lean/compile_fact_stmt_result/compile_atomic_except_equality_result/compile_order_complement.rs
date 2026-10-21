use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::{
    not_greater::NotGreaterFactSearchProofByBuiltinRule,
    not_less::NotLessFactSearchProofByBuiltinRule,
    not_greater_equal::NotGreaterEqualFactSearchProofByBuiltinRule,
    not_less_equal::NotLessEqualFactSearchProofByBuiltinRule,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::order_complement::FromKnownOrderComplementBuiltinRuleProof;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_order_complement(
        &self,
        goal: &AtomicFact,
        proof: &FromKnownOrderComplementBuiltinRuleProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (left_obj, right_obj, reversed, strict, premise_matches) =
            match (goal, &proof.premise_proof.fact) {
                (AtomicFact::LessEqualFact(goal), AtomicFact::NotGreaterFact(premise)) => (
                    &goal.left,
                    &goal.right,
                    false,
                    false,
                    premise.left.ir() == goal.left.ir() && premise.right.ir() == goal.right.ir(),
                ),
                (AtomicFact::GreaterEqualFact(goal), AtomicFact::NotLessFact(premise)) => (
                    &goal.left,
                    &goal.right,
                    true,
                    false,
                    premise.left.ir() == goal.left.ir() && premise.right.ir() == goal.right.ir(),
                ),
                (AtomicFact::LessFact(goal), AtomicFact::NotGreaterEqualFact(premise)) => (
                    &goal.left,
                    &goal.right,
                    false,
                    true,
                    premise.left.ir() == goal.left.ir() && premise.right.ir() == goal.right.ir(),
                ),
                (AtomicFact::GreaterFact(goal), AtomicFact::NotLessEqualFact(premise)) => (
                    &goal.left,
                    &goal.right,
                    true,
                    true,
                    premise.left.ir() == goal.left.ir() && premise.right.ir() == goal.right.ir(),
                ),
                _ => return Err(LeanCompileError::unsupported("Order/Complement")),
            };
        if !premise_matches || proof.real_carrier_proofs.len() != 2 {
            return Err(LeanCompileError::unsupported("Order/ComplementSubjects"));
        }
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(citation) =
            proof.premise_proof.searched_proof.as_ref()
        else {
            return Err(LeanCompileError::unsupported("Order/KnownPremiseRoute"));
        };
        let premise = self.compile_known_atomic(citation, &proof.premise_proof.fact, position)?;
        let mut real = Vec::new();
        for (index, (object, result)) in [left_obj, right_obj]
            .into_iter()
            .zip(&proof.real_carrier_proofs)
            .enumerate()
        {
            if membership_subject(&source_subject(result)?, object)? != StandardSet::R {
                return Err(LeanCompileError::unsupported("Order/ComplementRealCarrier"));
            }
            real.push(
                self.compile_verify(result, &position.atomic_search_prior(index)?)?
                    .1,
            );
        }
        let complete = position.atomic_search_prior(2)?;
        let left = self.compile_object_reference(left_obj, &complete)?;
        let right = self.compile_object_reference(right_obj, &complete)?;
        let (left, right, left_real, right_real) = if reversed {
            (right, left, &real[1], &real[0])
        } else {
            (left, right, &real[0], &real[1])
        };
        let (goal_bridge, complement_bridge, law) = if strict {
            ("lt_iff_asReal", "le_iff_asReal", "lt_of_not_ge")
        } else {
            ("le_iff_asReal", "lt_iff_asReal", "le_of_not_gt")
        };
        Ok(format!("(by\n  let _left := {left}\n  let _right := {right}\n  have _leftReal : Litex.In _left Litex.R := {left_real}\n  have _rightReal : Litex.In _right Litex.R := {right_real}\n  exact (Litex.NativeBridge.{goal_bridge} _left _right _leftReal _rightReal).mpr ({law} (fun _opposite => ({premise}) ((Litex.NativeBridge.{complement_bridge} _right _left _rightReal _leftReal).mpr _opposite))))"))
    }

    pub(in crate::compile_to_lean) fn compile_negative_order_builtin(
        &self,
        goal: &AtomicFact,
        rule: &AtomicExceptEqualityFactSearchProofByBuiltinRule,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use AtomicExceptEqualityFactSearchProofByBuiltinRule as Rule;
        let (proof, left, right, reverse, strict_premise) = match (goal, rule) {
            (
                AtomicFact::NotGreaterFact(g),
                Rule::NotGreaterFact(
                    NotGreaterFactSearchProofByBuiltinRule::FromKnownOrderComplement(p),
                ),
            ) => (p, &g.left, &g.right, false, false),
            (
                AtomicFact::NotLessFact(g),
                Rule::NotLessFact(NotLessFactSearchProofByBuiltinRule::FromKnownOrderComplement(p)),
            ) => (p, &g.left, &g.right, true, false),
            (
                AtomicFact::NotGreaterEqualFact(g),
                Rule::NotGreaterEqualFact(
                    NotGreaterEqualFactSearchProofByBuiltinRule::FromKnownOrderComplement(p),
                ),
            ) => (p, &g.left, &g.right, false, true),
            (
                AtomicFact::NotLessEqualFact(g),
                Rule::NotLessEqualFact(
                    NotLessEqualFactSearchProofByBuiltinRule::FromKnownOrderComplement(p),
                ),
            ) => (p, &g.left, &g.right, true, true),
            _ => {
                return Err(LeanCompileError::new(
                    "Order/NegativeBuiltin",
                    &format!(
                        "Unsupported selected negative order builtin for `{}`.",
                        goal.readable_string()
                    ),
                ))
            }
        };
        let valid = match (&proof.premise_proof.fact, reverse, strict_premise) {
            (AtomicFact::LessEqualFact(f), false, false) => {
                f.left.ir() == left.ir() && f.right.ir() == right.ir()
            }
            (AtomicFact::GreaterEqualFact(f), true, false) => {
                f.left.ir() == left.ir() && f.right.ir() == right.ir()
            }
            (AtomicFact::LessFact(f), false, true) => {
                f.left.ir() == left.ir() && f.right.ir() == right.ir()
            }
            (AtomicFact::GreaterFact(f), true, true) => {
                f.left.ir() == left.ir() && f.right.ir() == right.ir()
            }
            _ => false,
        };
        if !valid || proof.real_carrier_proofs.len() != 2 {
            return Err(LeanCompileError::unsupported("Order/ComplementSubjects"));
        }
        // The known premise was selected before the two ordered carrier checks.
        let premise = self
            .compile_order_known_premise(&proof.premise_proof, position)?
            .1;
        let mut real = Vec::new();
        for (index, (obj, result)) in [left, right]
            .into_iter()
            .zip(&proof.real_carrier_proofs)
            .enumerate()
        {
            if membership_subject(&source_subject(result)?, obj)? != StandardSet::R {
                return Err(LeanCompileError::unsupported("Order/ComplementRealCarrier"));
            }
            real.push(
                self.compile_verify(result, &position.atomic_search_prior(index)?)?
                    .1,
            );
        }
        let complete = position.atomic_search_prior(2)?;
        let left = self.compile_object_reference(left, &complete)?;
        let right = self.compile_object_reference(right, &complete)?;
        let (left, right, left_real, right_real) = if reverse {
            (right, left, &real[1], &real[0])
        } else {
            (left, right, &real[0], &real[1])
        };
        let (premise_bridge, rejected_bridge, law) = if strict_premise {
            ("lt_iff_asReal", "le_iff_asReal", "not_le_of_gt")
        } else {
            ("le_iff_asReal", "lt_iff_asReal", "not_lt_of_ge")
        };
        Ok(format!("(by\n  let _left := {left}\n  let _right := {right}\n  have _leftReal : Litex.In _left Litex.R := {left_real}\n  have _rightReal : Litex.In _right Litex.R := {right_real}\n  exact fun _opposite => {law} ((Litex.NativeBridge.{premise_bridge} _left _right _leftReal _rightReal).mp {premise}) ((Litex.NativeBridge.{rejected_bridge} _right _left _rightReal _leftReal).mp _opposite))"))
    }
}
