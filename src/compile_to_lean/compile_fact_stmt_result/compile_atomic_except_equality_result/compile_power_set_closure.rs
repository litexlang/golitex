use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::InFactSearchProofByKnownSpecialProperty;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_power_set_closure(
        &self,
        goal: &InFact,
        rule: &InFactSearchProofByKnownSpecialProperty,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::SetOperator(SetOperator::PowerSet(power)) = &goal.set else {
            return Err(LeanCompileError::unsupported("PowerSetClosure/Target"));
        };
        let base = self.compile_object_reference(&power.set, position)?;
        let subset = match (rule, &goal.element) {
            (
                InFactSearchProofByKnownSpecialProperty::ListSetInPowerSetFromMembers(proof),
                Obj::SetFormer(SetFormer::ListSet(value)),
            ) => {
                if proof.members.len() != value.list.len() {
                    return Err(LeanCompileError::unsupported(
                        "PowerSetClosure/LiteralMembers",
                    ));
                }
                let mut current = self.compile_object_reference(&goal.element, position)?;
                let mut stages = Vec::new();
                for (element, member) in value.list.iter().zip(&proof.members) {
                    let premise =
                        self.compile_power_set_known_member(member, element, &power.set, position)?;
                    stages.push((current.clone(), premise));
                    current = format!("({current}).val.tail");
                }
                let mut subset = format!("(Litex.emptySubset {base})");
                for (object, member) in stages.into_iter().rev() {
                    subset = format!("(Litex.insertSubset ({object}).val.element ({object}).val.tail {base} ({object}).wd {member} {subset})");
                }
                subset
            }
            (
                InFactSearchProofByKnownSpecialProperty::UnionInPowerSet(proof),
                Obj::SetOperator(SetOperator::Union(value)),
            ) => {
                let left = self.compile_power_set_known_member(
                    &proof.left,
                    &value.left,
                    &goal.set,
                    position,
                )?;
                let right = self.compile_power_set_known_member(
                    &proof.right,
                    &value.right,
                    &goal.set,
                    position,
                )?;
                let a = self.compile_object_reference(&value.left, position)?;
                let b = self.compile_object_reference(&value.right, position)?;
                format!("(Litex.unionSubsetOfBoth {a} {b} {base} ((Litex.inPowerSet_iff {a} {base}).mp {left}) ((Litex.inPowerSet_iff {b} {base}).mp {right}))")
            }
            (
                InFactSearchProofByKnownSpecialProperty::IntersectInPowerSetFromLeft(proof),
                Obj::SetOperator(SetOperator::Intersect(value)),
            ) => {
                let left = self.compile_power_set_known_member(
                    &proof.left,
                    &value.left,
                    &goal.set,
                    position,
                )?;
                let a = self.compile_object_reference(&value.left, position)?;
                let b = self.compile_object_reference(&value.right, position)?;
                format!("(Litex.intersectSubsetOfLeft {a} {b} {base} ((Litex.inPowerSet_iff {a} {base}).mp {left}))")
            }
            (
                InFactSearchProofByKnownSpecialProperty::IntersectInPowerSetFromRight(proof),
                Obj::SetOperator(SetOperator::Intersect(value)),
            ) => {
                let right = self.compile_power_set_known_member(
                    &proof.right,
                    &value.right,
                    &goal.set,
                    position,
                )?;
                let a = self.compile_object_reference(&value.left, position)?;
                let b = self.compile_object_reference(&value.right, position)?;
                format!("(Litex.intersectSubsetOfRight {a} {b} {base} ((Litex.inPowerSet_iff {b} {base}).mp {right}))")
            }
            (
                InFactSearchProofByKnownSpecialProperty::SetMinusInPowerSet(proof),
                Obj::SetOperator(SetOperator::SetMinus(value)),
            ) => {
                let left = self.compile_power_set_known_member(
                    &proof.left,
                    &value.left,
                    &goal.set,
                    position,
                )?;
                let a = self.compile_object_reference(&value.left, position)?;
                let b = self.compile_object_reference(&value.right, position)?;
                format!("(Litex.setMinusSubsetOfLeft {a} {b} {base} ((Litex.inPowerSet_iff {a} {base}).mp {left}))")
            }
            (
                InFactSearchProofByKnownSpecialProperty::SetMinusInPowerSetOfLeft(proof),
                Obj::SetOperator(SetOperator::SetMinus(value)),
            ) => {
                let a = self.compile_object_reference(&value.left, position)?;
                let b = self.compile_object_reference(&value.right, position)?;
                let equal = self.compile_equality_path(
                    &value.left,
                    &power.set,
                    &proof.left_equal_carrier,
                    position,
                )?;
                let left_subset = format!(
                    "(Litex.subsetOfSame {a} {a} {a} {base} rfl {equal} (Litex.subsetRefl {a}))"
                );
                format!("(Litex.setMinusSubsetOfLeft {a} {b} {base} {left_subset})")
            }
            _ => return Err(LeanCompileError::unsupported("PowerSetClosure/Constructor")),
        };
        let element = self.compile_object_reference(&goal.element, position)?;
        Ok(format!(
            "((Litex.inPowerSet_iff {element} {base}).mpr {subset})"
        ))
    }

    fn compile_power_set_known_member(
        &self,
        proof: &AtomicExceptEqualityFactKnownProof,
        element: &Obj,
        target: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if !matches!(&proof.fact, AtomicFact::InFact(member)
            if member.element.ir() == element.ir() && member.set.ir() == target.ir())
        {
            return Err(LeanCompileError::new(
                "PowerSetClosure/Premise",
                "The recorded membership has another operand or power-set carrier.",
            ));
        }
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(citation) =
            proof.searched_proof.as_ref()
        else {
            return Err(LeanCompileError::unsupported("PowerSetClosure/KnownRoute"));
        };
        self.compile_known_atomic(citation, &proof.fact, position)
    }
}
