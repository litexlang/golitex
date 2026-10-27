use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::subset::SubsetFactSearchProofByBuiltinRule;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_set_subset_rule(
        &self,
        fact: &SubsetFact,
        rule: &SubsetFactSearchProofByBuiltinRule,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match rule {
            SubsetFactSearchProofByBuiltinRule::FunctionRangeInCodomain(p) => {
                self.compile_function_range_subset(fact, p, position)
            }
            SubsetFactSearchProofByBuiltinRule::RealIntervalSubsetReal(_) => {
                self.compile_real_interval_subset(fact, position)
            }
            SubsetFactSearchProofByBuiltinRule::CompositionRangeSubset(p) => {
                self.compile_composition_range_subset(fact, &p.callable, position)
            }
            SubsetFactSearchProofByBuiltinRule::FunctionPreimageSubsetOfInputCarrier(p) => {
                self.compile_preimage_subset(fact, p, position)
            }
            SubsetFactSearchProofByBuiltinRule::SubsetSetMinusCommonRightMonotone(p) => {
                self.compile_subset_monotone(fact, &p.left_operand_subset_proof, false, position)
            }
            SubsetFactSearchProofByBuiltinRule::SubsetPowerSetMonotone(p) => {
                self.compile_subset_monotone(fact, &p.base_subset_proof, true, position)
            }
            SubsetFactSearchProofByBuiltinRule::SubsetTransitivity(p) => self
                .compile_subset_transitivity(
                    fact,
                    [&p.left_to_middle_proof, &p.middle_to_right_proof],
                    position,
                ),
            SubsetFactSearchProofByBuiltinRule::UnionSubsetFromBothOperands(p) => self
                .compile_union_upper_bound(
                    fact,
                    [&p.left_operand_subset_proof, &p.right_operand_subset_proof],
                    position,
                ),
            SubsetFactSearchProofByBuiltinRule::UnionSubsetFromComponentwise(p) => self
                .compile_union_subset_componentwise(fact, &p.proof_of_requirement_facts, position),
            SubsetFactSearchProofByBuiltinRule::SetMinusSubsetLeft(_) => {
                self.compile_set_minus_subset_left(fact, position)
            }
            SubsetFactSearchProofByBuiltinRule::IntersectSubsetLeft(_) => {
                self.compile_intersection_subset_operand(fact, true, position)
            }
            SubsetFactSearchProofByBuiltinRule::IntersectSubsetRight(_) => {
                self.compile_intersection_subset_operand(fact, false, position)
            }
            SubsetFactSearchProofByBuiltinRule::IntersectSubsetFromLeftUpperBound(p) => self
                .compile_intersection_subset_bound(
                    fact,
                    &p.left_operand_subset_proof,
                    true,
                    position,
                ),
            SubsetFactSearchProofByBuiltinRule::IntersectSubsetFromRightUpperBound(p) => self
                .compile_intersection_subset_bound(
                    fact,
                    &p.right_operand_subset_proof,
                    false,
                    position,
                ),
            SubsetFactSearchProofByBuiltinRule::StandardSetSubset(proof) => {
                if fact.left != Obj::StandardSet(proof.left.clone())
                    || fact.right != Obj::StandardSet(proof.right.clone())
                {
                    return Err(LeanCompileError::unsupported("Subset/StandardSubject"));
                }
                let member = standard_inclusion_term(&proof.left, &proof.right, "_a", "_ha")?;
                Ok(format!(
                    "(Litex.subsetOfForall {} {} (fun _a _ha => {member}))",
                    standard_term(&proof.left)?,
                    standard_term(&proof.right)?
                ))
            }
            SubsetFactSearchProofByBuiltinRule::SubsetReflexivity(_)
                if fact.left.ir() == fact.right.ir() =>
            {
                Ok(format!(
                    "(Litex.subsetRefl {})",
                    self.compile_object_reference(&fact.left, position)?
                ))
            }
            SubsetFactSearchProofByBuiltinRule::ListSetSubsetFromMembers(proof) => {
                self.compile_list_subset(fact, &proof.member_in_proofs, position)
            }
            SubsetFactSearchProofByBuiltinRule::SubsetUnionLeft(_)
            | SubsetFactSearchProofByBuiltinRule::SubsetUnionRight(_) => {
                let Obj::SetOperator(SetOperator::Union(union)) = &fact.right else {
                    return Err(LeanCompileError::unsupported("SubsetUnion/Target"));
                };
                let left = matches!(rule, SubsetFactSearchProofByBuiltinRule::SubsetUnionLeft(_));
                let selected = if left { &union.left } else { &union.right };
                if fact.left.ir() != selected.ir() {
                    return Err(LeanCompileError::unsupported("SubsetUnion/Operand"));
                }
                let a = self.compile_object_reference(&union.left, position)?;
                let b = self.compile_object_reference(&union.right, position)?;
                let injection = if left { "Or.inl" } else { "Or.inr" };
                Ok(format!("(fun _x _hx => (Litex.SetSemantics.union_members (M := M) (Litex.denote {a}) (Litex.denote {b}) _x).mpr ({injection} _hx))"))
            }
            SubsetFactSearchProofByBuiltinRule::SetBuilderSubsetOfParamSet(_) => {
                let Obj::SetFormer(SetFormer::SetBuilder(set)) = &fact.left else {
                    return Err(LeanCompileError::new(
                        "SetBuilder/SubsetSubject",
                        "Subset evidence has another constructor.",
                    ));
                };
                if set.param_set.ir() != fact.right.ir() {
                    return Err(LeanCompileError::new(
                        "SetBuilder/SubsetBound",
                        "Subset target is not the source bound.",
                    ));
                }
                Ok(format!("(by\n  let _set := {}\n  exact Litex.setBuilderSubset _set.val.bound _set.val.predicate)", self.compile_object_reference(&fact.left, position)?))
            }
            _ => Err(LeanCompileError::unsupported("Set/SubsetRule")),
        }
    }

    pub(in crate::compile_to_lean) fn compile_list_subset(
        &self,
        fact: &SubsetFact,
        proofs: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::SetFormer(SetFormer::ListSet(set)) = &fact.left else {
            return Err(LeanCompileError::new(
                "ListSet/SubsetSubject",
                "Selected subset evidence has another constructor.",
            ));
        };
        if proofs.len() != set.list.len() {
            return Err(LeanCompileError::new(
                "ListSet/SubsetArity",
                "Subset needs each recorded member proof.",
            ));
        }
        let upper = self.compile_object_reference(&fact.right, position)?;
        let mut term = format!("(Litex.emptySubset {upper})");
        for (i, (element, proof)) in set.list.iter().zip(proofs).enumerate().rev() {
            match source_subject(proof)? {
                Fact::AtomicFact(AtomicFact::InFact(f))
                    if f.element.ir() == element.ir() && f.set.ir() == fact.right.ir() => {}
                _ => {
                    return Err(LeanCompileError::new(
                        "ListSet/SubsetMember",
                        "The recorded child proves another element or upper bound.",
                    ))
                }
            }
            let member = self.compile_verify(proof, position)?.1;
            let suffix = format!("_set{}", ".val.tail".repeat(i));
            term = format!("(Litex.insertSubset {suffix}.val.element {suffix}.val.tail {upper} {suffix}.wd {member} {term})");
        }
        Ok(format!(
            "(by\n  let _set := {}\n  exact {term})",
            self.compile_object_reference(&fact.left, position)?
        ))
    }
}
