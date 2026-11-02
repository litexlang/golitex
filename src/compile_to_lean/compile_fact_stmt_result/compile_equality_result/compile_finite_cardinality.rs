use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_empty_from_cardinality(
        &self,
        fact: &EqualFact,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if requirements.len() != 1 {
            return Err(LeanCompileError::unsupported(
                "EmptyCardinality/Requirements",
            ));
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(eq)) = source_subject(&requirements[0])? else {
            return Err(LeanCompileError::unsupported("EmptyCardinality/Child"));
        };
        let Some(set) = finite_size_set(&eq.left) else {
            return Err(LeanCompileError::unsupported("EmptyCardinality/Size"));
        };
        if !is_exact_zero(&eq.right) {
            return Err(LeanCompileError::unsupported("EmptyCardinality/Zero"));
        }
        for (left, right, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            if left.ir() != set.ir()
                || !matches!(right,Obj::SetFormer(SetFormer::ListSet(s)) if s.list.is_empty())
            {
                continue;
            }
            let child = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(requirements),
                0,
            );
            let compiled = self.compile_verify(&requirements[0], &child)?;
            let complete = SourcePosition { before: 1, ..child };
            let size = self.compile_object_reference(&eq.left, &complete)?;
            return Ok(format!(
                "(Litex.emptyOfCardinalityZero {size} {}){}",
                compiled.1,
                if reversed { ".symm" } else { "" }
            ));
        }
        Err(LeanCompileError::unsupported("EmptyCardinality/Endpoints"))
    }

    pub(in crate::compile_to_lean) fn compile_equal_from_subset_cardinality(
        &self,
        fact: &EqualFact,
        size: &VerifyFactResult,
        subset: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Fact::AtomicFact(AtomicFact::EqualFact(eq)) = source_subject(size)? else {
            return Err(LeanCompileError::unsupported(
                "EqualCardinality/SizeEquality",
            ));
        };
        if !matches!((finite_size_set(&eq.left),finite_size_set(&eq.right)),(Some(a),Some(b)) if a.ir()==fact.left.ir() && b.ir()==fact.right.ir())
        {
            return Err(LeanCompileError::unsupported(
                "EqualCardinality/SizeSubjects",
            ));
        }
        let Fact::AtomicFact(AtomicFact::SubsetFact(inclusion)) = source_subject(subset)? else {
            return Err(LeanCompileError::unsupported("EqualCardinality/Subset"));
        };
        let reversed = if inclusion.left.ir() == fact.left.ir()
            && inclusion.right.ir() == fact.right.ir()
        {
            false
        } else if inclusion.left.ir() == fact.right.ir() && inclusion.right.ir() == fact.left.ir() {
            true
        } else {
            return Err(LeanCompileError::unsupported(
                "EqualCardinality/SubsetSubjects",
            ));
        };
        let first = SourcePosition::new(
            Some(position),
            SourceOwner::EqualityRequirements(std::slice::from_ref(size)),
            0,
        );
        let size_proof = self.compile_verify(size, &first)?;
        let definition = self.emit_internal_fact(&source_subject(size)?, &size_proof, &first)?;
        let first_complete = SourcePosition { before: 1, ..first };
        let second = SourcePosition::new(
            Some(&first_complete),
            SourceOwner::EqualityRequirements(std::slice::from_ref(subset)),
            0,
        );
        let subset_proof = self.compile_verify(subset, &second)?.1;
        let complete = SourcePosition {
            before: 1,
            ..second
        };
        let a = self.compile_object_reference(&eq.left, &complete)?;
        let b = self.compile_object_reference(&eq.right, &complete)?;
        let proof = if reversed {
            format!(
                "(Litex.sameOfFiniteSubsetCardinality {b} {a} (h_{}).symm {subset_proof}).symm",
                eq.fact_id.value()
            )
        } else {
            format!(
                "(Litex.sameOfFiniteSubsetCardinality {a} {b} h_{} {subset_proof})",
                eq.fact_id.value()
            )
        };
        Ok(format!(
            "(by\n  {}\n  exact {proof}\n)",
            definition.replace('\n', "\n  ")
        ))
    }

    pub(in crate::compile_to_lean) fn compile_cardinality_decomposition(
        &self,
        fact: &EqualFact,
        union: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (left, right, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Some(set) = finite_size_set(left) else {
                continue;
            };
            let Obj::ArithmeticOperator(ArithmeticOperator::Sub(difference)) = right else {
                continue;
            };
            let Some(intersection) = finite_size_set(&difference.right) else {
                continue;
            };
            let Obj::SetOperator(SetOperator::Intersect(intersection)) = intersection else {
                continue;
            };
            let (law, arguments) = if union {
                let Obj::SetOperator(SetOperator::Union(u)) = set else {
                    continue;
                };
                let Obj::ArithmeticOperator(ArithmeticOperator::Add(add)) =
                    difference.left.as_ref()
                else {
                    continue;
                };
                let (Some(a), Some(b)) = (finite_size_set(&add.left), finite_size_set(&add.right))
                else {
                    continue;
                };
                let reverse_union = if u.left.ir() == a.ir() && u.right.ir() == b.ir() {
                    false
                } else if u.left.ir() == b.ir() && u.right.ir() == a.ir() {
                    true
                } else {
                    continue;
                };
                let reverse_intersection = if intersection.left.ir() == a.ir()
                    && intersection.right.ir() == b.ir()
                {
                    false
                } else if intersection.left.ir() == b.ir() && intersection.right.ir() == a.ir() {
                    true
                } else {
                    continue;
                };
                ("finiteCardinalityUnionValue",format!("_card_rhs.val.left.val.left _card_rhs.val.left.val.right {reverse_union} {reverse_intersection}"))
            } else {
                let Obj::SetOperator(SetOperator::SetMinus(d)) = set else {
                    continue;
                };
                let Some(a) = finite_size_set(&difference.left) else {
                    continue;
                };
                if a.ir() != d.left.ir()
                    || intersection.left.ir() != d.left.ir()
                    || intersection.right.ir() != d.right.ir()
                {
                    continue;
                }
                (
                    "finiteCardinalityDifferenceValue",
                    "_card_rhs.val.left _card_lhs.val.set.val.right".to_owned(),
                )
            };
            let lhs = self.compile_object_reference(left, position)?;
            let rhs = self.compile_object_reference(right, position)?;
            return Ok(format!(
                "(let _card_lhs := {lhs}; let _card_rhs := {rhs}; (Litex.{law} {arguments}){})",
                if reversed { ".symm" } else { "" }
            ));
        }
        Err(LeanCompileError::unsupported(
            "CardinalityDecomposition/Endpoints",
        ))
    }
}
