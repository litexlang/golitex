use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_union_absorption(
        &self,
        fact: &EqualFact,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if requirements.len() != 1 {
            return Err(LeanCompileError::unsupported(
                "UnionAbsorption/Requirements",
            ));
        }
        let Fact::AtomicFact(AtomicFact::SubsetFact(subset)) = source_subject(&requirements[0])?
        else {
            return Err(LeanCompileError::unsupported("UnionAbsorption/Subset"));
        };
        for (union, retained, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Obj::SetOperator(SetOperator::Union(p)) = union else {
                continue;
            };
            let law = if retained.ir() == p.right.ir()
                && subset.left.ir() == p.left.ir()
                && subset.right.ir() == p.right.ir()
            {
                "unionOfSubsetRight"
            } else if retained.ir() == p.left.ir()
                && subset.left.ir() == p.right.ir()
                && subset.right.ir() == p.left.ir()
            {
                "unionOfSubsetLeft"
            } else {
                continue;
            };
            let child = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(requirements),
                0,
            );
            let proof = self.compile_verify(&requirements[0], &child)?.1;
            let term = self.compile_object_reference(union, position)?;
            let symm = if reversed { ".symm" } else { "" };
            return Ok(format!("(let _union := {term}; (Litex.{law} _union.val.left _union.val.right {proof}){symm})"));
        }
        Err(LeanCompileError::unsupported("UnionAbsorption/Endpoints"))
    }

    pub(in crate::compile_to_lean) fn compile_set_minus_recovery(
        &self,
        fact: &EqualFact,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if requirements.len() != 1 {
            return Err(LeanCompileError::unsupported(
                "SetMinusRecovery/Requirements",
            ));
        }
        let Fact::AtomicFact(AtomicFact::SubsetFact(subset)) = source_subject(&requirements[0])?
        else {
            return Err(LeanCompileError::unsupported("SetMinusRecovery/Subset"));
        };
        for (recovery, retained, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Obj::SetOperator(SetOperator::SetMinus(outer)) = recovery else {
                continue;
            };
            let Obj::SetOperator(SetOperator::SetMinus(inner)) = outer.right.as_ref() else {
                continue;
            };
            if outer.left.ir() != inner.left.ir()
                || retained.ir() != inner.right.ir()
                || subset.left.ir() != retained.ir()
                || subset.right.ir() != outer.left.ir()
            {
                continue;
            }
            let child = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(requirements),
                0,
            );
            let proof = self.compile_verify(&requirements[0], &child)?.1;
            let term = self.compile_object_reference(recovery, position)?;
            let symm = if reversed { ".symm" } else { "" };
            return Ok(format!("(let _recovery := {term}; (Litex.setMinusRecovery _recovery.val.left _recovery.val.right.val.right {proof}){symm})"));
        }
        Err(LeanCompileError::unsupported("SetMinusRecovery/Endpoints"))
    }

    pub(in crate::compile_to_lean) fn compile_empty_of_not_nonempty(
        &self,
        fact: &EqualFact,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if requirements.len() != 1 {
            return Err(LeanCompileError::unsupported(
                "EmptyOfNotNonempty/Requirements",
            ));
        }
        let Fact::AtomicFact(AtomicFact::NotIsNonemptySetFact(p)) =
            source_subject(&requirements[0])?
        else {
            return Err(LeanCompileError::unsupported("EmptyOfNotNonempty/Premise"));
        };
        for (set, empty, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            if set.ir() != p.set.ir()
                || !matches!(empty, Obj::SetFormer(SetFormer::ListSet(s)) if s.list.is_empty())
            {
                continue;
            }
            let child = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(requirements),
                0,
            );
            let proof = self.compile_verify(&requirements[0], &child)?.1;
            let term = self.compile_object_reference(set, position)?;
            let symm = if reversed { ".symm" } else { "" };
            return Ok(format!("(Litex.emptyOfNotNonempty {term} {proof}){symm}"));
        }
        Err(LeanCompileError::unsupported(
            "EmptyOfNotNonempty/Endpoints",
        ))
    }

    pub(in crate::compile_to_lean) fn compile_set_decomposition(
        &self,
        fact: &EqualFact,
        intersection: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (left, right, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let (law, arguments) = if intersection {
                let (
                    Obj::SetOperator(SetOperator::SetMinus(p)),
                    Obj::SetOperator(SetOperator::SetMinus(q)),
                ) = (left, right)
                else {
                    continue;
                };
                let Obj::SetOperator(SetOperator::Intersect(inner)) = p.right.as_ref() else {
                    continue;
                };
                if p.left.ir() != q.left.ir()
                    || p.left.ir() != inner.right.ir()
                    || q.right.ir() != inner.left.ir()
                {
                    continue;
                }
                (
                    "setMinusOfIntersection",
                    "_set.val.right.val.left _set.val.left",
                )
            } else {
                let (
                    Obj::SetOperator(SetOperator::Union(p)),
                    Obj::SetOperator(SetOperator::Union(q)),
                ) = (left, right)
                else {
                    continue;
                };
                let Obj::SetOperator(SetOperator::SetMinus(inner)) = p.right.as_ref() else {
                    continue;
                };
                if p.left.ir() != inner.right.ir()
                    || p.left.ir() != q.left.ir()
                    || inner.left.ir() != q.right.ir()
                {
                    continue;
                }
                (
                    "unionSetMinusDecomposition",
                    "_set.val.left _set.val.right.val.left",
                )
            };
            let term = self.compile_object_reference(left, position)?;
            let symm = if reversed { ".symm" } else { "" };
            return Ok(format!(
                "(let _set := {term}; (Litex.{law} {arguments}){symm})"
            ));
        }
        Err(LeanCompileError::unsupported("SetDecomposition/Endpoints"))
    }

    pub(in crate::compile_to_lean) fn compile_power_intersection(
        &self,
        fact: &EqualFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (left, right, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let (
                Obj::SetOperator(SetOperator::PowerSet(p)),
                Obj::SetOperator(SetOperator::Intersect(q)),
            ) = (left, right)
            else {
                continue;
            };
            let (
                Obj::SetOperator(SetOperator::Intersect(inner)),
                Obj::SetOperator(SetOperator::PowerSet(a)),
                Obj::SetOperator(SetOperator::PowerSet(b)),
            ) = (p.set.as_ref(), q.left.as_ref(), q.right.as_ref())
            else {
                continue;
            };
            if inner.left.ir() != a.set.ir() || inner.right.ir() != b.set.ir() {
                continue;
            }
            let term = self.compile_object_reference(left, position)?;
            let symm = if reversed { ".symm" } else { "" };
            return Ok(format!("(let _power := {term}; (Litex.powerSetIntersection _power.val.bound.val.left _power.val.bound.val.right){symm})"));
        }
        Err(LeanCompileError::unsupported("PowerIntersection/Endpoints"))
    }

    pub(in crate::compile_to_lean) fn compile_power_empty(
        &self,
        fact: &EqualFact,
        _position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let empty =
            |o: &Obj| matches!(o, Obj::SetFormer(SetFormer::ListSet(s)) if s.list.is_empty());
        for (left, right, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let (Obj::SetOperator(SetOperator::PowerSet(p)), Obj::SetFormer(SetFormer::ListSet(s))) =
                (left, right)
            else {
                continue;
            };
            if !empty(&p.set) || s.list.len() != 1 || !empty(&s.list[0]) {
                continue;
            }
            return Ok(format!(
                "(Litex.powerEmptyValue (M := M)){}",
                if reversed { ".symm" } else { "" }
            ));
        }
        Err(LeanCompileError::unsupported("PowerEmpty/Endpoints"))
    }

    pub(in crate::compile_to_lean) fn compile_family_union_identity(
        &self,
        fact: &EqualFact,
        rule: &EqualitySearchProofByBuiltinRule,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let empty =
            |o: &Obj| matches!(o, Obj::SetFormer(SetFormer::ListSet(s)) if s.list.is_empty());
        for (left, right, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Obj::SetOperator(SetOperator::FamilyUnion(p)) = left else {
                continue;
            };
            let application = match rule {
                EqualitySearchProofByBuiltinRule::FamilyUnionOfEmpty(_)
                    if empty(&p.left) && empty(right) =>
                {
                    "Litex.familyUnionEmptyValue (M := M)"
                }
                EqualitySearchProofByBuiltinRule::FamilyUnionOfSingleton(_) => {
                    let Obj::SetFormer(SetFormer::ListSet(s)) = p.left.as_ref() else {
                        continue;
                    };
                    if s.list.len() != 1 || s.list[0].ir() != right.ir() {
                        continue;
                    }
                    "Litex.familyUnionSingletonValue (Litex.denote _family.val.family.val.element) (Litex.isSet _family.val.family.val.element)"
                }
                EqualitySearchProofByBuiltinRule::FamilyUnionOfPowerSet(_) => {
                    let Obj::SetOperator(SetOperator::PowerSet(power)) = p.left.as_ref() else {
                        continue;
                    };
                    if power.set.ir() != right.ir() {
                        continue;
                    }
                    "Litex.familyUnionPowerValue _family.val.family.val.bound"
                }
                _ => continue,
            };
            let term = self.compile_object_reference(left, position)?;
            let symm = if reversed { ".symm" } else { "" };
            return Ok(format!("(let _family := {term}; ({application}){symm})"));
        }
        Err(LeanCompileError::unsupported(
            "FamilyUnion/SelectedIdentity",
        ))
    }
}
