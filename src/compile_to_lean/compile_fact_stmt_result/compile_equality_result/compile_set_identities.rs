use crate::compile_to_lean::helper::source_subject;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_set_identity(
        &self,
        fact: &EqualFact,
        rule: &EqualitySearchProofByBuiltinRule,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (left, right, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            if let Some((law, arguments)) = set_identity_shape(left, right, rule) {
                let object = self.compile_object_reference(left, position)?;
                let symm = if reversed { ".symm" } else { "" };
                // Project children from the original formed object. Their WD is
                // already carried by this producer; do not rebuild each child.
                return Ok(format!(
                    "(let _litex_set := {object}; (Litex.{law} {arguments}){symm})"
                ));
            }
        }
        Err(LeanCompileError::unsupported("SetIdentity/Endpoints"))
    }

    pub(super) fn compile_intersect_from_subset(
        &self,
        fact: &EqualFact,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if requirements.len() != 1 {
            return Err(LeanCompileError::unsupported(
                "IntersectFromSubset/Requirements",
            ));
        }
        let Fact::AtomicFact(AtomicFact::SubsetFact(subset)) = source_subject(&requirements[0])?
        else {
            return Err(LeanCompileError::unsupported("IntersectFromSubset/Premise"));
        };
        for (intersection, retained, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Some((a, b)) = set_operands(intersection, true) else {
                continue;
            };
            let side = if retained.ir() == a.ir()
                && subset.left.ir() == a.ir()
                && subset.right.ir() == b.ir()
            {
                "Left"
            } else if retained.ir() == b.ir()
                && subset.left.ir() == b.ir()
                && subset.right.ir() == a.ir()
            {
                "Right"
            } else {
                continue;
            };
            let prior = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(requirements),
                0,
            );
            let proof = self.compile_verify(&requirements[0], &prior)?.1;
            let object = self.compile_object_reference(intersection, position)?;
            let symm = if reversed { ".symm" } else { "" };
            return Ok(format!("(let _litex_set := {object}; (Litex.intersectOfSubset{side} _litex_set.val.left _litex_set.val.right {proof}){symm})"));
        }
        Err(LeanCompileError::unsupported(
            "IntersectFromSubset/Endpoints",
        ))
    }
}

fn set_operands(object: &Obj, intersection: bool) -> Option<(&Obj, &Obj)> {
    match object {
        Obj::SetOperator(SetOperator::Intersect(p)) if intersection => Some((&p.left, &p.right)),
        Obj::SetOperator(SetOperator::Union(p)) if !intersection => Some((&p.left, &p.right)),
        _ => None,
    }
}

fn empty_set(object: &Obj) -> bool {
    matches!(object, Obj::SetFormer(SetFormer::ListSet(p)) if p.list.is_empty())
}

/// Validate only the selected builtin. This is not a search over set identities.
fn set_identity_shape(
    left: &Obj,
    right: &Obj,
    rule: &EqualitySearchProofByBuiltinRule,
) -> Option<(&'static str, &'static str)> {
    use EqualitySearchProofByBuiltinRule as Rule;
    let intersection = matches!(
        rule,
        Rule::IntersectCommutative(_)
            | Rule::IntersectIdempotent(_)
            | Rule::IntersectEmptyLeft(_)
            | Rule::IntersectEmptyRight(_)
            | Rule::IntersectAssociative(_)
            | Rule::IntersectUnionDistributive(_)
    );
    let (a, b) = set_operands(left, intersection)?;
    match rule {
        Rule::IntersectCommutative(_) | Rule::UnionCommutative(_) => {
            let (c, d) = set_operands(right, intersection)?;
            (a.ir() == d.ir() && b.ir() == c.ir()).then_some((
                if intersection {
                    "intersectComm"
                } else {
                    "unionComm"
                },
                "_litex_set.val.left _litex_set.val.right",
            ))
        }
        Rule::IntersectIdempotent(_) | Rule::UnionIdempotent(_) => {
            (a.ir() == b.ir() && a.ir() == right.ir()).then_some((
                if intersection {
                    "intersectIdem"
                } else {
                    "unionIdem"
                },
                "_litex_set.val.left",
            ))
        }
        Rule::IntersectEmptyLeft(_) | Rule::UnionEmptyLeft(_) => (empty_set(a)
            && if intersection {
                empty_set(right)
            } else {
                b.ir() == right.ir()
            })
        .then_some((
            if intersection {
                "intersectEmptyLeft"
            } else {
                "unionEmptyLeft"
            },
            "_litex_set.val.right",
        )),
        Rule::IntersectEmptyRight(_) | Rule::UnionEmptyRight(_) => (empty_set(b)
            && if intersection {
                empty_set(right)
            } else {
                a.ir() == right.ir()
            })
        .then_some((
            if intersection {
                "intersectEmptyRight"
            } else {
                "unionEmptyRight"
            },
            "_litex_set.val.left",
        )),
        Rule::IntersectAssociative(_) | Rule::UnionAssociative(_) => {
            let (aa, ab) = set_operands(a, intersection)?;
            let (c, d) = set_operands(right, intersection)?;
            let (da, db) = set_operands(d, intersection)?;
            (aa.ir() == c.ir() && ab.ir() == da.ir() && b.ir() == db.ir()).then_some((
                if intersection {
                    "intersectAssoc"
                } else {
                    "unionAssoc"
                },
                "_litex_set.val.left.val.left _litex_set.val.left.val.right _litex_set.val.right",
            ))
        }
        Rule::IntersectUnionDistributive(_) => {
            let (ba, bb) = set_operands(b, false)?;
            let (c, d) = set_operands(right, false)?;
            let (ca, cb) = set_operands(c, true)?;
            let (da, db) = set_operands(d, true)?;
            (a.ir() == ca.ir() && a.ir() == da.ir() && ba.ir() == cb.ir() && bb.ir() == db.ir())
                .then_some((
                "intersectUnionDistrib",
                "_litex_set.val.left _litex_set.val.right.val.left _litex_set.val.right.val.right",
            ))
        }
        _ => None,
    }
}
