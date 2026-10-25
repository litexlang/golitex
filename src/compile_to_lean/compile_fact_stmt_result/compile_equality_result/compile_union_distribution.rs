use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_union_over_intersection(
        &self,
        fact: &EqualFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (left, right, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Obj::SetOperator(SetOperator::Union(source)) = left else {
                continue;
            };
            let Obj::SetOperator(SetOperator::Intersect(target)) = right else {
                continue;
            };
            for (plain, pair, source_swapped) in [
                (&source.left, &source.right, false),
                (&source.right, &source.left, true),
            ] {
                let Obj::SetOperator(SetOperator::Intersect(pair)) = pair.as_ref() else {
                    continue;
                };
                for (ab, ad, target_swapped) in [
                    (&target.left, &target.right, false),
                    (&target.right, &target.left, true),
                ] {
                    // Check each *other* factor. A repeated common factor cannot
                    // stand in for a missing B or D, even if the verifier accepted it.
                    let Some(ab_swapped) = union_factor_order(ab, plain, &pair.left) else {
                        continue;
                    };
                    let Some(ad_swapped) = union_factor_order(ad, plain, &pair.right) else {
                        continue;
                    };
                    let source_term = self.compile_object_reference(left, position)?;
                    let target_term = self.compile_object_reference(right, position)?;
                    let (a_field, pair_field) = if source_swapped {
                        ("right", "left")
                    } else {
                        ("left", "right")
                    };
                    let (ab_field, ad_field) = if target_swapped {
                        ("right", "left")
                    } else {
                        ("left", "right")
                    };
                    let source_same = if source_swapped {
                        "(Litex.unionComm _source.val.left _source.val.right)"
                    } else {
                        "(Litex.sameRefl _source)"
                    };
                    let ab_same = if ab_swapped {
                        "((Litex.unionComm _ab.val.left _ab.val.right).symm)"
                    } else {
                        "(Litex.sameRefl _ab)"
                    };
                    let ad_same = if ad_swapped {
                        "((Litex.unionComm _ad.val.left _ad.val.right).symm)"
                    } else {
                        "(Litex.sameRefl _ad)"
                    };
                    let target_same = if target_swapped {
                        "(Litex.intersectComm _ab _ad)"
                    } else {
                        "(Litex.sameRefl _target)"
                    };
                    let symm = if reversed { ".symm" } else { "" };
                    return Ok(format!("(let _source := {source_term};\nlet _target := {target_term};\nlet _a := _source.val.{a_field};\nlet _b := _source.val.{pair_field}.val.left;\nlet _d := _source.val.{pair_field}.val.right;\nlet _ab := _target.val.{ab_field};\nlet _ad := _target.val.{ad_field};\n({source_same}.trans ((Litex.unionIntersectDistrib _a _b _d).trans ((Litex.intersectCongr (Litex.union _a _b) (Litex.union _a _d) _ab _ad {ab_same} {ad_same}).trans {target_same}))){symm})"));
                }
            }
        }
        Err(LeanCompileError::unsupported("UnionOverIntersect/Factors"))
    }
}

fn union_factor_order(object: &Obj, common: &Obj, factor: &Obj) -> Option<bool> {
    let Obj::SetOperator(SetOperator::Union(pair)) = object else {
        return None;
    };
    if pair.left.ir() == common.ir() && pair.right.ir() == factor.ir() {
        Some(false)
    } else if pair.right.ir() == common.ir() && pair.left.ir() == factor.ir() {
        Some(true)
    } else {
        None
    }
}
