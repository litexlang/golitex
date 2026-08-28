//! Structural equality for set-valued expressions.

use super::super::*;

pub(in super::super) fn render_structural_set_equality(
    fact: &Fact,
    rule: LeanSetBuiltinCompilationKind,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let (left, right) = equality_parts(fact)?;
    render_fact(fact, context)?;
    let symmetric = |proof: String| format!("Litex.Same.symm ({proof})");
    match rule {
        LeanSetBuiltinCompilationKind::UnionCommutative => {
            let (Obj::Union(left_union), Obj::Union(right_union)) = (left, right) else {
                return Err("union commutativity changed its constructors".into());
            };
            if obj_equality_key(left_union.left.as_ref())
                != obj_equality_key(right_union.right.as_ref())
                || obj_equality_key(left_union.right.as_ref())
                    != obj_equality_key(right_union.left.as_ref())
            {
                return Err("union commutativity changed its swapped operands".into());
            }
            Ok(format!(
                "Litex.SetRules.unionCommutative {} {}",
                render_obj(left_union.left.as_ref(), context)?,
                render_obj(left_union.right.as_ref(), context)?
            ))
        }
        LeanSetBuiltinCompilationKind::UnionAssociative => {
            if let (Obj::Union(left_outer), Obj::Union(right_outer)) = (left, right) {
                if let Obj::Union(left_inner) = left_outer.left.as_ref() {
                    if obj_equality_key(left_inner.left.as_ref())
                        == obj_equality_key(right_outer.left.as_ref())
                    {
                        if let Obj::Union(right_inner) = right_outer.right.as_ref() {
                            if obj_equality_key(left_inner.right.as_ref())
                                == obj_equality_key(right_inner.left.as_ref())
                                && obj_equality_key(left_outer.right.as_ref())
                                    == obj_equality_key(right_inner.right.as_ref())
                            {
                                return Ok(format!(
                                    "Litex.SetRules.unionAssociative {} {} {}",
                                    render_obj(left_inner.left.as_ref(), context)?,
                                    render_obj(left_inner.right.as_ref(), context)?,
                                    render_obj(left_outer.right.as_ref(), context)?
                                ));
                            }
                        }
                    }
                }
            }
            let reversed: Fact =
                EqualFact::new(right.clone(), left.clone(), fact.line_file()).into();
            Ok(symmetric(render_structural_set_equality(
                &reversed, rule, context,
            )?))
        }
        LeanSetBuiltinCompilationKind::UnionIdempotent => {
            if let Obj::Union(union) = left {
                if obj_equality_key(union.left.as_ref()) == obj_equality_key(union.right.as_ref())
                    && obj_equality_key(union.left.as_ref()) == obj_equality_key(right)
                {
                    return Ok(format!(
                        "Litex.SetRules.unionIdempotent {}",
                        render_obj(right, context)?
                    ));
                }
            }
            if let Obj::Union(union) = right {
                if obj_equality_key(union.left.as_ref()) == obj_equality_key(union.right.as_ref())
                    && obj_equality_key(union.left.as_ref()) == obj_equality_key(left)
                {
                    return Ok(symmetric(format!(
                        "Litex.SetRules.unionIdempotent {}",
                        render_obj(left, context)?
                    )));
                }
            }
            Err("union idempotence changed its repeated operand".into())
        }
        LeanSetBuiltinCompilationKind::UnionEmptyIdentity => {
            for (union_side, plain_side, reverse) in [(left, right, false), (right, left, true)] {
                let Obj::Union(union) = union_side else {
                    continue;
                };
                let left_empty =
                    matches!(union.left.as_ref(), Obj::ListSet(set) if set.list.is_empty());
                let right_empty =
                    matches!(union.right.as_ref(), Obj::ListSet(set) if set.list.is_empty());
                let operand = if left_empty {
                    union.right.as_ref()
                } else if right_empty {
                    union.left.as_ref()
                } else {
                    continue;
                };
                if obj_equality_key(operand) != obj_equality_key(plain_side) {
                    continue;
                }
                let theorem = if left_empty {
                    "unionEmptyLeft"
                } else {
                    "unionEmptyRight"
                };
                let proof = format!(
                    "Litex.SetRules.{theorem} {}",
                    render_obj(plain_side, context)?
                );
                return Ok(if reverse { symmetric(proof) } else { proof });
            }
            Err("union empty identity changed its empty or retained operand".into())
        }
        LeanSetBuiltinCompilationKind::IntersectCommutative => {
            let (Obj::Intersect(left_intersection), Obj::Intersect(right_intersection)) =
                (left, right)
            else {
                return Err("intersection commutativity changed its constructors".into());
            };
            if obj_equality_key(left_intersection.left.as_ref())
                != obj_equality_key(right_intersection.right.as_ref())
                || obj_equality_key(left_intersection.right.as_ref())
                    != obj_equality_key(right_intersection.left.as_ref())
            {
                return Err("intersection commutativity changed its swapped operands".into());
            }
            Ok(format!(
                "Litex.SetRules.intersectCommutative {} {}",
                render_obj(left_intersection.left.as_ref(), context)?,
                render_obj(left_intersection.right.as_ref(), context)?
            ))
        }
        LeanSetBuiltinCompilationKind::IntersectAssociative => {
            if let (Obj::Intersect(left_outer), Obj::Intersect(right_outer)) = (left, right) {
                if let Obj::Intersect(left_inner) = left_outer.left.as_ref() {
                    if obj_equality_key(left_inner.left.as_ref())
                        == obj_equality_key(right_outer.left.as_ref())
                    {
                        if let Obj::Intersect(right_inner) = right_outer.right.as_ref() {
                            if obj_equality_key(left_inner.right.as_ref())
                                == obj_equality_key(right_inner.left.as_ref())
                                && obj_equality_key(left_outer.right.as_ref())
                                    == obj_equality_key(right_inner.right.as_ref())
                            {
                                return Ok(format!(
                                    "Litex.SetRules.intersectAssociative {} {} {}",
                                    render_obj(left_inner.left.as_ref(), context)?,
                                    render_obj(left_inner.right.as_ref(), context)?,
                                    render_obj(left_outer.right.as_ref(), context)?
                                ));
                            }
                        }
                    }
                }
            }
            let reversed: Fact =
                EqualFact::new(right.clone(), left.clone(), fact.line_file()).into();
            Ok(symmetric(render_structural_set_equality(
                &reversed, rule, context,
            )?))
        }
        _ => Err("non-equality set rule reached structural equality renderer".into()),
    }
}
