//! Elementary set algebra equality rules.

use super::super::*;

pub(in super::super) fn render_set_relation_reflexivity(
    fact: &Fact,
    expected_subset_spelling: bool,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let (source, target, negated, subset_spelling) = normalized_set_relation_parts(fact)?;
    if negated
        || subset_spelling != expected_subset_spelling
        || obj_equality_key(source) != obj_equality_key(target)
    {
        return Err("set-relation reflexivity changed its spelling or endpoints".into());
    }
    render_fact(fact, context)?;
    Ok("(fun _x __membership => __membership)".into())
}

pub(in super::super) fn render_extended_set_rule(
    fact: &Fact,
    rule: LeanSetBuiltinCompilationKind,
    premises: &[CompiledFactProofBody],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    render_fact(fact, context)?;
    match rule {
        LeanSetBuiltinCompilationKind::UnionSetMinusDecomposition
        | LeanSetBuiltinCompilationKind::IntersectIdempotent
        | LeanSetBuiltinCompilationKind::IntersectSetMinusSelfEmpty
        | LeanSetBuiltinCompilationKind::SetMinusSelfEmpty
        | LeanSetBuiltinCompilationKind::SetMinusEmptyRight
        | LeanSetBuiltinCompilationKind::SetMinusEmptyLeft
        | LeanSetBuiltinCompilationKind::SetMinusIntersectSelf => {
            if !premises.is_empty() {
                return Err("elementary structural set equality retained premises".into());
            }
            render_elementary_set_equality(fact, rule, context)
        }
        LeanSetBuiltinCompilationKind::UnionAbsorptionFromSubset => {
            if premises.len() != 1 {
                return Err("union absorption requires one subset premise".into());
            }
            render_union_absorption_from_subset(fact, &premises[0], context)
        }
        LeanSetBuiltinCompilationKind::IntersectSetMinusDisjointFromSubset => {
            if premises.len() != 1 {
                return Err("set-minus disjointness requires one subset premise".into());
            }
            render_intersect_set_minus_disjoint_from_subset(fact, &premises[0], context)
        }
        LeanSetBuiltinCompilationKind::EmptySubset => {
            if !premises.is_empty() {
                return Err("empty-subset rule retained premises".into());
            }
            let (empty, target) = subset_parts(fact)?;
            if !matches!(empty, Obj::ListSet(set) if set.list.is_empty()) {
                return Err("empty-subset rule changed its empty left endpoint".into());
            }
            Ok(format!(
                "Litex.SetRules.emptySubset {}",
                render_obj(target, context)?
            ))
        }
        LeanSetBuiltinCompilationKind::SubsetUnionLeft
        | LeanSetBuiltinCompilationKind::SubsetUnionRight => {
            if !premises.is_empty() {
                return Err("subset-union inclusion retained premises".into());
            }
            let (source, target) = subset_parts(fact)?;
            let Obj::Union(union) = target else {
                return Err("subset-union inclusion changed its target constructor".into());
            };
            let (expected, theorem) = if rule == LeanSetBuiltinCompilationKind::SubsetUnionLeft {
                (union.left.as_ref(), "subsetUnionLeft")
            } else {
                (union.right.as_ref(), "subsetUnionRight")
            };
            if obj_equality_key(source) != obj_equality_key(expected) {
                return Err("subset-union inclusion changed its selected operand".into());
            }
            Ok(format!(
                "Litex.SetRules.{theorem} {} {}",
                render_obj(union.left.as_ref(), context)?,
                render_obj(union.right.as_ref(), context)?
            ))
        }
        LeanSetBuiltinCompilationKind::UnionSubset => {
            if premises.len() != 2 {
                return Err("union-subset rule requires two ordered subset premises".into());
            }
            let (source, target) = subset_parts(fact)?;
            let Obj::Union(union) = source else {
                return Err("union-subset rule changed its source constructor".into());
            };
            for (premise, operand) in premises.iter().zip([&union.left, &union.right]) {
                let (premise_source, premise_target) = subset_parts(&premise.fact)?;
                if obj_equality_key(premise_source) != obj_equality_key(operand.as_ref())
                    || obj_equality_key(premise_target) != obj_equality_key(target)
                {
                    return Err("union-subset rule changed its ordered premises".into());
                }
            }
            Ok(format!(
                "Litex.SetRules.unionSubset ({}) ({})",
                premises[0].proof_expression, premises[1].proof_expression
            ))
        }
        LeanSetBuiltinCompilationKind::IntersectSubsetLeft
        | LeanSetBuiltinCompilationKind::IntersectSubsetRight
        | LeanSetBuiltinCompilationKind::SetMinusSubsetLeft => {
            if !premises.is_empty() {
                return Err("constructor-subset rule retained premises".into());
            }
            let (source, target) = subset_parts(fact)?;
            let (left, right, expected, theorem) = match (rule, source) {
                (LeanSetBuiltinCompilationKind::IntersectSubsetLeft, Obj::Intersect(value)) => (
                    value.left.as_ref(),
                    value.right.as_ref(),
                    value.left.as_ref(),
                    "intersectSubsetLeft",
                ),
                (LeanSetBuiltinCompilationKind::IntersectSubsetRight, Obj::Intersect(value)) => (
                    value.left.as_ref(),
                    value.right.as_ref(),
                    value.right.as_ref(),
                    "intersectSubsetRight",
                ),
                (LeanSetBuiltinCompilationKind::SetMinusSubsetLeft, Obj::SetMinus(value)) => (
                    value.left.as_ref(),
                    value.right.as_ref(),
                    value.left.as_ref(),
                    "setMinusSubsetLeft",
                ),
                _ => return Err("constructor-subset rule changed its constructor".into()),
            };
            if obj_equality_key(target) != obj_equality_key(expected) {
                return Err("constructor-subset rule changed its projected operand".into());
            }
            Ok(format!(
                "Litex.SetRules.{theorem} {} {}",
                render_obj(left, context)?,
                render_obj(right, context)?
            ))
        }
        LeanSetBuiltinCompilationKind::UnionFinite
        | LeanSetBuiltinCompilationKind::IntersectFinite
        | LeanSetBuiltinCompilationKind::SetMinusFiniteLeft => {
            let target = finite_set_parts(fact)?;
            let (left, right, theorem, expected_premises) = match (rule, target) {
                (LeanSetBuiltinCompilationKind::UnionFinite, Obj::Union(value)) => {
                    (value.left.as_ref(), value.right.as_ref(), "unionFinite", 2)
                }
                (LeanSetBuiltinCompilationKind::IntersectFinite, Obj::Intersect(value)) => (
                    value.left.as_ref(),
                    value.right.as_ref(),
                    "intersectFinite",
                    2,
                ),
                (LeanSetBuiltinCompilationKind::SetMinusFiniteLeft, Obj::SetMinus(value)) => (
                    value.left.as_ref(),
                    value.right.as_ref(),
                    "setMinusFiniteLeft",
                    1,
                ),
                _ => return Err("finite-set rule changed its target constructor".into()),
            };
            if premises.len() != expected_premises
                || obj_equality_key(finite_set_parts(&premises[0].fact)?) != obj_equality_key(left)
                || (expected_premises == 2
                    && obj_equality_key(finite_set_parts(&premises[1].fact)?)
                        != obj_equality_key(right))
            {
                return Err("finite-set rule changed its ordered finiteness premises".into());
            }
            let mut terms = vec![
                format!("Litex.SetRules.{theorem}"),
                render_obj(left, context)?,
                render_obj(right, context)?,
                format!("({})", premises[0].proof_expression),
            ];
            if expected_premises == 2 && rule == LeanSetBuiltinCompilationKind::UnionFinite {
                terms.push(format!("({})", premises[1].proof_expression));
            }
            Ok(terms.join(" "))
        }
        LeanSetBuiltinCompilationKind::UnionNonemptyLeft
        | LeanSetBuiltinCompilationKind::UnionNonemptyRight => {
            if premises.len() != 1 {
                return Err("union nonemptiness requires one selected premise".into());
            }
            let target = nonempty_set_parts(fact)?;
            let Obj::Union(union) = target else {
                return Err("union nonemptiness changed its target constructor".into());
            };
            let (expected, theorem) = if rule == LeanSetBuiltinCompilationKind::UnionNonemptyLeft {
                (union.left.as_ref(), "unionNonemptyLeft")
            } else {
                (union.right.as_ref(), "unionNonemptyRight")
            };
            if obj_equality_key(nonempty_set_parts(&premises[0].fact)?)
                != obj_equality_key(expected)
            {
                return Err("union nonemptiness changed its selected operand".into());
            }
            Ok(format!(
                "Litex.SetRules.{theorem} {} {} ({})",
                render_obj(union.left.as_ref(), context)?,
                render_obj(union.right.as_ref(), context)?,
                premises[0].proof_expression
            ))
        }
        LeanSetBuiltinCompilationKind::PowerSetMembershipOfSubset => {
            if premises.len() != 1 {
                return Err("power-set membership requires one subset premise".into());
            }
            let (subset, target) = membership_parts(fact)?;
            let Obj::PowerSet(power) = target else {
                return Err("power-set membership changed its target constructor".into());
            };
            let (premise_subset, premise_base) = subset_parts(&premises[0].fact)?;
            if obj_equality_key(subset) != obj_equality_key(premise_subset)
                || obj_equality_key(power.set.as_ref()) != obj_equality_key(premise_base)
            {
                return Err("power-set membership changed its subset endpoints".into());
            }
            Ok(format!(
                "Litex.SetRules.inPowerSetOfSubset ({})",
                premises[0].proof_expression
            ))
        }
        LeanSetBuiltinCompilationKind::PowerSetNonempty => {
            if !premises.is_empty() {
                return Err("power-set nonemptiness retained premises".into());
            }
            let Obj::PowerSet(power) = nonempty_set_parts(fact)? else {
                return Err("power-set nonemptiness changed its constructor".into());
            };
            Ok(format!(
                "Litex.SetRules.powerSetNonempty {}",
                render_obj(power.set.as_ref(), context)?
            ))
        }
        LeanSetBuiltinCompilationKind::PowerSetFinite => {
            if premises.len() != 1 {
                return Err("power-set finiteness requires one base finiteness premise".into());
            }
            let Obj::PowerSet(power) = finite_set_parts(fact)? else {
                return Err("power-set finiteness changed its constructor".into());
            };
            if obj_equality_key(finite_set_parts(&premises[0].fact)?)
                != obj_equality_key(power.set.as_ref())
            {
                return Err("power-set finiteness changed its base premise".into());
            }
            Ok(format!(
                "Litex.SetRules.powerSetFinite {} ({})",
                render_obj(power.set.as_ref(), context)?,
                premises[0].proof_expression
            ))
        }
        LeanSetBuiltinCompilationKind::IntersectEqLeftOfSubset
        | LeanSetBuiltinCompilationKind::IntersectEqRightOfSubset => {
            if premises.len() != 1 {
                return Err("intersection absorption requires one subset premise".into());
            }
            let (left, right) = equality_parts(fact)?;
            let Obj::Intersect(intersection) = left else {
                return Err("intersection absorption changed its equality constructor".into());
            };
            let (premise_left, premise_right) = subset_parts(&premises[0].fact)?;
            let (expected_result, expected_left, expected_right, theorem) =
                if rule == LeanSetBuiltinCompilationKind::IntersectEqLeftOfSubset {
                    (
                        intersection.left.as_ref(),
                        intersection.left.as_ref(),
                        intersection.right.as_ref(),
                        "intersectEqLeftOfSubset",
                    )
                } else {
                    (
                        intersection.right.as_ref(),
                        intersection.right.as_ref(),
                        intersection.left.as_ref(),
                        "intersectEqRightOfSubset",
                    )
                };
            if obj_equality_key(right) != obj_equality_key(expected_result)
                || obj_equality_key(premise_left) != obj_equality_key(expected_left)
                || obj_equality_key(premise_right) != obj_equality_key(expected_right)
            {
                return Err("intersection absorption changed its operands".into());
            }
            Ok(format!(
                "Litex.SetRules.{theorem} ({})",
                premises[0].proof_expression
            ))
        }
        LeanSetBuiltinCompilationKind::IntersectUnionDistributive
        | LeanSetBuiltinCompilationKind::SetMinusIntersectDeMorgan
        | LeanSetBuiltinCompilationKind::SetMinusUnionDeMorgan => {
            if !premises.is_empty() {
                return Err("structural three-set equality retained premises".into());
            }
            render_three_set_equality(fact, rule, context)
        }
        LeanSetBuiltinCompilationKind::SetMinusRecoverSubset
        | LeanSetBuiltinCompilationKind::SubsetEqSetMinusRecovery => {
            if premises.len() != 1 {
                return Err("set-minus recovery requires one subset premise".into());
            }
            let (subset, left) = subset_parts(&premises[0].fact)?;
            let (equality_left, equality_right) = equality_parts(fact)?;
            let (difference, plain, reverse) =
                if rule == LeanSetBuiltinCompilationKind::SetMinusRecoverSubset {
                    (equality_left, equality_right, false)
                } else {
                    (equality_right, equality_left, true)
                };
            let Obj::SetMinus(outer) = difference else {
                return Err("set-minus recovery changed its outer constructor".into());
            };
            let Obj::SetMinus(inner) = outer.right.as_ref() else {
                return Err("set-minus recovery changed its inner constructor".into());
            };
            if obj_equality_key(plain) != obj_equality_key(subset)
                || obj_equality_key(outer.left.as_ref()) != obj_equality_key(left)
                || obj_equality_key(inner.left.as_ref()) != obj_equality_key(left)
                || obj_equality_key(inner.right.as_ref()) != obj_equality_key(subset)
            {
                return Err("set-minus recovery changed its subset operands".into());
            }
            let proof = format!(
                "Litex.SetRules.setMinusRecoverSubset ({})",
                premises[0].proof_expression
            );
            Ok(if reverse {
                format!("Litex.Same.symm ({proof})")
            } else {
                proof
            })
        }
        _ => Err("base set rule reached extended set-rule renderer".into()),
    }
}

fn render_elementary_set_equality(
    fact: &Fact,
    rule: LeanSetBuiltinCompilationKind,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let (left, right) = equality_parts(fact)?;
    let symmetric = |proof: String| format!("Litex.Same.symm ({proof})");
    match rule {
        LeanSetBuiltinCompilationKind::IntersectIdempotent => {
            for (intersection_side, retained_side, reverse) in
                [(left, right, false), (right, left, true)]
            {
                let Obj::Intersect(intersection) = intersection_side else {
                    continue;
                };
                if obj_equality_key(intersection.left.as_ref())
                    == obj_equality_key(intersection.right.as_ref())
                    && obj_equality_key(intersection.left.as_ref())
                        == obj_equality_key(retained_side)
                {
                    let proof = format!(
                        "Litex.SetRules.intersectIdempotent {}",
                        render_obj(retained_side, context)?
                    );
                    return Ok(if reverse { symmetric(proof) } else { proof });
                }
            }
            Err("intersection idempotence changed its repeated operand".into())
        }
        LeanSetBuiltinCompilationKind::UnionSetMinusDecomposition => {
            for (decomposed_side, original_side, reverse) in
                [(left, right, false), (right, left, true)]
            {
                let (Obj::Union(decomposed), Obj::Union(original)) =
                    (decomposed_side, original_side)
                else {
                    continue;
                };
                for (plain, difference, decomposed_swapped) in [
                    (decomposed.left.as_ref(), decomposed.right.as_ref(), false),
                    (decomposed.right.as_ref(), decomposed.left.as_ref(), true),
                ] {
                    let Obj::SetMinus(difference) = difference else {
                        continue;
                    };
                    if obj_equality_key(plain) != obj_equality_key(difference.right.as_ref()) {
                        continue;
                    }
                    let original_swapped = if obj_equality_key(original.left.as_ref())
                        == obj_equality_key(plain)
                        && obj_equality_key(original.right.as_ref())
                            == obj_equality_key(difference.left.as_ref())
                    {
                        false
                    } else if obj_equality_key(original.right.as_ref()) == obj_equality_key(plain)
                        && obj_equality_key(original.left.as_ref())
                            == obj_equality_key(difference.left.as_ref())
                    {
                        true
                    } else {
                        continue;
                    };
                    let plain_source = render_obj(plain, context)?;
                    let base_source = render_obj(difference.left.as_ref(), context)?;
                    let difference_source =
                        render_obj(&Obj::SetMinus(difference.clone()), context)?;
                    let mut proof = format!(
                        "Litex.SetRules.unionSetMinusDecomposition {plain_source} {base_source}"
                    );
                    if decomposed_swapped {
                        proof = format!(
                            "Litex.Same.trans (Litex.SetRules.unionCommutative {difference_source} {plain_source}) ({proof})"
                        );
                    }
                    if original_swapped {
                        proof = format!(
                            "Litex.Same.trans ({proof}) (Litex.SetRules.unionCommutative {plain_source} {base_source})"
                        );
                    }
                    return Ok(if reverse { symmetric(proof) } else { proof });
                }
            }
            Err("union set-minus decomposition changed its linked operands".into())
        }
        LeanSetBuiltinCompilationKind::IntersectSetMinusSelfEmpty => {
            for (intersection_side, empty_side, reverse) in
                [(left, right, false), (right, left, true)]
            {
                let Obj::Intersect(intersection) = intersection_side else {
                    continue;
                };
                if !is_empty_set_obj(empty_side) {
                    continue;
                }
                for (plain, difference, swapped) in [
                    (
                        intersection.left.as_ref(),
                        intersection.right.as_ref(),
                        false,
                    ),
                    (
                        intersection.right.as_ref(),
                        intersection.left.as_ref(),
                        true,
                    ),
                ] {
                    let Obj::SetMinus(difference) = difference else {
                        continue;
                    };
                    if obj_equality_key(plain) != obj_equality_key(difference.right.as_ref()) {
                        continue;
                    }
                    let plain_source = render_obj(plain, context)?;
                    let base_source = render_obj(difference.left.as_ref(), context)?;
                    let difference_source =
                        render_obj(&Obj::SetMinus(difference.clone()), context)?;
                    let mut proof = format!(
                        "Litex.SetRules.intersectSetMinusSelfEmpty {plain_source} {base_source}"
                    );
                    if swapped {
                        proof = format!(
                            "Litex.Same.trans (Litex.SetRules.intersectCommutative {difference_source} {plain_source}) ({proof})"
                        );
                    }
                    return Ok(if reverse { symmetric(proof) } else { proof });
                }
            }
            Err("intersection/set-minus disjointness changed its removed operand".into())
        }
        LeanSetBuiltinCompilationKind::SetMinusSelfEmpty => {
            render_simple_set_minus_equality(left, right, context, "self").or_else(|_| {
                render_simple_set_minus_equality(right, left, context, "self").map(symmetric)
            })
        }
        LeanSetBuiltinCompilationKind::SetMinusEmptyRight => {
            render_simple_set_minus_equality(left, right, context, "empty_right").or_else(|_| {
                render_simple_set_minus_equality(right, left, context, "empty_right").map(symmetric)
            })
        }
        LeanSetBuiltinCompilationKind::SetMinusEmptyLeft => {
            render_simple_set_minus_equality(left, right, context, "empty_left").or_else(|_| {
                render_simple_set_minus_equality(right, left, context, "empty_left").map(symmetric)
            })
        }
        LeanSetBuiltinCompilationKind::SetMinusIntersectSelf => {
            for (restricted_side, plain_side, reverse) in
                [(left, right, false), (right, left, true)]
            {
                let (Obj::SetMinus(restricted), Obj::SetMinus(plain)) =
                    (restricted_side, plain_side)
                else {
                    continue;
                };
                let Obj::Intersect(intersection) = restricted.right.as_ref() else {
                    continue;
                };
                if obj_equality_key(restricted.left.as_ref())
                    != obj_equality_key(plain.left.as_ref())
                {
                    continue;
                }
                let (removed, theorem) = if obj_equality_key(intersection.right.as_ref())
                    == obj_equality_key(restricted.left.as_ref())
                    && obj_equality_key(intersection.left.as_ref())
                        == obj_equality_key(plain.right.as_ref())
                {
                    (intersection.left.as_ref(), "setMinusIntersectSelf")
                } else if obj_equality_key(intersection.left.as_ref())
                    == obj_equality_key(restricted.left.as_ref())
                    && obj_equality_key(intersection.right.as_ref())
                        == obj_equality_key(plain.right.as_ref())
                {
                    (intersection.right.as_ref(), "setMinusIntersectSelfCommuted")
                } else {
                    continue;
                };
                let proof = format!(
                    "Litex.SetRules.{theorem} {} {}",
                    render_obj(restricted.left.as_ref(), context)?,
                    render_obj(removed, context)?
                );
                return Ok(if reverse { symmetric(proof) } else { proof });
            }
            Err("set-minus/intersection simplification changed its retained operand".into())
        }
        _ => Err("non-elementary rule reached elementary set renderer".into()),
    }
}

fn render_simple_set_minus_equality(
    difference_side: &Obj,
    result_side: &Obj,
    context: &StmtResultToLeanCompilerEnvironmentStack,
    shape: &str,
) -> Result<String, String> {
    let Obj::SetMinus(difference) = difference_side else {
        return Err("set-minus unit changed its source constructor".into());
    };
    match shape {
        "self"
            if is_empty_set_obj(result_side)
                && obj_equality_key(difference.left.as_ref())
                    == obj_equality_key(difference.right.as_ref()) =>
        {
            Ok(format!(
                "Litex.SetRules.setMinusSelfEmpty {}",
                render_obj(difference.left.as_ref(), context)?
            ))
        }
        "empty_right"
            if is_empty_set_obj(difference.right.as_ref())
                && obj_equality_key(difference.left.as_ref()) == obj_equality_key(result_side) =>
        {
            Ok(format!(
                "Litex.SetRules.setMinusEmptyRight {}",
                render_obj(result_side, context)?
            ))
        }
        "empty_left"
            if is_empty_set_obj(difference.left.as_ref()) && is_empty_set_obj(result_side) =>
        {
            Ok(format!(
                "Litex.SetRules.setMinusEmptyLeft {}",
                render_obj(difference.right.as_ref(), context)?
            ))
        }
        _ => Err("set-minus unit changed its empty or retained operand".into()),
    }
}

fn render_union_absorption_from_subset(
    fact: &Fact,
    premise: &CompiledFactProofBody,
    _context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let (subset, container) = subset_parts(&premise.fact)?;
    let (left, right) = equality_parts(fact)?;
    let symmetric = |proof: String| format!("Litex.Same.symm ({proof})");
    for (union_side, retained_side, reverse) in [(left, right, false), (right, left, true)] {
        let Obj::Union(union) = union_side else {
            continue;
        };
        if obj_equality_key(retained_side) != obj_equality_key(container) {
            continue;
        }
        let theorem = if obj_equality_key(union.left.as_ref()) == obj_equality_key(subset)
            && obj_equality_key(union.right.as_ref()) == obj_equality_key(container)
        {
            "unionEqRightOfSubset"
        } else if obj_equality_key(union.right.as_ref()) == obj_equality_key(subset)
            && obj_equality_key(union.left.as_ref()) == obj_equality_key(container)
        {
            "unionEqLeftOfSubset"
        } else {
            continue;
        };
        let proof = format!("Litex.SetRules.{theorem} ({})", premise.proof_expression);
        return Ok(if reverse { symmetric(proof) } else { proof });
    }
    Err("union absorption changed its subset or retained operand".into())
}

fn render_intersect_set_minus_disjoint_from_subset(
    fact: &Fact,
    premise: &CompiledFactProofBody,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let (subset, removed) = subset_parts(&premise.fact)?;
    let (left, right) = equality_parts(fact)?;
    let symmetric = |proof: String| format!("Litex.Same.symm ({proof})");
    for (intersection_side, empty_side, reverse) in [(left, right, false), (right, left, true)] {
        let Obj::Intersect(intersection) = intersection_side else {
            continue;
        };
        if !is_empty_set_obj(empty_side) {
            continue;
        }
        for (candidate_subset, difference, swapped) in [
            (
                intersection.left.as_ref(),
                intersection.right.as_ref(),
                false,
            ),
            (
                intersection.right.as_ref(),
                intersection.left.as_ref(),
                true,
            ),
        ] {
            let Obj::SetMinus(difference) = difference else {
                continue;
            };
            if obj_equality_key(candidate_subset) != obj_equality_key(subset)
                || obj_equality_key(difference.right.as_ref()) != obj_equality_key(removed)
            {
                continue;
            }
            let mut proof = format!(
                "Litex.SetRules.intersectSetMinusOfSubsetEmpty {} ({})",
                render_obj(difference.left.as_ref(), context)?,
                premise.proof_expression
            );
            if swapped {
                proof = format!(
                    "Litex.Same.trans (Litex.SetRules.intersectCommutative {} {}) ({proof})",
                    render_obj(&Obj::SetMinus(difference.clone()), context)?,
                    render_obj(candidate_subset, context)?
                );
            }
            return Ok(if reverse { symmetric(proof) } else { proof });
        }
    }
    Err("set-minus disjointness changed its subset premise operands".into())
}

fn is_empty_set_obj(object: &Obj) -> bool {
    matches!(object, Obj::ListSet(set) if set.list.is_empty())
}

pub(in super::super) fn render_three_set_equality(
    fact: &Fact,
    rule: LeanSetBuiltinCompilationKind,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let (left, right) = equality_parts(fact)?;
    let (first, second, third, theorem) = match rule {
        LeanSetBuiltinCompilationKind::IntersectUnionDistributive => {
            let Obj::Intersect(left_intersection) = left else {
                return Err("intersection distributivity changed its left constructor".into());
            };
            let Obj::Union(left_union) = left_intersection.right.as_ref() else {
                return Err("intersection distributivity changed its inner union".into());
            };
            let Obj::Union(right_union) = right else {
                return Err("intersection distributivity changed its right constructor".into());
            };
            let (Obj::Intersect(right_left), Obj::Intersect(right_right)) =
                (right_union.left.as_ref(), right_union.right.as_ref())
            else {
                return Err("intersection distributivity changed its result intersections".into());
            };
            let first = left_intersection.left.as_ref();
            let second = left_union.left.as_ref();
            let third = left_union.right.as_ref();
            if obj_equality_key(right_left.left.as_ref()) != obj_equality_key(first)
                || obj_equality_key(right_left.right.as_ref()) != obj_equality_key(second)
                || obj_equality_key(right_right.left.as_ref()) != obj_equality_key(first)
                || obj_equality_key(right_right.right.as_ref()) != obj_equality_key(third)
            {
                return Err("intersection distributivity changed its repeated operands".into());
            }
            (first, second, third, "intersectUnionDistributive")
        }
        LeanSetBuiltinCompilationKind::SetMinusIntersectDeMorgan => {
            let Obj::SetMinus(left_difference) = left else {
                return Err("intersection De Morgan changed its left difference".into());
            };
            let Obj::Intersect(excluded) = left_difference.right.as_ref() else {
                return Err("intersection De Morgan changed its excluded intersection".into());
            };
            let Obj::Union(result) = right else {
                return Err("intersection De Morgan changed its result union".into());
            };
            let (Obj::SetMinus(result_left), Obj::SetMinus(result_right)) =
                (result.left.as_ref(), result.right.as_ref())
            else {
                return Err("intersection De Morgan changed its result differences".into());
            };
            let first = left_difference.left.as_ref();
            let second = excluded.left.as_ref();
            let third = excluded.right.as_ref();
            if obj_equality_key(result_left.left.as_ref()) != obj_equality_key(first)
                || obj_equality_key(result_left.right.as_ref()) != obj_equality_key(second)
                || obj_equality_key(result_right.left.as_ref()) != obj_equality_key(first)
                || obj_equality_key(result_right.right.as_ref()) != obj_equality_key(third)
            {
                return Err("intersection De Morgan changed its repeated operands".into());
            }
            (first, second, third, "setMinusIntersectDeMorgan")
        }
        LeanSetBuiltinCompilationKind::SetMinusUnionDeMorgan => {
            let Obj::SetMinus(left_difference) = left else {
                return Err("union De Morgan changed its left difference".into());
            };
            let Obj::Union(excluded) = left_difference.right.as_ref() else {
                return Err("union De Morgan changed its excluded union".into());
            };
            let Obj::Intersect(result) = right else {
                return Err("union De Morgan changed its result intersection".into());
            };
            let (Obj::SetMinus(result_left), Obj::SetMinus(result_right)) =
                (result.left.as_ref(), result.right.as_ref())
            else {
                return Err("union De Morgan changed its result differences".into());
            };
            let first = left_difference.left.as_ref();
            let second = excluded.left.as_ref();
            let third = excluded.right.as_ref();
            if obj_equality_key(result_left.left.as_ref()) != obj_equality_key(first)
                || obj_equality_key(result_left.right.as_ref()) != obj_equality_key(second)
                || obj_equality_key(result_right.left.as_ref()) != obj_equality_key(first)
                || obj_equality_key(result_right.right.as_ref()) != obj_equality_key(third)
            {
                return Err("union De Morgan changed its repeated operands".into());
            }
            (first, second, third, "setMinusUnionDeMorgan")
        }
        _ => return Err("non-three-set rule reached structural renderer".into()),
    };
    Ok(format!(
        "Litex.SetRules.{theorem} {} {} {}",
        render_obj(first, context)?,
        render_obj(second, context)?,
        render_obj(third, context)?
    ))
}
