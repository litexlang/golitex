//! Standard-set membership projection chains.

use super::super::*;

pub(in super::super) fn normalized_positive_order_operands(
    source_atomic_fact: &AtomicFact,
) -> Option<(&Obj, &Obj, bool)> {
    match source_atomic_fact {
        AtomicFact::LessFact(fact) => Some((&fact.left, &fact.right, false)),
        AtomicFact::GreaterFact(fact) => Some((&fact.right, &fact.left, false)),
        AtomicFact::LessEqualFact(fact) => Some((&fact.left, &fact.right, true)),
        AtomicFact::GreaterEqualFact(fact) => Some((&fact.right, &fact.left, true)),
        AtomicFact::NotLessFact(fact) => Some((&fact.right, &fact.left, true)),
        AtomicFact::NotGreaterFact(fact) => Some((&fact.left, &fact.right, true)),
        AtomicFact::NotLessEqualFact(fact) => Some((&fact.right, &fact.left, false)),
        AtomicFact::NotGreaterEqualFact(fact) => Some((&fact.left, &fact.right, false)),
        _ => None,
    }
}

pub(in super::super) fn standard_set_membership_projection_theorem_chain(
    source_set: StandardSet,
    target_set: StandardSet,
) -> Result<&'static [&'static str], String> {
    match (source_set, target_set) {
        (StandardSet::NPos, StandardSet::N) => Ok(&["inNOfInNPos"]),
        (StandardSet::NPos, StandardSet::Z) => Ok(&["inNOfInNPos", "inZOfInN"]),
        (StandardSet::NPos, StandardSet::Q) => Ok(&["inNOfInNPos", "inZOfInN", "inQOfInZ"]),
        (StandardSet::NPos, StandardSet::R) => {
            Ok(&["inNOfInNPos", "inZOfInN", "inQOfInZ", "inROfInQ"])
        }
        (StandardSet::NPos, StandardSet::C) => Ok(&[
            "inNOfInNPos",
            "inZOfInN",
            "inQOfInZ",
            "inROfInQ",
            "inCOfInR",
        ]),
        (StandardSet::RPos, StandardSet::R) => Ok(&["inROfInRPos"]),
        (StandardSet::RPos, StandardSet::C) => Ok(&["inROfInRPos", "inCOfInR"]),
        (StandardSet::ZStar, StandardSet::Z) => Ok(&["inZOfInZStar"]),
        (StandardSet::ZStar, StandardSet::Q) => Ok(&["inZOfInZStar", "inQOfInZ"]),
        (StandardSet::ZStar, StandardSet::R) => Ok(&["inZOfInZStar", "inQOfInZ", "inROfInQ"]),
        (StandardSet::ZStar, StandardSet::C) => {
            Ok(&["inZOfInZStar", "inQOfInZ", "inROfInQ", "inCOfInR"])
        }
        (StandardSet::QStar, StandardSet::Q) => Ok(&["inQOfInQStar"]),
        (StandardSet::QStar, StandardSet::R) => Ok(&["inQOfInQStar", "inROfInQ"]),
        (StandardSet::QStar, StandardSet::C) => Ok(&["inQOfInQStar", "inROfInQ", "inCOfInR"]),
        (StandardSet::RStar, StandardSet::R) => Ok(&["inROfInRStar"]),
        (StandardSet::RStar, StandardSet::C) => Ok(&["inROfInRStar", "inCOfInR"]),
        (StandardSet::CStar, StandardSet::C) => Ok(&["inCOfInCStar"]),
        (StandardSet::ZStar, StandardSet::QStar) => Ok(&["inQStarOfInZStar"]),
        (StandardSet::ZStar, StandardSet::RStar) => Ok(&["inQStarOfInZStar", "inRStarOfInQStar"]),
        (StandardSet::ZStar, StandardSet::CStar) => {
            Ok(&["inQStarOfInZStar", "inRStarOfInQStar", "inCStarOfInRStar"])
        }
        (StandardSet::QStar, StandardSet::RStar) => Ok(&["inRStarOfInQStar"]),
        (StandardSet::QStar, StandardSet::CStar) => Ok(&["inRStarOfInQStar", "inCStarOfInRStar"]),
        (StandardSet::RStar, StandardSet::CStar) => Ok(&["inCStarOfInRStar"]),
        (StandardSet::N, StandardSet::Z) => Ok(&["inZOfInN"]),
        (StandardSet::N, StandardSet::Q) => Ok(&["inZOfInN", "inQOfInZ"]),
        (StandardSet::N, StandardSet::R) => Ok(&["inZOfInN", "inQOfInZ", "inROfInQ"]),
        (StandardSet::N, StandardSet::C) => Ok(&["inZOfInN", "inQOfInZ", "inROfInQ", "inCOfInR"]),
        (StandardSet::Z, StandardSet::Q) => Ok(&["inQOfInZ"]),
        (StandardSet::Z, StandardSet::R) => Ok(&["inQOfInZ", "inROfInQ"]),
        (StandardSet::Z, StandardSet::C) => Ok(&["inQOfInZ", "inROfInQ", "inCOfInR"]),
        (StandardSet::Q, StandardSet::R) => Ok(&["inROfInQ"]),
        (StandardSet::Q, StandardSet::C) => Ok(&["inROfInQ", "inCOfInR"]),
        (StandardSet::R, StandardSet::C) => Ok(&["inCOfInR"]),
        _ => Err(format!(
            "unsupported standard-set membership projection `{source_set}` to `{target_set}`"
        )),
    }
}

pub(in super::super) fn render_base_set_builtin_rule_from_compiled_children(
    target: &Fact,
    rule: SetBuiltinRule,
    children: &[(Fact, String)],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    render_fact(target, context)?;
    match rule {
        SetBuiltinRule::SubsetReflexivity | SetBuiltinRule::SupersetReflexivity => {
            if !children.is_empty() {
                return Err("set-relation reflexivity retained child proofs".into());
            }
            render_set_relation_reflexivity(
                target,
                rule == SetBuiltinRule::SubsetReflexivity,
                context,
            )
        }
        SetBuiltinRule::UnionMembershipLeft | SetBuiltinRule::UnionMembershipRight => {
            let [(premise, proof)] = children else {
                return Err("union membership requires one selected child Result".into());
            };
            let (element, set) = membership_parts(target)?;
            let Obj::Union(union) = set else {
                return Err("union membership changed its target constructor".into());
            };
            let (premise_element, premise_set) = membership_parts(premise)?;
            let (selected_set, theorem) = if rule == SetBuiltinRule::UnionMembershipLeft {
                (union.left.as_ref(), "inUnionLeft")
            } else {
                (union.right.as_ref(), "inUnionRight")
            };
            if obj_equality_key(element) != obj_equality_key(premise_element)
                || obj_equality_key(selected_set) != obj_equality_key(premise_set)
            {
                return Err("union membership changed its selected side or element".into());
            }
            Ok(format!("Litex.SetRules.{theorem} ({proof})"))
        }
        SetBuiltinRule::IntersectMembershipBoth => {
            let [(left_fact, left_proof), (right_fact, right_proof)] = children else {
                return Err("intersection membership requires two ordered child Results".into());
            };
            let (element, set) = membership_parts(target)?;
            let Obj::Intersect(intersection) = set else {
                return Err("intersection membership changed its constructor".into());
            };
            for (premise, expected_set) in [
                (left_fact, intersection.left.as_ref()),
                (right_fact, intersection.right.as_ref()),
            ] {
                let (premise_element, premise_set) = membership_parts(premise)?;
                if obj_equality_key(element) != obj_equality_key(premise_element)
                    || obj_equality_key(expected_set) != obj_equality_key(premise_set)
                {
                    return Err("intersection membership changed its ordered side children".into());
                }
            }
            Ok(format!(
                "Litex.SetRules.inIntersect ({left_proof}) ({right_proof})"
            ))
        }
        SetBuiltinRule::IntersectNonMembershipLeft
        | SetBuiltinRule::IntersectNonMembershipRight => {
            let [(premise, proof)] = children else {
                return Err("intersection nonmembership requires one selected child Result".into());
            };
            let (element, set) = nonmembership_parts(target)?;
            let Obj::Intersect(intersection) = set else {
                return Err("intersection nonmembership changed its constructor".into());
            };
            let (premise_element, premise_set) = nonmembership_parts(premise)?;
            let (selected_set, theorem) = if rule == SetBuiltinRule::IntersectNonMembershipLeft {
                (intersection.left.as_ref(), "notInIntersectOfNotInLeft")
            } else {
                (intersection.right.as_ref(), "notInIntersectOfNotInRight")
            };
            if obj_equality_key(element) != obj_equality_key(premise_element)
                || obj_equality_key(selected_set) != obj_equality_key(premise_set)
            {
                return Err("intersection nonmembership changed its selected side".into());
            }
            Ok(format!("Litex.SetRules.{theorem} ({proof})"))
        }
        SetBuiltinRule::SetMinusMembership => {
            let [(left_fact, left_proof), (right_fact, right_proof)] = children else {
                return Err("set-minus membership requires two ordered child Results".into());
            };
            let (element, set) = membership_parts(target)?;
            let Obj::SetMinus(difference) = set else {
                return Err("set-minus membership changed its constructor".into());
            };
            let (left_element, left_set) = membership_parts(left_fact)?;
            let (right_element, right_set) = nonmembership_parts(right_fact)?;
            if obj_equality_key(element) != obj_equality_key(left_element)
                || obj_equality_key(element) != obj_equality_key(right_element)
                || obj_equality_key(difference.left.as_ref()) != obj_equality_key(left_set)
                || obj_equality_key(difference.right.as_ref()) != obj_equality_key(right_set)
            {
                return Err("set-minus membership changed its ordered children".into());
            }
            Ok(format!(
                "Litex.SetRules.inSetMinus ({left_proof}) ({right_proof})"
            ))
        }
        _ => Err("structural set rule reached base Result renderer".into()),
    }
}
