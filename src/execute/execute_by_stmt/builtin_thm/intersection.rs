//! Explicit intersection membership contracts; no automatic quantified search.
use super::helper::*;
use crate::ast::fact::Fact;
use crate::ast::obj::{Obj, SetOperator};
use crate::builtin_theorem::BuiltinTheoremId;
use crate::runtime::Runtime;

pub(super) fn prepare_intersection(
    rt: &mut Runtime,
    id: BuiltinTheoremId,
    args: &[Obj],
) -> Result<(Vec<Fact>, Vec<Fact>), String> {
    let element = args[0].clone();
    let intersection = args[1].clone();
    let member = atomic_in(rt, element.clone(), intersection.clone());
    match id {
        BuiltinTheoremId::FamilyIntersectionMember
        | BuiltinTheoremId::FamilyIntersectionMemberFacts => {
            let Obj::SetOperator(SetOperator::FamilyIntersect(family)) = &intersection else {
                return Err("second argument must be family_intersect(...)".into());
            };
            let family = family.left.as_ref().clone();
            // Absolute empty intersection is not a set equal to {}. These
            // set-valued contracts deliberately require a nonempty family.
            let mut requirements = vec![
                is_set(rt, family.clone()).into(),
                nonempty(rt, family.clone()).into(),
            ];
            let factor = rt.fresh_internal_param();
            let factor_obj = identifier(&factor);
            let set_fact = is_set(rt, factor_obj.clone());
            let in_factor = atomic_in(rt, element, factor_obj);
            let pointwise = forall(
                rt,
                factor,
                family.clone(),
                vec![set_fact.into()],
                vec![in_factor],
            );
            if id == BuiltinTheoremId::FamilyIntersectionMemberFacts {
                requirements.push(member.into());
                Ok((requirements, vec![pointwise]))
            } else {
                let set_factor = rt.fresh_internal_param();
                let set_fact = is_set(rt, identifier(&set_factor));
                let all_factors_are_sets = forall(rt, set_factor, family, vec![], vec![set_fact]);
                requirements.extend([all_factors_are_sets, pointwise]);
                Ok((requirements, vec![member.into()]))
            }
        }
        BuiltinTheoremId::IndexedIntersectionMember => {
            let Obj::SetOperator(SetOperator::IndexIntersect(indexed)) = &intersection else {
                return Err("second argument must be index_intersect(...)".into());
            };
            // Constructor WD retains the exact domain, powerset return carrier
            // and nonempty index requirements. Every fiber is checked explicitly.
            let index = rt.fresh_internal_param();
            let value = apply(&indexed.family_fn, vec![identifier(&index)])?;
            let in_fiber = atomic_in(rt, element.clone(), value);
            let pointwise = forall(
                rt,
                index,
                indexed.index_set.as_ref().clone(),
                vec![],
                vec![in_fiber],
            );
            let requirements = vec![
                atomic_in(rt, element, indexed.ambient_set.as_ref().clone()).into(),
                pointwise,
            ];
            Ok((requirements, vec![member.into()]))
        }
        _ => unreachable!(),
    }
}
