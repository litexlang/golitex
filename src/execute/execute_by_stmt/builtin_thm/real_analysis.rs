//! Native contracts of the legacy completeness, Archimedean and density theorems.
use super::helper::*;
use crate::ast::fact::Fact;
use crate::ast::obj::{Obj, StandardSet};
use crate::builtin_theorem::BuiltinTheoremId;
use crate::runtime::Runtime;

pub(super) fn prepare_real_analysis(
    rt: &mut Runtime,
    id: BuiltinTheoremId,
    args: &[Obj],
) -> Result<(Vec<Fact>, Vec<Fact>), String> {
    use BuiltinTheoremId::*;
    let real = Obj::StandardSet(StandardSet::R);
    let a = args[0].clone();
    if id == RealArchimedeanNaturalUpperBound {
        let requirement = atomic_in(rt, a.clone(), real).into();
        let n = rt.fresh_internal_param();
        let body = less(rt, a, identifier(&n));
        return Ok((
            vec![requirement],
            vec![exist(
                rt,
                typed(n, Obj::StandardSet(StandardSet::NPos)),
                vec![body],
                false,
            )],
        ));
    }
    let b = args[1].clone();
    if id == RationalBetweenReals {
        let requirements = vec![
            atomic_in(rt, a.clone(), real.clone()).into(),
            atomic_in(rt, b.clone(), real).into(),
            less(rt, a.clone(), b.clone()).into(),
        ];
        let q = rt.fresh_internal_param();
        let body = vec![less(rt, a, identifier(&q)), less(rt, identifier(&q), b)];
        return Ok((
            requirements,
            vec![exist(
                rt,
                typed(q, Obj::StandardSet(StandardSet::Q)),
                body,
                false,
            )],
        ));
    }
    let upper = matches!(
        id,
        RealLeastUpperBoundExists | RealMemberLeLeastUpperBound | RealLeastUpperBoundLeUpperBound
    );
    let name = if upper {
        "is_real_least_upper_bound"
    } else {
        "is_real_greatest_lower_bound"
    };
    let mut requirements = vec![
        subset(rt, a.clone(), real.clone()).into(),
        atomic_in(rt, b.clone(), real.clone()).into(),
    ];
    if matches!(id, RealLeastUpperBoundExists | RealGreatestLowerBoundExists) {
        requirements.push(nonempty(rt, a.clone()).into());
        requirements.push(bound_requirement(rt, a.clone(), b, upper));
        let c = rt.fresh_internal_param();
        let body = certificate(rt, name, a, identifier(&c));
        return Ok((
            requirements,
            vec![exist(rt, typed(c, real), vec![body], false)],
        ));
    }
    requirements.push(certificate(rt, name, a.clone(), b.clone()).into());
    let c = args[2].clone();
    let conclusion = if matches!(
        id,
        RealMemberLeLeastUpperBound | RealGreatestLowerBoundLeMember
    ) {
        requirements.push(atomic_in(rt, c.clone(), a).into());
        if upper {
            le(rt, c, b)
        } else {
            le(rt, b, c)
        }
    } else {
        requirements.push(atomic_in(rt, c.clone(), real).into());
        requirements.push(bound_requirement(rt, a, c.clone(), upper));
        if upper {
            le(rt, b, c)
        } else {
            le(rt, c, b)
        }
    };
    Ok((requirements, vec![conclusion.into()]))
}

fn bound_requirement(rt: &mut Runtime, set: Obj, value: Obj, upper: bool) -> Fact {
    let x = rt.fresh_internal_param();
    let body = if upper {
        le(rt, identifier(&x), value)
    } else {
        le(rt, value, identifier(&x))
    };
    forall(rt, x, set, vec![], vec![body])
}
