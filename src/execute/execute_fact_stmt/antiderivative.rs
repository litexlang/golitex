//! Antiderivatives are relations between existing functions, never new objects.
#[cfg(test)]
#[path = "../../../tests/unit/execute/riemann_integral/antiderivatives.rs"]
mod tests;
use super::riemann_integral::helper::*;
use crate::prelude::*;

pub(crate) const PREDICATE: &str = "is_antiderivative_on";

pub(crate) fn arguments(fact: &AtomicFact) -> Option<&[Obj]> {
    match fact {
        AtomicFact::NormalAtomicFact(f) if f.predicate == AtomicName::plain(PREDICATE.into()) => {
            Some(&f.body)
        }
        AtomicFact::NotNormalAtomicFact(f)
            if f.predicate == AtomicName::plain(PREDICATE.into()) =>
        {
            Some(&f.body)
        }
        _ => None,
    }
}

// Retain ordinary checked membership/subset facts as the WD evidence. Actual
// function domains may be larger than I and need not agree with one another.
pub(crate) fn domain_requirements(
    rt: &mut Runtime,
    args: &[Obj],
    state: VerifyState,
) -> RuntimeResult<Option<Vec<Fact>>> {
    let region = args[2].clone();
    let mut req = vec![subset(rt, region.clone(), real()).into()];
    // Equality on a region transfers classical derivatives only at interior
    // points. This first interface accepts R or explicit nonempty open intervals.
    // In particular it never turns equality on {0} into derivative equality.
    match &region {
        Obj::StandardSet(StandardSet::R) => {}
        Obj::SetFormer(SetFormer::IntervalObj(IntervalObj::LeftOpenRightOpen(bounds))) => {
            req.push(member(rt, *bounds.start.clone(), real()).into());
            req.push(member(rt, *bounds.end.clone(), real()).into());
            req.push(lt(rt, *bounds.start.clone(), *bounds.end.clone()).into());
        }
        _ => return Ok(None),
    }
    for function in &args[..2] {
        let Some(domain) = rt.checked_real_function_limit_domain(function, state)? else {
            return Ok(None);
        };
        let signature = domain.source.signature.clone();
        req.push(
            member(
                rt,
                function.clone(),
                Obj::FunctionSpace(FunctionSpace::FnSet(signature.clone())),
            )
            .into(),
        );
        req.push(subset(rt, domain.domain.clone(), real()).into());
        req.push(subset(rt, *signature.ret_set, real()).into());
        req.push(subset(rt, region.clone(), domain.domain).into());
    }
    Ok(Some(req))
}

pub(crate) fn relation(rt: &mut Runtime, primitive: Obj, function: Obj, region: Obj) -> AtomicFact {
    certificate(rt, PREDICATE, vec![primitive, function, region])
}

pub(crate) fn definition(rt: &mut Runtime, primitive: Obj, function: Obj, region: Obj) -> Fact {
    let x = rt.fresh_internal_param();
    let derivative = rt.derivative_candidate(
        primitive,
        id(&x),
        super::real_analysis::analysis_apply(function, id(&x)),
    );
    super::function_limit::function_limit_forall(rt, x, region, vec![], vec![derivative.into()])
}
