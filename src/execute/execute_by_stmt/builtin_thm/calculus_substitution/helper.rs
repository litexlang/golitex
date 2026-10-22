use crate::execute::execute_fact_stmt::real_analysis::analysis_apply as call;
use crate::execute::execute_fact_stmt::riemann_integral::helper::*;
use crate::prelude::*;

// Retain real signature and full coverage obligations in the ordinary theorem
// evidence, including when the outer function lives on a different interval.
pub(super) fn covering(
    rt: &mut Runtime,
    function: &Obj,
    region: &Obj,
) -> RuntimeResult<Option<Vec<Fact>>> {
    let Some(domain) = rt.checked_real_function_limit_domain(
        function,
        VerifyState::new(VerifyStateLevel::BuiltinRule),
    )?
    else {
        return Ok(None);
    };
    let signature = domain.source.signature.clone();
    Ok(Some(vec![
        member(
            rt,
            function.clone(),
            Obj::FunctionSpace(FunctionSpace::FnSet(signature.clone())),
        )
        .into(),
        subset(rt, domain.domain.clone(), real()).into(),
        subset(rt, *signature.ret_set, real()).into(),
        subset(rt, region.clone(), domain.domain).into(),
    ]))
}

pub(super) fn continuous(rt: &mut Runtime, function: Obj, region: Obj) -> Fact {
    let x = rt.fresh_internal_param();
    let condition = FunctionContinuousAtFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        function,
        point: id(&x),
        side: RealApproachSide::Both,
        line_file: None,
    };
    super::super::helper::forall(rt, x, region, vec![], vec![condition.into()])
}

pub(super) fn image(rt: &mut Runtime, function: Obj, source: Obj, target: Obj) -> Fact {
    let x = rt.fresh_internal_param();
    let condition = member(rt, call(function, id(&x)), target);
    super::super::helper::forall(rt, x, source, vec![], vec![condition])
}

pub(super) fn derivative(rt: &mut Runtime, function: Obj, value: Obj, region: Obj) -> Fact {
    let x = rt.fresh_internal_param();
    let condition = rt.derivative_candidate(function, id(&x), call(value, id(&x)));
    super::super::helper::forall(rt, x, region, vec![], vec![condition])
}

// The initial continuous-integrand interface accepts R, finite nonempty open
// intervals, or finite nonempty closed intervals (including a singleton).
pub(super) fn interval_region(rt: &mut Runtime, region: &Obj) -> Option<Vec<Fact>> {
    let mut req = vec![subset(rt, region.clone(), real()).into()];
    let (bounds, closed) = match region {
        Obj::StandardSet(StandardSet::R) => return Some(req),
        Obj::SetFormer(SetFormer::IntervalObj(IntervalObj::LeftOpenRightOpen(bounds))) => {
            (bounds, false)
        }
        Obj::SetFormer(SetFormer::IntervalObj(IntervalObj::LeftClosedRightClosed(bounds))) => {
            (bounds, true)
        }
        _ => return None,
    };
    req.push(member(rt, *bounds.start.clone(), real()).into());
    req.push(member(rt, *bounds.end.clone(), real()).into());
    req.push(if closed {
        le(rt, *bounds.start.clone(), *bounds.end.clone()).into()
    } else {
        lt(rt, *bounds.start.clone(), *bounds.end.clone()).into()
    });
    Some(req)
}
