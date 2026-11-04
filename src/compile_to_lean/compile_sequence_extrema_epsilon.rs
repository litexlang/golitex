//! Validate exact source bound and tail-hit subjects for selected epsilon schemas.
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::compile_sequence_analysis::call_matches;
use super::LeanCompileError;
use crate::prelude::*;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("SequenceExtremaEpsilon/{stage}"))
}
fn ident(p: &BoundName) -> Obj {
    Obj::Identifier(IdentifierObj::from_bound_name(p))
}
fn fresh(p: &BoundName, args: &[&Obj], previous: &[IdentifierId]) -> Result<(), LeanCompileError> {
    if previous.contains(&p.id) || args.iter().any(|o| contains_parameter(o, p.id)) {
        return Err(invalid("BinderCapture"));
    }
    Ok(())
}
fn delta(object: &Obj, value: &Obj, epsilon: &Obj, plus: bool) -> bool {
    match (object, plus) {
        (Obj::ArithmeticOperator(ArithmeticOperator::Add(p)), true) => {
            p.left.ir() == value.ir() && p.right.ir() == epsilon.ir()
        }
        (Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)), false) => {
            p.left.ir() == value.ir() && p.right.ir() == epsilon.ir()
        }
        _ => false,
    }
}
pub(super) fn validate_bound(
    upper: bool,
    sequence: &Obj,
    value: &Obj,
    epsilon: &Obj,
    goal: &Fact,
) -> Result<(), LeanCompileError> {
    let Fact::ExistFact(f) = goal else {
        return Err(invalid("BoundExistence"));
    };
    let cutoff = parameter(&f.typed_parameters, &Obj::StandardSet(StandardSet::NPos))?;
    fresh(cutoff, &[sequence, value, epsilon], &[])?;
    let [QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(subset))] = f.facts.as_slice()
    else {
        return Err(invalid("BoundSubset"));
    };
    let Obj::SetFormer(SetFormer::SetBuilder(tail)) = &subset.left else {
        return Err(invalid("Tail"));
    };
    fresh(
        &tail.param_binding,
        &[sequence, value, epsilon],
        &[cutoff.id],
    )?;
    if tail.param_set.as_ref() != &Obj::StandardSet(StandardSet::NPos)
        || !matches!(tail.facts.as_slice(),[QuantifierFreeFact::AtomicFact(AtomicFact::GreaterEqualFact(g))]
            if g.left.ir()==ident(&tail.param_binding).ir() && g.right.ir()==ident(cutoff).ir())
    {
        return Err(invalid("TailCutoff"));
    }
    let Obj::FunctionSpace(FunctionSpace::PreimageSet(preimage)) = &subset.right else {
        return Err(invalid("Preimage"));
    };
    let Obj::SetFormer(SetFormer::SetBuilder(ray)) = preimage.target_set.as_ref() else {
        return Err(invalid("Ray"));
    };
    fresh(
        &ray.param_binding,
        &[sequence, value, epsilon],
        &[cutoff.id, tail.param_binding.id],
    )?;
    if preimage.function.ir() != sequence.ir()
        || ray.param_set.as_ref() != &Obj::StandardSet(StandardSet::R)
    {
        return Err(invalid("RaySubject"));
    }
    let [QuantifierFreeFact::AtomicFact(AtomicFact::LessFact(order))] = ray.facts.as_slice() else {
        return Err(invalid("StrictRay"));
    };
    let (actual, endpoint) = if upper {
        (&order.left, &order.right)
    } else {
        (&order.right, &order.left)
    };
    if actual.ir() != ident(&ray.param_binding).ir() || !delta(endpoint, value, epsilon, upper) {
        return Err(invalid("StrictRayEndpoint"));
    }
    Ok(())
}
pub(super) fn validate_hit(
    upper: bool,
    sequence: &Obj,
    value: &Obj,
    epsilon: &Obj,
    cutoff: &Obj,
    goal: &Fact,
) -> Result<(), LeanCompileError> {
    let Fact::ExistFact(f) = goal else {
        return Err(invalid("HitExistence"));
    };
    let n = parameter(&f.typed_parameters, &Obj::StandardSet(StandardSet::NPos))?;
    fresh(n, &[sequence, value, epsilon, cutoff], &[])?;
    let [QuantifierFreeFact::AndFact(conj)] = f.facts.as_slice() else {
        return Err(invalid("HitConjunction"));
    };
    let [AtomicFact::GreaterEqualFact(after), AtomicFact::LessFact(hit)] = conj.facts.as_slice()
    else {
        return Err(invalid("OrderedHitClauses"));
    };
    let (actual, endpoint) = if upper {
        (&hit.right, &hit.left)
    } else {
        (&hit.left, &hit.right)
    };
    if after.left.ir() != ident(n).ir()
        || after.right.ir() != cutoff.ir()
        || !call_matches(actual, sequence, &ident(n))
        || !delta(endpoint, value, epsilon, !upper)
    {
        return Err(invalid("HitSubjects"));
    }
    Ok(())
}
