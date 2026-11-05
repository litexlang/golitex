//! Intrinsic antiderivatives retain both original, independent function domains.
use super::compile_real_set_bounds::contains_parameter;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::multivariable::helper::actual_domain;
use crate::prelude::*;

pub(super) fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("Antiderivative/{stage}"))
}

pub(super) fn is_predicate(name: &AtomicName) -> bool {
    name == &AtomicName::plain("is_antiderivative_on".into())
}

pub(super) fn parts(fact: &AtomicFact) -> Option<(&[Obj], bool)> {
    match fact {
        AtomicFact::NormalAtomicFact(p) if is_predicate(&p.predicate) => Some((&p.body, false)),
        AtomicFact::NotNormalAtomicFact(p) if is_predicate(&p.predicate) => Some((&p.body, true)),
        _ => None,
    }
}

pub(super) fn context_count(region: &Obj) -> Result<usize, LeanCompileError> {
    match region {
        Obj::StandardSet(StandardSet::R) => Ok(9),
        Obj::SetFormer(SetFormer::IntervalObj(IntervalObj::LeftOpenRightOpen(_))) => Ok(12),
        _ => Err(invalid("OriginalOpenRegion")),
    }
}

fn real_member(fact: &Fact, element: &Obj) -> bool {
    matches!(fact,Fact::AtomicFact(AtomicFact::InFact(p)) if p.element.ir()==element.ir() && p.set==Obj::StandardSet(StandardSet::R))
}
fn subset(fact: &Fact, left: &Obj, right: &Obj) -> bool {
    matches!(fact,Fact::AtomicFact(AtomicFact::SubsetFact(p)) if p.left.ir()==left.ir() && p.right.ir()==right.ir())
}

pub(super) fn validate_context(args: &[Obj], req: &[&Fact]) -> Result<(), LeanCompileError> {
    let [primitive, function, region] = args else {
        return Err(invalid("PredicateArity"));
    };
    let count = context_count(region)?;
    if req.len() != count || !subset(req[0], region, &Obj::StandardSet(StandardSet::R)) {
        return Err(invalid("OriginalRegionDomain"));
    }
    let offset = count - 8;
    if let Obj::SetFormer(SetFormer::IntervalObj(IntervalObj::LeftOpenRightOpen(bounds))) = region {
        if !real_member(req[1], &bounds.start)
            || !real_member(req[2], &bounds.end)
            || !matches!(req[3],Fact::AtomicFact(AtomicFact::LessFact(p)) if p.left.ir()==bounds.start.ir() && p.right.ir()==bounds.end.ir())
        {
            return Err(invalid("OriginalIntervalEndpointsAndOrder"));
        }
    }
    for (i, function) in [primitive, function].into_iter().enumerate() {
        let index = offset + 4 * i;
        let Fact::AtomicFact(AtomicFact::InFact(member)) = req[index] else {
            return Err(invalid("OriginalFunctionMembership"));
        };
        let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &member.set else {
            return Err(invalid("OriginalFunctionSignature"));
        };
        let params = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|group| group.params.iter())
            .collect::<Vec<_>>();
        let [binder] = params.as_slice() else {
            return Err(invalid("OriginalUnarySignature"));
        };
        if member.element.ir() != function.ir()
            || args.iter().any(|arg| contains_parameter(arg, binder.id))
            || contains_parameter(&signature.ret_set, binder.id)
        {
            return Err(invalid("OriginalFunctionSubjectAndScope"));
        }
        let domain = actual_domain(signature).ok_or_else(|| invalid("OriginalActualDomain"))?;
        if !subset(req[index + 1], &domain, &Obj::StandardSet(StandardSet::R))
            || !subset(
                req[index + 2],
                &signature.ret_set,
                &Obj::StandardSet(StandardSet::R),
            )
            || !subset(req[index + 3], region, &domain)
        {
            return Err(invalid("OriginalFunctionDomainCoverage"));
        }
    }
    Ok(())
}

impl LitexToLeanCompiler {
    pub(super) fn validate_antiderivative_domain(
        &self,
        fact: &AtomicFact,
        req: &[&Fact],
    ) -> Result<(), LeanCompileError> {
        match parts(fact) {
            Some((args, _)) => validate_context(args, req),
            None => Ok(()),
        }
    }
}
