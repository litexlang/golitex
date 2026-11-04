//! Validate the original eventual-bound and every-tail-hit definition clauses.
use super::compile_real_set_bounds::contains_parameter;
use super::compile_sequence_extremum::invalid;
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

fn binder<'a>(
    groups: &'a TypedParameterList,
    index: usize,
    set: StandardSet,
) -> Result<&'a BoundName, LeanCompileError> {
    let g = groups
        .groups
        .get(index)
        .ok_or_else(|| invalid("BinderCount"))?;
    if g.params.len() != 1 || g.param_type != ParamType::Obj(Obj::StandardSet(set)) {
        return Err(invalid("BinderDomain"));
    }
    Ok(&g.params[0])
}
fn fresh(p: &BoundName, source: &[&Obj], prior: &[IdentifierId]) -> Result<(), LeanCompileError> {
    if prior.contains(&p.id) || source.iter().any(|s| contains_parameter(s, p.id)) {
        return Err(invalid("BinderCapture"));
    }
    Ok(())
}
fn ident(p: &BoundName) -> Obj {
    Obj::Identifier(IdentifierObj::from_bound_name(p))
}
fn delta_expression(object: &Obj, value: &Obj, epsilon: &Obj, plus: bool) -> bool {
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
pub(super) fn validate_extremum_clauses(
    upper: bool,
    sequence: &Obj,
    value: &Obj,
    clauses: &[Fact],
) -> Result<(), LeanCompileError> {
    let [Fact::ForallFact(bound), Fact::ForallFact(hits)] = clauses else {
        return Err(invalid("DefinitionClauses"));
    };
    if !bound.dom_facts.is_empty()
        || !hits.dom_facts.is_empty()
        || bound.typed_parameters.groups.len() != 1
        || hits.typed_parameters.groups.len() != 2
    {
        return Err(invalid("DefinitionPremises"));
    }
    let epsilon = binder(&bound.typed_parameters, 0, StandardSet::RPos)?;
    fresh(epsilon, &[sequence, value], &[])?;
    let [ExistOrAndChainAtomicFact::ExistFact(exists)] = bound.then_facts.as_slice() else {
        return Err(invalid("BoundExistence"));
    };
    if exists.typed_parameters.groups.len() != 1 {
        return Err(invalid("CutoffBinderCount"));
    }
    let cutoff = binder(&exists.typed_parameters, 0, StandardSet::NPos)?;
    fresh(cutoff, &[sequence, value], &[epsilon.id])?;
    let [QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(subset))] = exists.facts.as_slice()
    else {
        return Err(invalid("TailInclusion"));
    };
    let Obj::SetFormer(SetFormer::SetBuilder(tail)) = &subset.left else {
        return Err(invalid("Tail"));
    };
    if tail.param_set.as_ref() != &Obj::StandardSet(StandardSet::NPos) {
        return Err(invalid("TailCarrier"));
    }
    fresh(
        &tail.param_binding,
        &[sequence, value],
        &[epsilon.id, cutoff.id],
    )?;
    let [QuantifierFreeFact::AtomicFact(order)] = tail.facts.as_slice() else {
        return Err(invalid("TailOrder"));
    };
    let (a, b, strict) = source_order_oriented(order)?;
    if strict || a.ir() != ident(cutoff).ir() || b.ir() != ident(&tail.param_binding).ir() {
        return Err(invalid("TailCutoff"));
    }
    let Obj::FunctionSpace(FunctionSpace::PreimageSet(preimage)) = &subset.right else {
        return Err(invalid("Preimage"));
    };
    let Obj::SetFormer(SetFormer::SetBuilder(ray)) = preimage.target_set.as_ref() else {
        return Err(invalid("Ray"));
    };
    if preimage.function.ir() != sequence.ir()
        || ray.param_set.as_ref() != &Obj::StandardSet(StandardSet::R)
    {
        return Err(invalid("RaySubject"));
    }
    fresh(
        &ray.param_binding,
        &[sequence, value],
        &[epsilon.id, cutoff.id, tail.param_binding.id],
    )?;
    let [QuantifierFreeFact::AtomicFact(order)] = ray.facts.as_slice() else {
        return Err(invalid("RayOrder"));
    };
    let (a, b, strict) = source_order_oriented(order)?;
    let (actual, bound_value) = if upper { (a, b) } else { (b, a) };
    if !strict
        || actual.ir() != ident(&ray.param_binding).ir()
        || !delta_expression(bound_value, value, &ident(epsilon), upper)
    {
        return Err(invalid("EventualBound"));
    }
    let epsilon = binder(&hits.typed_parameters, 0, StandardSet::RPos)?;
    let cutoff = binder(&hits.typed_parameters, 1, StandardSet::NPos)?;
    fresh(epsilon, &[sequence, value], &[])?;
    fresh(cutoff, &[sequence, value], &[epsilon.id])?;
    let [ExistOrAndChainAtomicFact::ExistFact(exists)] = hits.then_facts.as_slice() else {
        return Err(invalid("HitExistence"));
    };
    if exists.typed_parameters.groups.len() != 1 {
        return Err(invalid("HitBinderCount"));
    }
    let n = binder(&exists.typed_parameters, 0, StandardSet::NPos)?;
    fresh(n, &[sequence, value], &[epsilon.id, cutoff.id])?;
    let [QuantifierFreeFact::AndFact(conj)] = exists.facts.as_slice() else {
        return Err(invalid("HitConjunction"));
    };
    let [after, hit] = conj.facts.as_slice() else {
        return Err(invalid("HitArity"));
    };
    let (a, b, strict) = source_order_oriented(after)?;
    if strict || a.ir() != ident(cutoff).ir() || b.ir() != ident(n).ir() {
        return Err(invalid("HitCutoff"));
    }
    let (a, b, strict) = source_order_oriented(hit)?;
    let (actual, near) = if upper { (b, a) } else { (a, b) };
    if !strict
        || !super::compile_sequence_analysis::call_matches(actual, sequence, &ident(n))
        || !delta_expression(near, value, &ident(epsilon), !upper)
    {
        return Err(invalid("HitValue"));
    }
    Ok(())
}
impl LitexToLeanCompiler {
    pub(super) fn compile_sequence_extremum_definition(
        &self,
        upper: bool,
        sequence: &Obj,
        value: &Obj,
        requirements: &[Fact],
        proofs: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        validate_extremum_clauses(upper, sequence, value, requirements)?;
        if proofs.len() != 2 {
            return Err(invalid("DefinitionProofArity"));
        }
        let mut terms = Vec::new();
        for (index, (requirement, proof)) in requirements.iter().zip(proofs).enumerate() {
            if source_subject(proof)? != *requirement {
                return Err(invalid("DefinitionProofSubject"));
            }
            let (ty, term) = self.compile_verify(proof, &position.atomic_search_prior(index)?)?;
            terms.push(format!("(show {ty} from {term})"));
        }
        Ok(format!(
            "(Litex.sequenceExtremumOfForall {upper} {} {} {} {})",
            self.compile_object_reference(sequence, position)?,
            self.compile_object_reference(value, position)?,
            terms[0],
            terms[1]
        ))
    }
}
