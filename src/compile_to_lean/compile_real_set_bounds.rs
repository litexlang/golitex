use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferRealSetBoundFactResult, InferRealSetBoundedFactResult,
};
use std::collections::HashMap;

pub(super) fn bound_parts(fact: &AtomicFact) -> Option<(&str, bool, &Obj, Option<&Obj>)> {
    Some(match fact {
        AtomicFact::RealSetBoundFact(f) => (bound_name(f.direction), false, &f.set, Some(&f.bound)),
        AtomicFact::NotRealSetBoundFact(f) => {
            (bound_name(f.direction), true, &f.set, Some(&f.bound))
        }
        AtomicFact::RealSetBoundedFact(f) => (bounded_name(f.boundedness), false, &f.set, None),
        AtomicFact::NotRealSetBoundedFact(f) => (bounded_name(f.boundedness), true, &f.set, None),
        _ => return None,
    })
}
fn bound_name(direction: RealBoundDirection) -> &'static str {
    match direction {
        RealBoundDirection::Upper => "RealUpperBound",
        RealBoundDirection::Lower => "RealLowerBound",
    }
}
fn bounded_name(kind: RealBoundedness) -> &'static str {
    match kind {
        RealBoundedness::Above => "RealBoundedAbove",
        RealBoundedness::Below => "RealBoundedBelow",
        RealBoundedness::Both => "RealBounded",
    }
}
pub(super) fn contains_parameter(obj: &Obj, id: IdentifierId) -> bool {
    let mut ids = std::collections::HashSet::new();
    crate::instantiate::collect_free_plain_ids(obj, &std::collections::HashSet::new(), &mut ids);
    ids.contains(&id)
}
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::new(
        &format!("RealBounds/{stage}"),
        "Real-bound evidence has another source set, bound, direction, binder, clause or proof identity.",
    )
}
pub(super) fn parameter<'a>(
    list: &'a TypedParameterList,
    carrier: &Obj,
) -> Result<&'a BoundName, LeanCompileError> {
    let [group] = list.groups.as_slice() else {
        return Err(invalid("Binder"));
    };
    let [p] = group.params.as_slice() else {
        return Err(invalid("Binder"));
    };
    if !matches!(&group.param_type, ParamType::Obj(s) if s.ir() == carrier.ir()) {
        return Err(invalid("Carrier"));
    }
    Ok(p)
}
pub(super) fn validate_bound<'a>(
    set: &Obj,
    bound: &Obj,
    direction: RealBoundDirection,
    fact: &'a Fact,
) -> Result<&'a BoundName, LeanCompileError> {
    let Fact::ForallFact(f) = fact else {
        return Err(invalid("Universal"));
    };
    let p = parameter(&f.typed_parameters, set)?;
    let x = Obj::Identifier(IdentifierObj::from_bound_name(p));
    let (left, right) = match direction {
        RealBoundDirection::Upper => (&x, bound),
        RealBoundDirection::Lower => (bound, &x),
    };
    if !f.dom_facts.is_empty()
        || !matches!(f.then_facts.as_slice(), [ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::LessEqualFact(c))] if c.left.ir() == left.ir() && c.right.ir() == right.ir())
    {
        return Err(invalid("OrderClause"));
    }
    if contains_parameter(set, p.id) || contains_parameter(bound, p.id) {
        return Err(invalid("BinderCapture"));
    }
    Ok(p)
}
pub(super) fn validate_existence(
    set: &Obj,
    direction: RealBoundDirection,
    fact: &Fact,
) -> Result<(), LeanCompileError> {
    let Fact::ExistFact(f) = fact else {
        return Err(invalid("Existence"));
    };
    let p = parameter(&f.typed_parameters, &Obj::StandardSet(StandardSet::R))?;
    let b = Obj::Identifier(IdentifierObj::from_bound_name(p));
    if !matches!(f.facts.as_slice(), [QuantifierFreeFact::AtomicFact(AtomicFact::RealSetBoundFact(c))] if c.set.ir() == set.ir() && c.bound.ir() == b.ir() && c.direction == direction)
        || contains_parameter(set, p.id)
    {
        return Err(invalid("ExistenceClause"));
    }
    Ok(())
}
fn directions(kind: RealBoundedness) -> &'static [RealBoundDirection] {
    use RealBoundDirection::*;
    match kind {
        RealBoundedness::Above => &[Upper],
        RealBoundedness::Below => &[Lower],
        RealBoundedness::Both => &[Lower, Upper],
    }
}

impl LitexToLeanCompiler {
    pub(super) fn validate_real_bound_domain(
        &self,
        fact: &AtomicFact,
        requirements: &[&Fact],
    ) -> Result<(), LeanCompileError> {
        let Some((_, _, set, bound)) = bound_parts(fact) else {
            return Ok(());
        };
        if requirements.len() != 1 + usize::from(bound.is_some())
            || !matches!(requirements.first(), Some(Fact::AtomicFact(AtomicFact::SubsetFact(f))) if f.left.ir() == set.ir() && f.right == Obj::StandardSet(StandardSet::R))
        {
            return Err(invalid("Domain"));
        }
        if let Some(bound) = bound {
            if !matches!(requirements[1], Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir() == bound.ir() && f.set == Obj::StandardSet(StandardSet::R))
            {
                return Err(invalid("BoundDomain"));
            }
        }
        Ok(())
    }

    pub(super) fn compile_real_bound_definition(
        &self,
        goal: &AtomicFact,
        requirements: &[Fact],
        proofs: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let count = match goal {
            AtomicFact::RealSetBoundFact(_) => 1,
            AtomicFact::RealSetBoundedFact(f) => directions(f.boundedness).len(),
            _ => return Err(invalid("Family")),
        };
        if requirements.len() != count || proofs.len() != count {
            return Err(invalid("DefinitionArity"));
        }
        let mut terms = Vec::new();
        for (index, (requirement, proof)) in requirements.iter().zip(proofs).enumerate() {
            if source_subject(proof)? != *requirement {
                return Err(invalid("ProofSubject"));
            }
            match goal {
                AtomicFact::RealSetBoundFact(f) => {
                    validate_bound(&f.set, &f.bound, f.direction, requirement)?;
                }
                AtomicFact::RealSetBoundedFact(f) => {
                    validate_existence(&f.set, directions(f.boundedness)[index], requirement)?
                }
                _ => unreachable!(),
            }
            let prior = position.atomic_search_prior(index)?;
            let mut checked = self.compile_verify(proof, &prior)?;
            if let Fact::ForallFact(f) = requirement {
                for id in f.typed_parameters.ordered_param_ids() {
                    let level = format!("Type v{}}}", id.value());
                    checked.0 = checked.0.replace(&level, "Type u}");
                    checked.1 = checked.1.replace(&level, "Type u}");
                }
            }
            terms.push(format!("(show {} from {})", checked.0, checked.1));
        }
        match goal {
            AtomicFact::RealSetBoundFact(f) => Ok(format!(
                "(Litex.real{}BoundOfForall {} {} {})",
                if f.direction == RealBoundDirection::Upper {
                    "Upper"
                } else {
                    "Lower"
                },
                self.compile_object_reference(&f.set, position)?,
                self.compile_object_reference(&f.bound, position)?,
                terms[0]
            )),
            _ if terms.len() == 2 => Ok(format!("⟨{}, {}⟩", terms[0], terms[1])),
            _ => Ok(terms.remove(0)),
        }
    }

    pub(super) fn compile_real_bound_inferences(
        &self,
        infer: &InferAtomicFactResult,
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let (source, derived) = match infer {
            InferAtomicFactResult::RealSetBoundFact(rules) if rules.len() == 1 => {
                let InferRealSetBoundFactResult::Definition(p) = &rules[0];
                (p.source_fact_id, &p.derived)
            }
            InferAtomicFactResult::RealSetBoundedFact(rules) if rules.len() == 1 => {
                let InferRealSetBoundedFactResult::Definition(p) = &rules[0];
                (p.source_fact_id, &p.derived)
            }
            _ => return Err(invalid("InferenceFamily")),
        };
        let Fact::AtomicFact(atomic) = seed else {
            return Err(invalid("InferenceSeed"));
        };
        let count = match atomic {
            AtomicFact::RealSetBoundFact(_) => 1,
            AtomicFact::RealSetBoundedFact(f) => {
                if f.boundedness == RealBoundedness::Both {
                    4
                } else {
                    1
                }
            }
            _ => return Err(invalid("InferenceSeed")),
        };
        if source != seed.fact_id() || derived.len() != count {
            return Err(invalid("InferenceIdentity"));
        }
        let mut out = Vec::new();
        for (index, stored) in derived.iter().enumerate() {
            let prior = SourcePosition {
                before: position.before + index,
                ..*position
            };
            let fact = self.resolve_fact(stored.primary_fact_id(), &prior)?;
            self.validate_store(&stored.store, &fact)?;
            let (proposition, term) = match atomic {
                AtomicFact::RealSetBoundFact(f) => {
                    let p = validate_bound(&f.set, &f.bound, f.direction, &fact)?;
                    let name = format!("_value_i{}", p.id.value());
                    let value = format!("(Litex.denote {name})");
                    let set = self.compile_object_reference(&f.set, &prior)?;
                    let binders = format!(
                        "{{_Host : Type _}} [_rep : Litex.Representation M _Host] ({name} : Litex.Obj (M := M) _Host) (_member : Litex.In {name} {set})"
                    );
                    let Fact::ForallFact(f) = &fact else {
                        unreachable!()
                    };
                    let bindings = HashMap::from([(p.id, value.clone())]);
                    let conclusion = self.compile_function_raw_predicate(
                        &f.then_facts[0].clone().into(),
                        &prior,
                        &bindings,
                    )?;
                    (
                        format!("∀ {binders}, {conclusion}"),
                        format!("(fun {binders} => ({}) {value} _member)", compiled.1),
                    )
                }
                AtomicFact::RealSetBoundedFact(f) => {
                    let dirs = directions(f.boundedness);
                    let projection;
                    if index < dirs.len() {
                        validate_existence(&f.set, dirs[index], &fact)?;
                        projection = index + 1;
                    } else {
                        let expected = if index == 2 {
                            RealBoundedness::Above
                        } else {
                            RealBoundedness::Below
                        };
                        if !matches!(&fact,Fact::AtomicFact(AtomicFact::RealSetBoundedFact(c)) if c.set.ir() == f.set.ir() && c.boundedness == expected)
                        {
                            return Err(invalid("BoundedComponent"));
                        }
                        projection = if index == 2 { 2 } else { 1 };
                    }
                    let term = if f.boundedness == RealBoundedness::Both {
                        format!("({}).{projection}", compiled.1)
                    } else {
                        compiled.1.clone()
                    };
                    (
                        self.compile_function_raw_predicate(&fact, &prior, &HashMap::new())?,
                        term,
                    )
                }
                _ => unreachable!(),
            };
            out.push(self.emit_internal_fact(&fact, &(proposition, term), &prior)?);
        }
        Ok(out)
    }
}
