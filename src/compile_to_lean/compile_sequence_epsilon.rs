//! Validate and replay the native epsilon-tail clauses of real sequences.
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::compile_sequence_analysis::call_matches;
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use std::collections::HashMap;

pub(super) fn limit_parts(fact: &AtomicFact) -> Option<(&Obj, &Obj, bool)> {
    match fact {
        AtomicFact::HasSequenceLimitFact(f) => Some((&f.sequence, &f.value, false)),
        AtomicFact::NotHasSequenceLimitFact(f) => Some((&f.sequence, &f.value, true)),
        _ => None,
    }
}
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::new(&format!("SequenceEpsilon/{stage}"),
        "The recorded epsilon clause differs in its carrier, binder, tail, function, distance or inclusion.")
}
fn identifier(p: &BoundName) -> Obj {
    Obj::Identifier(IdentifierObj::from_bound_name(p))
}
fn fresh(
    p: &BoundName,
    source: &[&Obj],
    preceding: &[IdentifierId],
) -> Result<(), LeanCompileError> {
    if preceding.contains(&p.id) || source.iter().any(|s| contains_parameter(s, p.id)) {
        Err(invalid("BinderCapture"))
    } else {
        Ok(())
    }
}
fn builder(obj: &Obj) -> Result<&SetBuilder, LeanCompileError> {
    match obj {
        Obj::SetFormer(SetFormer::SetBuilder(b)) => Ok(b),
        _ => Err(invalid("Builder")),
    }
}
fn clause(builder: &SetBuilder) -> Result<&AtomicFact, LeanCompileError> {
    match builder.facts.as_slice() {
        [QuantifierFreeFact::AtomicFact(f)] => Ok(f),
        _ => Err(invalid("BuilderClause")),
    }
}
fn tail<'a>(
    obj: &'a Obj,
    cutoff: &Obj,
    source: &[&Obj],
    outer: &[IdentifierId],
) -> Result<&'a BoundName, LeanCompileError> {
    let b = builder(obj)?;
    if b.param_set.as_ref() != &Obj::StandardSet(StandardSet::NPos) {
        return Err(invalid("TailCarrier"));
    }
    fresh(&b.param_binding, source, outer)?;
    let (left, right, strict) = source_order_oriented(clause(b)?)?;
    if strict || left.ir() != cutoff.ir() || right.ir() != identifier(&b.param_binding).ir() {
        return Err(invalid("TailComparison"));
    }
    Ok(&b.param_binding)
}
fn distance<'a>(
    fact: &'a AtomicFact,
    epsilon: &Obj,
) -> Result<(&'a Obj, &'a Obj), LeanCompileError> {
    let (left, right, strict) = source_order_oriented(fact)?;
    if !strict || right.ir() != epsilon.ir() {
        return Err(invalid("StrictEpsilon"));
    }
    let Obj::ArithmeticOperator(ArithmeticOperator::Abs(a)) = left else {
        return Err(invalid("DistanceAbs"));
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Sub(d)) = a.arg.as_ref() else {
        return Err(invalid("DistanceSub"));
    };
    Ok((&d.left, &d.right))
}
fn indexed_call(obj: &Obj, sequence: &Obj, pair: &Obj, coordinate: i128) -> bool {
    let Obj::FnObj(call) = obj else {
        return false;
    };
    let [args] = call.body.as_slice() else {
        return false;
    };
    let [arg] = args.as_slice() else {
        return false;
    };
    let Obj::FnObj(index) = arg.as_ref() else {
        return false;
    };
    let [indices] = index.body.as_slice() else {
        return false;
    };
    let [value] = indices.as_slice() else {
        return false;
    };
    matches!(value.as_ref(), Obj::Literal(Literal::Number(_)))
        && closed_integer(value) == Some(coordinate)
        && call_matches(arg, pair, value)
        && call_matches(obj, sequence, arg)
}
pub(super) fn validate_limit_existence<'a>(
    sequence: &Obj,
    fact: &'a Fact,
) -> Result<&'a PlainExistFact, LeanCompileError> {
    let Fact::ExistFact(f) = fact else {
        return Err(invalid("LimitExistence"));
    };
    let value = parameter(&f.typed_parameters, &Obj::StandardSet(StandardSet::R))?;
    fresh(value, &[sequence], &[])?;
    if !matches!(f.facts.as_slice(), [QuantifierFreeFact::AtomicFact(AtomicFact::HasSequenceLimitFact(c))]
        if c.sequence.ir() == sequence.ir() && c.value.ir() == identifier(value).ir())
    {
        return Err(invalid("LimitWitness"));
    }
    Ok(f)
}

/// `value=None` denotes the Cauchy two-index control; `Some` is a fixed limit.
pub(super) fn validate_epsilon_clause<'a>(
    sequence: &Obj,
    value: Option<&Obj>,
    fact: &'a Fact,
) -> Result<(&'a ForallFact, &'a BoundName), LeanCompileError> {
    let Fact::ForallFact(f) = fact else {
        return Err(invalid("Universal"));
    };
    let epsilon = parameter(&f.typed_parameters, &Obj::StandardSet(StandardSet::RPos))?;
    let mut source = vec![sequence];
    if let Some(v) = value {
        source.push(v);
    }
    fresh(epsilon, &source, &[])?;
    if !f.dom_facts.is_empty() {
        return Err(invalid("ExtraPremise"));
    }
    let [ExistOrAndChainAtomicFact::ExistFact(exists)] = f.then_facts.as_slice() else {
        return Err(invalid("CutoffExistence"));
    };
    validate_control_clause(sequence, value, &identifier(epsilon), exists)?;
    Ok((f, epsilon))
}

pub(super) fn validate_control_clause<'a>(
    sequence: &Obj,
    value: Option<&Obj>,
    epsilon: &Obj,
    exists: &'a PlainExistFact,
) -> Result<&'a BoundName, LeanCompileError> {
    let mut source = vec![sequence, epsilon];
    if let Some(value) = value {
        source.push(value);
    }
    let cutoff = parameter(
        &exists.typed_parameters,
        &Obj::StandardSet(StandardSet::NPos),
    )?;
    fresh(cutoff, &source, &[])?;
    let [QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(inclusion))] =
        exists.facts.as_slice()
    else {
        return Err(invalid("Inclusion"));
    };
    let outer = [cutoff.id];
    let e = epsilon;
    let n = identifier(cutoff);
    if let Some(value) = value {
        let tail_parameter = tail(&inclusion.left, &n, &source, &outer)?;
        let Obj::FunctionSpace(FunctionSpace::PreimageSet(preimage)) = &inclusion.right else {
            return Err(invalid("Preimage"));
        };
        if preimage.function.ir() != sequence.ir() {
            return Err(invalid("PreimageFunction"));
        }
        let ball = builder(&preimage.target_set)?;
        if ball.param_set.as_ref() != &Obj::StandardSet(StandardSet::R) {
            return Err(invalid("BallCarrier"));
        }
        fresh(
            &ball.param_binding,
            &source,
            &[cutoff.id, tail_parameter.id],
        )?;
        let (left, right) = distance(clause(ball)?, e)?;
        if left.ir() != identifier(&ball.param_binding).ir() || right.ir() != value.ir() {
            return Err(invalid("BallCenter"));
        }
    } else {
        let Obj::ProductShape(ProductShape::Cart(product)) = &inclusion.left else {
            return Err(invalid("TailProduct"));
        };
        let [left, right] = product.args.as_slice() else {
            return Err(invalid("TailProductArity"));
        };
        if left.ir() != right.ir() {
            return Err(invalid("TailProductFactors"));
        }
        let tail_parameter = tail(left, &n, &source, &outer)?;
        let pairs = builder(&inclusion.right)?;
        let Obj::ProductShape(ProductShape::Cart(carrier)) = pairs.param_set.as_ref() else {
            return Err(invalid("PairCarrier"));
        };
        if carrier.args.len() != 2
            || carrier
                .args
                .iter()
                .any(|a| a.as_ref() != &Obj::StandardSet(StandardSet::NPos))
        {
            return Err(invalid("PairIndices"));
        }
        fresh(
            &pairs.param_binding,
            &source,
            &[cutoff.id, tail_parameter.id],
        )?;
        let (left, right) = distance(clause(pairs)?, e)?;
        let pair = identifier(&pairs.param_binding);
        if !indexed_call(left, sequence, &pair, 1) || !indexed_call(right, sequence, &pair, 2) {
            return Err(invalid("PairCalls"));
        }
    }
    Ok(cutoff)
}

impl LitexToLeanCompiler {
    pub(super) fn compile_sequence_epsilon_definition(
        &self,
        sequence: &Obj,
        value: Option<&Obj>,
        requirements: &[Fact],
        proofs: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let ([clause], [proof]) = (requirements, proofs) else {
            return Err(invalid("DefinitionArity"));
        };
        validate_epsilon_clause(sequence, value, clause)?;
        if source_subject(proof)? != *clause {
            return Err(invalid("DefinitionSubject"));
        }
        let (ty, term) = self.compile_verify(proof, &position.atomic_search_prior(0)?)?;
        let sequence = self.compile_object_reference(sequence, position)?;
        let (law, args) = if let Some(value) = value {
            (
                "sequenceLimitOfForall",
                format!(
                    "{sequence} {}",
                    self.compile_object_reference(value, position)?
                ),
            )
        } else {
            ("sequenceCauchyOfForall", sequence)
        };
        Ok(format!("(Litex.{law} {args} (show {ty} from {term}))"))
    }

    pub(super) fn compile_sequence_epsilon_inference(
        &self,
        sequence: &Obj,
        fact: &Fact,
        term: &str,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let (all, epsilon) = validate_epsilon_clause(sequence, None, fact)?;
        let id = epsilon.id.value();
        let value = format!("_value_i{id}");
        let raw = format!("(Litex.denote {value})");
        let header = format!("{{_Host_i{id} : Type _}} [_rep_i{id} : Litex.Representation M _Host_i{id}] ({value} : Litex.Obj (M := M) _Host_i{id}) (_member_i{id} : Litex.In {value} (Litex.RPos (M := M)))");
        let conclusion = self.compile_function_raw_predicate(
            &all.then_facts[0].clone().into(),
            position,
            &HashMap::from([(epsilon.id, raw.clone())]),
        )?;
        Ok((
            format!("∀ {header}, {conclusion}"),
            format!("(fun {header} => ({term}) {raw} _member_i{id})"),
        ))
    }
}
