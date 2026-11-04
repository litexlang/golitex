//! Replay the exact pair-set epsilon/delta clauses of uniform continuity.
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::compile_sequence_analysis::call_matches;
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::prelude::*;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferFunctionContinuousFactResult};
use std::collections::HashMap;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("UniformContinuity/{stage}"))
}
fn identifier(p: &BoundName) -> Obj {
    Obj::Identifier(IdentifierObj::from_bound_name(p))
}
fn fresh(p: &BoundName, sources: &[&Obj], prior: &[IdentifierId]) -> Result<(), LeanCompileError> {
    if prior.contains(&p.id) || sources.iter().any(|s| contains_parameter(s, p.id)) {
        Err(invalid("BinderCapture"))
    } else {
        Ok(())
    }
}
fn builder(obj: &Obj) -> Result<&SetBuilder, LeanCompileError> {
    match obj {
        Obj::SetFormer(SetFormer::SetBuilder(b)) => Ok(b),
        _ => Err(invalid("PairBuilder")),
    }
}
pub(super) fn cart_domain(obj: &Obj) -> Result<&Obj, LeanCompileError> {
    let Obj::ProductShape(ProductShape::Cart(cart)) = obj else {
        return Err(invalid("CartesianSquare"));
    };
    let [left, right] = cart.args.as_slice() else {
        return Err(invalid("PairArity"));
    };
    if left.ir() != right.ir() {
        return Err(invalid("PairDomains"));
    }
    Ok(left)
}
pub(super) fn coordinate(call: &Obj, pair: &Obj, index: &str) -> bool {
    // Calls are compared using the same unary application representation as the producer.
    call_matches(
        call,
        pair,
        &Obj::Literal(Literal::Number(Number::new(index.to_owned()))),
    )
}
fn distance(
    builder: &SetBuilder,
    function: Option<&Obj>,
    radius: &Obj,
) -> Result<(), LeanCompileError> {
    let [QuantifierFreeFact::AtomicFact(close)] = builder.facts.as_slice() else {
        return Err(invalid("PairClause"));
    };
    let (left, right, strict) = source_order_oriented(close)?;
    if !strict || right.ir() != radius.ir() {
        return Err(invalid("StrictRadius"));
    }
    let Obj::ArithmeticOperator(ArithmeticOperator::Abs(abs)) = left else {
        return Err(invalid("AbsoluteDistance"));
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Sub(sub)) = abs.arg.as_ref() else {
        return Err(invalid("PairDifference"));
    };
    let pair = identifier(&builder.param_binding);
    let matches = |obj: &Obj, index| {
        if let Some(f) = function {
            let Obj::FnObj(call) = obj else {
                return false;
            };
            call.head.as_ref() == &FnObjHead::from_obj(f.clone())
                && matches!(call.body.as_slice(), [args] if matches!(args.as_slice(), [arg] if coordinate(arg, &pair, index)))
        } else {
            coordinate(obj, &pair, index)
        }
    };
    if !matches(&sub.left, "1") || !matches(&sub.right, "2") {
        return Err(invalid("CoordinateOrFunction"));
    }
    Ok(())
}

/// Returns the exact shared Cartesian domain; no replacement by a larger carrier.
pub(super) fn validate_uniform_control<'a>(
    function: &Obj,
    epsilon: &Obj,
    exists: &'a PlainExistFact,
) -> Result<(&'a Obj, &'a BoundName), LeanCompileError> {
    let delta = parameter(
        &exists.typed_parameters,
        &Obj::StandardSet(StandardSet::RPos),
    )?;
    let [QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(inclusion))] =
        exists.facts.as_slice()
    else {
        return Err(invalid("ControlInclusion"));
    };
    let near = builder(&inclusion.left)?;
    let image = builder(&inclusion.right)?;
    let domain = cart_domain(&near.param_set)?;
    if cart_domain(&image.param_set)?.ir() != domain.ir() {
        return Err(invalid("ActualDomain"));
    }
    let sources = [function, epsilon, domain];
    fresh(delta, &sources, &[])?;
    fresh(&near.param_binding, &sources, &[delta.id])?;
    fresh(
        &image.param_binding,
        &sources,
        &[delta.id, near.param_binding.id],
    )?;
    distance(near, None, &identifier(delta))?;
    distance(image, Some(function), epsilon)?;
    Ok((domain, delta))
}
pub(super) fn validate_uniform_clause<'a>(
    function: &Obj,
    fact: &'a Fact,
) -> Result<(&'a ForallFact, &'a BoundName, &'a Obj), LeanCompileError> {
    let Fact::ForallFact(all) = fact else {
        return Err(invalid("Universal"));
    };
    let epsilon = parameter(&all.typed_parameters, &Obj::StandardSet(StandardSet::RPos))?;
    if !all.dom_facts.is_empty() {
        return Err(invalid("ExtraPremise"));
    }
    let [ExistOrAndChainAtomicFact::ExistFact(exists)] = all.then_facts.as_slice() else {
        return Err(invalid("DeltaExistence"));
    };
    let (domain, _) = validate_uniform_control(function, &identifier(epsilon), exists)?;
    fresh(epsilon, &[function, domain], &[])?;
    Ok((all, epsilon, domain))
}

impl LitexToLeanCompiler {
    pub(super) fn compile_uniform_continuity_definition(
        &self,
        source: &FunctionContinuousFact,
        wd: &AtomicFactWellDefinedProof,
        proof: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::BuiltinFunctionContinuousDefinitionProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if source.property != FunctionContinuityProperty::UniformContinuous {
            return Err(invalid("DefinitionProperty"));
        }
        let PredicateDomainProof::FunctionAnalysis(formation) = &wd
            .as_detailed()
            .map_err(|_| invalid("DetailedFormation"))?
            .predicate_domain
        else {
            return Err(invalid("DefinitionFormation"));
        };
        let ([fact], [checked]) = (
            proof.requirement_facts.as_slice(),
            proof.proof_of_requirement_facts.as_slice(),
        ) else {
            return Err(invalid("DefinitionArity"));
        };
        let (_, _, domain) = validate_uniform_clause(&source.function, fact)?;
        if domain.ir() != formation.function_domain.domain.ir() || source_subject(checked)? != *fact
        {
            return Err(invalid("DefinitionSubjectOrDomain"));
        }
        let (ty, term) = self.compile_verify(checked, &position.atomic_search_prior(0)?)?;
        let formed = position.atomic_search_prior(1)?;
        let (view, equality) = self.compile_function_limit_domain_view(
            &source.function,
            &formation.function_domain,
            &formed,
        )?;
        let f = self.compile_object_reference(&source.function, &formed)?;
        Ok(format!("(by\n{view}\n  exact Litex.functionUniformOfForall {f} _domain {equality} (show {ty} from {term})\n)"))
    }

    pub(super) fn compile_uniform_continuity_inferences(
        &self,
        infer: &InferAtomicFactResult,
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let (
            InferAtomicFactResult::FunctionContinuousFact(rules),
            Fact::AtomicFact(AtomicFact::FunctionContinuousFact(source)),
        ) = (infer, seed)
        else {
            return Err(invalid("InferenceFamily"));
        };
        if source.property != FunctionContinuityProperty::UniformContinuous {
            return Err(invalid("InferenceProperty"));
        }
        let [InferFunctionContinuousFactResult::Definition(proof)] = rules.as_slice() else {
            return Err(invalid("InferenceRule"));
        };
        let [stored] = proof.derived.as_slice() else {
            return Err(invalid("InferenceArity"));
        };
        if proof.source_fact_id != seed.fact_id() {
            return Err(invalid("InferenceIdentity"));
        }
        let fact = self.resolve_fact(stored.primary_fact_id(), position)?;
        self.validate_store(&stored.store, &fact)?;
        let (all, epsilon, domain) = validate_uniform_clause(&source.function, &fact)?;
        let (view, equality) =
            self.compile_global_property_domain_view(&source.function, domain, position)?;
        let id = epsilon.id.value();
        let value = format!("_value_i{id}");
        let clause = self.compile_function_raw_predicate(
            &all.then_facts[0].clone().into(),
            position,
            &HashMap::from([(epsilon.id, format!("(Litex.denote {value})"))]),
        )?;
        let ty = format!("∀ {{_Host_i{id} : Type _}} [_rep_i{id} : Litex.Representation M _Host_i{id}] ({value} : Litex.Obj (M := M) _Host_i{id}), Litex.In {value} (Litex.RPos (M := M)) → {clause}");
        let f = self.compile_object_reference(&source.function, position)?;
        let term = format!("(by\n{view}\n  intro _Host _rep {value} _member_i{id}\n  exact Litex.functionUniformForall {f} _domain {equality} {} {value} _member_i{id}\n)", compiled.1);
        Ok(vec![self.emit_internal_fact(
            &fact,
            &(ty, term),
            position,
        )?])
    }
}
