//! Replay the stored epsilon-delta definition on its captured complete domain.
use super::compile_function_continuity::continuity_side;
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::compile_sequence_analysis::call_matches;
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferFunctionContinuousAtFactResult};
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(super) fn compile_function_continuity_definition(
        &self,
        source: &FunctionContinuousAtFact,
        wd: &AtomicFactWellDefinedProof,
        proof: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::BuiltinFunctionContinuousAtDefinitionProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
        let PredicateDomainProof::FunctionAnalysis(formation) = &wd.detailed_ref().predicate_domain
        else {
            return Err(invalid("Formation"));
        };
        let ([clause], [checked]) = (
            proof.requirement_facts.as_slice(),
            proof.proof_of_requirement_facts.as_slice(),
        ) else {
            return Err(invalid("DefinitionArity"));
        };
        validate_continuity_clause(source, &formation.function_domain.domain, clause)?;
        if source_subject(checked)? != *clause {
            return Err(invalid("DefinitionSubject"));
        }
        let (ty, term) = self.compile_verify(checked, &position.atomic_search_prior(0)?)?;
        let formed = position.atomic_search_prior(1)?;
        let (view, equal) = self.compile_function_limit_domain_view(
            &source.function,
            &formation.function_domain,
            &formed,
        )?;
        let function = self.compile_object_reference(&source.function, &formed)?;
        let point = self.compile_object_reference(&source.point, &formed)?;
        let side = continuity_side(source.side);
        Ok(format!("(by\n{view}\n  exact Litex.functionContinuousAtOfForall .{side} {function} {point} _domain {equal} (show {ty} from {term})\n)"))
    }

    pub(super) fn compile_function_continuity_inferences(
        &self,
        infer: &InferAtomicFactResult,
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let (
            InferAtomicFactResult::FunctionContinuousAtFact(rules),
            Fact::AtomicFact(AtomicFact::FunctionContinuousAtFact(source)),
        ) = (infer, seed)
        else {
            return Err(invalid("InferenceFamily"));
        };
        let [InferFunctionContinuousAtFactResult::Definition(proof)] = rules.as_slice() else {
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
        let (all, epsilon) =
            validate_continuity_clause(source, &proof.function_domain.domain, &fact)?;
        let (view, equal) = self.compile_function_limit_domain_view(
            &source.function,
            &proof.function_domain,
            position,
        )?;
        // Revalidate all original complete-domain obligations; no new search.
        let real =
            self.compile_real_function_domain(&source.function, &proof.function_domain, position)?;
        let id = epsilon.id.value();
        let value = format!("_value_i{id}");
        let raw = format!("(Litex.denote {value})");
        let header = format!("{{_Host_i{id} : Type _}} [_rep_i{id} : Litex.Representation M _Host_i{id}] ({value} : Litex.Obj (M := M) _Host_i{id}) (_member_i{id} : Litex.In {value} (Litex.RPos (M := M)))");
        let clause = self.compile_function_raw_predicate(
            &all.then_facts[0].clone().into(),
            position,
            &HashMap::from([(epsilon.id, raw.clone())]),
        )?;
        let function = self.compile_object_reference(&source.function, position)?;
        let point = self.compile_object_reference(&source.point, position)?;
        let side = continuity_side(source.side);
        let ty = format!("∀ {header}, {clause}");
        let term = format!("(by\n{view}\n  have _continuity_real : Litex.RealFunctionValue M (Litex.denote {function}) := {real}\n  intro _Host _rep {value} _member_i{id}\n  have _continuity_control := Litex.functionContinuousAtControl .{side} {function} {point} {value} _member_i{id} {}\n  have _continuity_domain_eq := {equal}\n  rw [← _continuity_domain_eq] at _continuity_control\n  exact _continuity_control\n)", compiled.1);
        Ok(vec![self.emit_internal_fact(
            &fact,
            &(ty, term),
            position,
        )?])
    }
}

pub(super) fn validate_continuity_clause<'a>(
    source: &FunctionContinuousAtFact,
    domain: &Obj,
    fact: &'a Fact,
) -> Result<(&'a ForallFact, &'a BoundName), LeanCompileError> {
    let Fact::ForallFact(all) = fact else {
        return Err(invalid("Universal"));
    };
    let epsilon = parameter(&all.typed_parameters, &Obj::StandardSet(StandardSet::RPos))?;
    fresh(epsilon, &[&source.function, &source.point, domain], &[])?;
    if !all.dom_facts.is_empty() {
        return Err(invalid("ExtraPremise"));
    }
    let [ExistOrAndChainAtomicFact::ExistFact(exists)] = all.then_facts.as_slice() else {
        return Err(invalid("DeltaExistence"));
    };
    validate_continuity_control(source, domain, &identifier(epsilon), exists)?;
    Ok((all, epsilon))
}

pub(super) fn validate_continuity_control<'a>(
    source: &FunctionContinuousAtFact,
    domain: &Obj,
    epsilon: &Obj,
    exists: &'a PlainExistFact,
) -> Result<&'a BoundName, LeanCompileError> {
    let delta = parameter(
        &exists.typed_parameters,
        &Obj::StandardSet(StandardSet::RPos),
    )?;
    let sources = [&source.function, &source.point, domain, epsilon];
    fresh(delta, &sources, &[])?;
    let [QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(inclusion))] =
        exists.facts.as_slice()
    else {
        return Err(invalid("ControlInclusion"));
    };
    let near = builder(&inclusion.left)?;
    if near.param_set.ir() != domain.ir() {
        return Err(invalid("NeighborhoodDomain"));
    }
    fresh(&near.param_binding, &sources, &[delta.id])?;
    let input = identifier(&near.param_binding);
    let clauses = &near.facts;
    let distance = match source.side {
        RealApproachSide::Both => {
            let [QuantifierFreeFact::AtomicFact(close)] = clauses.as_slice() else {
                return Err(invalid("NeighborhoodClause"));
            };
            close
        }
        RealApproachSide::Left | RealApproachSide::Right => {
            let [QuantifierFreeFact::AtomicFact(side), QuantifierFreeFact::AtomicFact(close)] =
                clauses.as_slice()
            else {
                return Err(invalid("SideClauses"));
            };
            let (left, right, strict) = source_order_oriented(side)?;
            let (expected_left, expected_right) = if source.side == RealApproachSide::Left {
                (&input, &source.point)
            } else {
                (&source.point, &input)
            };
            if strict || left.ir() != expected_left.ir() || right.ir() != expected_right.ir() {
                return Err(invalid("ClosedSide"));
            }
            close
        }
    };
    let (mut left, right, strict) = source_order_oriented(distance)?;
    if !strict || right.ir() != identifier(delta).ir() {
        return Err(invalid("StrictDelta"));
    }
    if source.side == RealApproachSide::Both {
        let Obj::ArithmeticOperator(ArithmeticOperator::Abs(abs)) = left else {
            return Err(invalid("NeighborhoodAbsolute"));
        };
        left = &abs.arg;
    }
    let Obj::ArithmeticOperator(ArithmeticOperator::Sub(sub)) = left else {
        return Err(invalid("NeighborhoodDistance"));
    };
    let (a, b) = if source.side == RealApproachSide::Left {
        (&source.point, &input)
    } else {
        (&input, &source.point)
    };
    if sub.left.ir() != a.ir() || sub.right.ir() != b.ir() {
        return Err(invalid("DistanceOrientation"));
    }
    let Obj::FunctionSpace(FunctionSpace::PreimageSet(preimage)) = &inclusion.right else {
        return Err(invalid("Preimage"));
    };
    if preimage.function.ir() != source.function.ir() {
        return Err(invalid("PreimageFunction"));
    }
    let ball = builder(&preimage.target_set)?;
    if ball.param_set.as_ref() != &Obj::StandardSet(StandardSet::R) {
        return Err(invalid("BallCarrier"));
    }
    fresh(
        &ball.param_binding,
        &sources,
        &[delta.id, near.param_binding.id],
    )?;
    let [QuantifierFreeFact::AtomicFact(close)] = ball.facts.as_slice() else {
        return Err(invalid("BallClause"));
    };
    let (left, right, strict) = source_order_oriented(close)?;
    if !strict || right.ir() != epsilon.ir() {
        return Err(invalid("StrictEpsilon"));
    }
    let Obj::ArithmeticOperator(ArithmeticOperator::Abs(abs)) = left else {
        return Err(invalid("BallAbsolute"));
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Sub(sub)) = abs.arg.as_ref() else {
        return Err(invalid("BallDistance"));
    };
    if sub.left.ir() != identifier(&ball.param_binding).ir()
        || !call_matches(&sub.right, &source.function, &source.point)
    {
        return Err(invalid("BallCenter"));
    }
    Ok(delta)
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
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("ContinuityDefinition/{stage}"))
}
