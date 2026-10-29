//! Check the recorded accumulation and epsilon-delta clauses before folding them.
use super::compile_function_limit::{finite_side, infinite_direction};
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::BuiltinFunctionLimitDefinitionProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::FunctionLimitApproachRealProof;
use crate::prelude::*;
use std::collections::HashMap;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("FunctionLimitDefinition/{stage}"))
}
fn identifier(p: &BoundName) -> Obj {
    Obj::Identifier(IdentifierObj::from_bound_name(p))
}
fn fresh(p: &BoundName, source: &[&Obj], prior: &[IdentifierId]) -> Result<(), LeanCompileError> {
    if prior.contains(&p.id) || source.iter().any(|s| contains_parameter(s, p.id)) {
        Err(invalid("BinderCapture"))
    } else {
        Ok(())
    }
}
fn distance_matches(distance: &Obj, side: &str, point: &Obj, input: &Obj) -> bool {
    let expression = if side == "both" {
        let Obj::ArithmeticOperator(ArithmeticOperator::Abs(a)) = distance else {
            return false;
        };
        a.arg.as_ref()
    } else {
        distance
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Sub(s)) = expression else {
        return false;
    };
    let (left, right) = if side == "left" {
        (point, input)
    } else {
        (input, point)
    };
    s.left.ir() == left.ir() && s.right.ir() == right.ir()
}
fn neighborhood_conditions(
    clauses: &[QuantifierFreeFact],
    side: &str,
    point: &Obj,
    input: &Obj,
    radius: &Obj,
) -> Result<(), LeanCompileError> {
    let [QuantifierFreeFact::AndFact(and)] = clauses else {
        return Err(invalid("PunctureConjunction"));
    };
    let [positive, close] = and.facts.as_slice() else {
        return Err(invalid("PunctureArity"));
    };
    let (zero, distance, strict) = source_order_oriented(positive)?;
    let (same_distance, bound, close_strict) = source_order_oriented(close)?;
    if !strict
        || !close_strict
        || !is_zero(zero)
        || bound.ir() != radius.ir()
        || !distance_matches(distance, side, point, input)
        || !distance_matches(same_distance, side, point, input)
    {
        return Err(invalid("PunctureDistance"));
    }
    Ok(())
}
fn universal<'a>(
    fact: &'a Fact,
    domain: &Obj,
) -> Result<(&'a ForallFact, &'a BoundName), LeanCompileError> {
    let Fact::ForallFact(f) = fact else {
        return Err(invalid("Universal"));
    };
    if !f.dom_facts.is_empty() {
        return Err(invalid("ExtraPremise"));
    }
    Ok((f, parameter(&f.typed_parameters, domain)?))
}

pub(super) fn validate_limit_existence(
    function: &Obj,
    approach: &LimitApproach,
    fact: &Fact,
) -> Result<(), LeanCompileError> {
    let Fact::ExistFact(f) = fact else {
        return Err(invalid("Existence"));
    };
    let value = parameter(&f.typed_parameters, &Obj::StandardSet(StandardSet::R))?;
    let mut source = vec![function];
    source.extend(approach.point());
    fresh(value, &source, &[])?;
    if !matches!(f.facts.as_slice(), [QuantifierFreeFact::AtomicFact(AtomicFact::HasFunctionLimitFact(p))]
        if p.function.ir() == function.ir() && p.approach == *approach
            && p.value.ir() == identifier(value).ir())
    {
        return Err(invalid("ExistenceCandidate"));
    }
    Ok(())
}

pub(super) fn validate_accumulation_clause<'a>(
    goal: &HasFunctionLimitFact,
    accumulation: &'a Fact,
) -> Result<&'a Obj, LeanCompileError> {
    let finite = goal.approach.point().is_some();
    let mut source = vec![&goal.function, &goal.value];
    source.extend(goal.approach.point());
    let radius_domain = Obj::StandardSet(if finite {
        StandardSet::RPos
    } else {
        StandardSet::R
    });
    let (all, radius) = universal(accumulation, &radius_domain)?;
    fresh(radius, &source, &[])?;
    let [ExistOrAndChainAtomicFact::ExistFact(exists)] = all.then_facts.as_slice() else {
        return Err(invalid("AccumulationWitness"));
    };
    let [group] = exists.typed_parameters.groups.as_slice() else {
        return Err(invalid("AccumulationBinder"));
    };
    let [input] = group.params.as_slice() else {
        return Err(invalid("AccumulationBinder"));
    };
    let ParamType::Obj(domain) = &group.param_type else {
        return Err(invalid("AccumulationDomain"));
    };
    fresh(input, &source, &[radius.id])?;
    if contains_parameter(domain, radius.id) || contains_parameter(domain, input.id) {
        return Err(invalid("DomainCapture"));
    }
    approach_conditions(
        &exists.facts,
        &goal.approach,
        &identifier(input),
        &identifier(radius),
    )?;

    Ok(domain)
}

fn validate_clauses<'a>(
    goal: &HasFunctionLimitFact,
    facts: &'a [Fact],
) -> Result<&'a Obj, LeanCompileError> {
    let [accumulation, epsilon] = facts else {
        return Err(invalid("ClauseArity"));
    };
    let domain = validate_accumulation_clause(goal, accumulation)?;
    let finite = goal.approach.point().is_some();
    let mut source = vec![&goal.function, &goal.value];
    source.extend(goal.approach.point());
    let radius_domain = Obj::StandardSet(if finite {
        StandardSet::RPos
    } else {
        StandardSet::R
    });
    let (all, epsilon) = universal(epsilon, &Obj::StandardSet(StandardSet::RPos))?;
    let mut scoped_source = source.clone();
    scoped_source.push(domain);
    fresh(epsilon, &scoped_source, &[])?;
    let [ExistOrAndChainAtomicFact::ExistFact(exists)] = all.then_facts.as_slice() else {
        return Err(invalid("EpsilonWitness"));
    };
    let delta = parameter(&exists.typed_parameters, &radius_domain)?;
    fresh(delta, &scoped_source, &[epsilon.id])?;
    let [QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(subset))] = exists.facts.as_slice()
    else {
        return Err(invalid("ControlInclusion"));
    };
    let Obj::SetFormer(SetFormer::SetBuilder(neighborhood)) = &subset.left else {
        return Err(invalid("Neighborhood"));
    };
    if neighborhood.param_set.ir() != domain.ir() {
        return Err(invalid("NeighborhoodDomain"));
    }
    fresh(
        &neighborhood.param_binding,
        &scoped_source,
        &[epsilon.id, delta.id],
    )?;
    approach_conditions(
        &neighborhood.facts,
        &goal.approach,
        &identifier(&neighborhood.param_binding),
        &identifier(delta),
    )?;
    let Obj::FunctionSpace(FunctionSpace::PreimageSet(preimage)) = &subset.right else {
        return Err(invalid("Preimage"));
    };
    if preimage.function.ir() != goal.function.ir() {
        return Err(invalid("PreimageFunction"));
    }
    let Obj::SetFormer(SetFormer::SetBuilder(ball)) = preimage.target_set.as_ref() else {
        return Err(invalid("Ball"));
    };
    if ball.param_set.as_ref() != &Obj::StandardSet(StandardSet::R) {
        return Err(invalid("BallCarrier"));
    }
    fresh(
        &ball.param_binding,
        &scoped_source,
        &[epsilon.id, delta.id, neighborhood.param_binding.id],
    )?;
    let [QuantifierFreeFact::AtomicFact(less)] = ball.facts.as_slice() else {
        return Err(invalid("BallCondition"));
    };
    let (distance, bound, strict) = source_order_oriented(less)?;
    if !strict
        || bound.ir() != identifier(epsilon).ir()
        || !distance_matches(
            distance,
            "both",
            &goal.value,
            &identifier(&ball.param_binding),
        )
    {
        return Err(invalid("BallDistance"));
    }
    Ok(domain)
}

fn approach_conditions(
    clauses: &[QuantifierFreeFact],
    approach: &LimitApproach,
    input: &Obj,
    bound: &Obj,
) -> Result<(), LeanCompileError> {
    if approach.point().is_some() {
        let (side, point) = finite_side(approach)?;
        return neighborhood_conditions(clauses, side, point, input, bound);
    }
    let direction = infinite_direction(approach)?;
    let [QuantifierFreeFact::AtomicFact(fact)] = clauses else {
        return Err(invalid("InfinityTail"));
    };
    let (left, right, strict) = source_order_oriented(fact)?;
    let (expected_left, expected_right) = if direction == "positive" {
        (bound, input)
    } else {
        (input, bound)
    };
    if !strict || left.ir() != expected_left.ir() || right.ir() != expected_right.ir() {
        return Err(invalid("InfinityDirection"));
    }
    Ok(())
}

impl LitexToLeanCompiler {
    pub(super) fn compile_function_limit_definition(
        &self,
        goal: &HasFunctionLimitFact,
        wd: &AtomicFactWellDefinedProof,
        proof: &BuiltinFunctionLimitDefinitionProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let domain = validate_clauses(goal, &proof.requirement_facts)?;
        let PredicateDomainProof::FunctionLimit(formation) = &wd.detailed_ref().predicate_domain
        else {
            return Err(invalid("Formation"));
        };
        if formation.function_domain.domain.ir() != domain.ir() {
            return Err(invalid("EffectiveDomain"));
        }
        if proof.requirement_facts.len() != proof.proof_of_requirement_facts.len() {
            return Err(invalid("ProofArity"));
        }
        let mut clauses = Vec::new();
        for (index, (fact, checked)) in proof
            .requirement_facts
            .iter()
            .zip(&proof.proof_of_requirement_facts)
            .enumerate()
        {
            if source_subject(checked)? != *fact {
                return Err(invalid("ProofSubject"));
            }
            let (ty, term) = self.compile_verify(checked, &position.atomic_search_prior(index)?)?;
            clauses.push(format!("(show {ty} from {term})"));
        }
        let formed = position.atomic_search_prior(2)?;
        let function = self.compile_object_reference(&goal.function, &formed)?;
        let value = self.compile_object_reference(&goal.value, &formed)?;
        let (domain_view, domain_equal) = self.compile_function_limit_domain_view(
            &goal.function,
            &formation.function_domain,
            &formed,
        )?;
        let value_real = source_subject(&formation.value_real)?.fact_id().value();
        let fold = match (&goal.approach, &formation.approach_real) {
            (approach, FunctionLimitApproachRealProof::Finite(point_real))
                if approach.point().is_some() =>
            {
                let (side, point) = finite_side(approach)?;
                let point = self.compile_object_reference(point, &formed)?;
                format!("Litex.finiteFunctionLimitOfForall .{side} {function} {point} {value} _domain _function_limit_domain {domain_equal} h_{} h_{value_real} {} {}", source_subject(point_real)?.fact_id().value(), clauses[0], clauses[1])
            }
            (
                LimitApproach::AtPositiveInfinity,
                FunctionLimitApproachRealProof::AtPositiveInfinity,
            )
            | (
                LimitApproach::AtNegativeInfinity,
                FunctionLimitApproachRealProof::AtNegativeInfinity,
            ) => {
                let direction = infinite_direction(&goal.approach)?;
                format!("Litex.infiniteFunctionLimitOfForall .{direction} {function} {value} _domain _function_limit_domain {domain_equal} h_{value_real} {} {}", clauses[0], clauses[1])
            }
            _ => return Err(invalid("ApproachReal")),
        };
        Ok(format!("(by\n{domain_view}\n  exact {fold}\n)"))
    }
    pub(super) fn compile_function_limit_domain_view(
        &self,
        function_obj: &Obj,
        proof: &crate::execute::execute_fact_stmt::function_limit::RealFunctionLimitDomainProof,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        // This is the exact domain view already certified by the function's
        // complete signature. It is not a source constructor hoisted out of a
        // quantified proof. Its raw denotation matches the recorded clauses.
        let raw_domain =
            self.compile_function_raw_expression_bound(&proof.domain, position, &HashMap::new())?;
        let function = self.compile_object_reference(function_obj, position)?;
        let source = &proof.source;
        let signature = self.compile_complete_domain_signature(source, position)?;
        let member = self.compile_complete_domain_member(function_obj, source, position)?;
        let base = self.compile_object_reference(
            &source.signature.set_bound_parameters.groups[0].param_type,
            position,
        )?;
        let (domain_set, compare) = if source.signature.dom_facts.is_empty() {
            (format!("(Litex.isSet {base})"), format!("change M.mem x (Litex.denote {base}) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote {base}) (fun _ => True))\n    rw [Litex.SetSemantics.sep_members]\n    exact ⟨fun hx => ⟨hx, True.intro⟩, And.left⟩"))
        } else {
            (format!("(Litex.SetSemantics.sep_isSet (Litex.denote {base}) _ (Litex.isSet {base}))"), format!("change M.mem x (Litex.SetSemantics.sepValue (Litex.denote {base}) _) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote {base}) _)\n    rw [Litex.SetSemantics.sep_members, Litex.SetSemantics.sep_members]\n    exact ⟨fun ⟨hx, _, hg⟩ => ⟨hx, hg⟩, fun ⟨hx, hg⟩ => ⟨hx, hx, hg⟩⟩"))
        };
        let prefix = format!("  let _signature := {signature}\n  have _member : Litex.In {function} (Litex.fnSet _signature) := {member}\n  let _source_domain := {raw_domain}\n  have _domain_set : M.isSet _source_domain := {domain_set}\n  have _domain_match : _source_domain = _signature.domain := by\n    apply Litex.SetSemantics.ext _ _ _domain_set _signature.domain_isSet\n    intro x\n    {compare}\n  let _domain := Litex.semanticObject _source_domain _domain_set");
        Ok((prefix, "(_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _signature.domain_isSet _member).symm)".into()))
    }
}
