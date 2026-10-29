//! A constant limit still requires the recorded nontrivial approach to the domain.
use super::compile_function_limit::{finite_side, infinite_direction};
use super::compile_function_limit_definition::validate_accumulation_clause;
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::compile_sequence_analysis::call_matches;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("ConstantFunctionLimit/{stage}"))
}

pub(super) fn validate_constant_clauses(
    goal: &HasFunctionLimitFact,
    requirements: &[Fact],
) -> Result<(), LeanCompileError> {
    let [real, accumulation, equation] = requirements else {
        return Err(invalid("Arity"));
    };
    if !matches!(real, Fact::AtomicFact(AtomicFact::InFact(f))
        if f.element.ir() == goal.value.ir() && f.set == Obj::StandardSet(StandardSet::R))
    {
        return Err(invalid("RealValue"));
    }
    let domain = validate_accumulation_clause(goal, accumulation)?;
    let Fact::ForallFact(all) = equation else {
        return Err(invalid("PointwiseEquation"));
    };
    let input = parameter(&all.typed_parameters, domain)?;
    if !all.dom_facts.is_empty()
        || [&goal.function, &goal.value, domain]
            .iter()
            .any(|x| contains_parameter(x, input.id))
        || goal
            .approach
            .point()
            .is_some_and(|p| contains_parameter(p, input.id))
    {
        return Err(invalid("BinderCapture"));
    }
    let arg = Obj::Identifier(IdentifierObj::from_bound_name(input));
    if !matches!(all.then_facts.as_slice(), [ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(f))]
        if call_matches(&f.left, &goal.function, &arg) && f.right.ir() == goal.value.ir())
    {
        return Err(invalid("EquationSubject"));
    }
    Ok(())
}

impl LitexToLeanCompiler {
    pub(super) fn compile_constant_function_limit(
        &self,
        goal: &HasFunctionLimitFact,
        wd: &FactWellDefinedProof,
        requirements: &[Fact],
        references: &[String],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let FactWellDefinedProof::AtomicExceptEquality(atomic) = wd else {
            return Err(invalid("Formation"));
        };
        let PredicateDomainProof::FunctionLimit(formation) =
            &atomic.detailed_ref().predicate_domain
        else {
            return Err(invalid("RealDomain"));
        };
        let domain = validate_accumulation_clause(goal, &requirements[1])?;
        if domain.ir() != formation.function_domain.domain.ir() {
            return Err(invalid("EffectiveDomain"));
        }
        let (view, equality) = self.compile_function_limit_domain_view(
            &goal.function,
            &formation.function_domain,
            position,
        )?;
        let real_domain = self.compile_real_function_domain(
            &goal.function,
            &formation.function_domain,
            position,
        )?;
        let function = self.compile_object_reference(&goal.function, position)?;
        let value = self.compile_object_reference(&goal.value, position)?;
        let law = if goal.approach.point().is_some() {
            let (side, point) = finite_side(&goal.approach)?;
            let point = self.compile_object_reference(point, position)?;
            format!("Litex.finiteFunctionLimitConstant .{side} {function} {point} {value} _domain _constant_real_domain {equality} {} {} {} {}", references[3], references[4], references[5], references[6])
        } else {
            let direction = infinite_direction(&goal.approach)?;
            format!("Litex.infiniteFunctionLimitConstant .{direction} {function} {value} _domain _constant_real_domain {equality} {} {} {}", references[3], references[4], references[5])
        };
        Ok(format!("(by\n{view}\n  have _constant_real_domain : Litex.RealFunctionValue M (Litex.denote {function}) := {real_domain}\n  exact {law}\n)"))
    }
}
