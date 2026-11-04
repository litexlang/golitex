//! Global continuity is pointwise continuity on the original complete domain.
use super::compile_function_limit_definition::signature_domain_matches;
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    FunctionAnalysisPredicateDomainProof, PredicateDomainProof,
};
use crate::prelude::*;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferFunctionContinuousFactResult};

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("GlobalContinuity/{stage}"))
}

pub(super) fn parts(fact: &AtomicFact) -> Option<(&Obj, bool)> {
    match fact {
        AtomicFact::FunctionContinuousFact(f) => Some((&f.function, false)),
        AtomicFact::NotFunctionContinuousFact(f) => Some((&f.function, true)),
        _ => None,
    }
}

pub(super) fn validate_pointwise<'a>(
    function: &Obj,
    domain: &Obj,
    fact: &'a Fact,
) -> Result<&'a BoundName, LeanCompileError> {
    let Fact::ForallFact(all) = fact else {
        return Err(invalid("OriginalForall"));
    };
    let point = parameter(&all.typed_parameters, domain)?;
    if !all.dom_facts.is_empty()
        || contains_parameter(function, point.id)
        || contains_parameter(domain, point.id)
        || !matches!(all.then_facts.as_slice(), [ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::FunctionContinuousAtFact(f))]
            if f.function.ir()==function.ir()&&f.point.ir()==Obj::Identifier(IdentifierObj::from_bound_name(point)).ir()&&f.side==RealApproachSide::Both)
    {
        return Err(invalid("OriginalPointwiseBody"));
    }
    Ok(point)
}

impl LitexToLeanCompiler {
    pub(super) fn compile_global_continuity_domain(
        &self,
        fact: &AtomicFact,
        proof: &FunctionAnalysisPredicateDomainProof,
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let (function, _) = parts(fact).ok_or_else(|| invalid("PredicateFamily"))?;
        if !proof.requirements.is_empty() {
            return Err(invalid("OriginalDomainRequirements"));
        }
        let real = self.compile_real_function_domain(function, &proof.function_domain, position)?;
        let f = self.compile_object_reference(function, position)?;
        Ok(vec![format!(
            "have _global_continuity_real : Litex.RealFunctionValue M (Litex.denote {f}) := {real}"
        )])
    }

    pub(super) fn compile_global_continuity_definition(
        &self,
        source: &FunctionContinuousFact,
        wd: &AtomicFactWellDefinedProof,
        proof: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::BuiltinFunctionContinuousDefinitionProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if source.property != FunctionContinuityProperty::Continuous {
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
        validate_pointwise(&source.function, &formation.function_domain.domain, fact)?;
        if source_subject(checked)? != *fact {
            return Err(invalid("DefinitionSubject"));
        }
        let (ty, term) = self.compile_verify(checked, &position.atomic_search_prior(0)?)?;
        let formed = position.atomic_search_prior(1)?;
        let (view, equality) = self.compile_function_limit_domain_view(
            &source.function,
            &formation.function_domain,
            &formed,
        )?;
        let f = self.compile_object_reference(&source.function, &formed)?;
        Ok(format!("(by\n{view}\n  exact Litex.functionContinuousOfForall {f} _domain {equality} (show {ty} from {term})\n)"))
    }

    pub(super) fn compile_global_continuity_inferences(
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
        if source.property != FunctionContinuityProperty::Continuous {
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
        let Fact::ForallFact(all) = &fact else {
            return Err(invalid("InferenceForall"));
        };
        let [group] = all.typed_parameters.groups.as_slice() else {
            return Err(invalid("InferenceParameter"));
        };
        let ParamType::Obj(domain) = &group.param_type else {
            return Err(invalid("InferenceDomain"));
        };
        let point = validate_pointwise(&source.function, domain, &fact)?;
        let (view, equality) =
            self.compile_global_property_domain_view(&source.function, domain, position)?;
        let f = self.compile_object_reference(&source.function, position)?;
        // The declaration certifies this complete domain as a signature value;
        // inference did not introduce a separate source-level set constructor.
        let d = self.compile_function_raw_expression_bound(
            domain,
            position,
            &std::collections::HashMap::new(),
        )?;
        let id = point.id.value();
        let ty = format!("∀ {{_Host_i{id} : Type _}} [_rep_i{id} : Litex.Representation M _Host_i{id}] (_value_i{id} : Litex.Obj (M := M) _Host_i{id}), M.mem (Litex.denote _value_i{id}) {d} → Litex.FunctionContinuousAt .both {f} _value_i{id}");
        let term = format!(
            "(by\n{view}\n  intro _global_host _global_rep _global_point _global_member\n  exact Litex.functionContinuousForall {f} _domain {equality} {} _global_point _global_member\n)",
            compiled.1
        );
        Ok(vec![self.emit_internal_fact(
            &fact,
            &(ty, term),
            position,
        )?])
    }
    pub(super) fn compile_global_property_domain_view(
        &self,
        function: &Obj,
        domain: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        // This result records the original forall, but no domain proof. A
        // formed literal owns its exact signature and intrinsic membership;
        // parameter functions borrow their original declaration below.
        if let Obj::FunctionSpace(FunctionSpace::AnonymousFn(literal)) = function {
            if !signature_domain_matches(domain, &literal.body) {
                return Err(invalid("InferenceLiteralDomain"));
            }
            let term = self.compile_object_reference(function, position)?;
            let signature = format!("({term}).val.signature");
            let member = format!("(Litex.formulaFnInFnSet {term})");
            return self.compile_verified_limit_domain_view(
                function,
                domain,
                &literal.body,
                &signature,
                &member,
                position,
            );
        }
        let Obj::Identifier(IdentifierObj::Plain { id, .. }) = function else {
            return Err(invalid("InferenceFunctionParameter"));
        };
        let (_, Some(carrier), fact_id, _) = position.visible_parameter(*id, &self.runtime)? else {
            return Err(invalid("InferenceCarrier"));
        };
        let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = carrier else {
            return Err(invalid("InferenceSignature"));
        };
        if !signature_domain_matches(domain, signature) {
            return Err(invalid("InferenceActualDomain"));
        }
        let (member_source, member) = self.cited_fact_reference(fact_id, position)?;
        if !matches!(member_source, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==function.ir()&&f.set.ir()==carrier.ir())
        {
            return Err(invalid("InferenceMembership"));
        }
        let sig = format!(
            "({}).val",
            self.compile_object_reference(carrier, position)?
        );
        self.compile_verified_limit_domain_view(
            function, domain, signature, &sig, &member, position,
        )
    }
}
