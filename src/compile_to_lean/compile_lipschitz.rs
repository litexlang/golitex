//! The original Lipschitz estimate keeps its constant, pair order and complete domain.
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::compile_uniform_continuity::{cart_domain, coordinate};
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    FunctionAnalysisPredicateDomainProof, PredicateDomainProof, PredicateDomainRequirementProof,
};
use crate::prelude::*;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferFunctionLipschitzFactResult};
use std::collections::HashMap;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("Lipschitz/{stage}"))
}
pub(super) fn parts(fact: &AtomicFact) -> Option<(&Obj, &Obj, bool)> {
    match fact {
        AtomicFact::FunctionLipschitzFact(f) => Some((&f.function, &f.constant, false)),
        AtomicFact::NotFunctionLipschitzFact(f) => Some((&f.function, &f.constant, true)),
        _ => None,
    }
}
fn pair_distance(obj: &Obj, function: Option<&Obj>, pair: &Obj) -> bool {
    let Obj::ArithmeticOperator(ArithmeticOperator::Abs(abs)) = obj else {
        return false;
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Sub(sub)) = abs.arg.as_ref() else {
        return false;
    };
    let matches = |obj: &Obj, index| {
        if let Some(f) = function {
            let Obj::FnObj(call) = obj else {
                return false;
            };
            call.head.as_ref() == &FnObjHead::from_obj(f.clone())
                && matches!(call.body.as_slice(), [args] if matches!(args.as_slice(), [arg] if coordinate(arg, pair, index)))
        } else {
            coordinate(obj, pair, index)
        }
    };
    matches(&sub.left, "1") && matches(&sub.right, "2")
}

pub(super) fn validate_estimate<'a>(
    function: &Obj,
    constant: &Obj,
    fact: &'a Fact,
) -> Result<(&'a ForallFact, &'a BoundName, &'a Obj), LeanCompileError> {
    let Fact::ForallFact(all) = fact else {
        return Err(invalid("EstimateForall"));
    };
    let [group] = all.typed_parameters.groups.as_slice() else {
        return Err(invalid("PairParameter"));
    };
    let ParamType::Obj(cart) = &group.param_type else {
        return Err(invalid("PairCarrier"));
    };
    let pair = parameter(&all.typed_parameters, cart)?;
    let domain = cart_domain(cart)?;
    if !all.dom_facts.is_empty()
        || [function, constant, domain]
            .iter()
            .any(|obj| contains_parameter(obj, pair.id))
    {
        return Err(invalid("ExtraPremiseOrCapture"));
    }
    let [ExistOrAndChainAtomicFact::AtomicFact(bound)] = all.then_facts.as_slice() else {
        return Err(invalid("EstimateClause"));
    };
    let (left, right, strict) = source_order_oriented(bound)?;
    let Obj::ArithmeticOperator(ArithmeticOperator::Mul(mul)) = right else {
        return Err(invalid("ConstantMultiplier"));
    };
    let p = Obj::Identifier(IdentifierObj::from_bound_name(pair));
    if strict
        || mul.left.ir() != constant.ir()
        || !pair_distance(left, Some(function), &p)
        || !pair_distance(&mul.right, None, &p)
    {
        return Err(invalid("OriginalEstimate"));
    }
    Ok((all, pair, domain))
}
fn nonnegative(fact: &Fact, constant: &Obj) -> bool {
    let Fact::AtomicFact(atom) = fact else {
        return false;
    };
    matches!(source_order_oriented(atom), Ok((zero,k,false)) if is_zero(zero) && k.ir()==constant.ir())
}

impl LitexToLeanCompiler {
    pub(super) fn compile_lipschitz_domain(
        &self,
        fact: &AtomicFact,
        proof: &FunctionAnalysisPredicateDomainProof,
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let (function, constant, _) = parts(fact).ok_or_else(|| invalid("PredicateFamily"))?;
        let [real, positive] = proof.requirements.as_slice() else {
            return Err(invalid("ConstantRequirements"));
        };
        if !matches!(&real.requirement, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==constant.ir() && f.set==Obj::StandardSet(StandardSet::R))
            || !nonnegative(&positive.requirement, constant)
        {
            return Err(invalid("ConstantDomain"));
        }
        let domain =
            self.compile_real_function_domain(function, &proof.function_domain, position)?;
        let f = self.compile_object_reference(function, position)?;
        let mut lines = vec![format!(
            "have _lipschitz_real : Litex.RealFunctionValue M (Litex.denote {f}) := {domain}"
        )];
        let args = atomic_fact_args_ref(fact);
        for (index, r) in proof.requirements.iter().enumerate() {
            let prior = SourcePosition {
                before: args.len() + index,
                ..*position
            };
            let (ty, term) = match &r.result {
                PredicateDomainRequirementProof::Verified(p) => {
                    if source_subject(p)? != r.requirement {
                        return Err(invalid("ConstantEvidence"));
                    }
                    self.compile_verify(p, &prior)?
                }
                PredicateDomainRequirementProof::CheckedArgument(p) => (
                    self.compile_function_raw_predicate(&r.requirement, &prior, &HashMap::new())?,
                    self.compile_checked_domain_argument(&r.requirement, p, &args, index, &prior)?,
                ),
            };
            lines.push(format!(
                "have h_{} : {ty} := {term}",
                r.requirement.fact_id().value()
            ));
        }
        Ok(lines)
    }

    /// Re-emit the original requirement's complete formation in its original cursor.
    /// The global uniform conclusion has no constant argument and cannot supply this WD.
    pub(super) fn compile_lipschitz_checked_formation(
        &self,
        checked: &VerifyFactResult,
        function: &Obj,
        constant: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, String, String), LeanCompileError> {
        let VerifyFactResult::AtomicExceptEquality(result) = checked else {
            return Err(invalid("CheckedAtomic"));
        };
        let VerifyAtomicExceptEqualityFactResult::Success(success) = result.as_ref() else {
            return Err(invalid("CheckedSuccess"));
        };
        if !matches!(&success.fact, AtomicFact::FunctionLipschitzFact(f) if f.function.ir()==function.ir() && f.constant.ir()==constant.ir())
        {
            return Err(invalid("CheckedSubject"));
        }
        let source = SourcePosition::new(Some(position), SourceOwner::AtomicVerify(success), 0);
        self.compile_lipschitz_formation(&success.fact, &success.well_defined_proof, &source)
    }

    fn compile_lipschitz_formation(
        &self,
        fact: &AtomicFact,
        wd: &AtomicFactWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, String, String), LeanCompileError> {
        let (_, constant, negative) = parts(fact).ok_or_else(|| invalid("FormationFamily"))?;
        if negative {
            return Err(invalid("PositiveFormation"));
        }
        let lines = self.compile_atomic_wd_locals(wd, fact, position)?;
        let formed = SourcePosition::new(
            Some(position),
            SourceOwner::AtomicWDLocals(wd, 2),
            usize::MAX,
        );
        let k = self.compile_object_reference(constant, &formed)?;
        match &wd
            .as_detailed()
            .map_err(|_| invalid("DetailedFormation"))?
            .predicate_domain
        {
            PredicateDomainProof::FunctionAnalysis(formation) => {
                let [_, positive] = formation.requirements.as_slice() else {
                    return Err(invalid("ConstantRequirements"));
                };
                Ok((
                    lines,
                    k,
                    format!("h_{}", positive.requirement.fact_id().value()),
                ))
            }
            PredicateDomainProof::ByKnownFact(cite) => {
                // The existing known-atomic consumer validates the exact citation and
                // both original argument equalities; no replacement WD search occurs.
                self.compile_known_atomic(cite, fact, &formed)?;
                let mut callback = |source: &AtomicFact,
                                    source_wd: &AtomicFactWellDefinedProof,
                                    prior: &SourcePosition<'_>| {
                    let (_, old_constant, negative) =
                        parts(source).ok_or_else(|| invalid("CitedFamily"))?;
                    if negative {
                        return Err(invalid("CitedPositive"));
                    }
                    let (mut old_lines, old_k, old_h) =
                        self.compile_lipschitz_formation(source, source_wd, prior)?;
                    let [_, equal] = cite
                        .why_parameters_of_known_fact_are_equal_to_givens
                        .as_slice()
                    else {
                        return Err(invalid("CitedEqualities"));
                    };
                    let obligation = EqualFact {
                        fact_id: fact.fact_id(),
                        left: old_constant.clone(),
                        right: constant.clone(),
                        line_file: None,
                    };
                    let equality = self.compile_equality_search(&obligation, equal, &formed)?;
                    old_lines.push(format!("have _lipschitz_constant_eq : Litex.denote {old_k} = Litex.denote {k} := {equality}"));
                    old_lines.push(format!("have _lipschitz_nonnegative : Litex.RealLeValue M (M.number 0) (Litex.denote {k}) := by\n  rw [← _lipschitz_constant_eq]\n  exact {old_h}"));
                    Ok((old_lines, "_lipschitz_nonnegative".to_string()))
                };
                let (old_lines, h) =
                    self.with_cited_atomic_formation(cite.cite_fact_id, &formed, &mut callback)?;
                let mut lines = lines;
                lines.extend(old_lines);
                Ok((lines, k, h))
            }
            _ => Err(invalid("CheckedFormation")),
        }
    }

    pub(super) fn compile_lipschitz_definition(
        &self,
        source: &FunctionLipschitzFact,
        wd: &AtomicFactWellDefinedProof,
        proof: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::BuiltinFunctionLipschitzDefinitionProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
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
        let (_, _, domain) = validate_estimate(&source.function, &source.constant, fact)?;
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
        let k = self.compile_object_reference(&source.constant, &formed)?;
        Ok(format!("(by\n{view}\n  exact Litex.functionLipschitzOfForall {f} {k} _domain {equality} (show {ty} from {term})\n)"))
    }

    pub(super) fn compile_lipschitz_inferences(
        &self,
        infer: &InferAtomicFactResult,
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let (
            InferAtomicFactResult::FunctionLipschitzFact(rules),
            Fact::AtomicFact(AtomicFact::FunctionLipschitzFact(source)),
        ) = (infer, seed)
        else {
            return Err(invalid("InferenceFamily"));
        };
        let [InferFunctionLipschitzFactResult::Definition(proof)] = rules.as_slice() else {
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
        let (all, pair, domain) = validate_estimate(&source.function, &source.constant, &fact)?;
        let (view, equality) =
            self.compile_global_property_domain_view(&source.function, domain, position)?;
        let id = pair.id.value();
        let value = format!("_value_i{id}");
        let body = self.compile_function_raw_predicate(
            &all.then_facts[0].clone().into(),
            position,
            &HashMap::from([(pair.id, format!("(Litex.denote {value})"))]),
        )?;
        let d = self.compile_function_raw_expression_bound(domain, position, &HashMap::new())?;
        let ty=format!("∀ {{_Host_i{id} : Type _}} [_rep_i{id} : Litex.Representation M _Host_i{id}] ({value} : Litex.Obj (M := M) _Host_i{id}), M.mem (Litex.denote {value}) (Litex.FiniteFunction.cartValue ![{d},{d}]) → {body}");
        let f = self.compile_object_reference(&source.function, position)?;
        let k = self.compile_object_reference(&source.constant, position)?;
        let term=format!("(by\n{view}\n  intro _Host _rep {value} _member_i{id}\n  exact Litex.functionLipschitzForall {f} {k} _domain {equality} {} {value} _member_i{id}\n)",compiled.1);
        Ok(vec![self.emit_internal_fact(
            &fact,
            &(ty, term),
            position,
        )?])
    }
}
