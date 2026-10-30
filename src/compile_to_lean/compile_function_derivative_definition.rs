//! Replay the original derivative definition consequences, with captured domains.
use super::compile_function_derivative::validate_derivative_existence;
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::compile_sequence_analysis::call_matches;
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferHasDerivativeAtFactResult};
use std::collections::HashMap;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("DerivativeDefinition/{stage}"))
}
fn identifier(p: &BoundName) -> Obj {
    Obj::Identifier(IdentifierObj::from_bound_name(p))
}
fn difference(obj: &Obj, left: &Obj, right: &Obj) -> bool {
    matches!(obj,Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)) if p.left.ir()==left.ir()&&p.right.ir()==right.ir())
}
fn fresh(p: &BoundName, sources: &[&Obj], prior: &[IdentifierId]) -> Result<(), LeanCompileError> {
    if prior.contains(&p.id) || sources.iter().any(|s| contains_parameter(s, p.id)) {
        return Err(invalid("BinderCapture"));
    }
    Ok(())
}
pub(super) fn validate_derivative_interior(
    function: &Obj,
    point: &Obj,
    domain: &Obj,
    fact: &Fact,
) -> Result<(), LeanCompileError> {
    let Fact::ExistFact(exists) = fact else {
        return Err(invalid("InteriorExistence"));
    };
    let radius = parameter(
        &exists.typed_parameters,
        &Obj::StandardSet(StandardSet::RPos),
    )?;
    fresh(radius, &[function, point, domain], &[])?;
    let [QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(subset))] = exists.facts.as_slice()
    else {
        return Err(invalid("InteriorInclusion"));
    };
    let Obj::SetFormer(SetFormer::SetBuilder(ball)) = &subset.left else {
        return Err(invalid("InteriorBall"));
    };
    if subset.right.ir() != domain.ir()
        || ball.param_set.as_ref() != &Obj::StandardSet(StandardSet::R)
    {
        return Err(invalid("InteriorDomain"));
    }
    fresh(
        &ball.param_binding,
        &[function, point, domain],
        &[radius.id],
    )?;
    let [QuantifierFreeFact::AtomicFact(order)] = ball.facts.as_slice() else {
        return Err(invalid("InteriorOrder"));
    };
    let (left, right, strict) = source_order_oriented(order)?;
    let Obj::ArithmeticOperator(ArithmeticOperator::Abs(abs)) = left else {
        return Err(invalid("InteriorDistance"));
    };
    if !strict
        || right.ir() != identifier(radius).ir()
        || !difference(&abs.arg, &identifier(&ball.param_binding), point)
    {
        return Err(invalid("InteriorRadius"));
    }
    Ok(())
}
fn validate_quotient<'a>(
    source: &HasDerivativeAtFact,
    domain: &Obj,
    fact: &'a Fact,
) -> Result<&'a AnonymousFn, LeanCompileError> {
    let Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(limit)) = fact else {
        return Err(invalid("QuotientLimit"));
    };
    if !matches!(&limit.approach,LimitApproach::AtPoint(p) if p.ir()==source.point.ir())
        || limit.value.ir() != source.value.ir()
    {
        return Err(invalid("QuotientCandidate"));
    }
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(q)) = &limit.function else {
        return Err(invalid("QuotientFunction"));
    };
    let [group] = q.body.set_bound_parameters.groups.as_slice() else {
        return Err(invalid("QuotientInput"));
    };
    let [x] = group.params.as_slice() else {
        return Err(invalid("QuotientArity"));
    };
    if group.param_type.ir() != domain.ir()
        || q.body.ret_set.as_ref() != &Obj::StandardSet(StandardSet::R)
    {
        return Err(invalid("QuotientSignature"));
    }
    fresh(
        x,
        &[&source.function, &source.point, &source.value, domain],
        &[],
    )?;
    let [QuantifierFreeFact::AtomicFact(AtomicFact::NotEqualFact(nonzero))] =
        q.body.dom_facts.as_slice()
    else {
        return Err(invalid("QuotientNonzero"));
    };
    if !difference(&nonzero.left, &identifier(x), &source.point) || !is_zero(&nonzero.right) {
        return Err(invalid("QuotientGuard"));
    }
    let Obj::ArithmeticOperator(ArithmeticOperator::Div(div)) = q.equal_to.as_ref() else {
        return Err(invalid("QuotientBody"));
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Sub(numerator)) = div.left.as_ref() else {
        return Err(invalid("QuotientNumerator"));
    };
    if !difference(&div.right, &identifier(x), &source.point)
        || !call_matches(&numerator.left, &source.function, &identifier(x))
        || !call_matches(&numerator.right, &source.function, &source.point)
    {
        return Err(invalid("QuotientDifference"));
    }
    Ok(q)
}
impl LitexToLeanCompiler {
    pub(super) fn compile_derivative_inferences(
        &self,
        infer: &InferAtomicFactResult,
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let (
            InferAtomicFactResult::HasDerivativeAtFact(rules),
            Fact::AtomicFact(AtomicFact::HasDerivativeAtFact(source)),
        ) = (infer, seed)
        else {
            return Err(invalid("InferenceFamily"));
        };
        let [InferHasDerivativeAtFactResult::Definition(proof)] = rules.as_slice() else {
            return Err(invalid("InferenceRule"));
        };
        if proof.source_fact_id != seed.fact_id()
            || proof.derived.len()
                != if proof.function_domain.is_some() {
                    4
                } else {
                    2
                }
        {
            return Err(invalid("InferenceIdentity"));
        }
        let facts = proof
            .derived
            .iter()
            .map(|s| {
                let f = self.resolve_fact(s.primary_fact_id(), position)?;
                self.validate_store(&s.store, &f)?;
                Ok(f)
            })
            .collect::<Result<Vec<_>, LeanCompileError>>()?;
        let function = self.compile_object_reference(&source.function, position)?;
        let point = self.compile_object_reference(&source.point, position)?;
        let value = self.compile_object_reference(&source.value, position)?;
        let mut lines = Vec::new();
        if let Some(domain) = &proof.function_domain {
            validate_derivative_interior(
                &source.function,
                &source.point,
                &domain.domain,
                &facts[0],
            )?;
            let quotient = validate_quotient(source, &domain.domain, &facts[1])?;
            let (view, equal) =
                self.compile_function_limit_domain_view(&source.function, domain, position)?;
            let ty = self.compile_function_raw_predicate(&facts[0], position, &HashMap::new())?;
            let term=format!("(by\n{view}\n  have _derivative_interior := Litex.derivativeInteriorOfCandidate (Litex.denote {function}) (Litex.denote {point}) (Litex.denote {value}) {}\n  unfold Litex.DerivativeInteriorClauseValue at _derivative_interior\n  have _derivative_domain_eq := {equal}\n  rw [← _derivative_domain_eq] at _derivative_interior\n  exact _derivative_interior\n)",compiled.1);
            lines.push(self.emit_internal_fact(&facts[0], &(ty, term), position)?);
            let (quotient_view, q) = self.compile_derivative_quotient_view(
                &source.function,
                &source.point,
                domain,
                quotient,
                position,
            )?;
            let ty=format!("Litex.HasFiniteFunctionLimitValue M .both {q} (Litex.denote {point}) (Litex.denote {value})");
            let term=format!("(by\n{quotient_view}\n  exact (Litex.derivativeQuotientGraph (Litex.denote {function}) (Litex.denote {point}) (Litex.denote {value}) _derivative_quotient_domain _derivative_real _derivative_quotient_set _derivative_quotient_spec {}).2\n)",compiled.1);
            lines.push(self.emit_internal_fact(&facts[1], &(ty, term), position)?);
        }
        let offset = usize::from(proof.function_domain.is_some()) * 2;
        validate_derivative_existence(&source.function, &source.point, &facts[offset])?;
        let Fact::AtomicFact(AtomicFact::FunctionDifferentiableAtFact(diff)) = &facts[offset + 1]
        else {
            return Err(invalid("Differentiability"));
        };
        if diff.function.ir() != source.function.ir() || diff.point.ir() != source.point.ir() {
            return Err(invalid("DifferentiabilitySubject"));
        }
        let existence=format!("(Litex.derivativeExistsValueOfCandidate (Litex.denote {function}) (Litex.denote {point}) (Litex.denote {value}) {})",compiled.1);
        for fact in &facts[offset..] {
            let ty = self.compile_function_raw_predicate(fact, position, &HashMap::new())?;
            lines.push(self.emit_internal_fact(fact, &(ty, existence.clone()), position)?);
        }
        Ok(lines)
    }
}

impl LitexToLeanCompiler {
    pub(super) fn compile_differentiability_inferences(
        &self,
        infer: &InferAtomicFactResult,
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        use crate::store_fact_and_infer::InferFunctionDifferentiableAtFactResult;
        let (
            InferAtomicFactResult::FunctionDifferentiableAtFact(rules),
            Fact::AtomicFact(AtomicFact::FunctionDifferentiableAtFact(source)),
        ) = (infer, seed)
        else {
            return Err(invalid("DifferentiableInferenceFamily"));
        };
        let [InferFunctionDifferentiableAtFactResult::Definition(proof)] = rules.as_slice() else {
            return Err(invalid("DifferentiableInferenceRule"));
        };
        if proof.source_fact_id != seed.fact_id()
            || proof.function_domain.is_some() != proof.interior.is_some()
        {
            return Err(invalid("DifferentiableInferenceIdentity"));
        }
        let existence = self.resolve_fact(proof.existence.primary_fact_id(), position)?;
        self.validate_store(&proof.existence.store, &existence)?;
        validate_derivative_existence(&source.function, &source.point, &existence)?;
        let ty = self.compile_function_raw_predicate(&existence, position, &HashMap::new())?;
        let mut lines =
            vec![self.emit_internal_fact(&existence, &(ty, compiled.1.clone()), position)?];
        if let (Some(domain), Some(stored)) = (&proof.function_domain, &proof.interior) {
            let interior = self.resolve_fact(stored.primary_fact_id(), position)?;
            self.validate_store(&stored.store, &interior)?;
            validate_derivative_interior(
                &source.function,
                &source.point,
                &domain.domain,
                &interior,
            )?;
            let (view, equal) =
                self.compile_function_limit_domain_view(&source.function, domain, position)?;
            let real = self.compile_real_function_domain(&source.function, domain, position)?;
            let ty = self.compile_function_raw_predicate(&interior, position, &HashMap::new())?;
            let f = self.compile_object_reference(&source.function, position)?;
            let p = self.compile_object_reference(&source.point, position)?;
            let term=format!("(by\n{view}\n  have _derivative_real : Litex.RealFunctionValue M (Litex.denote {f}) := {real}\n  have _derivative_interior := Litex.derivativeInteriorOfExistence (Litex.denote {f}) (Litex.denote {p}) {}\n  unfold Litex.DerivativeInteriorClauseValue at _derivative_interior\n  have _derivative_domain_eq := {equal}\n  rw [← _derivative_domain_eq] at _derivative_interior\n  exact _derivative_interior\n)",compiled.1);
            lines.push(self.emit_internal_fact(&interior, &(ty, term), position)?);
        }
        Ok(lines)
    }
}

impl LitexToLeanCompiler {
    fn compile_derivative_quotient_view(
        &self,
        function: &Obj,
        point: &Obj,
        domain: &crate::execute::execute_fact_stmt::function_limit::RealFunctionLimitDomainProof,
        quotient: &AnonymousFn,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let (view, equal) = self.compile_function_limit_domain_view(function, domain, position)?;
        let real = self.compile_real_function_domain(function, domain, position)?;
        let function = self.compile_object_reference(function, position)?;
        let point = self.compile_object_reference(point, position)?;
        let (input, output, body) =
            self.compile_function_literal_parts(quotient, position, &HashMap::new())?;
        let (base_set, compare) = if domain.domain == Obj::StandardSet(StandardSet::RPos) {
            ("(M.standard_isSet .real)","dsimp only [_derivative_quotient_domain, _source_domain]\n    rw [Litex.SetSemantics.sep_members, Litex.positiveReal_members]\n    exact and_assoc.symm")
        } else {
            ("_domain_set", "exact Litex.SetSemantics.sep_members _ _ _")
        };
        let q = format!("(Litex.FunctionSemantics.graphValue (M := M) {input} {output} {body})");
        let prefix=format!("{view}\n  have _derivative_real : Litex.RealFunctionValue M (Litex.denote {function}) := {real}\n  let _derivative_quotient_domain := {input}\n  have _derivative_quotient_set : M.isSet _derivative_quotient_domain := Litex.SetSemantics.sep_isSet _ _ {base_set}\n  have _derivative_domain_eq := {equal}\n  have _derivative_quotient_spec : ∀ x, M.mem x _derivative_quotient_domain ↔ M.mem x (Litex.FunctionSemantics.domainValue (Litex.denote {function})) ∧ M.subValue x (Litex.denote {point}) ≠ M.number 0 := by\n    intro x\n    rw [← _derivative_domain_eq]\n    {compare}");
        Ok((prefix, q))
    }
    pub(super) fn compile_derivative_definition(
        &self,
        source: &HasDerivativeAtFact,
        wd: &AtomicFactWellDefinedProof,
        proof:&crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::BuiltinHasDerivativeAtDefinitionProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
        let PredicateDomainProof::FunctionAnalysis(formation) = &wd.detailed_ref().predicate_domain
        else {
            return Err(invalid("Formation"));
        };
        let ([interior, limit], [interior_proof, limit_proof]) = (
            proof.requirement_facts.as_slice(),
            proof.proof_of_requirement_facts.as_slice(),
        ) else {
            return Err(invalid("DefinitionArity"));
        };
        validate_derivative_interior(
            &source.function,
            &source.point,
            &formation.function_domain.domain,
            interior,
        )?;
        let quotient = validate_quotient(source, &formation.function_domain.domain, limit)?;
        let mut terms = Vec::new();
        for (i, (fact, proof)) in [interior, limit]
            .into_iter()
            .zip([interior_proof, limit_proof])
            .enumerate()
        {
            if source_subject(proof)? != *fact {
                return Err(invalid("DefinitionProofSubject"));
            }
            let (ty, term) = self.compile_verify(proof, &position.atomic_search_prior(i)?)?;
            terms.push(format!("(show {ty} from {term})"));
        }
        let formed = position.atomic_search_prior(2)?;
        let (view, _) = self.compile_derivative_quotient_view(
            &source.function,
            &source.point,
            &formation.function_domain,
            quotient,
            &formed,
        )?;
        let f = self.compile_object_reference(&source.function, &formed)?;
        let p = self.compile_object_reference(&source.point, &formed)?;
        let v = self.compile_object_reference(&source.value, &formed)?;
        Ok(format!("(by\n{view}\n  have _derivative_interior : Litex.DerivativeInteriorClauseValue M (Litex.denote {f}) (Litex.denote {p}) := by\n    unfold Litex.DerivativeInteriorClauseValue\n    rw [← _derivative_domain_eq]\n    exact {}\n  exact Litex.derivativeOfQuotientGraph (Litex.denote {f}) (Litex.denote {p}) (Litex.denote {v}) _derivative_quotient_domain _derivative_real _derivative_quotient_set _derivative_quotient_spec _derivative_interior {}\n)",terms[0],terms[1]))
    }
    pub(super) fn compile_differentiability_definition(
        &self,
        source: &FunctionDifferentiableAtFact,
        proof:&crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::BuiltinFunctionDifferentiableAtDefinitionProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let ([fact], [checked]) = (
            proof.requirement_facts.as_slice(),
            proof.proof_of_requirement_facts.as_slice(),
        ) else {
            return Err(invalid("DifferentiableDefinitionArity"));
        };
        validate_derivative_existence(&source.function, &source.point, fact)?;
        if source_subject(checked)? != *fact {
            return Err(invalid("DifferentiableDefinitionSubject"));
        }
        let (ty, term) = self.compile_verify(checked, &position.atomic_search_prior(0)?)?;
        Ok(format!("(show {ty} from {term})"))
    }
}
