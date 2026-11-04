//! Replay the original unpunctured epsilon clause of Euclidean continuity.
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
};
use std::collections::HashMap;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("MultivariableContinuity/{stage}"))
}
pub(super) fn parts(fact: &AtomicFact) -> Option<(&MultivariableAnalysisRelation, bool)> {
    let (r, negative) = match fact {
        AtomicFact::MultivariableAnalysisFact(f) => (&f.relation, false),
        AtomicFact::NotMultivariableAnalysisFact(f) => (&f.relation, true),
        _ => return None,
    };
    matches!(
        r,
        MultivariableAnalysisRelation::ScalarContinuousAt(_)
            | MultivariableAnalysisRelation::VectorContinuousAt(_)
    )
    .then_some((r, negative))
}
fn law(r: &MultivariableAnalysisRelation, fold: bool) -> &'static str {
    match (
        matches!(r, MultivariableAnalysisRelation::ScalarContinuousAt(_)),
        fold,
    ) {
        (true, true) => "scalarMultivariableContinuousAtFromDefinition",
        (true, false) => "scalarMultivariableContinuousAtToDefinition",
        (false, true) => "vectorMultivariableContinuousAtFromDefinition",
        (false, false) => "vectorMultivariableContinuousAtToDefinition",
    }
}

fn validate_clause(
    r: &MultivariableAnalysisRelation,
    domain: &Obj,
    fact: &Fact,
) -> Result<(), LeanCompileError> {
    use super::compile_multivariable_scalar_limit::distance;
    use crate::execute::execute_fact_stmt::multivariable::helper::{apply, identifier};
    let args = r.argument_refs();
    let protected: Vec<_> = args
        .iter()
        .copied()
        .chain(std::iter::once(domain))
        .collect();
    let fresh = |p: &BoundName, prior: &[IdentifierId]| {
        if prior.contains(&p.id) || protected.iter().any(|o| contains_parameter(o, p.id)) {
            Err(invalid("ClauseCapture"))
        } else {
            Ok(())
        }
    };
    fn strict(f: &QuantifierFreeFact) -> Result<(&Obj, &Obj), LeanCompileError> {
        let QuantifierFreeFact::AtomicFact(a) = f else {
            return Err(invalid("ClauseOrder"));
        };
        let (a, b, true) = source_order_oriented(a)? else {
            return Err(invalid("ClauseStrictOrder"));
        };
        Ok((a, b))
    }
    let Fact::ForallFact(all) = fact else {
        return Err(invalid("EpsilonForall"));
    };
    if !all.dom_facts.is_empty() {
        return Err(invalid("EpsilonPremises"));
    }
    let epsilon = parameter(&all.typed_parameters, &Obj::StandardSet(StandardSet::RPos))?;
    fresh(epsilon, &[])?;
    let [ExistOrAndChainAtomicFact::ExistFact(exists)] = all.then_facts.as_slice() else {
        return Err(invalid("DeltaWitness"));
    };
    let delta = parameter(
        &exists.typed_parameters,
        &Obj::StandardSet(StandardSet::RPos),
    )?;
    fresh(delta, &[epsilon.id])?;
    let [QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(inclusion))] =
        exists.facts.as_slice()
    else {
        return Err(invalid("ControlInclusion"));
    };
    let (Obj::SetFormer(SetFormer::SetBuilder(near)), Obj::SetFormer(SetFormer::SetBuilder(good))) =
        (&inclusion.left, &inclusion.right)
    else {
        return Err(invalid("ControlSets"));
    };
    if near.param_set.ir() != domain.ir() || good.param_set.ir() != domain.ir() {
        return Err(invalid("OriginalDomain"));
    }
    fresh(&near.param_binding, &[epsilon.id, delta.id])?;
    fresh(
        &good.param_binding,
        &[epsilon.id, delta.id, near.param_binding.id],
    )?;
    let [upper] = near.facts.as_slice() else {
        return Err(invalid("UnpuncturedNeighborhood"));
    };
    let (d, bound) = strict(upper)?;
    distance(d, &identifier(&near.param_binding), args[1], args[2])?;
    if bound.ir() != identifier(delta).ir() {
        return Err(invalid("ControlRadius"));
    }
    let [error] = good.facts.as_slice() else {
        return Err(invalid("ControlError"));
    };
    let (error, bound) = strict(error)?;
    if bound.ir() != identifier(epsilon).ir() {
        return Err(invalid("ControlEpsilon"));
    }
    let input = apply(args[0], vec![identifier(&good.param_binding)]);
    let target = apply(args[0], vec![args[1].clone()]);
    if matches!(r, MultivariableAnalysisRelation::VectorContinuousAt(_)) {
        distance(error, &input, &target, args[3])?;
    } else if !matches!(error,Obj::ArithmeticOperator(ArithmeticOperator::Abs(a))
        if matches!(a.arg.as_ref(),Obj::ArithmeticOperator(ArithmeticOperator::Sub(s))
            if s.left.ir()==input.ir() && s.right.ir()==target.ir()))
    {
        return Err(invalid("OriginalFunctionAtPoint"));
    }
    Ok(())
}

impl LitexToLeanCompiler {
    fn continuity_raw_arguments(
        &self,
        r: &MultivariableAnalysisRelation,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        r.argument_refs()
            .into_iter()
            .map(|o| self.compile_function_raw_expression_bound(o, position, &HashMap::new()))
            .collect::<Result<Vec<_>, _>>()
            .map(|v| v.join(" "))
    }

    fn continuity_from_clause(
        &self,
        r: &MultivariableAnalysisRelation,
        source: &CompleteFunctionDomainProof,
        input: &str,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (view, equal) =
            self.compile_multivariable_limit_view(r.argument_refs()[0], source, position)?;
        let raw = self.continuity_raw_arguments(r, position)?;
        Ok(format!("(by\n{view}\n  apply Litex.{} {raw}\n  intro epsilon h_epsilon\n  obtain ⟨delta,hd,hcontrol⟩ := {input} (Litex.semanticObject epsilon (M.member_isSet h_epsilon)) h_epsilon\n  refine ⟨delta,hd,?_⟩\n  intro input hi hclose\n  have hi : M.mem input _multivariable_source_domain := {equal}.symm ▸ hi\n  have good := hcontrol input ((Litex.SetSemantics.sep_members _ _ _).mpr ⟨hi,hi,hclose⟩)\n  exact ((Litex.SetSemantics.sep_members _ _ _).mp good).2.2\n)",law(r,true)))
    }

    fn continuity_to_clause(
        &self,
        r: &MultivariableAnalysisRelation,
        source: &CompleteFunctionDomainProof,
        input: &str,
        polymorphic: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (view, equal) =
            self.compile_multivariable_limit_view(r.argument_refs()[0], source, position)?;
        let raw = self.continuity_raw_arguments(r, position)?;
        let intro = if polymorphic {
            "  intro _Host _rep epsilon h_epsilon"
        } else {
            "  intro epsilon h_epsilon"
        };
        Ok(format!("(by\n{view}\n{intro}\n  obtain ⟨delta,hd,hcontrol⟩ := Litex.{} {raw} {input} (Litex.denote epsilon) h_epsilon\n  refine ⟨delta,hd,?_⟩\n  change ∀ input : M.Value, M.mem input _ → M.mem input _\n  intro input h_input\n  obtain ⟨hi,_,hclose⟩ := (Litex.SetSemantics.sep_members _ _ _).mp h_input\n  apply (Litex.SetSemantics.sep_members _ _ _).mpr\n  exact ⟨hi,hi,hcontrol input ({equal} ▸ hi) hclose⟩\n)",law(r,false)))
    }

    pub(super) fn compile_multivariable_continuity_definition(
        &self,
        r: &MultivariableAnalysisRelation,
        wd: &AtomicFactWellDefinedProof,
        requirements: &[Fact],
        proofs: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let ([requirement], [proof]) = (requirements, proofs) else {
            return Err(invalid("DefinitionStages"));
        };
        let PredicateDomainProof::MultivariableAnalysis(capture) = &wd
            .as_detailed()
            .map_err(|_| invalid("DefinitionDetailedWD"))?
            .predicate_domain
        else {
            return Err(invalid("DefinitionOriginalDomain"));
        };
        let domain = crate::execute::execute_fact_stmt::multivariable::helper::actual_domain(
            &capture.function_domain.signature,
        )
        .ok_or_else(|| invalid("ActualDomain"))?;
        validate_clause(r, &domain, requirement)?;
        if source_subject(proof)? != *requirement {
            return Err(invalid("DefinitionProofSubject"));
        }
        let (ty, term) = self.compile_verify(proof, &position.atomic_search_prior(0)?)?;
        let folded = self.continuity_from_clause(
            r,
            &capture.function_domain,
            "_continuity_control",
            position,
        )?;
        Ok(format!(
            "(by\n  have _continuity_control : {ty} := {term}\n  exact {folded}\n)"
        ))
    }

    pub(super) fn compile_multivariable_continuity_inferences(
        &self,
        infer: &InferAtomicFactResult,
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let (InferAtomicFactResult::MultivariableAnalysisFact(rules), Fact::AtomicFact(a)) =
            (infer, seed)
        else {
            return Err(invalid("InferenceFamily"));
        };
        let (r, false) = parts(a).ok_or_else(|| invalid("InferencePredicate"))? else {
            return Err(invalid("InferenceNegative"));
        };
        let [InferMultivariableAnalysisFactResult::Definition(capture)] = rules.as_slice() else {
            return Err(invalid("InferenceRule"));
        };
        if capture.source_fact_id != seed.fact_id()
            || capture.derived.len() != usize::from(capture.function_domain.is_some())
        {
            return Err(invalid("InferenceIdentity"));
        }
        let Some(source) = &capture.function_domain else {
            return Ok(Vec::new());
        };
        let target = self.resolve_fact(capture.derived[0].primary_fact_id(), position)?;
        self.validate_store(&capture.derived[0].store, &target)?;
        let domain = crate::execute::execute_fact_stmt::multivariable::helper::actual_domain(
            &source.signature,
        )
        .ok_or_else(|| invalid("InferenceDomain"))?;
        validate_clause(r, &domain, &target)?;
        let ty = self.compile_multivariable_clause_value_proposition(&target, position)?;
        let term = self.continuity_to_clause(r, source, &compiled.1, false, position)?;
        Ok(vec![self.emit_internal_fact(
            &target,
            &(ty, term),
            position,
        )?])
    }

    pub(super) fn compile_builtin_multivariable_continuity(
        &self,
        call: &TheoremCall,
        builtin: &BuiltinThmApplication,
        derivation: &TheoremDerivationProof,
        type_proofs: &[VerifyFactResult],
        type_stores: &[StoreFactAndInferResult],
        function_domain: Option<&BuiltinFunctionDomainProof>,
        dom_proofs: &[VerifyFactResult],
        dom_stores: &[StoreFactAndInferResult],
        conclusions_wd: &[FactWellDefinedProof],
        position: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, String, Vec<Fact>), LeanCompileError> {
        use BuiltinTheoremId::*;
        let (fold, vector) = match builtin.theorem {
            MultiContinuousAtFromDefinition => (true, false),
            MultiContinuousAtToDefinition => (false, false),
            VectorContinuousAtFromDefinition => (true, true),
            VectorContinuousAtToDefinition => (false, true),
            _ => return Err(invalid("Id")),
        };
        let context = 5 + usize::from(vector);
        let count = context + 1;
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
            || args != &builtin.arguments
            || args.len() != 3 + usize::from(vector)
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("OriginalStages"));
        }
        let Fact::AtomicFact(a) = (if fold {
            &builtin.conclusions[0]
        } else {
            &builtin.requirements[context]
        }) else {
            return Err(invalid("PositivePredicate"));
        };
        let (r, false) = parts(a).ok_or_else(|| invalid("PredicateFamily"))? else {
            return Err(invalid("NegativePredicate"));
        };
        if matches!(r, MultivariableAnalysisRelation::VectorContinuousAt(_)) != vector
            || !r
                .argument_refs()
                .iter()
                .zip(args)
                .all(|(a, b)| a.ir() == b.ir())
        {
            return Err(invalid("OriginalArguments"));
        }
        let source = if fold {
            let FactWellDefinedProof::AtomicExceptEquality(wd) = &conclusions_wd[0] else {
                return Err(invalid("OriginalFormation"));
            };
            let PredicateDomainProof::MultivariableAnalysis(capture) = &wd
                .as_detailed()
                .map_err(|_| invalid("DetailedFormation"))?
                .predicate_domain
            else {
                return Err(invalid("OriginalDomain"));
            };
            if capture.requirements.len()!=context || !builtin.requirements[..context].iter().zip(&capture.requirements).all(|(a,b)|
                crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::quantifier_free_source_facts_alpha_equal(a,&b.requirement)) {return Err(invalid("OriginalContext"));}
            &capture.function_domain
        } else {
            let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(
                rules,
            ))) = &dom_stores[context].infer
            else {
                return Err(invalid("OriginalInference"));
            };
            let [InferMultivariableAnalysisFactResult::Definition(capture)] = rules.as_slice()
            else {
                return Err(invalid("OriginalInference"));
            };
            if capture.source_fact_id != builtin.requirements[context].fact_id()
                || capture.derived.len() != 1
            {
                return Err(invalid("OriginalInferenceIdentity"));
            }
            capture
                .function_domain
                .as_ref()
                .ok_or_else(|| invalid("OriginalCompleteDomain"))?
        };
        super::compile_builtin_derivative_schema::validate_context(
            r,
            &builtin.requirements[..context],
            source,
        )?;
        let domain = crate::execute::execute_fact_stmt::multivariable::helper::actual_domain(
            &source.signature,
        )
        .ok_or_else(|| invalid("ActualDomain"))?;
        validate_clause(
            r,
            &domain,
            if fold {
                &builtin.requirements[context]
            } else {
                &builtin.conclusions[0]
            },
        )?;
        let mut definitions = Vec::new();
        for (index, ((requirement, checked), store)) in builtin
            .requirements
            .iter()
            .zip(dom_proofs)
            .zip(dom_stores)
            .enumerate()
        {
            if source_subject(checked)? != *requirement {
                return Err(invalid("OriginalProofSubject"));
            }
            let prior = SourcePosition {
                before: index,
                ..*position
            };
            let compiled = self.compile_verify(checked, &prior)?;
            self.validate_store(&store.store, requirement)?;
            definitions.push(self.emit_internal_fact(requirement, &compiled, &prior)?);
            definitions.extend(self.compile_stored_inferences(
                store,
                requirement,
                &(compiled.0, format!("h_{}", requirement.fact_id().value())),
                &SourcePosition {
                    before: index + 1,
                    ..*position
                },
            )?);
        }
        let formed = SourcePosition {
            before: count,
            ..*position
        };
        self.compile_fact_wd(&conclusions_wd[0], &builtin.conclusions[0], &formed)?;
        let statement = self.compile_formed_fact_proposition(
            &conclusions_wd[0],
            &builtin.conclusions[0],
            &formed,
        )?;
        let input = format!("h_{}", builtin.requirements[context].fact_id().value());
        let proof = if fold {
            self.continuity_from_clause(r, source, &input, &formed)?
        } else {
            self.continuity_to_clause(r, source, &input, true, &formed)?
        };
        Ok((
            definitions,
            format!("(show {statement} from {proof})"),
            builtin.conclusions.clone(),
        ))
    }
}
