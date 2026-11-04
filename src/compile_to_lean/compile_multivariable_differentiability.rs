//! Differentiability is the recorded existence of an exact differential matrix.
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
};
use std::collections::HashMap;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("MultivariableDifferentiability/{stage}"))
}

pub(super) fn parts(fact: &AtomicFact) -> Option<(&MultivariableAnalysisRelation, bool)> {
    let (f, negative) = match fact {
        AtomicFact::MultivariableAnalysisFact(f) => (&f.relation, false),
        AtomicFact::NotMultivariableAnalysisFact(f) => (&f.relation, true),
        _ => return None,
    };
    matches!(
        f,
        MultivariableAnalysisRelation::ScalarDifferentiableAt(_)
            | MultivariableAnalysisRelation::TotalDifferentiableAt(_)
    )
    .then_some((f, negative))
}

fn existence(r: &MultivariableAnalysisRelation, fact: &Fact) -> Result<(), LeanCompileError> {
    let Fact::ExistFact(e) = fact else {
        return Err(invalid("Existence"));
    };
    let args = r.argument_refs();
    let scalar = matches!(r, MultivariableAnalysisRelation::ScalarDifferentiableAt(_));
    let rows = if scalar {
        crate::execute::execute_fact_stmt::multivariable::helper::number(1)
    } else {
        args[3].clone()
    };
    let p = parameter(
        &e.typed_parameters,
        &super::compile_total_differential::matrix_set(&rows, args[2]),
    )?;
    if args.iter().any(|o| contains_parameter(o, p.id)) {
        return Err(invalid("ExistenceCapture"));
    }
    let [QuantifierFreeFact::AtomicFact(AtomicFact::MultivariableAnalysisFact(f))] =
        e.facts.as_slice()
    else {
        return Err(invalid("ExistenceCandidate"));
    };
    if !matches!(
        (&f.relation, scalar),
        (MultivariableAnalysisRelation::ScalarDifferentialAt(_), true)
            | (MultivariableAnalysisRelation::TotalDerivativeAt(_), false)
    ) {
        return Err(invalid("ExistenceFamily"));
    }
    let candidate = f.relation.argument_refs();
    let value = Obj::Identifier(IdentifierObj::from_bound_name(p));
    if candidate.len() != args.len() + 1
        || !candidate[..args.len()]
            .iter()
            .zip(args)
            .all(|(a, b)| a.ir() == b.ir())
        || candidate.last().unwrap().ir() != value.ir()
    {
        return Err(invalid("ExistenceArguments"));
    }
    Ok(())
}

fn law(r: &MultivariableAnalysisRelation, fold: bool) -> &'static str {
    match (
        matches!(r, MultivariableAnalysisRelation::ScalarDifferentiableAt(_)),
        fold,
    ) {
        (true, true) => "scalarDifferentiableAtFromDefinition",
        (true, false) => "scalarDifferentiableAtToDefinition",
        (false, true) => "vectorDifferentiableAtFromDefinition",
        (false, false) => "vectorDifferentiableAtToDefinition",
    }
}

impl LitexToLeanCompiler {
    pub(super) fn compile_multivariable_differentiability_definition(
        &self,
        r: &MultivariableAnalysisRelation,
        requirements: &[Fact],
        proofs: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let ([requirement], [proof]) = (requirements, proofs) else {
            return Err(invalid("DefinitionStages"));
        };
        existence(r, requirement)?;
        if source_subject(proof)? != *requirement {
            return Err(invalid("DefinitionProofSubject"));
        }
        let (ty, term) = self.compile_verify(proof, &position.atomic_search_prior(0)?)?;
        let args = r
            .argument_refs()
            .into_iter()
            .map(|o| self.compile_function_raw_expression_bound(o, position, &HashMap::new()))
            .collect::<Result<Vec<_>, _>>()?
            .join(" ");
        Ok(format!("(by\n  have _differentiability_exists : {ty} := {term}\n  apply Litex.{} {args}\n  obtain ⟨a,ha,hc⟩ := _differentiability_exists\n  exact ⟨a,ha,hc⟩\n)",law(r,true)))
    }

    pub(super) fn compile_multivariable_differentiability_inferences(
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
        let (view, _) =
            self.compile_multivariable_limit_view(r.argument_refs()[0], source, position)?;
        let target = self.resolve_fact(capture.derived[0].primary_fact_id(), position)?;
        self.validate_store(&capture.derived[0].store, &target)?;
        existence(r, &target)?;
        let ty = self.compile_function_raw_predicate(&target, position, &HashMap::new())?;
        let args = r
            .argument_refs()
            .into_iter()
            .map(|o| self.compile_function_raw_expression_bound(o, position, &HashMap::new()))
            .collect::<Result<Vec<_>, _>>()?
            .join(" ");
        let term = format!(
            "(by\n{view}\n  obtain ⟨a,ha,hc⟩ := Litex.{} {args} {}\n  exact ⟨a,ha,hc⟩\n)",
            law(r, false),
            compiled.1
        );
        Ok(vec![self.emit_internal_fact(
            &target,
            &(ty, term),
            position,
        )?])
    }

    pub(super) fn compile_builtin_multivariable_differentiability(
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
            MultiDifferentiableAtFromDefinition => (true, false),
            MultiDifferentiableAtToDefinition => (false, false),
            VectorDifferentiableAtFromDefinition => (true, true),
            VectorDifferentiableAtToDefinition => (false, true),
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
        if matches!(r, MultivariableAnalysisRelation::TotalDifferentiableAt(_)) != vector
            || !r
                .argument_refs()
                .iter()
                .zip(args)
                .all(|(a, b)| a.ir() == b.ir())
        {
            return Err(invalid("OriginalArguments"));
        }
        existence(
            r,
            if fold {
                &builtin.requirements[context]
            } else {
                &builtin.conclusions[0]
            },
        )?;
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
                crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::quantifier_free_source_facts_alpha_equal(a,&b.requirement)) {
                return Err(invalid("OriginalContext"));
            }
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
        let raw = args
            .iter()
            .map(|o| self.compile_function_raw_expression_bound(o, &formed, &HashMap::new()))
            .collect::<Result<Vec<_>, _>>()?
            .join(" ");
        let input = format!("h_{}", builtin.requirements[context].fact_id().value());
        let proof = if fold {
            format!(
                "(by\n  apply Litex.{} {raw}\n  obtain ⟨a,ha,hc⟩ := {input}\n  exact ⟨a,ha,hc⟩\n)",
                law(r, true)
            )
        } else {
            format!(
                "(by\n  obtain ⟨a,ha,hc⟩ := Litex.{} {raw} {input}\n  exact ⟨a,ha,hc⟩\n)",
                law(r, false)
            )
        };
        Ok((
            definitions,
            format!("(show {statement} from {proof})"),
            builtin.conclusions.clone(),
        ))
    }
}
