//! Replay the supplied first-partial function and both complete domain captures.
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::compile_sequence_analysis::call_matches;
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::execute::execute_fact_stmt::function_domain::{
    function_domains_alpha_equal, CompleteFunctionDomainProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
};
use std::collections::HashMap;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("SecondPartialFunction/{stage}"))
}
fn inferred_source<'a>(
    store: &'a StoreFactAndInferResult,
    fact: &Fact,
    derived: usize,
) -> Result<&'a CompleteFunctionDomainProof, LeanCompileError> {
    let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(rules))) =
        &store.infer
    else {
        return Err(invalid("OriginalInference"));
    };
    let [InferMultivariableAnalysisFactResult::Definition(p)] = rules.as_slice() else {
        return Err(invalid("OriginalInferenceRule"));
    };
    if p.source_fact_id != fact.fact_id() || p.derived.len() != derived {
        return Err(invalid("OriginalInferenceIdentity"));
    }
    p.function_domain
        .as_ref()
        .ok_or_else(|| invalid("OriginalCompleteDomain"))
}
fn formed_source(
    wd: &FactWellDefinedProof,
    requirements: usize,
) -> Result<&CompleteFunctionDomainProof, LeanCompileError> {
    let FactWellDefinedProof::AtomicExceptEquality(wd) = wd else {
        return Err(invalid("OriginalFormation"));
    };
    let PredicateDomainProof::MultivariableAnalysis(p) = &wd
        .as_detailed()
        .map_err(|_| invalid("DetailedFormation"))?
        .predicate_domain
    else {
        return Err(invalid("OriginalDomain"));
    };
    if p.requirements.len() != requirements {
        return Err(invalid("OriginalFormationStages"));
    }
    Ok(&p.function_domain)
}
fn relation(
    fact: &Fact,
    second: bool,
    args: &[&Obj],
) -> Result<MultivariableAnalysisRelation, LeanCompileError> {
    let Fact::AtomicFact(AtomicFact::MultivariableAnalysisFact(p)) = fact else {
        return Err(invalid("PositiveCandidate"));
    };
    if !matches!(
        (&p.relation, second),
        (
            MultivariableAnalysisRelation::SecondPartialDerivativeAt(_),
            true
        ) | (MultivariableAnalysisRelation::PartialDerivativeAt(_), false)
    ) {
        return Err(invalid("CandidateFamily"));
    }
    let actual = p.relation.argument_refs();
    if actual.len() != args.len() || !actual.iter().zip(args).all(|(a, b)| a.ir() == b.ir()) {
        return Err(invalid("CandidateArguments"));
    }
    Ok(p.relation.clone())
}
fn first_clause(args: &[Obj], domain: &Obj, fact: &Fact) -> Result<(), LeanCompileError> {
    let Fact::ForallFact(p) = fact else {
        return Err(invalid("FirstPartialsForall"));
    };
    let x = parameter(&p.typed_parameters, domain)?;
    if !p.dom_facts.is_empty() || args.iter().any(|o| contains_parameter(o, x.id)) {
        return Err(invalid("FirstPartialsScope"));
    }
    let [ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::MultivariableAnalysisFact(q))] =
        p.then_facts.as_slice()
    else {
        return Err(invalid("FirstPartialConclusion"));
    };
    let MultivariableAnalysisRelation::PartialDerivativeAt(q) = &q.relation else {
        return Err(invalid("FirstPartialFamily"));
    };
    let xx = Obj::Identifier(IdentifierObj::from_bound_name(x));
    if q.function.ir() != args[0].ir()
        || q.point.ir() != xx.ir()
        || q.dimension.ir() != args[3].ir()
        || q.coordinate.ir() != args[4].ir()
        || !call_matches(&q.value, &args[1], &xx)
    {
        return Err(invalid("FirstPartialSubject"));
    }
    Ok(())
}
impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_second_partial_function(
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
        let fold = match builtin.theorem {
            BuiltinTheoremId::SecondPartialAtFromFunction => true,
            BuiltinTheoremId::SecondPartialAtToFunction => false,
            _ => return Err(invalid("Identity")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || !matches!(&call.name,AtomicName::Plain{name} if name==builtin.theorem.as_str())
            || args != &builtin.arguments
            || args.len() != 7
            || builtin.requirements.len() != 16
            || dom_proofs.len() != 16
            || dom_stores.len() != 16
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("OriginalStages"));
        }
        let second_args = [&args[0], &args[2], &args[3], &args[4], &args[5], &args[6]];
        let partial_args = [&args[1], &args[2], &args[3], &args[5], &args[6]];
        let second = relation(
            if fold {
                &builtin.conclusions[0]
            } else {
                &builtin.requirements[14]
            },
            true,
            &second_args,
        )?;
        relation(
            if fold {
                &builtin.requirements[15]
            } else {
                &builtin.conclusions[0]
            },
            false,
            &partial_args,
        )?;
        let source_f = if fold {
            formed_source(&conclusions_wd[0], 8)?
        } else {
            inferred_source(&dom_stores[14], &builtin.requirements[14], 2)?
        };
        let source_g = if fold {
            inferred_source(&dom_stores[15], &builtin.requirements[15], 3)?
        } else {
            formed_source(&conclusions_wd[0], 7)?
        };
        if !function_domains_alpha_equal(&source_f.signature, &source_g.signature) {
            return Err(invalid("SameCompleteDomain"));
        }
        super::compile_builtin_derivative_schema::validate_context(
            &second,
            &builtin.requirements[..7],
            source_f,
        )?;
        let mut g_args = second
            .argument_refs()
            .into_iter()
            .cloned()
            .collect::<Vec<_>>();
        g_args[0] = args[1].clone();
        let g_context = second.with_arguments(&g_args);
        super::compile_builtin_derivative_schema::validate_context(
            &g_context,
            &builtin.requirements[7..14],
            source_g,
        )?;
        let domain = crate::execute::execute_fact_stmt::multivariable::helper::actual_domain(
            &source_f.signature,
        )
        .ok_or_else(|| invalid("ActualDomain"))?;
        let first_index = if fold { 14 } else { 15 };
        first_clause(args, &domain, &builtin.requirements[first_index])?;
        let (definitions, refs) = self.compile_function_limit_requirements(
            &builtin.requirements,
            dom_proofs,
            dom_stores,
            position,
        )?;
        let formed = SourcePosition {
            before: 16,
            ..*position
        };
        self.compile_fact_wd(&conclusions_wd[0], &builtin.conclusions[0], &formed)?;
        let scope = SourcePosition::new(
            Some(&formed),
            SourceOwner::FactWD(&conclusions_wd[0]),
            usize::MAX,
        );
        let raw = args
            .iter()
            .map(|o| self.compile_function_raw_expression_bound(o, &scope, &HashMap::new()))
            .collect::<Result<Vec<_>, _>>()?;
        let (view_f, equal_f) =
            self.compile_multivariable_limit_view(&args[0], source_f, &scope)?;
        let (view_g, equal_g) =
            self.compile_multivariable_limit_view(&args[1], source_g, &scope)?;
        let real_f = self.compile_euclidean_limit_function_context(
            &[args[0].clone(), args[2].clone(), args[3].clone()],
            &builtin.requirements[..4],
            source_f,
            None,
            &scope,
        )?;
        let real_g = self.compile_euclidean_limit_function_context(
            &[args[1].clone(), args[2].clone(), args[3].clone()],
            &builtin.requirements[7..11],
            source_g,
            None,
            &scope,
        )?;
        let source_domain =
            self.compile_function_raw_expression_bound(&domain, &scope, &HashMap::new())?;
        let f = &raw[0];
        let g = &raw[1];
        let n = &raw[3];
        let axis = &raw[4];
        let first = &refs[first_index];
        let original = &refs[if fold { 15 } else { 14 }];
        let head = raw.join(" ");
        let law = if fold {
            "secondPartialOfFirstPartialFunction"
        } else {
            "firstPartialFunctionOfSecondPartial"
        };
        let extra = if fold {
            format!(
                "_second_real_f _second_real_g _second_same_domain (_second_domain_f ▸ {})",
                refs[4]
            )
        } else {
            "_second_real_g _second_same_domain".into()
        };
        let nested = |s: &str| format!("  {}", s.replace('\n', "\n  "));
        let proof=format!("(by\n  have _second_real_f : Litex.RealMultivariableFunctionValue M {f} {n} := by\n{}\n{}\n    exact _multivariable_real\n  have _second_real_g : Litex.RealMultivariableFunctionValue M {g} {n} := by\n{}\n{}\n    exact _multivariable_real\n  have _second_domain_f : {source_domain} = Litex.FunctionSemantics.domainValue {f} := by\n{}\n    exact {equal_f}\n  have _second_domain_g : {source_domain} = Litex.FunctionSemantics.domainValue {g} := by\n{}\n    exact {equal_g}\n  have _second_same_domain := _second_domain_g.symm.trans _second_domain_f\n  have _second_first : ∀ x, M.mem x (Litex.FunctionSemantics.domainValue {f}) → Litex.HasPartialDerivativeAtValue M {f} x {n} {axis} (Litex.FunctionSemantics.callValue {g} x) := by\n    intro x hx\n    have hx : M.mem x {source_domain} := _second_domain_f.symm ▸ hx\n    exact {first} (Litex.semanticObject x (M.member_isSet hx)) hx\n  exact Litex.{law} {head} {extra} _second_first {original}\n)",nested(&view_f),nested(&real_f),nested(&view_g),nested(&real_g),nested(&view_f),nested(&view_g));
        let statement = self.compile_formed_fact_proposition(
            &conclusions_wd[0],
            &builtin.conclusions[0],
            &formed,
        )?;
        Ok((
            definitions,
            format!("(show {statement} from {proof})"),
            builtin.conclusions.clone(),
        ))
    }
}
