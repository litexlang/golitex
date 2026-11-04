//! Replay the original local first-partial witness, without choosing a new one.
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    PredicateDomainProof, PredicateDomainRequirementProof,
};
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
};
use std::collections::HashMap;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("SecondPartialDefinition/{stage}"))
}
impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_second_partial_definition(
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
            BuiltinTheoremId::SecondPartialAtFromDefinition => true,
            BuiltinTheoremId::SecondPartialAtToDefinition => false,
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
            || args.len() != 6
            || builtin.requirements.len() != 8
            || dom_proofs.len() != 8
            || dom_stores.len() != 8
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("OriginalStages"));
        }
        let candidate = if fold {
            &builtin.conclusions[0]
        } else {
            &builtin.requirements[7]
        };
        let Fact::AtomicFact(AtomicFact::MultivariableAnalysisFact(candidate)) = candidate else {
            return Err(invalid("PositiveCandidate"));
        };
        let MultivariableAnalysisRelation::SecondPartialDerivativeAt(r) = &candidate.relation
        else {
            return Err(invalid("CandidateFamily"));
        };
        let actual = candidate.relation.argument_refs();
        if actual.len() != args.len() || !actual.iter().zip(args).all(|(a, b)| a.ir() == b.ir()) {
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
            if capture.requirements.len()!=8 || !builtin.requirements[..7].iter().zip(&capture.requirements[..7]).all(|(a,b)|crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::quantifier_free_source_facts_alpha_equal(a,&b.requirement)) {return Err(invalid("OriginalContext"));}
            let member = &capture.requirements[7];
            if !matches!(&member.requirement,Fact::AtomicFact(AtomicFact::InFact(m)) if m.element.ir()==r.value.ir() && m.set==Obj::StandardSet(StandardSet::R))
            {
                return Err(invalid("ValueCarrier"));
            }
            let PredicateDomainRequirementProof::Verified(proof) = &member.result else {
                return Err(invalid("OriginalValueProof"));
            };
            if source_subject(proof)? != member.requirement {
                return Err(invalid("OriginalValueSubject"));
            }
            &capture.function_domain
        } else {
            let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(
                rules,
            ))) = &dom_stores[7].infer
            else {
                return Err(invalid("OriginalInference"));
            };
            let [InferMultivariableAnalysisFactResult::Definition(capture)] = rules.as_slice()
            else {
                return Err(invalid("OriginalInferenceRule"));
            };
            if capture.source_fact_id != builtin.requirements[7].fact_id()
                || capture.derived.len() != 2
            {
                return Err(invalid("OriginalInferenceIdentity"));
            }
            capture
                .function_domain
                .as_ref()
                .ok_or_else(|| invalid("OriginalCompleteDomain"))?
        };
        super::compile_builtin_derivative_schema::validate_context(
            &candidate.relation,
            &builtin.requirements[..7],
            source,
        )?;
        let domain = crate::execute::execute_fact_stmt::multivariable::helper::actual_domain(
            &source.signature,
        )
        .ok_or_else(|| invalid("ActualDomain"))?;
        super::compile_second_partial::validate_clauses(
            r,
            &domain,
            if fold {
                &builtin.requirements[7..]
            } else {
                &builtin.conclusions
            },
        )?;
        let (definitions, refs) = self.compile_function_limit_requirements(
            &builtin.requirements,
            dom_proofs,
            dom_stores,
            position,
        )?;
        let formed = SourcePosition {
            before: 8,
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
        let (view, equal) = self.compile_multivariable_limit_view(&r.function, source, &scope)?;
        let tail = raw[1..].join(" ");
        let head = format!("{} _multivariable_source_domain {tail}", raw[0]);
        let original = &refs[7];
        let proof = if fold {
            format!("(by\n{view}\n  have _second_partial_original_clause : Litex.SecondPartialDefinitionValue M {head} := {original}\n  exact Litex.secondPartialFromDefiningClause {head} {equal} _second_partial_original_clause\n)")
        } else {
            format!("(by\n{view}\n  exact Litex.secondPartialDefiningClause {head} {equal} {original}\n)")
        };
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
