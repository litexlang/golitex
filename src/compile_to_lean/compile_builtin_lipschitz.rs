//! Original Lipschitz schemas replay their ordered context, stores and formation.
use super::compile_function_limit_definition::signature_domain_matches;
use super::compile_function_limit_unary::real_limit_signature;
use super::compile_lipschitz::validate_estimate;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::prelude::*;
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("LipschitzBuiltin/{stage}"))
}
impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_lipschitz(
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
        let from = match builtin.theorem {
            BuiltinTheoremId::FnLipschitzFromEstimate => true,
            BuiltinTheoremId::FnLipschitzUniform => false,
            _ => return Err(invalid("Identity")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
            || args != &builtin.arguments
            || args.len() != builtin.theorem.arity()
            || args.len() != 2
            || builtin.requirements.len() != 4
            || dom_proofs.len() != 4
            || dom_stores.len() != 4
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("OriginalStages"));
        }
        let req = &builtin.requirements;
        let (signature, _) = real_limit_signature(&req[..3], &args[0])?;
        let goal = &builtin.conclusions[0];
        let domain = if from {
            if !matches!(goal,Fact::AtomicFact(AtomicFact::FunctionLipschitzFact(f)) if f.function.ir()==args[0].ir() && f.constant.ir()==args[1].ir())
            {
                return Err(invalid("LipschitzConclusion"));
            }
            validate_estimate(&args[0], &args[1], &req[3])?.2.clone()
        } else {
            if !matches!(&req[3],Fact::AtomicFact(AtomicFact::FunctionLipschitzFact(f)) if f.function.ir()==args[0].ir() && f.constant.ir()==args[1].ir())
                || !matches!(goal,Fact::AtomicFact(AtomicFact::FunctionContinuousFact(f)) if f.function.ir()==args[0].ir() && f.property==FunctionContinuityProperty::UniformContinuous)
            {
                return Err(invalid("UniformConclusionOrPremise"));
            }
            let FactWellDefinedProof::AtomicExceptEquality(wd) = &conclusions_wd[0] else {
                return Err(invalid("UniformFormation"));
            };
            let PredicateDomainProof::FunctionAnalysis(formation) = &wd
                .as_detailed()
                .map_err(|_| invalid("DetailedFormation"))?
                .predicate_domain
            else {
                return Err(invalid("UniformDomain"));
            };
            formation.function_domain.domain.clone()
        };
        if !signature_domain_matches(&domain, signature) {
            return Err(invalid("OriginalCompleteDomain"));
        }
        let (definitions, references) =
            self.compile_function_limit_requirements(req, dom_proofs, dom_stores, position)?;
        let formed = SourcePosition {
            before: 4,
            ..*position
        };
        self.compile_fact_wd(&conclusions_wd[0], goal, &formed)?;
        let scope = SourcePosition::new(
            Some(&formed),
            SourceOwner::FactWD(&conclusions_wd[0]),
            usize::MAX,
        );
        let statement = self.compile_formed_fact_proposition(&conclusions_wd[0], goal, &formed)?;
        let mut context = self.compile_function_limit_context(
            0,
            &args[0],
            &domain,
            &req[..3],
            &references[..3],
            &scope,
        )?;
        let f = self.compile_object_reference(&args[0], &scope)?;
        if from {
            let k = self.compile_object_reference(&args[1], &scope)?;
            context.push(format!(
                "exact Litex.functionLipschitzOfForall {f} {k} _law0_domain _law_domain_0 {}",
                references[3]
            ));
        } else {
            let prior = SourcePosition {
                before: 3,
                ..*position
            };
            let (wd, k, hk) = self.compile_lipschitz_checked_formation(
                &dom_proofs[3],
                &args[0],
                &args[1],
                &prior,
            )?;
            context.extend(wd);
            context.push(format!("exact Litex.functionLipschitzUniform (Litex.denote {f}) (Litex.denote {k}) {hk} {}",references[3]));
        }
        let proof = format!(
            "(by\n{}\n)",
            context
                .join("\n")
                .lines()
                .map(|l| format!("  {l}"))
                .collect::<Vec<_>>()
                .join("\n")
        );
        Ok((
            definitions,
            format!("(show {statement} from {proof})"),
            builtin.conclusions.clone(),
        ))
    }
}
