//! The original global/pointwise schemas retain all context and storage stages.
use super::compile_function_limit_definition::signature_domain_matches;
use super::compile_function_limit_unary::real_limit_signature;
use super::compile_global_continuity::validate_pointwise;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::prelude::*;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("GlobalContinuityBuiltin/{stage}"))
}
impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_global_continuity(
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
            BuiltinTheoremId::FnContinuousFromPointwise => true,
            BuiltinTheoremId::FnContinuousAt => false,
            _ => return Err(invalid("Identity")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        let count = if from { 4 } else { 5 };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
            || args != &builtin.arguments
            || args.len() != builtin.theorem.arity()
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("OriginalStages"));
        }
        let req = &builtin.requirements;
        let (signature, _) = real_limit_signature(&req[..3], &args[0])?;
        let goal = &builtin.conclusions[0];
        let domain = if from {
            let Fact::ForallFact(all) = &req[3] else {
                return Err(invalid("PointwiseForall"));
            };
            let [group] = all.typed_parameters.groups.as_slice() else {
                return Err(invalid("PointwiseParameter"));
            };
            let ParamType::Obj(domain) = &group.param_type else {
                return Err(invalid("PointwiseDomain"));
            };
            if !signature_domain_matches(domain, signature) {
                return Err(invalid("OriginalCompleteDomain"));
            }
            validate_pointwise(&args[0], domain, &req[3])?;
            if !matches!(goal,Fact::AtomicFact(AtomicFact::FunctionContinuousFact(f)) if f.function.ir()==args[0].ir()&&f.property==FunctionContinuityProperty::Continuous)
            {
                return Err(invalid("GlobalConclusion"));
            }
            domain
        } else {
            if !matches!(&req[3],Fact::AtomicFact(AtomicFact::FunctionContinuousFact(f)) if f.function.ir()==args[0].ir()&&f.property==FunctionContinuityProperty::Continuous)
            {
                return Err(invalid("GlobalPremise"));
            }
            let Fact::AtomicFact(AtomicFact::InFact(point)) = &req[4] else {
                return Err(invalid("OriginalPointMember"));
            };
            if point.element.ir() != args[1].ir()
                || !signature_domain_matches(&point.set, signature)
            {
                return Err(invalid("OriginalPointDomain"));
            }
            if !matches!(goal,Fact::AtomicFact(AtomicFact::FunctionContinuousAtFact(f)) if f.function.ir()==args[0].ir()&&f.point.ir()==args[1].ir()&&f.side==RealApproachSide::Both)
            {
                return Err(invalid("PointwiseConclusion"));
            }
            &point.set
        };
        let (definitions, references) =
            self.compile_function_limit_requirements(req, dom_proofs, dom_stores, position)?;
        let formed = SourcePosition {
            before: count,
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
            domain,
            &req[..3],
            &references[..3],
            &scope,
        )?;
        let f = self.compile_object_reference(&args[0], &scope)?;
        let law = if from {
            format!(
                "exact Litex.functionContinuousOfForall {f} _law0_domain _law_domain_0 {}",
                references[3]
            )
        } else {
            let p = self.compile_object_reference(&args[1], &scope)?;
            format!("exact Litex.functionContinuousAtPoint (Litex.denote {f}) (Litex.denote {p}) {} (_law_domain_0 ▸ {})",references[3],references[4])
        };
        context.push(law);
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
