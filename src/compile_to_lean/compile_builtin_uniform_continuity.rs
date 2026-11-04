//! Consume the three original uniform-continuity schemas and ordered evidence.
use super::compile_function_limit_definition::signature_domain_matches;
use super::compile_function_limit_unary::real_limit_signature;
use super::compile_uniform_continuity::{validate_uniform_clause, validate_uniform_control};
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::prelude::*;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("UniformContinuityBuiltin/{stage}"))
}
fn uniform(fact: &Fact, function: &Obj, property: FunctionContinuityProperty) -> bool {
    matches!(fact, Fact::AtomicFact(AtomicFact::FunctionContinuousFact(f)) if f.function.ir()==function.ir() && f.property==property)
}
impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_uniform_continuity(
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
        let count = match builtin.theorem {
            FnUniformFromEpsilon | FnUniformContinuous => 4,
            FnUniformControl => 5,
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
        let domain = match builtin.theorem {
            FnUniformFromEpsilon => {
                let (_, _, domain) = validate_uniform_clause(&args[0], &req[3])?;
                if !uniform(
                    goal,
                    &args[0],
                    FunctionContinuityProperty::UniformContinuous,
                ) {
                    return Err(invalid("UniformConclusion"));
                }
                domain.clone()
            }
            FnUniformControl => {
                if !uniform(
                    &req[3],
                    &args[0],
                    FunctionContinuityProperty::UniformContinuous,
                ) || !matches!(&req[4], Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==args[1].ir() && f.set==Obj::StandardSet(StandardSet::RPos))
                {
                    return Err(invalid("UniformAndPositiveEpsilon"));
                }
                let Fact::ExistFact(exists) = goal else {
                    return Err(invalid("ControlExistence"));
                };
                validate_uniform_control(&args[0], &args[1], exists)?
                    .0
                    .clone()
            }
            FnUniformContinuous => {
                if !uniform(
                    &req[3],
                    &args[0],
                    FunctionContinuityProperty::UniformContinuous,
                ) || !uniform(goal, &args[0], FunctionContinuityProperty::Continuous)
                {
                    return Err(invalid("UniformToContinuous"));
                }
                let FactWellDefinedProof::AtomicExceptEquality(wd) = &conclusions_wd[0] else {
                    return Err(invalid("ContinuousFormation"));
                };
                let crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof::FunctionAnalysis(formation) = &wd.as_detailed().map_err(|_| invalid("DetailedFormation"))?.predicate_domain else {
                    return Err(invalid("ContinuousDomain"));
                };
                formation.function_domain.domain.clone()
            }
            _ => unreachable!(),
        };
        if !signature_domain_matches(&domain, signature) {
            return Err(invalid("OriginalCompleteDomain"));
        }
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
            &domain,
            &req[..3],
            &references[..3],
            &scope,
        )?;
        let f = self.compile_object_reference(&args[0], &scope)?;
        let law = match builtin.theorem {
            FnUniformFromEpsilon => format!(
                "exact Litex.functionUniformOfForall {f} _law0_domain _law_domain_0 {}",
                references[3]
            ),
            FnUniformControl => {
                let epsilon = self.compile_object_reference(&args[1], &scope)?;
                format!("have _uniform_control := Litex.functionUniformControl {f} {epsilon} {} {}\nrw [← _law_domain_0] at _uniform_control\nexact _uniform_control", references[4], references[3])
            }
            FnUniformContinuous => format!(
                "exact Litex.functionUniformImpliesContinuous (Litex.denote {f}) _law_real_0 {}",
                references[3]
            ),
            _ => unreachable!(),
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
