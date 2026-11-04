//! Fold or project the original punctured quotient limit, without new search.
use super::compile_function_derivative_definition::{
    validate_derivative_interior, validate_quotient,
};
use super::compile_function_limit_definition::signature_domain_matches;
use super::compile_function_limit_unary::real_limit_signature;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::prelude::*;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("DerivativeQuotientBuiltin/{stage}"))
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_derivative_quotient(
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
            BuiltinTheoremId::FnDerivativeAtFromLimit => true,
            BuiltinTheoremId::FnDerivativeAtToLimit => false,
            _ => return Err(invalid("Identity")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        let count = if from { 7 } else { 5 };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
            || args != &builtin.arguments
            || args.len() != 3
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
        let Fact::AtomicFact(AtomicFact::InFact(point)) = &req[3] else {
            return Err(invalid("PointMember"));
        };
        if point.element.ir() != args[1].ir() || !signature_domain_matches(&point.set, signature) {
            return Err(invalid("OriginalPointDomain"));
        }
        let goal = &builtin.conclusions[0];
        let (candidate, limit) = if from {
            if !matches!(&req[4], Fact::AtomicFact(AtomicFact::InFact(m)) if m.element.ir()==args[2].ir()&&m.set==Obj::StandardSet(StandardSet::R))
            {
                return Err(invalid("OriginalValueCarrier"));
            }
            (goal, &req[6])
        } else {
            (&req[4], goal)
        };
        let Fact::AtomicFact(AtomicFact::HasDerivativeAtFact(source)) = candidate else {
            return Err(invalid("OriginalDerivativeCandidate"));
        };
        if source.function.ir() != args[0].ir()
            || source.point.ir() != args[1].ir()
            || source.value.ir() != args[2].ir()
        {
            return Err(invalid("OriginalCandidateSubject"));
        }
        let quotient = validate_quotient(source, &point.set, limit)?;
        if from {
            validate_derivative_interior(&args[0], &args[1], &point.set, &req[5])?;
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
        let f = self.compile_object_reference(&args[0], &scope)?;
        let p = self.compile_object_reference(&args[1], &scope)?;
        let v = self.compile_object_reference(&args[2], &scope)?;
        // A candidate can reuse ByKnownFact WD. The original three explicit
        // context premises still provide its complete domain and real signature.
        let mut context = self.compile_function_limit_context(
            0,
            &source.function,
            &point.set,
            &req[..3],
            &references[..3],
            &scope,
        )?;
        context.push("let _source_domain := Litex.denote _law0_domain".into());
        context
            .push("have _domain_set : M.isSet _source_domain := Litex.isSet _law0_domain".into());
        context.push(format!(
            "have _derivative_real : Litex.RealFunctionValue M (Litex.denote {f}) := _law_real_0"
        ));
        context.push("have _derivative_domain_eq := _law_domain_0".into());
        let (body, _) = self.compile_derivative_quotient_body_view(
            &f,
            &source.point,
            &point.set,
            quotient,
            &scope,
        )?;
        let view = format!(
            "{}\n{body}",
            context
                .join("\n")
                .lines()
                .map(|l| format!("  {l}"))
                .collect::<Vec<_>>()
                .join("\n")
        );
        let proof = if from {
            format!("(by\n{view}\n  have _interior : Litex.DerivativeInteriorClauseValue M (Litex.denote {f}) (Litex.denote {p}) := by\n    unfold Litex.DerivativeInteriorClauseValue\n    rw [← _derivative_domain_eq]\n    exact {}\n  exact Litex.derivativeOfQuotientGraph (Litex.denote {f}) (Litex.denote {p}) (Litex.denote {v}) _derivative_quotient_domain _derivative_real _derivative_quotient_set _derivative_quotient_spec _interior {}\n)", references[5], references[6])
        } else {
            format!("(by\n{view}\n  exact (Litex.derivativeQuotientGraph (Litex.denote {f}) (Litex.denote {p}) (Litex.denote {v}) _derivative_quotient_domain _derivative_real _derivative_quotient_set _derivative_quotient_spec {}).2\n)", references[4])
        };
        Ok((
            definitions,
            format!("(show {statement} from {proof})"),
            builtin.conclusions.clone(),
        ))
    }
}
