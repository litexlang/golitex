//! Oriented reversal and local equality retain the original Riemann certificates.
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::compile_riemann_integral::{endpoint_rewrites, validate_domain_requirement};
use super::compile_sequence_analysis::call_matches;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::execute::execute_fact_stmt::riemann_integral::helper::{id, mul, num, sorted_interval};
use crate::prelude::*;
use std::collections::HashMap;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("RiemannTransport/{stage}"))
}
fn candidate(fact: &Fact, f: &Obj, a: &Obj, b: &Obj, value: &Obj) -> Result<(), LeanCompileError> {
    if matches!(fact,Fact::AtomicFact(AtomicFact::HasRiemannIntegralFact(p))
        if p.function.ir()==f.ir() && p.lower.ir()==a.ir() && p.upper.ir()==b.ir() && p.value.ir()==value.ir())
    {
        Ok(())
    } else {
        Err(invalid("OriginalPositiveCandidate"))
    }
}
fn equation(fact: &Fact, args: &[Obj]) -> Result<(), LeanCompileError> {
    let Fact::ForallFact(p) = fact else {
        return Err(invalid("OriginalEquationUniversal"));
    };
    let interval = sorted_interval(args[2].clone(), args[3].clone());
    let x = parameter(&p.typed_parameters, &interval)?;
    if args.iter().any(|a| contains_parameter(a, x.id)) || !p.dom_facts.is_empty() {
        return Err(invalid("OriginalEquationScope"));
    }
    let [ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq))] =
        p.then_facts.as_slice()
    else {
        return Err(invalid("OriginalEquationClause"));
    };
    if !call_matches(&eq.left, &args[0], &id(x)) || !call_matches(&eq.right, &args[1], &id(x)) {
        return Err(invalid("OriginalEquationFunctionsAndPoint"));
    }
    Ok(())
}
impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_riemann_transport(
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
        let reverse = match builtin.theorem {
            BuiltinTheoremId::RiemannIntegralReverse => true,
            BuiltinTheoremId::RiemannIntegralExtensional => false,
            _ => return Err(invalid("Identity")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        let (arity, count, original) = if reverse { (4, 4, 3) } else { (5, 8, 6) };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || !matches!(&call.name,AtomicName::Plain{name} if name==builtin.theorem.as_str())
            || args != &builtin.arguments
            || args.len() != arity
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("OriginalStages"));
        }
        let (a, b, value) = if reverse {
            (&args[1], &args[2], &args[3])
        } else {
            (&args[2], &args[3], &args[4])
        };
        candidate(&builtin.requirements[original], &args[0], a, b, value)?;
        if reverse {
            candidate(
                &builtin.conclusions[0],
                &args[0],
                b,
                a,
                &mul(num("-1"), value.clone()),
            )?;
        } else {
            candidate(&builtin.conclusions[0], &args[1], a, b, value)?;
            equation(&builtin.requirements[7], args)?;
        }
        let VerifyFactResult::AtomicExceptEquality(p) = &dom_proofs[original] else {
            return Err(invalid("OriginalCandidateVerification"));
        };
        let VerifyAtomicExceptEqualityFactResult::Success(p) = p.as_ref() else {
            return Err(invalid("OriginalCandidateSuccess"));
        };
        let (source_domain, _, _) = self.riemann_certificate_domain(
            &p.fact,
            &p.well_defined_proof,
            &SourcePosition {
                before: original,
                ..*position
            },
        )?;
        for (index, requirement) in builtin.requirements[..3].iter().enumerate() {
            validate_domain_requirement(requirement, index, a, b, &source_domain)?;
        }
        let (definitions, refs) = self.compile_function_limit_requirements(
            &builtin.requirements,
            dom_proofs,
            dom_stores,
            position,
        )?;
        let formed = SourcePosition {
            before: count,
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
        let proof = if reverse {
            format!(
                "(Litex.riemannIntegralReverseCandidate {} {})",
                raw.join(" "),
                refs[3]
            )
        } else {
            let Fact::AtomicFact(goal) = &builtin.conclusions[0] else {
                return Err(invalid("OriginalGoal"));
            };
            let FactWellDefinedProof::AtomicExceptEquality(wd) = &conclusions_wd[0] else {
                return Err(invalid("OriginalGoalFormation"));
            };
            let (target_domain, real, (view, equal)) =
                self.riemann_certificate_domain(goal, wd, &formed)?;
            for (index, requirement) in builtin.requirements[3..6].iter().enumerate() {
                validate_domain_requirement(requirement, index, a, b, &target_domain)?;
            }
            let reductions = self.compile_riemann_endpoint_reductions(a, b, &scope)?;
            let mut cover = vec![
                format!("have _transport_domain_equal := {equal}"),
                "rw [← _transport_domain_equal]".into(),
            ];
            let mut formula = Vec::new();
            if let Some((proofs, names)) = &reductions {
                for lines in [&mut cover, &mut formula] {
                    lines.push(proofs.clone());
                    lines.push("unfold Litex.riemannIntervalValue".into());
                    lines.push(endpoint_rewrites(names, "").replace("\n  ", "\n"));
                }
            }
            cover.push(format!("exact {}", refs[5]));
            formula.push("intro x hx".into());
            formula.push(format!(
                "exact {} (Litex.semanticObject (M := M) x (M.member_isSet hx)) hx",
                refs[7]
            ));
            let indent = |s: &str| s.replace('\n', "\n  ");
            format!("(by\n{view}\n  have _transport_real : Litex.RealFunctionValue M {} := {}\n  have _transport_cover : ∀ x, M.mem x (Litex.riemannIntervalValue {} {}) → M.mem x (Litex.FunctionSemantics.domainValue {}) := by\n    {}\n  have _transport_equal : ∀ x, M.mem x (Litex.riemannIntervalValue {} {}) → Litex.FunctionSemantics.callValue {} x = Litex.FunctionSemantics.callValue {} x := by\n    {}\n  exact Litex.riemannIntegralLocalAgreement {} _transport_real _transport_cover _transport_equal {}\n)",raw[1],indent(&real),raw[2],raw[3],raw[1],cover.join("\n").replace('\n',"\n    "),raw[2],raw[3],raw[0],raw[1],formula.join("\n").replace('\n',"\n    "),raw.join(" "),refs[6])
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
