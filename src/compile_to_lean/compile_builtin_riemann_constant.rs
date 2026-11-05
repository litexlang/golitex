//! Replay the supplied function's original interval-local constant equation.
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
use crate::execute::execute_fact_stmt::riemann_integral::helper::{id, mul, sorted_interval, sub};
use crate::prelude::*;
use std::collections::HashMap;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("RiemannConstant/{stage}"))
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_riemann_constant(
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
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        if builtin.theorem != BuiltinTheoremId::RiemannIntegralConstant
            || !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || !matches!(&call.name,AtomicName::Plain{name} if name==builtin.theorem.as_str())
            || args != &builtin.arguments
            || args.len() != 4
            || builtin.requirements.len() != 5
            || dom_proofs.len() != 5
            || dom_stores.len() != 5
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("OriginalStages"));
        }
        let [f, a, b, c] = args.as_slice() else {
            return Err(invalid("Arguments"));
        };
        if !matches!(&builtin.requirements[3],Fact::AtomicFact(AtomicFact::InFact(p))
            if p.element.ir()==c.ir() && p.set==Obj::StandardSet(StandardSet::R))
        {
            return Err(invalid("OriginalConstantReal"));
        }
        let Fact::ForallFact(formula) = &builtin.requirements[4] else {
            return Err(invalid("OriginalIntervalEquation"));
        };
        let x = parameter(
            &formula.typed_parameters,
            &sorted_interval(a.clone(), b.clone()),
        )?;
        if !formula.dom_facts.is_empty() || args.iter().any(|o| contains_parameter(o, x.id)) {
            return Err(invalid("OriginalEquationScope"));
        }
        let [ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq))] =
            formula.then_facts.as_slice()
        else {
            return Err(invalid("OriginalEquationClause"));
        };
        if !call_matches(&eq.left, f, &id(x)) || eq.right.ir() != c.ir() {
            return Err(invalid("OriginalEquationFunctionPointAndConstant"));
        }
        let Fact::AtomicFact(goal @ AtomicFact::HasRiemannIntegralFact(candidate)) =
            &builtin.conclusions[0]
        else {
            return Err(invalid("OriginalPositiveGoal"));
        };
        let expected = mul(c.clone(), sub(b.clone(), a.clone()));
        if candidate.function.ir() != f.ir()
            || candidate.lower.ir() != a.ir()
            || candidate.upper.ir() != b.ir()
            || candidate.value.ir() != expected.ir()
        {
            return Err(invalid("OriginalFunctionEndpointsAndArea"));
        }
        let (definitions, refs) = self.compile_function_limit_requirements(
            &builtin.requirements,
            dom_proofs,
            dom_stores,
            position,
        )?;
        let formed = SourcePosition {
            before: 5,
            ..*position
        };
        self.compile_fact_wd(&conclusions_wd[0], &builtin.conclusions[0], &formed)?;
        let FactWellDefinedProof::AtomicExceptEquality(wd) = &conclusions_wd[0] else {
            return Err(invalid("OriginalGoalFormation"));
        };
        let (domain, real, (view, domain_equal)) =
            self.riemann_certificate_domain(goal, wd, &formed)?;
        for (index, requirement) in builtin.requirements[..3].iter().enumerate() {
            validate_domain_requirement(requirement, index, a, b, &domain)?;
        }
        let scope = SourcePosition::new(
            Some(&formed),
            SourceOwner::FactWD(&conclusions_wd[0]),
            usize::MAX,
        );
        let raw = args
            .iter()
            .map(|o| self.compile_function_raw_expression_bound(o, &scope, &HashMap::new()))
            .collect::<Result<Vec<_>, _>>()?;
        let mut cover = vec![
            format!("have _constant_domain_equal := {domain_equal}"),
            "rw [← _constant_domain_equal]".into(),
        ];
        let mut equal = Vec::new();
        if let Some((proofs, names)) = self.compile_riemann_endpoint_reductions(a, b, &scope)? {
            for lines in [&mut cover, &mut equal] {
                lines.push(proofs.clone());
                lines.push("unfold Litex.riemannIntervalValue".into());
                lines.push(endpoint_rewrites(&names, "").replace("\n  ", "\n"));
            }
        }
        cover.push(format!("exact {}", refs[2]));
        equal.push("intro x hx".into());
        equal.push(format!(
            "exact {} (Litex.semanticObject (M := M) x (M.member_isSet hx)) hx",
            refs[4]
        ));
        let proof = format!(
            "(by\n{view}\n  have _constant_real : Litex.RealFunctionValue M {} := {}\n  have _constant_cover : ∀ x, M.mem x (Litex.riemannIntervalValue {} {}) → M.mem x (Litex.FunctionSemantics.domainValue {}) := by\n    {}\n  have _constant_equal : ∀ x, M.mem x (Litex.riemannIntervalValue {} {}) → Litex.FunctionSemantics.callValue {} x = {} := by\n    {}\n  exact Litex.riemannIntegralConstantCandidate {} _constant_real {} {} {} _constant_cover _constant_equal\n)",
            raw[0],real.replace('\n',"\n  "),raw[1],raw[2],raw[0],cover.join("\n").replace('\n',"\n    "),raw[1],raw[2],raw[0],raw[3],equal.join("\n").replace('\n',"\n    "),raw.join(" "),refs[0],refs[1],refs[3]
        );
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
