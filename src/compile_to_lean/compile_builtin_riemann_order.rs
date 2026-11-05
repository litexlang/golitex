//! Integral comparisons consume the original candidates and local inequalities.
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
use crate::execute::execute_fact_stmt::riemann_integral::helper::{
    abs, id, interval, mul, num, sorted_interval, sub,
};
use crate::prelude::*;
use std::collections::HashMap;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("RiemannOrder/{stage}"))
}
fn candidate(fact: &Fact, f: &Obj, a: &Obj, b: &Obj, v: &Obj) -> bool {
    matches!(fact,Fact::AtomicFact(AtomicFact::HasRiemannIntegralFact(p))
        if p.function.ir()==f.ir() && p.lower.ir()==a.ir() && p.upper.ir()==b.ir() && p.value.ir()==v.ir())
}
fn less_equal(fact: &Fact, left: &Obj, right: &Obj) -> bool {
    matches!(fact,Fact::AtomicFact(AtomicFact::LessEqualFact(p))
        if p.left.ir()==left.ir() && p.right.ir()==right.ir())
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_riemann_order(
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
        let compare = match builtin.theorem {
            BuiltinTheoremId::RiemannIntegralCompare => true,
            BuiltinTheoremId::RiemannIntegralBound => false,
            _ => return Err(invalid("Identity")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        let (arity, count, ai, original) = if compare { (6, 10, 2, 7) } else { (5, 7, 1, 3) };
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
        let (a, b, v) = (&args[ai], &args[ai + 1], &args[ai + 2]);
        if !candidate(&builtin.requirements[original], &args[0], a, b, v) {
            return Err(invalid("OriginalFirstPositiveCandidate"));
        }
        if compare {
            if !less_equal(&builtin.requirements[6], a, b)
                || !candidate(&builtin.requirements[8], &args[1], a, b, &args[5])
                || !less_equal(&builtin.conclusions[0], v, &args[5])
            {
                return Err(invalid("OriginalSecondCandidateOrderAndConclusion"));
            }
        } else if !matches!(&builtin.requirements[4],Fact::AtomicFact(AtomicFact::InFact(p))
            if p.element.ir()==args[4].ir() && p.set==Obj::StandardSet(StandardSet::R))
            || !less_equal(&builtin.requirements[5], &num("0"), &args[4])
            || !less_equal(
                &builtin.conclusions[0],
                &abs(v.clone()),
                &mul(args[4].clone(), abs(sub(b.clone(), a.clone()))),
            )
        {
            return Err(invalid("OriginalRealNonnegativeBoundAndAbsoluteWidth"));
        }
        let Fact::ForallFact(formula) = &builtin.requirements[count - 1] else {
            return Err(invalid("OriginalIntervalComparison"));
        };
        let domain = if compare {
            interval(a.clone(), b.clone())
        } else {
            sorted_interval(a.clone(), b.clone())
        };
        let x = parameter(&formula.typed_parameters, &domain)?;
        if !formula.dom_facts.is_empty() || args.iter().any(|o| contains_parameter(o, x.id)) {
            return Err(invalid("OriginalComparisonScope"));
        }
        let [ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::LessEqualFact(eq))] =
            formula.then_facts.as_slice()
        else {
            return Err(invalid("OriginalComparisonPolarity"));
        };
        if compare {
            if !call_matches(&eq.left, &args[0], &id(x))
                || !call_matches(&eq.right, &args[1], &id(x))
            {
                return Err(invalid("OriginalComparedFunctionsAndPoint"));
            }
        } else {
            let Obj::ArithmeticOperator(ArithmeticOperator::Abs(value)) = &eq.left else {
                return Err(invalid("OriginalAbsoluteComparison"));
            };
            if !call_matches(&value.arg, &args[0], &id(x)) || eq.right.ir() != args[4].ir() {
                return Err(invalid("OriginalBoundedFunctionPointAndBound"));
            }
        }
        let mut real_source = None;
        for (index, f, start) in if compare {
            vec![(7, &args[0], 0), (8, &args[1], 3)]
        } else {
            vec![(3, &args[0], 0)]
        } {
            let VerifyFactResult::AtomicExceptEquality(p) = &dom_proofs[index] else {
                return Err(invalid("OriginalCandidateVerification"));
            };
            let VerifyAtomicExceptEqualityFactResult::Success(p) = p.as_ref() else {
                return Err(invalid("OriginalCandidateSuccess"));
            };
            let (domain, real, view) = self.riemann_certificate_domain(
                &p.fact,
                &p.well_defined_proof,
                &SourcePosition {
                    before: index,
                    ..*position
                },
            )?;
            if !matches!(&p.fact,AtomicFact::HasRiemannIntegralFact(p) if p.function.ir()==f.ir()) {
                return Err(invalid("OriginalCandidateFunction"));
            }
            for (i, r) in builtin.requirements[start..start + 3].iter().enumerate() {
                validate_domain_requirement(r, i, a, b, &domain)?;
            }
            if !compare {
                real_source = Some((real, view.0));
            }
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
        let mut local = Vec::new();
        if !compare {
            if let Some((proofs, names)) = self.compile_riemann_endpoint_reductions(a, b, &scope)? {
                local.push(proofs);
                local.push("unfold Litex.riemannIntervalValue".into());
                local.push(endpoint_rewrites(&names, "").replace("\n  ", "\n"));
            }
        }
        local.push("intro x hx".into());
        local.push(format!(
            "exact {} (Litex.semanticObject (M := M) x (M.member_isSet hx)) hx",
            refs[count - 1]
        ));
        let proof = if compare {
            format!("(by\n  have _original_comparison : ∀ x, M.mem x (Litex.riemannClosedIntervalValue {} {}) → Litex.RealLeValue M (Litex.FunctionSemantics.callValue {} x) (Litex.FunctionSemantics.callValue {} x) := by\n    {}\n  exact Litex.riemannIntegralLocalCompare {} {} _original_comparison {} {}\n)",raw[2],raw[3],raw[0],raw[1],local.join("\n").replace('\n',"\n    "),raw.join(" "),refs[6],refs[7],refs[8])
        } else {
            let (real, view) = real_source.ok_or_else(|| invalid("OriginalRealFunction"))?;
            format!("(by\n{view}\n  have _original_real : Litex.RealFunctionValue M {} := {}\n  have _original_bound : ∀ x, M.mem x (Litex.riemannIntervalValue {} {}) → Litex.RealLeValue M (Litex.absValue (Litex.FunctionSemantics.callValue {} x)) {} := by\n    {}\n  exact Litex.riemannIntegralAbsoluteBound {} _original_real {} {} {} _original_bound\n)",raw[0],real.replace('\n',"\n  "),raw[1],raw[2],raw[0],raw[4],local.join("\n").replace('\n',"\n    "),raw.join(" "),refs[4],refs[5],refs[3])
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
