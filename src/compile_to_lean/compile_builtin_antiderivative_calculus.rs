//! Chain and constant-difference laws retain their original source functions.
use super::compile_antiderivative::{context_count, invalid, parts, validate_context};
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::compile_sequence_analysis::call_matches;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::execute::execute_fact_stmt::real_analysis::analysis_apply;
use crate::execute::execute_fact_stmt::riemann_integral::helper::open_interval;
use crate::prelude::*;
use std::collections::HashMap;

fn candidate(fact: &Fact, args: &[&Obj]) -> Result<(), LeanCompileError> {
    let Fact::AtomicFact(f) = fact else {
        return Err(invalid("CalculusPositiveCandidate"));
    };
    let Some((actual, false)) = parts(f) else {
        return Err(invalid("CalculusPositiveCandidate"));
    };
    if actual.len() != 3 || !actual.iter().zip(args).all(|(a, b)| a.ir() == b.ir()) {
        return Err(invalid("CalculusCandidateArguments"));
    }
    Ok(())
}
fn universal<'a>(
    fact: &'a Fact,
    region: &Obj,
    args: &[Obj],
    count: usize,
) -> Result<&'a ForallFact, LeanCompileError> {
    let Fact::ForallFact(p) = fact else {
        return Err(invalid("CalculusOriginalUniversal"));
    };
    let x = parameter(&p.typed_parameters, region)?;
    if !p.dom_facts.is_empty()
        || p.then_facts.len() != count
        || args.iter().any(|a| contains_parameter(a, x.id))
    {
        return Err(invalid("CalculusUniversalScope"));
    }
    Ok(p)
}
fn equality(fact: &ExistOrAndChainAtomicFact, left: &Obj, right: &Obj) -> bool {
    matches!(fact,ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(p)) if p.left.ir()==left.ir()&&p.right.ir()==right.ir())
}
impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_antiderivative_calculus(
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
        let compose = match builtin.theorem {
            BuiltinTheoremId::AntiderivativeCompose => true,
            BuiltinTheoremId::AntiderivativeDifferenceConstant => false,
            _ => return Err(invalid("CalculusIdentity")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("CalculusArguments"));
        };
        if args.len() != builtin.theorem.arity() {
            return Err(invalid("CalculusArity"));
        }
        let region = if compose {
            args[6].clone()
        } else {
            open_interval(args[3].clone(), args[4].clone())
        };
        let width = context_count(&region)?;
        let first = if compose {
            context_count(&args[7])?
        } else {
            width
        };
        let base = if compose {
            first + 2 * width
        } else {
            2 + 2 * width
        };
        let count = base + if compose { 4 } else { 2 };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || !matches!(&call.name,AtomicName::Plain{name} if name==builtin.theorem.as_str())
            || args != &builtin.arguments
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("CalculusOriginalStages"));
        }
        let req = &builtin.requirements;
        let contexts = if compose {
            vec![
                (
                    vec![args[0].clone(), args[1].clone(), args[7].clone()],
                    0,
                    first,
                ),
                (
                    vec![args[2].clone(), args[3].clone(), region.clone()],
                    first,
                    width,
                ),
                (
                    vec![args[4].clone(), args[5].clone(), region.clone()],
                    first + width,
                    width,
                ),
            ]
        } else {
            if !matches!(&req[0],Fact::AtomicFact(AtomicFact::LessFact(p)) if p.left.ir()==args[3].ir()&&p.right.ir()==args[4].ir())
                || !matches!(&req[1],Fact::AtomicFact(AtomicFact::InFact(p)) if p.element.ir()==args[5].ir()&&p.set.ir()==region.ir())
            {
                return Err(invalid("CalculusOriginalOrderAndBasePoint"));
            }
            vec![
                (
                    vec![args[0].clone(), args[2].clone(), region.clone()],
                    2,
                    width,
                ),
                (
                    vec![args[1].clone(), args[2].clone(), region.clone()],
                    2 + width,
                    width,
                ),
            ]
        };
        for (a, start, n) in &contexts {
            validate_context(a, &req[*start..start + n].iter().collect::<Vec<_>>())?;
        }
        if compose {
            candidate(&req[base], &[&args[0], &args[1], &args[7]])?;
            candidate(&builtin.conclusions[0], &[&args[4], &args[5], &region])?;
            let p = universal(&req[base + 1], &region, args, 1)?;
            let x = parameter(&p.typed_parameters, &region)?;
            let point = Obj::Identifier(IdentifierObj::from_bound_name(x));
            if !matches!(&p.then_facts[0],ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(p)) if call_matches(&p.element,&args[2],&point)&&p.set.ir()==args[7].ir())
            {
                return Err(invalid("CalculusOriginalFullImage"));
            }
            let p = universal(&req[base + 2], &region, args, 1)?;
            let x = parameter(&p.typed_parameters, &region)?;
            let point = Obj::Identifier(IdentifierObj::from_bound_name(x));
            if !matches!(&p.then_facts[0],ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::HasDerivativeAtFact(p)) if p.function.ir()==args[2].ir()&&p.point.ir()==point.ir()&&call_matches(&p.value,&args[3],&point))
            {
                return Err(invalid("CalculusOriginalInnerDerivative"));
            }
            let p = universal(&req[base + 3], &region, args, 2)?;
            let x = parameter(&p.typed_parameters, &region)?;
            let point = Obj::Identifier(IdentifierObj::from_bound_name(x));
            let inner = analysis_apply(args[2].clone(), point.clone());
            let primitive = analysis_apply(args[0].clone(), inner.clone());
            let product = crate::rational_expression::helper::mul_objs(
                analysis_apply(args[1].clone(), inner),
                analysis_apply(args[3].clone(), point.clone()),
            );
            if !equality(
                &p.then_facts[0],
                &analysis_apply(args[4].clone(), point.clone()),
                &primitive,
            ) || !equality(
                &p.then_facts[1],
                &analysis_apply(args[5].clone(), point),
                &product,
            ) {
                return Err(invalid("CalculusOriginalOrderedChainEquations"));
            }
        } else {
            candidate(&req[base], &[&args[0], &args[2], &region])?;
            candidate(&req[base + 1], &[&args[1], &args[2], &region])?;
            let p = universal(&builtin.conclusions[0], &region, args, 1)?;
            let x = parameter(&p.typed_parameters, &region)?;
            let point = Obj::Identifier(IdentifierObj::from_bound_name(x));
            let difference = |x: Obj| {
                crate::rational_expression::helper::sub_objs(
                    analysis_apply(args[0].clone(), x.clone()),
                    analysis_apply(args[1].clone(), x),
                )
            };
            if !equality(
                &p.then_facts[0],
                &difference(point),
                &difference(args[5].clone()),
            ) {
                return Err(invalid("CalculusOriginalDifferenceAndBasePoint"));
            }
        }
        let (definitions, refs) =
            self.compile_function_limit_requirements(req, dom_proofs, dom_stores, position)?;
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
        let mut terms = Vec::new();
        for (i, (a, start, n)) in contexts.iter().enumerate() {
            terms.push(self.antiderivative_context_function_terms(
                a,
                &req[*start..start + n].iter().collect::<Vec<_>>(),
                &refs[*start..start + n],
                0,
                &format!("calculus_{i}_"),
                &scope,
            )?);
        }
        let nested = |s: &str| s.replace('\n', "\n  ");
        let mut lines = vec![format!(
            "  have _calculus_first_real : Litex.RealFunctionValue M {} := {}",
            raw[0],
            nested(&terms[0].0)
        )];
        if compose {
            let interior = match &region {
                Obj::StandardSet(StandardSet::R) => "Litex.realLineRegionInterior (M := M)".into(),
                Obj::SetFormer(SetFormer::IntervalObj(IntervalObj::LeftOpenRightOpen(p))) => {
                    format!(
                        "Litex.realOpenIntervalRegionInterior {} {}",
                        self.compile_function_raw_expression_bound(
                            &p.start,
                            &scope,
                            &HashMap::new()
                        )?,
                        self.compile_function_raw_expression_bound(
                            &p.end,
                            &scope,
                            &HashMap::new()
                        )?
                    )
                }
                _ => return Err(invalid("CalculusOriginalOpenRegion")),
            };
            lines.push(format!(
                "  have _calculus_inner_real : Litex.RealFunctionValue M {} := {}",
                raw[2],
                nested(&terms[1].0)
            ));
            lines.push(format!("  have _calculus_target_cover : ∀ x, M.mem x {} → M.mem x (Litex.FunctionSemantics.domainValue {}) := {}",raw[6],raw[4],nested(&terms[2].1)));
            lines.push(format!(
                "  have _calculus_interior : Litex.RealRegionInteriorValue M {} := {interior}",
                raw[6]
            ));
            lines.push(format!("  have _calculus_image : ∀ x, M.mem x {} → M.mem (Litex.FunctionSemantics.callValue {} x) {} := by\n    intro x hx\n    exact {} (Litex.semanticObject x (M.member_isSet hx)) hx",raw[6],raw[2],raw[7],refs[base+1]));
            lines.push(format!("  have _calculus_derivative : ∀ x, M.mem x {} → Litex.HasDerivativeAtValue M {} x (Litex.FunctionSemantics.callValue {} x) := by\n    intro x hx\n    exact {} (Litex.semanticObject x (M.member_isSet hx)) hx",raw[6],raw[2],raw[3],refs[base+2]));
            lines.push(format!("  have _calculus_equations : ∀ x, M.mem x {} → Litex.FunctionSemantics.callValue {} x = Litex.FunctionSemantics.callValue {} (Litex.FunctionSemantics.callValue {} x) ∧ Litex.FunctionSemantics.callValue {} x = M.mulValue (Litex.FunctionSemantics.callValue {} (Litex.FunctionSemantics.callValue {} x)) (Litex.FunctionSemantics.callValue {} x) := by\n    intro x hx\n    exact {} (Litex.semanticObject x (M.member_isSet hx)) hx",raw[6],raw[4],raw[0],raw[2],raw[5],raw[1],raw[2],raw[3],refs[base+3]));
            lines.push(format!("  exact Litex.antiderivativeComposeFunctions {} _calculus_first_real _calculus_inner_real _calculus_interior _calculus_target_cover {} _calculus_image _calculus_derivative _calculus_equations",raw.join(" "),refs[base]));
        } else {
            let raw_region =
                self.compile_function_raw_expression_bound(&region, &scope, &HashMap::new())?;
            lines.push(format!(
                "  have _calculus_second_real : Litex.RealFunctionValue M {} := {}",
                raw[1],
                nested(&terms[1].0)
            ));
            lines.push(format!("  have _calculus_first_cover : ∀ x, M.mem x {raw_region} → M.mem x (Litex.FunctionSemantics.domainValue {}) := {}",raw[0],nested(&terms[0].1)));
            lines.push(format!("  have _calculus_second_cover : ∀ x, M.mem x {raw_region} → M.mem x (Litex.FunctionSemantics.domainValue {}) := {}",raw[1],nested(&terms[1].1)));
            lines.push("  intro _PointHost _PointRep point h_point".into());
            lines.push(format!("  exact Litex.antiderivativeDifferenceConstantInterval {} _calculus_first_real _calculus_second_real {} {} _calculus_first_cover _calculus_second_cover {} {} {} (Litex.denote point) h_point",raw.join(" "),refs[3],refs[4],refs[1],refs[base],refs[base+1]));
        }
        let statement = self.compile_formed_fact_proposition(
            &conclusions_wd[0],
            &builtin.conclusions[0],
            &formed,
        )?;
        Ok((
            definitions,
            format!("(show {statement} from (by\n{}\n))", lines.join("\n")),
            builtin.conclusions.clone(),
        ))
    }
}
