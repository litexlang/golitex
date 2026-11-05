//! Native antiderivative algebra uses the supplied functions and local equations.
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
use crate::prelude::*;
use std::collections::HashMap;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Action {
    Shift,
    Add,
    Scale,
}
fn candidate(fact: &Fact, expected: &[&Obj]) -> Result<(), LeanCompileError> {
    let Fact::AtomicFact(fact) = fact else {
        return Err(invalid("AlgebraPositiveCandidate"));
    };
    let Some((args, false)) = parts(fact) else {
        return Err(invalid("AlgebraPositiveCandidate"));
    };
    if args.len() != 3 || !args.iter().zip(expected).all(|(a, b)| a.ir() == b.ir()) {
        return Err(invalid("AlgebraCandidateArguments"));
    }
    Ok(())
}
fn equation(
    fact: &ExistOrAndChainAtomicFact,
    target: &Obj,
    left: &Obj,
    right: &Obj,
    input: &Obj,
    multiply: bool,
) -> bool {
    let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(p)) = fact else {
        return false;
    };
    if !call_matches(&p.left, target, input) {
        return false;
    }
    match (&p.right, multiply) {
        (Obj::ArithmeticOperator(ArithmeticOperator::Add(p)), false) => {
            p.left.ir() == left.ir() && p.right.ir() == right.ir()
        }
        (Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)), true) => {
            p.left.ir() == left.ir() && p.right.ir() == right.ir()
        }
        _ => false,
    }
}
fn validate_equations(
    action: Action,
    args: &[Obj],
    region: &Obj,
    fact: &Fact,
) -> Result<(), LeanCompileError> {
    let Fact::ForallFact(p) = fact else {
        return Err(invalid("AlgebraPointwiseUniversal"));
    };
    let x = parameter(&p.typed_parameters, region)?;
    if !p.dom_facts.is_empty()
        || args.iter().any(|a| contains_parameter(a, x.id))
        || p.then_facts.len() != if action == Action::Shift { 1 } else { 2 }
    {
        return Err(invalid("AlgebraPointwiseScope"));
    }
    let input = Obj::Identifier(IdentifierObj::from_bound_name(x));
    let call = |f: &Obj| {
        crate::execute::execute_fact_stmt::real_analysis::analysis_apply(f.clone(), input.clone())
    };
    let valid = match action {
        Action::Shift => equation(
            &p.then_facts[0],
            &args[2],
            &call(&args[0]),
            &args[4],
            &input,
            false,
        ),
        Action::Add => {
            equation(
                &p.then_facts[0],
                &args[4],
                &call(&args[0]),
                &call(&args[2]),
                &input,
                false,
            ) && equation(
                &p.then_facts[1],
                &args[5],
                &call(&args[1]),
                &call(&args[3]),
                &input,
                false,
            )
        }
        Action::Scale => {
            equation(
                &p.then_facts[0],
                &args[2],
                &args[5],
                &call(&args[0]),
                &input,
                true,
            ) && equation(
                &p.then_facts[1],
                &args[3],
                &args[5],
                &call(&args[1]),
                &input,
                true,
            )
        }
    };
    if valid {
        Ok(())
    } else {
        Err(invalid("AlgebraOriginalEquations"))
    }
}
impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_antiderivative_algebra(
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
        let (action, arity, region_index) = match builtin.theorem {
            BuiltinTheoremId::AntiderivativeShift => (Action::Shift, 5, 3),
            BuiltinTheoremId::AntiderivativeAdd => (Action::Add, 7, 6),
            BuiltinTheoremId::AntiderivativeScale => (Action::Scale, 6, 4),
            _ => return Err(invalid("AlgebraIdentity")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("AlgebraArguments"));
        };
        if args.len() != arity {
            return Err(invalid("AlgebraArity"));
        }
        let region = &args[region_index];
        let context = context_count(region)?;
        let count = context + 3;
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
            return Err(invalid("AlgebraOriginalStages"));
        }
        let req = &builtin.requirements;
        let first_args = vec![args[0].clone(), args[1].clone(), region.clone()];
        validate_context(&first_args, &req[..context].iter().collect::<Vec<_>>())?;
        candidate(&req[context], &[&args[0], &args[1], region])?;
        if action == Action::Add {
            candidate(&req[context + 1], &[&args[2], &args[3], region])?;
        } else {
            let constant = &args[if action == Action::Shift { 4 } else { 5 }];
            if !matches!(&req[context+1],Fact::AtomicFact(AtomicFact::InFact(p)) if p.element.ir()==constant.ir() && p.set==Obj::StandardSet(StandardSet::R))
            {
                return Err(invalid("AlgebraRealConstant"));
            }
        }
        validate_equations(action, args, region, &req[context + 2])?;
        let (target, value) = match action {
            Action::Shift => (2, 1),
            Action::Add => (4, 5),
            Action::Scale => (2, 3),
        };
        candidate(
            &builtin.conclusions[0],
            &[&args[target], &args[value], region],
        )?;
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
        let raw_region = &raw[region_index];
        let (real_first, _) = self.antiderivative_context_function_terms(
            &first_args,
            &req[..context].iter().collect::<Vec<_>>(),
            &refs[..context],
            0,
            "anti_first_",
            &scope,
        )?;
        let Fact::AtomicFact(goal) = &builtin.conclusions[0] else {
            return Err(invalid("AlgebraGoal"));
        };
        let FactWellDefinedProof::AtomicExceptEquality(goal_wd) = &conclusions_wd[0] else {
            return Err(invalid("AlgebraGoalFormation"));
        };
        let (_, cover) =
            self.antiderivative_function_from_formation(goal, goal_wd, 0, "anti_target_", &formed)?;
        let interior = match region {
            Obj::StandardSet(StandardSet::R) => "Litex.realLineRegionInterior (M := M)".into(),
            Obj::SetFormer(SetFormer::IntervalObj(IntervalObj::LeftOpenRightOpen(bounds))) => {
                format!(
                    "Litex.realOpenIntervalRegionInterior {} {}",
                    self.compile_function_raw_expression_bound(
                        &bounds.start,
                        &scope,
                        &HashMap::new()
                    )?,
                    self.compile_function_raw_expression_bound(
                        &bounds.end,
                        &scope,
                        &HashMap::new()
                    )?
                )
            }
            _ => return Err(invalid("AlgebraOriginalRegion")),
        };
        let nested = |s: &str| s.replace('\n', "\n  ");
        let mut lines=vec![format!("  have _anti_real_first : Litex.RealFunctionValue M {} := {}",raw[0],nested(&real_first)),format!("  have _anti_target_cover : ∀ x, M.mem x {raw_region} → M.mem x (Litex.FunctionSemantics.domainValue {}) := {}",raw[target],nested(&cover)),format!("  have _anti_interior : Litex.RealRegionInteriorValue M {raw_region} := {interior}")];
        if action == Action::Add {
            let VerifyFactResult::AtomicExceptEquality(p) = &dom_proofs[context + 1] else {
                return Err(invalid("AlgebraSecondCandidateProof"));
            };
            let VerifyAtomicExceptEqualityFactResult::Success(p) = p.as_ref() else {
                return Err(invalid("AlgebraSecondCandidateSuccess"));
            };
            let (real_second, _) = self.antiderivative_function_from_formation(
                &p.fact,
                &p.well_defined_proof,
                0,
                "anti_second_",
                &SourcePosition {
                    before: context + 1,
                    ..*position
                },
            )?;
            lines.push(format!(
                "  have _anti_real_second : Litex.RealFunctionValue M {} := {}",
                raw[2],
                nested(&real_second)
            ));
        }
        let formula = &refs[context + 2];
        for i in 0..if action == Action::Shift { 1 } else { 2 } {
            let (out,rhs)=match (action,i) {
                (Action::Shift,_)=>(&raw[2],format!("M.addValue (Litex.FunctionSemantics.callValue {} x) {}",raw[0],raw[4])),
                (Action::Add,0)=>(&raw[4],format!("M.addValue (Litex.FunctionSemantics.callValue {} x) (Litex.FunctionSemantics.callValue {} x)",raw[0],raw[2])),
                (Action::Add,_)=>(&raw[5],format!("M.addValue (Litex.FunctionSemantics.callValue {} x) (Litex.FunctionSemantics.callValue {} x)",raw[1],raw[3])),
                (Action::Scale,0)=>(&raw[2],format!("M.mulValue {} (Litex.FunctionSemantics.callValue {} x)",raw[5],raw[0])),
                (Action::Scale,_)=>(&raw[3],format!("M.mulValue {} (Litex.FunctionSemantics.callValue {} x)",raw[5],raw[1])),
            };
            let projection = if action == Action::Shift {
                String::new()
            } else {
                format!(".{}", i + 1)
            };
            lines.push(format!("  have _anti_equation_{i} : ∀ x, M.mem x {raw_region} → Litex.FunctionSemantics.callValue {out} x = {rhs} := by\n    intro x hx\n    exact ({formula} (Litex.semanticObject x (M.member_isSet hx)) hx){projection}"));
        }
        lines.push(match action {
            Action::Shift=>format!("  exact Litex.antiderivativeShiftFunction {} _anti_real_first _anti_interior _anti_target_cover {} {} _anti_equation_0",raw.join(" "),refs[context+1],refs[context]),
            Action::Add=>format!("  exact Litex.antiderivativeAddFunctions {} _anti_real_first _anti_real_second _anti_interior _anti_target_cover {} {} _anti_equation_0 _anti_equation_1",raw.join(" "),refs[context],refs[context+1]),
            Action::Scale=>format!("  exact Litex.antiderivativeScaleFunctions {} _anti_real_first _anti_interior _anti_target_cover {} {} _anti_equation_0 _anti_equation_1",raw.join(" "),refs[context+1],refs[context]),
        });
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
