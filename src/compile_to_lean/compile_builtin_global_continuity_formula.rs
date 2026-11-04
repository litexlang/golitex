//! Global formula continuity consumes its original complete domain and equation.
use super::compile_function_limit_definition::signature_domain_matches;
use super::compile_function_limit_unary::real_limit_signature;
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

pub(super) fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("GlobalContinuityFormula/{stage}"))
}

fn elementary_formula(theorem: BuiltinTheoremId, input: &Obj, base: Option<&Obj>) -> Option<Obj> {
    use BuiltinTheoremId::*;
    let arg = Box::new(input.clone());
    Some(match theorem {
        FnContinuousLn => Obj::ExpLogOperator(ExpLogOperator::Ln(Ln { arg })),
        FnContinuousLog => Obj::ExpLogOperator(ExpLogOperator::Log(Log {
            base: Box::new(base?.clone()),
            arg,
        })),
        FnContinuousSqrt => Obj::ExpLogOperator(ExpLogOperator::Sqrt(Sqrt { arg })),
        FnContinuousTan => Obj::TrigOperator(TrigOperator::Tan(Tan { arg })),
        FnContinuousCot => Obj::TrigOperator(TrigOperator::Cot(Cot { arg })),
        FnContinuousSec => Sec { arg }.into(),
        FnContinuousCsc => Csc { arg }.into(),
        FnContinuousCoth => Coth { arg }.into(),
        FnContinuousCsch => Csch { arg }.into(),
        FnContinuousExp => Obj::ExpLogOperator(ExpLogOperator::Exp(Exp { arg })),
        FnContinuousSin => Obj::TrigOperator(TrigOperator::Sin(Sin { arg })),
        FnContinuousCos => Obj::TrigOperator(TrigOperator::Cos(Cos { arg })),
        FnContinuousArcsin => Obj::TrigOperator(TrigOperator::Arcsin(Arcsin { arg })),
        FnContinuousArccos => Obj::TrigOperator(TrigOperator::Arccos(Arccos { arg })),
        FnContinuousArctan => Obj::TrigOperator(TrigOperator::Arctan(Arctan { arg })),
        FnContinuousArccot => Obj::TrigOperator(TrigOperator::Arccot(Arccot { arg })),
        FnContinuousSinh => Sinh { arg }.into(),
        FnContinuousCosh => Cosh { arg }.into(),
        FnContinuousTanh => Tanh { arg }.into(),
        FnContinuousSech => Sech { arg }.into(),
        _ => return None,
    })
}
impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_global_continuity_formula(
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
        let law = match builtin.theorem {
            FnContinuousConstant => "functionContinuousOfConstant",
            FnContinuousIdentity => "functionContinuousOfIdentity",
            FnContinuousLn => "functionContinuousOfLn",
            FnContinuousLog => "functionContinuousOfLog",
            FnContinuousSqrt => "functionContinuousOfSqrt",
            FnContinuousTan => "functionContinuousOfTan",
            FnContinuousCot => "functionContinuousOfCot",
            FnContinuousSec => "functionContinuousOfSec",
            FnContinuousCsc => "functionContinuousOfCsc",
            FnContinuousCoth => "functionContinuousOfCoth",
            FnContinuousCsch => "functionContinuousOfCsch",
            FnContinuousExp => "functionContinuousOfExp",
            FnContinuousSin => "functionContinuousOfSin",
            FnContinuousCos => "functionContinuousOfCos",
            FnContinuousArcsin => "functionContinuousOfArcsin",
            FnContinuousArccos => "functionContinuousOfArccos",
            FnContinuousArctan => "functionContinuousOfArctan",
            FnContinuousArccot => "functionContinuousOfArccot",
            FnContinuousSinh => "functionContinuousOfSinh",
            FnContinuousCosh => "functionContinuousOfCosh",
            FnContinuousTanh => "functionContinuousOfTanh",
            FnContinuousSech => "functionContinuousOfSech",
            _ => return Err(invalid("Identity")),
        };
        let constant = builtin.theorem == FnContinuousConstant;
        let logarithm = builtin.theorem == FnContinuousLog;
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        let count = if logarithm {
            6
        } else if constant {
            5
        } else {
            4
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
        if constant
            && !matches!(&req[3],Fact::AtomicFact(AtomicFact::InFact(m)) if m.element.ir()==args[1].ir()&&m.set==Obj::StandardSet(StandardSet::R))
        {
            return Err(invalid("OriginalConstantCarrier"));
        }
        if logarithm
            && (!matches!(&req[3],Fact::AtomicFact(AtomicFact::InFact(m)) if m.element.ir()==args[1].ir() && m.set==Obj::StandardSet(StandardSet::RPos))
                || !matches!(&req[4],Fact::AtomicFact(AtomicFact::NotEqualFact(n)) if n.left.ir()==args[1].ir() && super::helper::closed_integer(&n.right)==Some(1)))
        {
            return Err(invalid("OriginalLogBase"));
        }
        let Fact::ForallFact(all) = &req[count - 1] else {
            return Err(invalid("OriginalFormula"));
        };
        let [group] = all.typed_parameters.groups.as_slice() else {
            return Err(invalid("FormulaParameter"));
        };
        let ParamType::Obj(domain) = &group.param_type else {
            return Err(invalid("FormulaDomain"));
        };
        if !signature_domain_matches(domain, signature) {
            return Err(invalid("OriginalCompleteDomain"));
        }
        let x = parameter(&all.typed_parameters, domain)?;
        let input = Obj::Identifier(IdentifierObj::from_bound_name(x));
        let rhs = if constant {
            args[1].clone()
        } else if builtin.theorem == FnContinuousIdentity {
            input.clone()
        } else {
            elementary_formula(builtin.theorem, &input, args.get(1))
                .ok_or_else(|| invalid("ElementaryFormula"))?
        };
        if !all.dom_facts.is_empty()
            || args.iter().any(|a| contains_parameter(a, x.id))
            || contains_parameter(domain, x.id)
            || !matches!(all.then_facts.as_slice(),[ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(e))] if call_matches(&e.left,&args[0],&input)&&e.right.ir()==rhs.ir())
        {
            return Err(invalid("OriginalFormulaBody"));
        }
        let goal = &builtin.conclusions[0];
        if !matches!(goal,Fact::AtomicFact(AtomicFact::FunctionContinuousFact(f)) if f.function.ir()==args[0].ir()&&f.property==FunctionContinuityProperty::Continuous)
        {
            return Err(invalid("OriginalConclusion"));
        }
        let (definitions, refs) =
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
            &refs[..3],
            &scope,
        )?;
        let f = self.compile_object_reference(&args[0], &scope)?;
        let formula=format!("(by\n  intro _global_input _global_member\n  exact {} (Litex.objectAtLevel _global_input (M.member_isSet _global_member)) (show M.mem _global_input (Litex.denote _law0_domain) from _law_domain_0.symm ▸ _global_member)\n)",refs[count-1]);
        let restricted = matches!(
            builtin.theorem,
            FnContinuousLn
                | FnContinuousLog
                | FnContinuousTan
                | FnContinuousCot
                | FnContinuousSec
                | FnContinuousCsc
                | FnContinuousCoth
                | FnContinuousCsch
        );
        if restricted {
            let condition = self.compile_original_continuity_formula_condition(
                builtin.theorem,
                &dom_proofs[count - 1],
                &SourcePosition {
                    before: count - 1,
                    ..*position
                },
            )?;
            context.push(format!("let _original_continuity_condition := {condition}"));
        }
        let condition = format!("(by\n  intro _global_input _global_member\n  exact _original_continuity_condition (Litex.objectAtLevel _global_input (M.member_isSet _global_member)) (show M.mem _global_input (Litex.denote _law0_domain) from _law_domain_0.symm ▸ _global_member)\n)");
        let law = if logarithm {
            let base = self.compile_object_reference(&args[1], &scope)?;
            format!("exact Litex.{law} (Litex.denote {f}) (Litex.denote {base}) _law_real_0 {} {} {condition} {formula}",refs[3],refs[4])
        } else if restricted {
            format!("exact Litex.{law} (Litex.denote {f}) _law_real_0 {condition} {formula}")
        } else if constant {
            let c = self.compile_object_reference(&args[1], &scope)?;
            format!("exact Litex.functionContinuousOfConstant (Litex.denote {f}) (Litex.denote {c}) _law_real_0 {} {formula}",refs[3])
        } else {
            format!("exact Litex.{law} (Litex.denote {f}) _law_real_0 {formula}")
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
