//! Replay unary continuity formulas on their original output-domain subset.
use super::compile_function_continuity::continuity_side;
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

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_continuity_unary(
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
        let (side, rule) = match builtin.theorem {
            FnContinuousAtNeg => (RealApproachSide::Both, Unary::Neg),
            FnContinuousLeftNeg => (RealApproachSide::Left, Unary::Neg),
            FnContinuousRightNeg => (RealApproachSide::Right, Unary::Neg),
            FnContinuousAtAbs => (RealApproachSide::Both, Unary::Abs),
            FnContinuousLeftAbs => (RealApproachSide::Left, Unary::Abs),
            FnContinuousRightAbs => (RealApproachSide::Right, Unary::Abs),
            FnContinuousAtScale => (RealApproachSide::Both, Unary::Scale),
            FnContinuousLeftScale => (RealApproachSide::Left, Unary::Scale),
            FnContinuousRightScale => (RealApproachSide::Right, Unary::Scale),
            FnContinuousAtPower => (RealApproachSide::Both, Unary::Power),
            FnContinuousLeftPower => (RealApproachSide::Left, Unary::Power),
            FnContinuousRightPower => (RealApproachSide::Right, Unary::Power),
            _ => return Err(invalid("Id")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        let has_parameter = matches!(rule, Unary::Scale | Unary::Power);
        let count = 11 + usize::from(has_parameter);
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || !matches!(&call.name,AtomicName::Plain{name} if name==builtin.theorem.as_str())
            || args != &builtin.arguments
            || args.len() != 3 + usize::from(has_parameter)
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("Stages"));
        }
        let req = &builtin.requirements;
        let (input, _) = real_limit_signature(&req[..3], &args[0])?;
        let (output, _) = real_limit_signature(&req[4..7], &args[1])?;
        let Fact::AtomicFact(AtomicFact::SubsetFact(subset)) = &req[7] else {
            return Err(invalid("DomainSubset"));
        };
        if !signature_domain_matches(&subset.left, output)
            || !signature_domain_matches(&subset.right, input)
        {
            return Err(invalid("DomainSubsetSubject"));
        }
        for (index, domain) in [(3, &subset.right), (8, &subset.left)] {
            if !matches!(&req[index],Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==args[2].ir()&&f.set.ir()==domain.ir())
            {
                return Err(invalid("PointDomain"));
            }
        }
        if !matches!(&req[9],Fact::AtomicFact(AtomicFact::FunctionContinuousAtFact(f)) if f.side==side&&f.function.ir()==args[0].ir()&&f.point.ir()==args[2].ir())
        {
            return Err(invalid("SourceContinuity"));
        }
        let operation_parameter = has_parameter.then(|| &args[3]);
        if let Some(parameter) = operation_parameter {
            let carrier = Obj::StandardSet(if matches!(rule, Unary::Power) {
                StandardSet::N
            } else {
                StandardSet::R
            });
            if !matches!(&req[10],Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==parameter.ir()&&f.set==carrier)
            {
                return Err(invalid("OperationParameter"));
            }
        }
        let formula_index = count - 1;
        let Fact::ForallFact(all) = &req[formula_index] else {
            return Err(invalid("Formula"));
        };
        let x = parameter(&all.typed_parameters, &subset.left)?;
        let value = Obj::Identifier(IdentifierObj::from_bound_name(x));
        if !all.dom_facts.is_empty()
            || args
                .iter()
                .chain([&subset.left, &subset.right])
                .any(|a| contains_parameter(a, x.id))
            || !matches!(all.then_facts.as_slice(),[ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq))]
                if call_matches(&eq.left,&args[1],&value)&&rule.argument(&eq.right,operation_parameter).is_some_and(|a|call_matches(a,&args[0],&value)))
        {
            return Err(invalid("FormulaSubject"));
        }
        let goal = &builtin.conclusions[0];
        if !matches!(goal,Fact::AtomicFact(AtomicFact::FunctionContinuousAtFact(f)) if f.side==side&&f.function.ir()==args[1].ir()&&f.point.ir()==args[2].ir())
        {
            return Err(invalid("Conclusion"));
        }
        let (definitions, refs) =
            self.compile_function_limit_requirements(req, dom_proofs, dom_stores, position)?;
        let formed = SourcePosition {
            before: count,
            ..*position
        };
        let wd = &conclusions_wd[0];
        self.compile_fact_wd(wd, goal, &formed)?;
        let statement = self.compile_formed_fact_proposition(wd, goal, &formed)?;
        let scope = SourcePosition::new(Some(&formed), SourceOwner::FactWD(wd), usize::MAX);
        let mut steps = self.compile_function_limit_context(
            0,
            &args[0],
            &subset.right,
            &req[..3],
            &refs[..3],
            &scope,
        )?;
        steps.extend(self.compile_function_limit_context(
            1,
            &args[1],
            &subset.left,
            &req[4..7],
            &refs[4..7],
            &scope,
        )?);
        let object = |a: &Obj| {
            self.compile_object_reference(a, &scope)
                .map(|s| format!("(Litex.denote {s})"))
        };
        let (raw_op, native_op, hop, continuous): (String, String, String, &str) = match rule {
            Unary::Neg => (
                "M.negValue".into(),
                "(fun x : ℝ => -x)".into(),
                "(by intro x; rw [M.neg_numbers, Complex.ofReal_neg])".into(),
                "continuous_neg",
            ),
            Unary::Abs => (
                "(Litex.absValue (M := M))".into(),
                "(fun x : ℝ => |x|)".into(),
                "Litex.absValue_number".into(),
                "continuous_abs",
            ),
            Unary::Scale | Unary::Power => {
                let parameter = self.compile_object_reference(
                    operation_parameter.expect("validated parameter"),
                    &scope,
                )?;
                let member = &refs[10];
                if matches!(rule, Unary::Scale) {
                    steps.push(format!(
                        "let _law_parameter := Litex.NativeBridge.asReal {parameter} {member}"
                    ));
                    steps.push(format!("have _law_parameter_value : Litex.denote {parameter} = M.number (_law_parameter : ℂ) := Litex.NativeBridge.asReal_spec {parameter} {member}"));
                    (format!("(fun value => M.mulValue (Litex.denote {parameter}) value)"),"(fun x : ℝ => _law_parameter*x)".into(),"(by intro x; rw [_law_parameter_value, M.mul_numbers, Complex.ofReal_mul])".into(),"(continuous_const.mul continuous_id)")
                } else {
                    steps.push(format!(
                        "let _law_parameter := Litex.NativeBridge.asNat {parameter} {member}"
                    ));
                    steps.push(format!("have _law_parameter_value : Litex.denote {parameter} = M.number (_law_parameter : ℂ) := Litex.NativeBridge.asNat_spec {parameter} {member}"));
                    (format!("(fun value => M.powValue value (Litex.denote {parameter}))"),"(fun x : ℝ => x^_law_parameter)".into(),"(by intro x; rw [_law_parameter_value, M.pow_numbers_nat, Complex.ofReal_pow])".into(),"(continuous_id.pow _law_parameter)")
                }
            }
        };
        steps.push(format!("have _law_subset : ∀ input, M.mem input (Litex.FunctionSemantics.domainValue {}) → M.mem input (Litex.FunctionSemantics.domainValue {}) := by\n  intro input hinput\n  have _law_input : M.mem input (Litex.denote _law1_domain) := _law_domain_1.symm ▸ hinput\n  exact _law_domain_0 ▸ ({} input _law_input)",object(&args[1])?,object(&args[0])?,refs[7]));
        let point_member = format!(
            "(show M.mem {} (Litex.FunctionSemantics.domainValue {}) from _law_domain_1 ▸ {})",
            object(&args[2])?,
            object(&args[1])?,
            refs[8]
        );
        let formula=format!("(by\n  intro input hinput\n  have _law_input : M.mem input (Litex.denote _law1_domain) := _law_domain_1.symm ▸ hinput\n  exact {} (Litex.semanticObject input (M.member_isSet _law_input)) _law_input\n)",refs[formula_index]);
        let side = continuity_side(side);
        steps.push(format!("exact Litex.functionContinuousAtMap .{side} {} {} {} _law_real_0 _law_real_1 _law_subset {point_member} {raw_op} {native_op} {hop} {formula} {continuous} {}",object(&args[0])?,object(&args[1])?,object(&args[2])?,refs[9]));
        Ok((
            definitions,
            format!(
                "(show {statement} from by\n  {}\n)",
                steps.join("\n").replace('\n', "\n  ")
            ),
            builtin.conclusions.clone(),
        ))
    }
}
#[derive(Clone, Copy)]
enum Unary {
    Neg,
    Abs,
    Scale,
    Power,
}
impl Unary {
    fn argument<'a>(self, object: &'a Obj, parameter: Option<&Obj>) -> Option<&'a Obj> {
        match (self, object) {
            (Self::Neg, Obj::ArithmeticOperator(ArithmeticOperator::Neg(p))) => Some(&p.arg),
            (Self::Abs, Obj::ArithmeticOperator(ArithmeticOperator::Abs(p))) => Some(&p.arg),
            (Self::Scale, Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)))
                if parameter.is_some_and(|v| p.left.ir() == v.ir()) =>
            {
                Some(&p.right)
            }
            (Self::Power, Obj::ArithmeticOperator(ArithmeticOperator::Pow(p)))
                if parameter.is_some_and(|v| p.exponent.ir() == v.ir()) =>
            {
                Some(&p.base)
            }
            _ => None,
        }
    }
}
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("UnaryContinuity/{stage}"))
}
