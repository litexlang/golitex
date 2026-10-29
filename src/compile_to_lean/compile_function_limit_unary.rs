//! Replay unary limit algebra from captured complete domains and pointwise equations.
use super::compile_function_limit::{finite_side, infinite_direction};
use super::compile_function_limit_definition::signature_domain_matches;
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

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("UnaryFunctionLimit/{stage}"))
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
                if parameter.is_some_and(|a| p.left.ir() == a.ir()) =>
            {
                Some(&p.right)
            }
            (Self::Power, Obj::ArithmeticOperator(ArithmeticOperator::Pow(p)))
                if parameter.is_some_and(|a| p.exponent.ir() == a.ir()) =>
            {
                Some(&p.base)
            }
            _ => None,
        }
    }
}

pub(super) fn real_limit_signature<'a>(
    requirements: &'a [Fact],
    function: &Obj,
) -> Result<(&'a FnSet, &'a Obj), LeanCompileError> {
    let [Fact::AtomicFact(AtomicFact::InFact(member)), Fact::AtomicFact(AtomicFact::SubsetFact(input)), Fact::AtomicFact(AtomicFact::SubsetFact(output))] =
        requirements
    else {
        return Err(invalid("RealContext"));
    };
    let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &member.set else {
        return Err(invalid("Signature"));
    };
    let [group] = signature.set_bound_parameters.groups.as_slice() else {
        return Err(invalid("UnarySignature"));
    };
    if group.params.len() != 1
        || member.element.ir() != function.ir()
        || input.left.ir() != group.param_type.ir()
        || input.right != Obj::StandardSet(StandardSet::R)
        || output.left.ir() != signature.ret_set.ir()
        || output.right != Obj::StandardSet(StandardSet::R)
    {
        return Err(invalid("RealContextSubject"));
    }
    Ok((signature, &member.set))
}

impl LitexToLeanCompiler {
    pub(super) fn compile_function_limit_context(
        &self,
        index: usize,
        function: &Obj,
        domain: &Obj,
        requirements: &[Fact],
        references: &[String],
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let (source, signature) = real_limit_signature(requirements, function)?;
        if !signature_domain_matches(domain, source) {
            return Err(invalid("EffectiveDomain"));
        }
        let signature = format!(
            "({}).val",
            self.compile_object_reference(signature, position)?
        );
        let function_obj = function;
        let function = self.compile_object_reference(function_obj, position)?;
        let (view, equal) = self.compile_named_limit_domain_view(
            function_obj,
            domain,
            source,
            &signature,
            &references[0],
            &format!("law{index}_"),
            position,
        )?;
        let view = view
            .lines()
            .map(|line| line.strip_prefix("  ").unwrap_or(line))
            .collect::<Vec<_>>()
            .join("\n");
        Ok(vec![
            view,
            format!("have _law_real_{index} : Litex.RealFunctionValue M (Litex.denote {function}) := by\n  refine ⟨_law{index}_signature, _law{index}_member, ?_, {}⟩\n  intro x hx\n  exact {} x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1", references[2], references[1]),
            format!("have _law_domain_{index} : Litex.denote _law{index}_domain = Litex.FunctionSemantics.domainValue (Litex.denote {function}) := {equal}"),
        ])
    }

    pub(super) fn compile_builtin_function_limit_unary(
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
        let (rule, finite) = match builtin.theorem {
            FnLimitAtNeg | FnLimitLeftNeg | FnLimitRightNeg => (Unary::Neg, true),
            FnLimitPosInfNeg | FnLimitNegInfNeg => (Unary::Neg, false),
            FnLimitAtAbs | FnLimitLeftAbs | FnLimitRightAbs => (Unary::Abs, true),
            FnLimitPosInfAbs | FnLimitNegInfAbs => (Unary::Abs, false),
            FnLimitAtScale | FnLimitLeftScale | FnLimitRightScale => (Unary::Scale, true),
            FnLimitPosInfScale | FnLimitNegInfScale => (Unary::Scale, false),
            FnLimitAtPower | FnLimitLeftPower | FnLimitRightPower => (Unary::Power, true),
            FnLimitPosInfPower | FnLimitNegInfPower => (Unary::Power, false),
            _ => return Err(invalid("Id")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        let base = 3 + usize::from(finite);
        let has_parameter = matches!(rule, Unary::Scale | Unary::Power);
        let count = base + 6 + usize::from(has_parameter);
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || !matches!(&call.name, AtomicName::Plain { name } if name == builtin.theorem.as_str())
            || args != &builtin.arguments
            || args.len() != base + usize::from(has_parameter)
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("Stages"));
        }
        let approach = match builtin.theorem {
            FnLimitAtNeg | FnLimitAtAbs | FnLimitAtScale | FnLimitAtPower => {
                LimitApproach::AtPoint(args[2].clone().into())
            }
            FnLimitLeftNeg | FnLimitLeftAbs | FnLimitLeftScale | FnLimitLeftPower => {
                LimitApproach::FromLeft(args[2].clone().into())
            }
            FnLimitRightNeg | FnLimitRightAbs | FnLimitRightScale | FnLimitRightPower => {
                LimitApproach::FromRight(args[2].clone().into())
            }
            FnLimitPosInfNeg | FnLimitPosInfAbs | FnLimitPosInfScale | FnLimitPosInfPower => {
                LimitApproach::AtPositiveInfinity
            }
            FnLimitNegInfNeg | FnLimitNegInfAbs | FnLimitNegInfScale | FnLimitNegInfPower => {
                LimitApproach::AtNegativeInfinity
            }
            _ => return Err(invalid("Approach")),
        };
        let req = &builtin.requirements;
        let (first, _) = real_limit_signature(&req[..3], &args[0])?;
        let (second, _) = real_limit_signature(&req[base..base + 3], &args[1])?;
        if finite
            && !matches!(&req[3], Fact::AtomicFact(AtomicFact::InFact(f))
            if f.element.ir() == args[2].ir() && f.set == Obj::StandardSet(StandardSet::R))
        {
            return Err(invalid("RealPoint"));
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(domains)) = &req[base + 3] else {
            return Err(invalid("DomainEquality"));
        };
        if !signature_domain_matches(&domains.left, second)
            || !signature_domain_matches(&domains.right, first)
        {
            return Err(invalid("DomainEqualitySubject"));
        }
        let value = &args[base - 1];
        if !matches!(&req[base+4], Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(f))
            if f.function.ir() == args[0].ir() && f.approach == approach && f.value.ir() == value.ir())
        {
            return Err(invalid("Candidate"));
        }
        let operation_parameter = has_parameter.then(|| &args[base]);
        if let Some(parameter) = operation_parameter {
            let carrier = Obj::StandardSet(if matches!(rule, Unary::Power) {
                StandardSet::N
            } else {
                StandardSet::R
            });
            if !matches!(&req[base+5], Fact::AtomicFact(AtomicFact::InFact(f))
                if f.element.ir() == parameter.ir() && f.set == carrier)
            {
                return Err(invalid("OperationParameter"));
            }
        }
        let equation_index = base + 5 + usize::from(has_parameter);
        let Fact::ForallFact(equation) = &req[equation_index] else {
            return Err(invalid("PointwiseEquation"));
        };
        let input = parameter(&equation.typed_parameters, &domains.right)?;
        if !equation.dom_facts.is_empty()
            || args
                .iter()
                .chain([&domains.left, &domains.right])
                .any(|x| contains_parameter(x, input.id))
        {
            return Err(invalid("PointwiseBinder"));
        }
        let x = Obj::Identifier(IdentifierObj::from_bound_name(input));
        if !matches!(equation.then_facts.as_slice(), [ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(f))]
            if call_matches(&f.left, &args[1], &x) && rule.argument(&f.right, operation_parameter).is_some_and(|a| call_matches(a, &args[0], &x)))
        {
            return Err(invalid("PointwiseSubject"));
        }
        let Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(goal)) = &builtin.conclusions[0]
        else {
            return Err(invalid("Conclusion"));
        };
        if goal.function.ir() != args[1].ir()
            || goal.approach != approach
            || rule
                .argument(&goal.value, operation_parameter)
                .is_none_or(|a| a.ir() != value.ir())
        {
            return Err(invalid("ConclusionSubject"));
        }
        let (definitions, refs) =
            self.compile_function_limit_requirements(req, dom_proofs, dom_stores, position)?;
        let formed = SourcePosition {
            before: count,
            ..*position
        };
        let wd = &conclusions_wd[0];
        self.compile_fact_wd(wd, &builtin.conclusions[0], &formed)?;
        let scope = SourcePosition::new(Some(&formed), SourceOwner::FactWD(wd), usize::MAX);
        let statement =
            self.compile_formed_fact_proposition(wd, &builtin.conclusions[0], &formed)?;
        let mut steps = self.compile_function_limit_context(
            0,
            &args[0],
            &domains.right,
            &req[..3],
            &refs[..3],
            &scope,
        )?;
        steps.extend(self.compile_function_limit_context(
            1,
            &args[1],
            &domains.left,
            &req[base..base + 3],
            &refs[base..base + 3],
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
                let member = &refs[base + 5];
                if matches!(rule, Unary::Scale) {
                    steps.push(format!(
                        "let _law_parameter := Litex.NativeBridge.asReal {parameter} {member}"
                    ));
                    steps.push(format!("have _law_parameter_value : Litex.denote {parameter} = M.number (_law_parameter : ℂ) := Litex.NativeBridge.asReal_spec {parameter} {member}"));
                    (format!("(fun value => M.mulValue (Litex.denote {parameter}) value)"),
                        "(fun x : ℝ => _law_parameter*x)".into(),
                        "(by intro x; rw [_law_parameter_value, M.mul_numbers, Complex.ofReal_mul])".into(),
                        "(continuous_const.mul continuous_id)")
                } else {
                    steps.push(format!(
                        "let _law_parameter := Litex.NativeBridge.asNat {parameter} {member}"
                    ));
                    steps.push(format!("have _law_parameter_value : Litex.denote {parameter} = M.number (_law_parameter : ℂ) := Litex.NativeBridge.asNat_spec {parameter} {member}"));
                    (format!("(fun value => M.powValue value (Litex.denote {parameter}))"),
                        "(fun x : ℝ => x^_law_parameter)".into(),
                        "(by intro x; rw [_law_parameter_value, M.pow_numbers_nat, Complex.ofReal_pow])".into(),
                        "(continuous_id.pow _law_parameter)")
                }
            }
        };

        let hformula = format!("(by\n  intro input hinput\n  have _law_input : M.mem input (Litex.denote _law0_domain) := by\n    rw [_law_domain_0]\n    exact hinput\n  exact {} (Litex.semanticObject input (M.member_isSet _law_input)) _law_input\n)", refs[equation_index]);
        let arguments = if finite {
            let (side, point) = finite_side(&approach)?;
            format!(
                ".{side} {} {} {} {} {}",
                object(&args[0])?,
                object(&args[1])?,
                object(point)?,
                object(value)?,
                object(&goal.value)?
            )
        } else {
            format!(
                ".{} {} {} {} {}",
                infinite_direction(&approach)?,
                object(&args[0])?,
                object(&args[1])?,
                object(value)?,
                object(&goal.value)?
            )
        };
        steps.push(format!("exact Litex.{}FunctionLimitMap {arguments} _law_real_0 _law_real_1 (_law_domain_1.symm.trans ({}.trans _law_domain_0)) {raw_op} {native_op} {hop} rfl {hformula} {continuous} {}", if finite {"finite"} else {"infinite"}, refs[base+3], refs[base+4]));
        Ok((
            definitions,
            format!(
                "(show {statement} from (by\n  {}\n))",
                steps.join("\n").replace('\n', "\n  ")
            ),
            builtin.conclusions.clone(),
        ))
    }
}
