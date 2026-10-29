//! Additive and multiplicative limit laws retain all three complete domains.
use super::compile_function_limit::{finite_side, infinite_direction};
use super::compile_function_limit_definition::signature_domain_matches;
use super::compile_function_limit_unary::real_limit_signature;
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::compile_sequence_analysis::call_matches;
use super::helper::is_zero;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::prelude::*;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("BinaryFunctionLimit/{stage}"))
}

#[derive(Clone, Copy)]
enum Binary {
    Add,
    Subtract,
    Multiply,
    Divide,
}
impl Binary {
    fn arguments(self, object: &Obj) -> Option<(&Obj, &Obj)> {
        match (self, object) {
            (Self::Add, Obj::ArithmeticOperator(ArithmeticOperator::Add(p))) => {
                Some((&p.left, &p.right))
            }
            (Self::Subtract, Obj::ArithmeticOperator(ArithmeticOperator::Sub(p))) => {
                Some((&p.left, &p.right))
            }
            (Self::Multiply, Obj::ArithmeticOperator(ArithmeticOperator::Mul(p))) => {
                Some((&p.left, &p.right))
            }
            (Self::Divide, Obj::ArithmeticOperator(ArithmeticOperator::Div(p))) => {
                Some((&p.left, &p.right))
            }
            _ => None,
        }
    }
    fn lean(self) -> Option<(&'static str, &'static str, &'static str, &'static str)> {
        Some(match self {
            Self::Add => (
                "M.addValue",
                "(fun x y : ℝ => x+y)",
                "(by intro x y; rw [M.add_numbers, Complex.ofReal_add])",
                "(continuous_fst.add continuous_snd)",
            ),
            Self::Subtract => (
                "M.subValue",
                "(fun x y : ℝ => x-y)",
                "(by intro x y; rw [M.sub_numbers, Complex.ofReal_sub])",
                "(continuous_fst.sub continuous_snd)",
            ),
            Self::Multiply => (
                "M.mulValue",
                "(fun x y : ℝ => x*y)",
                "(by intro x y; rw [M.mul_numbers, Complex.ofReal_mul])",
                "(continuous_fst.mul continuous_snd)",
            ),
            Self::Divide => return None,
        })
    }
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_function_limit_binary(
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
            FnLimitAtAdd | FnLimitLeftAdd | FnLimitRightAdd => (Binary::Add, true),
            FnLimitAtSubtract | FnLimitLeftSubtract | FnLimitRightSubtract => {
                (Binary::Subtract, true)
            }
            FnLimitAtMultiply | FnLimitLeftMultiply | FnLimitRightMultiply => {
                (Binary::Multiply, true)
            }
            FnLimitPosInfAdd | FnLimitNegInfAdd => (Binary::Add, false),
            FnLimitPosInfSubtract | FnLimitNegInfSubtract => (Binary::Subtract, false),
            FnLimitPosInfMultiply | FnLimitNegInfMultiply => (Binary::Multiply, false),
            FnLimitAtDivide | FnLimitLeftDivide | FnLimitRightDivide => (Binary::Divide, true),
            FnLimitPosInfDivide | FnLimitNegInfDivide => (Binary::Divide, false),
            _ => return Err(invalid("Id")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        let base = 3 + usize::from(finite);
        let division = matches!(rule, Binary::Divide);
        let count = base + 11 + 2 * usize::from(division);
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || !matches!(&call.name, AtomicName::Plain { name } if name == builtin.theorem.as_str())
            || args != &builtin.arguments
            || args.len() != base + 2
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("Stages"));
        }
        let approach = match builtin.theorem {
            FnLimitAtAdd | FnLimitAtSubtract | FnLimitAtMultiply | FnLimitAtDivide => {
                LimitApproach::AtPoint(args[3].clone().into())
            }
            FnLimitLeftAdd | FnLimitLeftSubtract | FnLimitLeftMultiply | FnLimitLeftDivide => {
                LimitApproach::FromLeft(args[3].clone().into())
            }
            FnLimitRightAdd | FnLimitRightSubtract | FnLimitRightMultiply | FnLimitRightDivide => {
                LimitApproach::FromRight(args[3].clone().into())
            }
            FnLimitPosInfAdd
            | FnLimitPosInfSubtract
            | FnLimitPosInfMultiply
            | FnLimitPosInfDivide => LimitApproach::AtPositiveInfinity,
            FnLimitNegInfAdd
            | FnLimitNegInfSubtract
            | FnLimitNegInfMultiply
            | FnLimitNegInfDivide => LimitApproach::AtNegativeInfinity,
            _ => return Err(invalid("Approach")),
        };
        let req = &builtin.requirements;
        let (first, _) = real_limit_signature(&req[..3], &args[0])?;
        let (second, _) = real_limit_signature(&req[base..base + 3], &args[1])?;
        let (output, _) = real_limit_signature(&req[base + 4..base + 7], &args[2])?;
        if finite
            && !matches!(&req[3], Fact::AtomicFact(AtomicFact::InFact(f))
            if f.element.ir() == args[3].ir() && f.set == Obj::StandardSet(StandardSet::R))
        {
            return Err(invalid("RealPoint"));
        }
        let (
            Fact::AtomicFact(AtomicFact::EqualFact(other_domain)),
            Fact::AtomicFact(AtomicFact::EqualFact(output_domain)),
        ) = (&req[base + 3], &req[base + 7])
        else {
            return Err(invalid("DomainEqualities"));
        };
        if !signature_domain_matches(&other_domain.right, first)
            || !signature_domain_matches(&other_domain.left, second)
            || !signature_domain_matches(&output_domain.left, output)
            || output_domain.right.ir() != other_domain.right.ir()
        {
            return Err(invalid("DomainSubjects"));
        }
        for index in 0..2 {
            if !matches!(&req[base+8+index], Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(f))
                if f.function.ir() == args[index].ir() && f.approach == approach && f.value.ir() == args[base+index].ir())
            {
                return Err(invalid("Candidate"));
            }
        }
        if division {
            if !matches!(&req[base+10], Fact::AtomicFact(AtomicFact::NotEqualFact(f))
                if f.left.ir() == args[base+1].ir() && is_zero(&f.right))
            {
                return Err(invalid("NonzeroLimit"));
            }
            let Fact::ForallFact(all) = &req[base + 11] else {
                return Err(invalid("NonzeroDenominator"));
            };
            let input = parameter(&all.typed_parameters, &other_domain.right)?;
            let x = Obj::Identifier(IdentifierObj::from_bound_name(input));
            if !all.dom_facts.is_empty()
                || args
                    .iter()
                    .chain([&other_domain.right])
                    .any(|a| contains_parameter(a, input.id))
                || !matches!(all.then_facts.as_slice(), [ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::NotEqualFact(f))]
                    if call_matches(&f.left,&args[1],&x) && is_zero(&f.right))
            {
                return Err(invalid("NonzeroDenominatorSubject"));
            }
        }
        let equation_index = base + 10 + 2 * usize::from(division);
        let Fact::ForallFact(equation) = &req[equation_index] else {
            return Err(invalid("PointwiseEquation"));
        };
        let input = parameter(&equation.typed_parameters, &other_domain.right)?;
        if !equation.dom_facts.is_empty()
            || args
                .iter()
                .chain([&other_domain.left, &other_domain.right, &output_domain.left])
                .any(|x| contains_parameter(x, input.id))
        {
            return Err(invalid("PointwiseBinder"));
        }
        let x = Obj::Identifier(IdentifierObj::from_bound_name(input));
        if !matches!(equation.then_facts.as_slice(), [ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(f))]
            if call_matches(&f.left, &args[2], &x) && rule.arguments(&f.right).is_some_and(|(a,b)| call_matches(a,&args[0],&x) && call_matches(b,&args[1],&x)))
        {
            return Err(invalid("PointwiseSubject"));
        }
        let Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(goal)) = &builtin.conclusions[0]
        else {
            return Err(invalid("Conclusion"));
        };
        if goal.function.ir() != args[2].ir()
            || goal.approach != approach
            || rule
                .arguments(&goal.value)
                .is_none_or(|(a, b)| a.ir() != args[base].ir() || b.ir() != args[base + 1].ir())
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
            &other_domain.right,
            &req[..3],
            &refs[..3],
            &scope,
        )?;
        steps.extend(self.compile_function_limit_context(
            1,
            &args[1],
            &other_domain.left,
            &req[base..base + 3],
            &refs[base..base + 3],
            &scope,
        )?);
        steps.extend(self.compile_function_limit_context(
            2,
            &args[2],
            &output_domain.left,
            &req[base + 4..base + 7],
            &refs[base + 4..base + 7],
            &scope,
        )?);
        let object = |a: &Obj| {
            self.compile_object_reference(a, &scope)
                .map(|s| format!("(Litex.denote {s})"))
        };
        let hformula = format!("(by\n  intro input hinput\n  have _law_input : M.mem input (Litex.denote _law0_domain) := by\n    rw [_law_domain_0]\n    exact hinput\n  exact {} (Litex.semanticObject input (M.member_isSet _law_input)) _law_input\n)", refs[equation_index]);
        let objects = format!(
            "{} {} {}",
            object(&args[0])?,
            object(&args[1])?,
            object(&args[2])?
        );
        let arguments = if finite {
            let (side, point) = finite_side(&approach)?;
            format!(".{side} {objects} {}", object(point)?)
        } else {
            format!(".{} {objects}", infinite_direction(&approach)?)
        };
        if let Some((raw_op, native_op, hop, continuous)) = rule.lean() {
            steps.push(format!("exact Litex.{}FunctionLimitMapTwo {arguments} {} {} {} _law_real_0 _law_real_1 _law_real_2 (_law_domain_1.symm.trans ({}.trans _law_domain_0)) (_law_domain_2.symm.trans ({}.trans _law_domain_0)) {raw_op} {native_op} {hop} rfl {hformula} {continuous} {} {}",
            if finite {"finite"} else {"infinite"}, object(&args[base])?, object(&args[base+1])?, object(&goal.value)?, refs[base+3], refs[base+7], refs[base+8], refs[base+9]));
        } else {
            let hdenominator = format!("(by\n  intro input hinput\n  have _law_input : M.mem input (Litex.denote _law0_domain) := by\n    rw [_law_domain_0]\n    exact hinput\n  exact {} (Litex.semanticObject input (M.member_isSet _law_input)) _law_input\n)", refs[base+11]);
            steps.push(format!("exact Litex.{}FunctionLimitDivide {arguments} {} {} {} _law_real_0 _law_real_1 _law_real_2 (_law_domain_1.symm.trans ({}.trans _law_domain_0)) (_law_domain_2.symm.trans ({}.trans _law_domain_0)) rfl {} {hdenominator} {hformula} {} {}",
                if finite {"finite"} else {"infinite"}, object(&args[base])?, object(&args[base+1])?, object(&goal.value)?, refs[base+3], refs[base+7], refs[base+10], refs[base+8], refs[base+9]));
        }
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
