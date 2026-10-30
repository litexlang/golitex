//! Replay binary continuity formulas with both original domain inclusions.
use super::compile_function_continuity::continuity_side;
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

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_continuity_binary(
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
            FnContinuousAtAdd => (RealApproachSide::Both, Binary::Add),
            FnContinuousLeftAdd => (RealApproachSide::Left, Binary::Add),
            FnContinuousRightAdd => (RealApproachSide::Right, Binary::Add),
            FnContinuousAtSubtract => (RealApproachSide::Both, Binary::Subtract),
            FnContinuousLeftSubtract => (RealApproachSide::Left, Binary::Subtract),
            FnContinuousRightSubtract => (RealApproachSide::Right, Binary::Subtract),
            FnContinuousAtMultiply => (RealApproachSide::Both, Binary::Multiply),
            FnContinuousLeftMultiply => (RealApproachSide::Left, Binary::Multiply),
            FnContinuousRightMultiply => (RealApproachSide::Right, Binary::Multiply),
            FnContinuousAtDivide => (RealApproachSide::Both, Binary::Divide),
            FnContinuousLeftDivide => (RealApproachSide::Left, Binary::Divide),
            FnContinuousRightDivide => (RealApproachSide::Right, Binary::Divide),
            _ => return Err(invalid("Id")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        let division = matches!(rule, Binary::Divide);
        let count = 16 + usize::from(division);
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || !matches!(&call.name,AtomicName::Plain{name} if name==builtin.theorem.as_str())
            || args != &builtin.arguments
            || args.len() != 4
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("Stages"));
        }
        let req = &builtin.requirements;
        let (first, _) = real_limit_signature(&req[..3], &args[0])?;
        let (output, _) = real_limit_signature(&req[4..7], &args[2])?;
        let (second, _) = real_limit_signature(&req[10..13], &args[1])?;
        let (
            Fact::AtomicFact(AtomicFact::SubsetFact(left)),
            Fact::AtomicFact(AtomicFact::SubsetFact(right)),
        ) = (&req[7], &req[13])
        else {
            return Err(invalid("DomainInclusions"));
        };
        if !signature_domain_matches(&left.left, output)
            || !signature_domain_matches(&left.right, first)
            || right.left.ir() != left.left.ir()
            || !signature_domain_matches(&right.right, second)
        {
            return Err(invalid("DomainSubjects"));
        }
        for (index, domain) in [(3, &left.right), (8, &left.left)] {
            if !matches!(&req[index],Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==args[3].ir()&&f.set.ir()==domain.ir())
            {
                return Err(invalid("PointDomain"));
            }
        }
        for (index, function) in [(9, &args[0]), (14, &args[1])] {
            if !matches!(&req[index],Fact::AtomicFact(AtomicFact::FunctionContinuousAtFact(f)) if f.side==side&&f.function.ir()==function.ir()&&f.point.ir()==args[3].ir())
            {
                return Err(invalid("SourceContinuity"));
            }
        }
        if division
            && !matches!(&req[15],Fact::AtomicFact(AtomicFact::NotEqualFact(f)) if call_matches(&f.left,&args[1],&args[3])&&is_zero(&f.right))
        {
            return Err(invalid("PointNonzero"));
        }
        let formula_index = count - 1;
        let Fact::ForallFact(all) = &req[formula_index] else {
            return Err(invalid("Formula"));
        };
        let x = parameter(&all.typed_parameters, &left.left)?;
        let value = Obj::Identifier(IdentifierObj::from_bound_name(x));
        if !all.dom_facts.is_empty()
            || args
                .iter()
                .chain([&left.left, &left.right, &right.right])
                .any(|a| contains_parameter(a, x.id))
            || !matches!(all.then_facts.as_slice(),[ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq))]
                if call_matches(&eq.left,&args[2],&value)&&rule.arguments(&eq.right).is_some_and(|(a,b)|call_matches(a,&args[0],&value)&&call_matches(b,&args[1],&value)))
        {
            return Err(invalid("FormulaSubject"));
        }
        let goal = &builtin.conclusions[0];
        if !matches!(goal,Fact::AtomicFact(AtomicFact::FunctionContinuousAtFact(f)) if f.side==side&&f.function.ir()==args[2].ir()&&f.point.ir()==args[3].ir())
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
            &left.right,
            &req[..3],
            &refs[..3],
            &scope,
        )?;
        steps.extend(self.compile_function_limit_context(
            1,
            &args[2],
            &left.left,
            &req[4..7],
            &refs[4..7],
            &scope,
        )?);
        steps.extend(self.compile_function_limit_context(
            2,
            &args[1],
            &right.right,
            &req[10..13],
            &refs[10..13],
            &scope,
        )?);
        let object = |a: &Obj| {
            self.compile_object_reference(a, &scope)
                .map(|s| format!("(Litex.denote {s})"))
        };
        for (index, function, cite) in [(0, &args[0], &refs[7]), (2, &args[1], &refs[13])] {
            steps.push(format!("have _law_subset_{index} : ∀ input, M.mem input (Litex.FunctionSemantics.domainValue {}) → M.mem input (Litex.FunctionSemantics.domainValue {}) := by\n  intro input hinput\n  have _law_input : M.mem input (Litex.denote _law1_domain) := _law_domain_1.symm ▸ hinput\n  exact _law_domain_{index} ▸ ({cite} input _law_input)",object(&args[2])?,object(function)?));
        }
        let point_member = format!(
            "(show M.mem {} (Litex.FunctionSemantics.domainValue {}) from _law_domain_1 ▸ {})",
            object(&args[3])?,
            object(&args[2])?,
            refs[8]
        );
        let formula=format!("(by\n  intro input hinput\n  have _law_input : M.mem input (Litex.denote _law1_domain) := _law_domain_1.symm ▸ hinput\n  exact {} (Litex.semanticObject input (M.member_isSet _law_input)) _law_input\n)",refs[formula_index]);
        let side = continuity_side(side);
        let arguments=format!(".{side} {} {} {} {} _law_real_0 _law_real_2 _law_real_1 _law_subset_0 _law_subset_2 {point_member}",object(&args[0])?,object(&args[1])?,object(&args[2])?,object(&args[3])?);
        if let Some((raw, native, hop, continuous)) = rule.lean() {
            steps.push(format!("exact Litex.functionContinuousAtMapTwo {arguments} {raw} {native} {hop} {formula} {continuous} {} {}",refs[9],refs[14]));
        } else {
            steps.push(format!(
                "exact Litex.functionContinuousAtDivide {arguments} {formula} {} {} {}",
                refs[15], refs[9], refs[14]
            ));
        }
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
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("BinaryContinuity/{stage}"))
}
