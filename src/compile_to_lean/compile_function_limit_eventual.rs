//! Eventual positivity/nonzero conclusions consume the recorded limit condition.
use super::compile_function_limit::{finite_side, infinite_direction};
use super::compile_function_limit_definition::{approach_conditions, signature_domain_matches};
use super::compile_function_limit_unary::real_limit_signature;
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::helper::{is_zero, source_order_oriented};
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::prelude::*;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("EventualFunctionLimit/{stage}"))
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_function_limit_eventual(
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
        let (positive, finite) = match builtin.theorem {
            FnLimitAtEventuallyPositive
            | FnLimitLeftEventuallyPositive
            | FnLimitRightEventuallyPositive => (true, true),
            FnLimitAtEventuallyNonzero
            | FnLimitLeftEventuallyNonzero
            | FnLimitRightEventuallyNonzero => (false, true),
            FnLimitPosInfEventuallyPositive | FnLimitNegInfEventuallyPositive => (true, false),
            FnLimitPosInfEventuallyNonzero | FnLimitNegInfEventuallyNonzero => (false, false),
            _ => return Err(invalid("Id")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        let base = 3 + usize::from(finite);
        let count = base + 2;
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || !matches!(&call.name, AtomicName::Plain { name } if name == builtin.theorem.as_str())
            || args != &builtin.arguments
            || args.len() != base - 1
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("Stages"));
        }
        let approach = match builtin.theorem {
            FnLimitAtEventuallyPositive | FnLimitAtEventuallyNonzero => {
                LimitApproach::AtPoint(args[1].clone().into())
            }
            FnLimitLeftEventuallyPositive | FnLimitLeftEventuallyNonzero => {
                LimitApproach::FromLeft(args[1].clone().into())
            }
            FnLimitRightEventuallyPositive | FnLimitRightEventuallyNonzero => {
                LimitApproach::FromRight(args[1].clone().into())
            }
            FnLimitPosInfEventuallyPositive | FnLimitPosInfEventuallyNonzero => {
                LimitApproach::AtPositiveInfinity
            }
            FnLimitNegInfEventuallyPositive | FnLimitNegInfEventuallyNonzero => {
                LimitApproach::AtNegativeInfinity
            }
            _ => return Err(invalid("Approach")),
        };
        let req = &builtin.requirements;
        let (signature, _) = real_limit_signature(&req[..3], &args[0])?;
        if finite
            && !matches!(&req[3], Fact::AtomicFact(AtomicFact::InFact(f))
            if f.element.ir() == args[1].ir() && f.set == Obj::StandardSet(StandardSet::R))
        {
            return Err(invalid("Point"));
        }
        let value = &args[base - 2];
        if !matches!(&req[base], Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(f))
            if f.function.ir() == args[0].ir() && f.approach == approach && f.value.ir() == value.ir())
        {
            return Err(invalid("Candidate"));
        }
        if positive {
            let Fact::AtomicFact(condition) = &req[base + 1] else {
                return Err(invalid("PositiveCondition"));
            };
            let (zero, subject, strict) = source_order_oriented(condition)?;
            if !strict || !is_zero(zero) || subject.ir() != value.ir() {
                return Err(invalid("PositiveSubject"));
            }
        } else if !matches!(&req[base+1], Fact::AtomicFact(AtomicFact::NotEqualFact(f))
            if f.left.ir() == value.ir() && is_zero(&f.right))
        {
            return Err(invalid("NonzeroSubject"));
        }
        let goal = &builtin.conclusions[0];
        let Fact::ExistFact(exists) = goal else {
            return Err(invalid("Threshold"));
        };
        let threshold_set = Obj::StandardSet(if finite {
            StandardSet::RPos
        } else {
            StandardSet::R
        });
        let threshold = parameter(&exists.typed_parameters, &threshold_set)?;
        let [QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(subset))] =
            exists.facts.as_slice()
        else {
            return Err(invalid("LocalInclusion"));
        };
        let Obj::SetFormer(SetFormer::SetBuilder(neighborhood)) = &subset.left else {
            return Err(invalid("Neighborhood"));
        };
        let domain = neighborhood.param_set.as_ref();
        if !signature_domain_matches(domain, signature)
            || args.iter().chain([domain]).any(|a| {
                contains_parameter(a, threshold.id)
                    || contains_parameter(a, neighborhood.param_binding.id)
            })
            || threshold.id == neighborhood.param_binding.id
        {
            return Err(invalid("DomainOrBinders"));
        }
        approach_conditions(
            &neighborhood.facts,
            &approach,
            &Obj::Identifier(IdentifierObj::from_bound_name(&neighborhood.param_binding)),
            &Obj::Identifier(IdentifierObj::from_bound_name(threshold)),
        )?;
        let Obj::FunctionSpace(FunctionSpace::PreimageSet(preimage)) = &subset.right else {
            return Err(invalid("Preimage"));
        };
        let target = Obj::StandardSet(if positive {
            StandardSet::RPos
        } else {
            StandardSet::RStar
        });
        if preimage.function.ir() != args[0].ir() || preimage.target_set.as_ref() != &target {
            return Err(invalid("Target"));
        }
        let (definitions, refs) =
            self.compile_function_limit_requirements(req, dom_proofs, dom_stores, position)?;
        let formed = SourcePosition {
            before: count,
            ..*position
        };
        let wd = &conclusions_wd[0];
        self.compile_fact_wd(wd, goal, &formed)?;
        let scope = SourcePosition::new(Some(&formed), SourceOwner::FactWD(wd), usize::MAX);
        let statement = self.compile_formed_fact_proposition(wd, goal, &formed)?;
        let mut steps = self.compile_function_limit_context(
            0,
            &args[0],
            domain,
            &req[..3],
            &refs[..3],
            &scope,
        )?;
        let function = self.compile_object_reference(&args[0], &scope)?;
        let value = self.compile_object_reference(value, &scope)?;
        let domain = "_law0_domain";
        let (prefix, arguments) = if finite {
            let (side, point) = finite_side(&approach)?;
            (
                "finite",
                format!(
                    ".{side} {function} {} {value} {domain}",
                    self.compile_object_reference(point, &scope)?
                ),
            )
        } else {
            (
                "infinite",
                format!(
                    ".{} {function} {value} {domain}",
                    infinite_direction(&approach)?
                ),
            )
        };
        steps.push(format!("obtain ⟨_threshold, _threshold_member, _control⟩ := Litex.{prefix}FunctionLimitEventually{} {arguments} _law_real_0 _law_domain_0 {} {}",if positive {"Positive"} else {"Nonzero"},refs[base],refs[base+1]));
        steps.push("refine ⟨_threshold, _threshold_member, ?_⟩".into());
        steps.push("exact _control".into());
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
