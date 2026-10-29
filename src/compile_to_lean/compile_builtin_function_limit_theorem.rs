//! Explicit function-limit invocations retain their native schema and premises.
use super::compile_function_limit_constant::ElementaryLimit;
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::prelude::*;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("FunctionLimitTheorem/{stage}"))
}

#[derive(Clone, Copy)]
enum Rule {
    Unique,
    Exists,
    Selected,
    Constant,
    Identity,
    FromEpsilon,
    Accumulation,
    Control,
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_function_limit_theorem(
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
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        if matches!(
            builtin.theorem,
            FnLimitAtRealAccumulation
                | FnLimitLeftRealAccumulation
                | FnLimitRightRealAccumulation
                | FnLimitPosInfRealAccumulation
                | FnLimitNegInfRealAccumulation
        ) {
            if !matches!(derivation, TheoremDerivationProof::NativeSchema)
                || !type_proofs.is_empty()
                || !type_stores.is_empty()
                || function_domain.is_some()
                || !matches!(&call.name, AtomicName::Plain { name } if name == builtin.theorem.as_str())
                || args != &builtin.arguments
            {
                return Err(invalid("RealAccumulationStages"));
            }
            return self.compile_real_limit_accumulation(
                builtin,
                dom_proofs,
                dom_stores,
                conclusions_wd,
                position,
            );
        }
        let rule = match builtin.theorem {
            FnLimitAtUnique | FnLimitLeftUnique | FnLimitRightUnique | FnLimitPosInfUnique
            | FnLimitNegInfUnique => Rule::Unique,
            FnLimitAtExists | FnLimitLeftExists | FnLimitRightExists | FnLimitPosInfExists
            | FnLimitNegInfExists => Rule::Exists,
            FnLimitAtSelected
            | FnLimitLeftSelected
            | FnLimitRightSelected
            | FnLimitPosInfSelected
            | FnLimitNegInfSelected => Rule::Selected,
            FnLimitAtConstant
            | FnLimitLeftConstant
            | FnLimitRightConstant
            | FnLimitPosInfConstant
            | FnLimitNegInfConstant => Rule::Constant,
            FnLimitAtIdentity | FnLimitLeftIdentity | FnLimitRightIdentity => Rule::Identity,
            FnLimitAtFromEpsilon
            | FnLimitLeftFromEpsilon
            | FnLimitRightFromEpsilon
            | FnLimitPosInfFromEpsilon
            | FnLimitNegInfFromEpsilon => Rule::FromEpsilon,
            FnLimitAtAccumulation
            | FnLimitLeftAccumulation
            | FnLimitRightAccumulation
            | FnLimitPosInfAccumulation
            | FnLimitNegInfAccumulation => Rule::Accumulation,
            FnLimitAtControl | FnLimitLeftControl | FnLimitRightControl | FnLimitPosInfControl
            | FnLimitNegInfControl => Rule::Control,
            _ => return Err(invalid("Id")),
        };
        let finite = matches!(
            builtin.theorem,
            FnLimitAtUnique
                | FnLimitAtExists
                | FnLimitAtSelected
                | FnLimitLeftUnique
                | FnLimitLeftExists
                | FnLimitLeftSelected
                | FnLimitRightUnique
                | FnLimitRightExists
                | FnLimitRightSelected
                | FnLimitAtIdentity
                | FnLimitLeftIdentity
                | FnLimitRightIdentity
                | FnLimitAtConstant
                | FnLimitLeftConstant
                | FnLimitRightConstant
                | FnLimitAtFromEpsilon
                | FnLimitLeftFromEpsilon
                | FnLimitRightFromEpsilon
                | FnLimitAtAccumulation
                | FnLimitLeftAccumulation
                | FnLimitRightAccumulation
                | FnLimitAtControl
                | FnLimitLeftControl
                | FnLimitRightControl
        );
        let offset = if finite { 2 } else { 1 };
        let arity = offset
            + match rule {
                Rule::Unique | Rule::Control => 2,
                Rule::Exists | Rule::Constant | Rule::FromEpsilon | Rule::Accumulation => 1,
                Rule::Selected | Rule::Identity => 0,
            };
        let count = 3
            + usize::from(finite)
            + match rule {
                Rule::Unique | Rule::Control => 2,
                Rule::Constant | Rule::Identity | Rule::FromEpsilon => 3,
                _ => 1,
            };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || !matches!(&call.name, AtomicName::Plain { name } if name == builtin.theorem.as_str())
            || args != &builtin.arguments
            || args.len() != arity
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("Stages"));
        }
        let approach = match builtin.theorem {
            FnLimitAtUnique
            | FnLimitAtExists
            | FnLimitAtSelected
            | FnLimitAtConstant
            | FnLimitAtIdentity
            | FnLimitAtFromEpsilon
            | FnLimitAtAccumulation
            | FnLimitAtControl => LimitApproach::AtPoint(args[1].clone().into()),
            FnLimitLeftUnique
            | FnLimitLeftExists
            | FnLimitLeftSelected
            | FnLimitLeftConstant
            | FnLimitLeftIdentity
            | FnLimitLeftFromEpsilon
            | FnLimitLeftAccumulation
            | FnLimitLeftControl => LimitApproach::FromLeft(args[1].clone().into()),
            FnLimitRightUnique
            | FnLimitRightExists
            | FnLimitRightSelected
            | FnLimitRightConstant
            | FnLimitRightIdentity
            | FnLimitRightFromEpsilon
            | FnLimitRightAccumulation
            | FnLimitRightControl => LimitApproach::FromRight(args[1].clone().into()),
            FnLimitPosInfUnique
            | FnLimitPosInfExists
            | FnLimitPosInfSelected
            | FnLimitPosInfConstant
            | FnLimitPosInfFromEpsilon
            | FnLimitPosInfAccumulation
            | FnLimitPosInfControl => LimitApproach::AtPositiveInfinity,
            FnLimitNegInfUnique
            | FnLimitNegInfExists
            | FnLimitNegInfSelected
            | FnLimitNegInfConstant
            | FnLimitNegInfFromEpsilon
            | FnLimitNegInfAccumulation
            | FnLimitNegInfControl => LimitApproach::AtNegativeInfinity,
            _ => return Err(invalid("Id")),
        };
        let req = &builtin.requirements;
        let Fact::AtomicFact(AtomicFact::InFact(member)) = &req[0] else {
            return Err(invalid("FunctionMembership"));
        };
        let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &member.set else {
            return Err(invalid("Signature"));
        };
        let parameters = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(move |_| g.param_type.as_ref()))
            .collect::<Vec<_>>();
        let [input] = parameters.as_slice() else {
            return Err(invalid("UnarySignature"));
        };
        let real = Obj::StandardSet(StandardSet::R);
        if member.element.ir() != args[0].ir()
            || !matches!(&req[1], Fact::AtomicFact(AtomicFact::SubsetFact(f)) if f.left.ir() == input.ir() && f.right == real)
            || !matches!(&req[2], Fact::AtomicFact(AtomicFact::SubsetFact(f)) if f.left.ir() == signature.ret_set.ir() && f.right == real)
            || (finite
                && !matches!(&req[3], Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir() == args[1].ir() && f.set == real))
        {
            return Err(invalid("RealDomain"));
        }
        let candidate_start = 3 + usize::from(finite);
        let candidates = match rule {
            Rule::Unique => 2,
            Rule::Exists | Rule::Accumulation | Rule::Control => 1,
            _ => 0,
        };
        for (fact, value) in req[candidate_start..candidate_start + candidates]
            .iter()
            .zip(&args[offset..offset + candidates])
        {
            if !matches!(fact, Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(f))
                if f.function.ir() == args[0].ir() && f.approach == approach && f.value.ir() == value.ir())
            {
                return Err(invalid("Candidate"));
            }
        }
        let goal = &builtin.conclusions[0];
        let selected = match rule {
            Rule::Unique => {
                if !matches!(goal, Fact::AtomicFact(AtomicFact::EqualFact(f))
                    if f.left.ir() == args[offset].ir() && f.right.ir() == args[offset + 1].ir())
                {
                    return Err(invalid("Conclusion"));
                }
                None
            }
            Rule::Exists => {
                super::compile_function_limit_definition::validate_limit_existence(
                    &args[0], &approach, goal,
                )?;
                None
            }
            Rule::Selected => {
                super::compile_function_limit_definition::validate_limit_existence(
                    &args[0],
                    &approach,
                    &req[candidate_start],
                )?;
                let Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(f)) = goal else {
                    return Err(invalid("SelectedConclusion"));
                };
                if f.function.ir() != args[0].ir()
                    || f.approach != approach
                    || !matches!(&f.value, Obj::LimitOperator(LimitOperator::Function(p))
                        if p.function.ir() == args[0].ir() && p.approach == approach)
                {
                    return Err(invalid("SelectedSubject"));
                }
                Some(&f.value)
            }
            Rule::Constant | Rule::Identity => {
                let Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(f)) = goal else {
                    return Err(invalid("ConstantConclusion"));
                };
                if f.function.ir() != args[0].ir()
                    || f.approach != approach
                    || f.value.ir()
                        != (if matches!(rule, Rule::Identity) {
                            &args[1]
                        } else {
                            &args[offset]
                        })
                        .ir()
                {
                    return Err(invalid("ConstantSubject"));
                }
                super::compile_function_limit_constant::validate_elementary_clauses(
                    f,
                    &req[candidate_start..],
                    if matches!(rule, Rule::Identity) {
                        ElementaryLimit::Identity
                    } else {
                        ElementaryLimit::Constant
                    },
                )?;
                None
            }
            Rule::FromEpsilon => {
                let Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(f)) = goal else {
                    return Err(invalid("EpsilonConclusion"));
                };
                if f.function.ir() != args[0].ir()
                    || f.approach != approach
                    || f.value.ir() != args[offset].ir()
                {
                    return Err(invalid("EpsilonSubject"));
                }
                super::compile_function_limit_definition::validate_clauses(
                    f,
                    &req[candidate_start + 1..],
                )?;
                None
            }
            Rule::Accumulation | Rule::Control => {
                if matches!(rule, Rule::Control)
                    && !matches!(&req[candidate_start + 1], Fact::AtomicFact(AtomicFact::InFact(f))
                    if f.element.ir() == args[offset + 1].ir() && f.set == Obj::StandardSet(StandardSet::RPos))
                {
                    return Err(invalid("PositiveEpsilon"));
                }
                None
            }
        };
        let (definitions, references) =
            self.compile_function_limit_requirements(req, dom_proofs, dom_stores, position)?;
        let formed = SourcePosition {
            before: count,
            ..*position
        };
        let wd = &conclusions_wd[0];
        self.compile_fact_wd(wd, goal, &formed)?;
        let scope = SourcePosition::new(Some(&formed), SourceOwner::FactWD(wd), usize::MAX);
        let statement = self.compile_formed_fact_proposition(wd, goal, &formed)?;
        let objects = args
            .iter()
            .map(|a| self.compile_object_reference(a, &scope))
            .collect::<Result<Vec<_>, _>>()?;
        let suffix = match rule {
            Rule::Unique => "CandidatesEqual",
            Rule::Exists => "Exists",
            Rule::Selected => "Selected",
            Rule::Constant => "Constant",
            Rule::Identity => "Identity",
            Rule::FromEpsilon => "OfForall",
            Rule::Accumulation => "Accumulation",
            Rule::Control => "Control",
        };
        let law = if matches!(rule, Rule::Accumulation | Rule::Control) {
            self.compile_function_limit_projection(
                goal,
                req,
                &dom_proofs[candidate_start],
                candidate_start,
                matches!(rule, Rule::Control).then(|| &args[offset + 1]),
                &references,
                &formed,
            )?
        } else if matches!(rule, Rule::FromEpsilon) {
            let Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(f)) = goal else {
                return Err(invalid("EpsilonConclusion"));
            };
            self.compile_function_limit_from_epsilon(
                f,
                wd,
                &req[candidate_start..],
                &references,
                &scope,
            )?
        } else if matches!(rule, Rule::Constant | Rule::Identity) {
            let Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(f)) = goal else {
                return Err(invalid("ConstantConclusion"));
            };
            self.compile_elementary_function_limit(
                f,
                wd,
                if matches!(rule, Rule::Identity) {
                    ElementaryLimit::Identity
                } else {
                    ElementaryLimit::Constant
                },
                &req[candidate_start..],
                &references,
                &scope,
            )?
        } else if matches!(rule, Rule::Selected) {
            format!(
                "Litex.{}FunctionLimitSelected {}",
                if finite { "finite" } else { "infinite" },
                self.compile_object_reference(selected.expect("validated selector"), &scope)?
            )
        } else if finite {
            let (side, _) = super::compile_function_limit::finite_side(&approach)?;
            format!(
                "Litex.finiteFunctionLimit{suffix} .{side} {} {}",
                objects.join(" "),
                references[candidate_start..].join(" ")
            )
        } else {
            let direction = super::compile_function_limit::infinite_direction(&approach)?;
            format!(
                "Litex.infiniteFunctionLimit{suffix} .{direction} {} {}",
                objects.join(" "),
                references[candidate_start..].join(" ")
            )
        };
        Ok((
            definitions,
            format!("(show {statement} from {law})"),
            builtin.conclusions.clone(),
        ))
    }
    pub(super) fn compile_function_limit_requirements(
        &self,
        req: &[Fact],
        dom_proofs: &[VerifyFactResult],
        dom_stores: &[StoreFactAndInferResult],
        position: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, Vec<String>), LeanCompileError> {
        if req.len() != dom_proofs.len() || req.len() != dom_stores.len() {
            return Err(invalid("RequirementArity"));
        }
        let mut definitions = Vec::new();
        let mut references = Vec::new();
        for (index, ((requirement, checked), stored)) in
            req.iter().zip(dom_proofs).zip(dom_stores).enumerate()
        {
            if source_subject(checked)? != *requirement {
                return Err(invalid("PremiseSubject"));
            }
            self.validate_store(&stored.store, requirement)?;
            let prior = SourcePosition {
                before: index,
                ..*position
            };
            let compiled = self.compile_verify(checked, &prior)?;
            definitions.push(self.emit_internal_fact(requirement, &compiled, &prior)?);
            let reference = format!("h_{}", requirement.fact_id().value());
            definitions.extend(self.compile_stored_inferences(
                stored,
                requirement,
                &(compiled.0, reference.clone()),
                &SourcePosition {
                    before: index + 1,
                    ..*position
                },
            )?);
            references.push(reference);
        }
        Ok((definitions, references))
    }
}
