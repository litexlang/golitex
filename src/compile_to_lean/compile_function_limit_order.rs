//! Local comparison of two recorded limits on the same complete domain.
use super::compile_function_limit::{finite_side, infinite_direction};
use super::compile_function_limit_definition::{approach_conditions, signature_domain_matches};
use super::compile_function_limit_unary::real_limit_signature;
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::compile_sequence_analysis::call_matches;
use super::helper::source_order_oriented;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::prelude::*;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("FunctionLimitOrder/{stage}"))
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_function_limit_order(
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
        let finite = match builtin.theorem {
            FnLimitAtCompare | FnLimitLeftCompare | FnLimitRightCompare => true,
            FnLimitPosInfCompare | FnLimitNegInfCompare => false,
            _ => return Err(invalid("Id")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        let base = 3 + usize::from(finite);
        let count = base + 8;
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || !matches!(&call.name,AtomicName::Plain{name} if name==builtin.theorem.as_str())
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
            FnLimitAtCompare => LimitApproach::AtPoint(args[2].clone().into()),
            FnLimitLeftCompare => LimitApproach::FromLeft(args[2].clone().into()),
            FnLimitRightCompare => LimitApproach::FromRight(args[2].clone().into()),
            FnLimitPosInfCompare => LimitApproach::AtPositiveInfinity,
            FnLimitNegInfCompare => LimitApproach::AtNegativeInfinity,
            _ => return Err(invalid("Approach")),
        };
        let req = &builtin.requirements;
        let (first, _) = real_limit_signature(&req[..3], &args[0])?;
        let (second, _) = real_limit_signature(&req[base..base + 3], &args[1])?;
        if finite
            && !matches!(&req[3],Fact::AtomicFact(AtomicFact::InFact(f))
            if f.element.ir()==args[2].ir() && f.set==Obj::StandardSet(StandardSet::R))
        {
            return Err(invalid("Point"));
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(domains)) = &req[base + 3] else {
            return Err(invalid("DomainEquality"));
        };
        if !signature_domain_matches(&domains.right, first)
            || !signature_domain_matches(&domains.left, second)
        {
            return Err(invalid("DomainSubjects"));
        }
        for index in 0..2 {
            if !matches!(&req[base+4+index],Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(f))
                if f.function.ir()==args[index].ir() && f.approach==approach && f.value.ir()==args[base-1+index].ir())
            {
                return Err(invalid("Candidates"));
            }
        }
        let threshold = &args[base + 1];
        let threshold_set = Obj::StandardSet(if finite {
            StandardSet::RPos
        } else {
            StandardSet::R
        });
        if !matches!(&req[base+6],Fact::AtomicFact(AtomicFact::InFact(f))
            if f.element.ir()==threshold.ir() && f.set==threshold_set)
        {
            return Err(invalid("Threshold"));
        }
        let Fact::ForallFact(all) = &req[base + 7] else {
            return Err(invalid("LocalComparison"));
        };
        let [group] = all.typed_parameters.groups.as_slice() else {
            return Err(invalid("LocalParameter"));
        };
        let ParamType::Obj(neighborhood) = &group.param_type else {
            return Err(invalid("LocalCarrier"));
        };
        let input = parameter(&all.typed_parameters, neighborhood)?;
        let Obj::SetFormer(SetFormer::SetBuilder(builder)) = neighborhood else {
            return Err(invalid("Neighborhood"));
        };
        if builder.param_set.ir() != domains.right.ir()
            || input.id == builder.param_binding.id
            || !all.dom_facts.is_empty()
            || args.iter().chain([&domains.right]).any(|a| {
                contains_parameter(a, input.id) || contains_parameter(a, builder.param_binding.id)
            })
        {
            return Err(invalid("LocalDomainOrBinders"));
        }
        approach_conditions(
            &builder.facts,
            &approach,
            &Obj::Identifier(IdentifierObj::from_bound_name(&builder.param_binding)),
            threshold,
        )?;
        let x = Obj::Identifier(IdentifierObj::from_bound_name(input));
        let [ExistOrAndChainAtomicFact::AtomicFact(order)] = all.then_facts.as_slice() else {
            return Err(invalid("LocalOrder"));
        };
        let (low, high, strict) = source_order_oriented(order)?;
        if strict || !call_matches(low, &args[0], &x) || !call_matches(high, &args[1], &x) {
            return Err(invalid("LocalOrderSubject"));
        }
        let goal = &builtin.conclusions[0];
        let Fact::AtomicFact(order) = goal else {
            return Err(invalid("Conclusion"));
        };
        let (low, high, strict) = source_order_oriented(order)?;
        if strict || low.ir() != args[base - 1].ir() || high.ir() != args[base].ir() {
            return Err(invalid("ConclusionSubject"));
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
        let (prefix, arguments) = if finite {
            let (side, point) = finite_side(&approach)?;
            (
                "finite",
                format!(
                    ".{side} {} {} {}",
                    object(&args[0])?,
                    object(&args[1])?,
                    object(point)?
                ),
            )
        } else {
            (
                "infinite",
                format!(
                    ".{} {} {}",
                    infinite_direction(&approach)?,
                    object(&args[0])?,
                    object(&args[1])?
                ),
            )
        };
        let local=format!("(by\n  intro input hinput\n  exact {} (Litex.semanticObject input (M.member_isSet hinput)) hinput\n)",refs[base+7]);
        steps.push(format!("exact Litex.{prefix}FunctionLimitCompare {arguments} {} {} (Litex.denote _law0_domain) {} {} _law_domain_0 (_law_domain_1.symm.trans ({}.trans _law_domain_0)) {} {} {local}",object(&args[base-1])?,object(&args[base])?,self.compile_object_reference(threshold,&scope)?,refs[base+6],refs[base+3],refs[base+4],refs[base+5]));
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
