//! Squeeze uses the recorded local chain and all three complete function domains.
use super::compile_compound_fact::chain_edge;
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
    LeanCompileError::unsupported(&format!("FunctionLimitSqueeze/{stage}"))
}
impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_function_limit_squeeze(
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
            FnLimitAtSqueeze | FnLimitLeftSqueeze | FnLimitRightSqueeze => true,
            FnLimitPosInfSqueeze | FnLimitNegInfSqueeze => false,
            _ => return Err(invalid("Id")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        let base = 3 + usize::from(finite);
        let count = base + 12;
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
            FnLimitAtSqueeze => LimitApproach::AtPoint(args[3].clone().into()),
            FnLimitLeftSqueeze => LimitApproach::FromLeft(args[3].clone().into()),
            FnLimitRightSqueeze => LimitApproach::FromRight(args[3].clone().into()),
            FnLimitPosInfSqueeze => LimitApproach::AtPositiveInfinity,
            FnLimitNegInfSqueeze => LimitApproach::AtNegativeInfinity,
            _ => return Err(invalid("Approach")),
        };
        let req = &builtin.requirements;
        let (first, _) = real_limit_signature(&req[..3], &args[0])?;
        let (middle, _) = real_limit_signature(&req[base..base + 3], &args[1])?;
        let (upper, _) = real_limit_signature(&req[base + 4..base + 7], &args[2])?;
        if finite
            && !matches!(&req[3],Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==args[3].ir()&&f.set==Obj::StandardSet(StandardSet::R))
        {
            return Err(invalid("Point"));
        }
        let (
            Fact::AtomicFact(AtomicFact::EqualFact(middle_domain)),
            Fact::AtomicFact(AtomicFact::EqualFact(upper_domain)),
        ) = (&req[base + 3], &req[base + 7])
        else {
            return Err(invalid("DomainEqualities"));
        };
        if !signature_domain_matches(&middle_domain.right, first)
            || !signature_domain_matches(&middle_domain.left, middle)
            || !signature_domain_matches(&upper_domain.left, upper)
            || upper_domain.right.ir() != middle_domain.right.ir()
        {
            return Err(invalid("DomainSubjects"));
        }
        let value = &args[base];
        let threshold = &args[base + 1];
        for (index, function) in [(base + 8, &args[0]), (base + 9, &args[2])] {
            if !matches!(&req[index],Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(f)) if f.function.ir()==function.ir()&&f.approach==approach&&f.value.ir()==value.ir())
            {
                return Err(invalid("Candidates"));
            }
        }
        let threshold_set = Obj::StandardSet(if finite {
            StandardSet::RPos
        } else {
            StandardSet::R
        });
        if !matches!(&req[base+10],Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==threshold.ir()&&f.set==threshold_set)
        {
            return Err(invalid("Threshold"));
        }
        let Fact::ForallFact(all) = &req[base + 11] else {
            return Err(invalid("LocalChain"));
        };
        let [group] = all.typed_parameters.groups.as_slice() else {
            return Err(invalid("LocalParameter"));
        };
        let ParamType::Obj(neighborhood) = &group.param_type else {
            return Err(invalid("Neighborhood"));
        };
        let input = parameter(&all.typed_parameters, neighborhood)?;
        let Obj::SetFormer(SetFormer::SetBuilder(builder)) = neighborhood else {
            return Err(invalid("Neighborhood"));
        };
        if builder.param_set.ir() != middle_domain.right.ir()
            || !all.dom_facts.is_empty()
            || input.id == builder.param_binding.id
            || args.iter().chain([&middle_domain.right]).any(|a| {
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
        let [ExistOrAndChainAtomicFact::ChainFact(chain)] = all.then_facts.as_slice() else {
            return Err(invalid("Chain"));
        };
        if chain.objs.len() != 3 || chain.prop_names.len() != 2 {
            return Err(invalid("ChainArity"));
        }
        let x = Obj::Identifier(IdentifierObj::from_bound_name(input));
        for index in 0..2 {
            let edge = chain_edge(chain, index, chain.fact_id)?;
            let (low, high, strict) = source_order_oriented(&edge)?;
            if strict
                || !call_matches(low, &args[index], &x)
                || !call_matches(high, &args[index + 1], &x)
            {
                return Err(invalid("ChainSubject"));
            }
        }
        let goal = &builtin.conclusions[0];
        if !matches!(goal,Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(f)) if f.function.ir()==args[1].ir()&&f.approach==approach&&f.value.ir()==value.ir())
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
        let scope = SourcePosition::new(Some(&formed), SourceOwner::FactWD(wd), usize::MAX);
        let statement = self.compile_formed_fact_proposition(wd, goal, &formed)?;
        let mut steps = self.compile_function_limit_context(
            0,
            &args[0],
            &middle_domain.right,
            &req[..3],
            &refs[..3],
            &scope,
        )?;
        steps.extend(self.compile_function_limit_context(
            1,
            &args[1],
            &middle_domain.left,
            &req[base..base + 3],
            &refs[base..base + 3],
            &scope,
        )?);
        steps.extend(self.compile_function_limit_context(
            2,
            &args[2],
            &upper_domain.left,
            &req[base + 4..base + 7],
            &refs[base + 4..base + 7],
            &scope,
        )?);
        let object = |a: &Obj| {
            self.compile_object_reference(a, &scope)
                .map(|s| format!("(Litex.denote {s})"))
        };
        let objects = format!(
            "{} {} {}",
            object(&args[0])?,
            object(&args[1])?,
            object(&args[2])?
        );
        let (prefix, arguments) = if finite {
            let (side, point) = finite_side(&approach)?;
            ("finite", format!(".{side} {objects} {}", object(point)?))
        } else {
            (
                "infinite",
                format!(".{} {objects}", infinite_direction(&approach)?),
            )
        };
        let local=format!("(by\n  intro input hinput\n  exact {} (Litex.semanticObject input (M.member_isSet hinput)) hinput\n)",refs[base+11]);
        steps.push(format!("exact Litex.{prefix}FunctionLimitSqueeze {arguments} {} (Litex.denote _law0_domain) {} {} _law_real_1 _law_domain_0 (_law_domain_1.symm.trans ({}.trans _law_domain_0)) (_law_domain_2.symm.trans ({}.trans _law_domain_0)) {} {} {local}",object(value)?,self.compile_object_reference(threshold,&scope)?,refs[base+10],refs[base+3],refs[base+7],refs[base+8],refs[base+9]));
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
