//! Local equality transfers a limit without equating the complete domains.
use super::compile_function_limit::{finite_side, infinite_direction};
use super::compile_function_limit_definition::{
    approach_conditions, signature_domain_matches, validate_accumulation_clause,
};
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
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("LocalFunctionLimit/{stage}"))
}
impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_function_limit_local(
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
            FnLimitAtLocalEqual | FnLimitLeftLocalEqual | FnLimitRightLocalEqual => true,
            FnLimitPosInfLocalEqual | FnLimitNegInfLocalEqual => false,
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
            || args.len() != base + 1
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("Stages"));
        }
        let approach = match builtin.theorem {
            FnLimitAtLocalEqual => LimitApproach::AtPoint(args[2].clone().into()),
            FnLimitLeftLocalEqual => LimitApproach::FromLeft(args[2].clone().into()),
            FnLimitRightLocalEqual => LimitApproach::FromRight(args[2].clone().into()),
            FnLimitPosInfLocalEqual => LimitApproach::AtPositiveInfinity,
            FnLimitNegInfLocalEqual => LimitApproach::AtNegativeInfinity,
            _ => return Err(invalid("Approach")),
        };
        let req = &builtin.requirements;
        let (first, _) = real_limit_signature(&req[..3], &args[0])?;
        let (second, _) = real_limit_signature(&req[base..base + 3], &args[1])?;
        if finite
            && !matches!(&req[3],Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==args[2].ir()&&f.set==Obj::StandardSet(StandardSet::R))
        {
            return Err(invalid("Point"));
        }
        let value = &args[base - 1];
        let threshold = &args[base];
        if !matches!(&req[base+3],Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(f)) if f.function.ir()==args[0].ir()&&f.approach==approach&&f.value.ir()==value.ir())
        {
            return Err(invalid("Candidate"));
        }
        let threshold_set = Obj::StandardSet(if finite {
            StandardSet::RPos
        } else {
            StandardSet::R
        });
        if !matches!(&req[base+4],Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==threshold.ir()&&f.set==threshold_set)
        {
            return Err(invalid("Threshold"));
        }
        let goal = &builtin.conclusions[0];
        let Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(candidate)) = goal else {
            return Err(invalid("Conclusion"));
        };
        if candidate.function.ir() != args[1].ir()
            || candidate.approach != approach
            || candidate.value.ir() != value.ir()
        {
            return Err(invalid("ConclusionSubject"));
        }
        let output_domain = validate_accumulation_clause(candidate, &req[base + 5])?;
        let Fact::AtomicFact(AtomicFact::SubsetFact(subset)) = &req[base + 6] else {
            return Err(invalid("LocalInclusion"));
        };
        if !signature_domain_matches(&subset.right, first)
            || !signature_domain_matches(output_domain, second)
        {
            return Err(invalid("Domains"));
        }
        let Obj::SetFormer(SetFormer::SetBuilder(builder)) = &subset.left else {
            return Err(invalid("Neighborhood"));
        };
        if builder.param_set.ir() != output_domain.ir()
            || args
                .iter()
                .chain([&subset.right, output_domain])
                .any(|a| contains_parameter(a, builder.param_binding.id))
        {
            return Err(invalid("NeighborhoodDomain"));
        }
        approach_conditions(
            &builder.facts,
            &approach,
            &Obj::Identifier(IdentifierObj::from_bound_name(&builder.param_binding)),
            threshold,
        )?;
        let Fact::ForallFact(all) = &req[base + 7] else {
            return Err(invalid("LocalEquation"));
        };
        let input = parameter(&all.typed_parameters, &subset.left)?;
        if !all.dom_facts.is_empty()
            || input.id == builder.param_binding.id
            || args
                .iter()
                .chain([&subset.left, &subset.right, output_domain])
                .any(|a| contains_parameter(a, input.id))
        {
            return Err(invalid("LocalBinder"));
        }
        let x = Obj::Identifier(IdentifierObj::from_bound_name(input));
        if !matches!(all.then_facts.as_slice(),[ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(f))] if call_matches(&f.left,&args[1],&x)&&call_matches(&f.right,&args[0],&x))
        {
            return Err(invalid("LocalEquationSubject"));
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
            &subset.right,
            &req[..3],
            &refs[..3],
            &scope,
        )?;
        steps.extend(self.compile_function_limit_context(
            1,
            &args[1],
            output_domain,
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
        let inclusion=format!("(by\n  intro input hinput\n  have _member : M.mem input (Litex.denote _law0_domain) := {} input hinput\n  rw [_law_domain_0] at _member\n  exact _member\n)",refs[base+6]);
        let equation=format!("(by\n  intro input hinput\n  exact {} (Litex.semanticObject input (M.member_isSet hinput)) hinput\n)",refs[base+7]);
        steps.push(format!("exact Litex.{prefix}FunctionLimitLocalEqual {arguments} {} (Litex.denote _law1_domain) {} {} _law_real_1 _law_domain_1 {} {} {inclusion} {equation}",object(value)?,self.compile_object_reference(threshold,&scope)?,refs[base+4],refs[base+3],refs[base+5]));
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
