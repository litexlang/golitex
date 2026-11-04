//! Replay the original local mapping, independent output accumulation and outer condition.
use super::compile_function_limit_definition::{approach_conditions, signature_domain_matches};
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
    LeanCompileError::unsupported(&format!("FunctionLimitComposition/{stage}"))
}
fn composition(object: &Obj, outer: &Obj, inner: &Obj, input: &Obj) -> bool {
    let Obj::FnObj(call) = object else {
        return false;
    };
    let [arguments] = call.body.as_slice() else {
        return false;
    };
    let [value] = arguments.as_slice() else {
        return false;
    };
    call_matches(object, outer, value) && call_matches(value, inner, input)
}
impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_function_limit_composition(
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
        let punctured = match builtin.theorem {
            FnLimitAtContinuousCompose => false,
            FnLimitAtPuncturedCompose => true,
            _ => return Err(invalid("Identity")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || !matches!(&call.name, AtomicName::Plain{name} if name==builtin.theorem.as_str())
            || args != &builtin.arguments
            || args.len() != 5 + usize::from(punctured)
            || builtin.requirements.len() != 13
            || dom_proofs.len() != 13
            || dom_stores.len() != 13
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("OriginalStages"));
        }
        let req = &builtin.requirements;
        let (inner, _) = real_limit_signature(&req[..3], &args[0])?;
        let (outer, _) = real_limit_signature(&req[3..6], &args[1])?;
        let (output, _) = real_limit_signature(&req[6..9], &args[2])?;
        let approach = LimitApproach::AtPoint(args[3].clone().into());
        if !matches!(&req[9],Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(f))
            if f.function.ir()==args[0].ir() && f.approach==approach && f.value.ir()==args[4].ir())
        {
            return Err(invalid("InnerLimit"));
        }
        let Fact::AtomicFact(AtomicFact::RealAccumulationFact(acc)) = &req[10] else {
            return Err(invalid("IndependentAccumulation"));
        };
        if acc.side != RealApproachSide::Both
            || acc.point.ir() != args[3].ir()
            || !signature_domain_matches(&acc.domain, output)
        {
            return Err(invalid("AccumulationDomainPointSide"));
        }
        let valid_outer = if punctured {
            matches!(&req[11],Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(f))
                if f.function.ir()==args[1].ir()
                    && f.approach==LimitApproach::AtPoint(args[4].clone().into())
                    && f.value.ir()==args[5].ir())
        } else {
            matches!(&req[11],Fact::AtomicFact(AtomicFact::FunctionContinuousAtFact(f))
                if f.function.ir()==args[1].ir() && f.point.ir()==args[4].ir()
                    && f.side==RealApproachSide::Both)
        };
        if !valid_outer {
            return Err(invalid("OuterCondition"));
        }
        let Fact::ExistFact(exists) = &req[12] else {
            return Err(invalid("LocalMappingExists"));
        };
        let radius = parameter(
            &exists.typed_parameters,
            &Obj::StandardSet(StandardSet::RPos),
        )?;
        let [QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(mapping))] =
            exists.facts.as_slice()
        else {
            return Err(invalid("LocalMappingSubset"));
        };
        let Obj::SetFormer(SetFormer::SetBuilder(neighborhood)) = &mapping.left else {
            return Err(invalid("LocalNeighborhood"));
        };
        let Obj::SetFormer(SetFormer::SetBuilder(allowed)) = &mapping.right else {
            return Err(invalid("LocalAllowed"));
        };
        if neighborhood.param_set.ir() != acc.domain.ir()
            || allowed.param_set.ir() != acc.domain.ir()
            || allowed.facts.len() != 3 + usize::from(punctured)
        {
            return Err(invalid("CompleteOutputDomainOrClauseCount"));
        }
        let [QuantifierFreeFact::AtomicFact(AtomicFact::InFact(input)), QuantifierFreeFact::AtomicFact(AtomicFact::InFact(image)), rest @ ..] =
            allowed.facts.as_slice()
        else {
            return Err(invalid("LocalMappingMemberships"));
        };
        let x = Obj::Identifier(IdentifierObj::from_bound_name(&allowed.param_binding));
        if input.element.ir() != x.ir()
            || !signature_domain_matches(&input.set, inner)
            || !call_matches(&image.element, &args[0], &x)
            || !signature_domain_matches(&image.set, outer)
        {
            return Err(invalid("LocalMappingSubjects"));
        }
        let equation = if punctured {
            let [QuantifierFreeFact::AtomicFact(AtomicFact::NotEqualFact(avoid)), eq] = rest else {
                return Err(invalid("PuncturedExclusion"));
            };
            if !call_matches(&avoid.left, &args[0], &x) || avoid.right.ir() != args[4].ir() {
                return Err(invalid("PuncturedExclusionSubject"));
            }
            eq
        } else {
            let [eq] = rest else {
                return Err(invalid("LocalEquationCount"));
            };
            eq
        };
        if !matches!(equation,QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(eq))
            if call_matches(&eq.left,&args[2],&x) && composition(&eq.right,&args[1],&args[0],&x))
        {
            return Err(invalid("LocalCompositionEquation"));
        }
        let ids = [
            radius.id,
            neighborhood.param_binding.id,
            allowed.param_binding.id,
        ];
        if ids[0] == ids[1]
            || ids[0] == ids[2]
            || ids[1] == ids[2]
            || args
                .iter()
                .chain([&acc.domain, &input.set, &image.set])
                .any(|o| ids.iter().any(|id| contains_parameter(o, *id)))
            || contains_parameter(&mapping.right, radius.id)
        {
            return Err(invalid("LocalBinderCapture"));
        }
        approach_conditions(
            &neighborhood.facts,
            &approach,
            &Obj::Identifier(IdentifierObj::from_bound_name(&neighborhood.param_binding)),
            &Obj::Identifier(IdentifierObj::from_bound_name(radius)),
        )?;
        let goal = &builtin.conclusions[0];
        if !matches!(goal,Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(f))
            if f.function.ir()==args[2].ir() && f.approach==approach
                && if punctured { f.value.ir()==args[5].ir() } else { call_matches(&f.value,&args[1],&args[4]) })
        {
            return Err(invalid("Conclusion"));
        }
        let (definitions, refs) =
            self.compile_function_limit_requirements(req, dom_proofs, dom_stores, position)?;
        let formed = SourcePosition {
            before: 13,
            ..*position
        };
        let wd = &conclusions_wd[0];
        self.compile_fact_wd(wd, goal, &formed)?;
        let statement = self.compile_formed_fact_proposition(wd, goal, &formed)?;
        let scope = SourcePosition::new(Some(&formed), SourceOwner::FactWD(wd), usize::MAX);
        let mut steps = Vec::new();
        for (index, domain) in [&input.set, &image.set, &acc.domain]
            .into_iter()
            .enumerate()
        {
            steps.extend(self.compile_function_limit_context(
                index,
                &args[index],
                domain,
                &req[index * 3..index * 3 + 3],
                &refs[index * 3..index * 3 + 3],
                &scope,
            )?);
        }
        let object = |a: &Obj| {
            self.compile_object_reference(a, &scope)
                .map(|s| format!("(Litex.denote {s})"))
        };
        let out = object(&args[2])?;
        let point = object(&args[3])?;
        steps.push(format!("have _compose_accumulation : Litex.RealAccumulationValue M .both (Litex.FunctionSemantics.domainValue {out}) {point} := by\n  rw [← _law_domain_2]\n  exact {}",refs[10]));
        if !punctured {
            let VerifyFactResult::AtomicExceptEquality(proof) = &dom_proofs[11] else {
                return Err(invalid("OriginalOuterProof"));
            };
            let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_ref() else {
                return Err(invalid("OriginalOuterSuccess"));
            };
            let original = SourcePosition {
                before: 11,
                ..*position
            };
            let centre = self.compile_continuity_point_formation(
                &proof.fact,
                &proof.well_defined_proof,
                &original,
            )?;
            if !signature_domain_matches(&centre.domain, outer) {
                return Err(invalid("OriginalOuterCompleteDomain"));
            }
            let mut body = centre.bindings;
            body.push(format!("exact {}", centre.membership));
            steps.push(format!("have _compose_centre : M.mem {} (Litex.FunctionSemantics.domainValue {}) := by\n  {}",object(&args[4])?,object(&args[1])?,body.join("\n").replace('\n',"\n  ")));
        }
        steps.push(format!(
            "obtain ⟨_compose_radius, _compose_positive, _compose_mapping⟩ := {}",
            refs[12]
        ));
        let conjunction = if punctured {
            "⟨_law_domain_0 ▸ _compose_clauses.1, _law_domain_1 ▸ _compose_clauses.2.1, _compose_clauses.2.2.1, _compose_clauses.2.2.2⟩"
        } else {
            "⟨_law_domain_0 ▸ _compose_clauses.1, _law_domain_1 ▸ _compose_clauses.2.1, _compose_clauses.2.2⟩"
        };
        let local=format!("(by\n  intro input hinput\n  have _compose_near : M.mem input (Litex.finiteLimitNeighborhoodValue .both (Litex.denote _law2_domain) {point} (Litex.denote _compose_radius)) := by\n    rw [_law_domain_2]\n    exact hinput\n  obtain ⟨_, _compose_member, _compose_clauses⟩ := (Litex.SetSemantics.sep_members _ _ _).mp (_compose_mapping input _compose_near)\n  exact {conjunction}\n)");
        let objects = args[..5]
            .iter()
            .map(object)
            .collect::<Result<Vec<_>, _>>()?
            .join(" ");
        steps.push(if punctured {
            format!("exact Litex.finiteFunctionLimitPuncturedCompose {objects} {} _compose_radius _compose_positive _law_real_2 {} _compose_accumulation {} {local}",object(&args[5])?,refs[9],refs[11])
        } else {
            format!("exact Litex.finiteFunctionLimitContinuousCompose {objects} _compose_radius _compose_positive _law_real_1 _law_real_2 _compose_centre {} _compose_accumulation {} {local}",refs[9],refs[11])
        });
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
