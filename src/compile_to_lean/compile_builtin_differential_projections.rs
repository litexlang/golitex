//! Coordinate projections retain the original differential and domain captures.
use super::compile_builtin_derivative_schema::validate_context;
use super::compile_real_set_bounds::contains_parameter;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::execute::execute_fact_stmt::multivariable::helper as schema;
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
};

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("DifferentialProjection/{stage}"))
}
fn relation(fact: &Fact) -> Result<&MultivariableAnalysisRelation, LeanCompileError> {
    let Fact::AtomicFact(AtomicFact::MultivariableAnalysisFact(p)) = fact else {
        return Err(invalid("OriginalPositiveRelation"));
    };
    Ok(&p.relation)
}
fn candidate(fact: &Fact, name: &str, args: &[&Obj]) -> Result<(), LeanCompileError> {
    let r = relation(fact)?;
    let actual = r.argument_refs();
    if r.predicate_name() != name
        || actual.len() != args.len()
        || !actual.iter().zip(args).all(|(a, b)| a.ir() == b.ir())
    {
        return Err(invalid("OriginalCandidateOrProjection"));
    }
    Ok(())
}
fn gradient_row(value: &Obj, matrix: &Obj, n: &Obj, args: &[Obj]) -> bool {
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(p)) = value else {
        return false;
    };
    let [group] = p.body.set_bound_parameters.groups.as_slice() else {
        return false;
    };
    let [axis] = group.params.as_slice() else {
        return false;
    };
    if group.param_type.ir() != schema::indices(n.clone()).ir()
        || !p.body.dom_facts.is_empty()
        || *p.body.ret_set != Obj::StandardSet(StandardSet::R)
        || args.iter().any(|a| contains_parameter(a, axis.id))
    {
        return false;
    }
    p.equal_to.ir()
        == schema::apply(
            matrix,
            vec![
                schema::number(1),
                Obj::Identifier(IdentifierObj::from_bound_name(axis)),
            ],
        )
        .ir()
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_differential_projections(
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
        let (context, source_name, law) = match builtin.theorem {
            ScalarDifferentialAtPartial => (
                5,
                "has_scalar_differential_at",
                "scalarDifferentialPartialCandidate",
            ),
            ScalarDifferentialAtGradient => (
                5,
                "has_scalar_differential_at",
                "scalarDifferentialGradientRow",
            ),
            TotalDerivativeAtJacobian => (
                6,
                "has_total_derivative_at",
                "totalDifferentialJacobianCandidate",
            ),
            _ => return Err(invalid("Identity")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        let count = context + 1;
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || !matches!(&call.name,AtomicName::Plain{name} if name==builtin.theorem.as_str())
            || args != &builtin.arguments
            || args.len() != builtin.theorem.arity()
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("OriginalStages"));
        }
        let total = builtin.theorem == TotalDerivativeAtJacobian;
        let partial = builtin.theorem == ScalarDifferentialAtPartial;
        let source_args = args[..if total { 5 } else { 4 }].iter().collect::<Vec<_>>();
        candidate(&builtin.requirements[context], source_name, &source_args)?;
        if total {
            candidate(&builtin.conclusions[0], "has_jacobian_at", &source_args)?;
        } else if partial {
            let entry = schema::apply(&args[3], vec![schema::number(1), args[4].clone()]);
            candidate(
                &builtin.conclusions[0],
                "has_partial_derivative_at",
                &[&args[0], &args[1], &args[2], &args[4], &entry],
            )?;
        } else {
            let goal = relation(&builtin.conclusions[0])?;
            let out = goal.argument_refs();
            if goal.predicate_name() != "has_gradient_at"
                || out.len() != 4
                || !out[..3]
                    .iter()
                    .zip(&args[..3])
                    .all(|(a, b)| a.ir() == b.ir())
                || !gradient_row(out[3], &args[3], &args[2], args)
            {
                return Err(invalid("OriginalFreshGradientRow"));
            }
        }
        let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(rules))) =
            &dom_stores[context].infer
        else {
            return Err(invalid("OriginalInference"));
        };
        let [InferMultivariableAnalysisFactResult::Definition(capture)] = rules.as_slice() else {
            return Err(invalid("OriginalInference"));
        };
        if capture.source_fact_id != builtin.requirements[context].fact_id()
            || capture.derived.len() != 3
        {
            return Err(invalid("OriginalInferenceIdentity"));
        }
        let source = capture
            .function_domain
            .as_ref()
            .ok_or_else(|| invalid("OriginalCompleteDomain"))?;
        validate_context(
            relation(&builtin.requirements[context])?,
            &builtin.requirements[..context],
            source,
        )?;
        let (definitions, refs) = self.compile_function_limit_requirements(
            &builtin.requirements,
            dom_proofs,
            dom_stores,
            position,
        )?;
        let formed = SourcePosition {
            before: count,
            ..*position
        };
        self.compile_fact_wd(&conclusions_wd[0], &builtin.conclusions[0], &formed)?;
        let FactWellDefinedProof::AtomicExceptEquality(wd) = &conclusions_wd[0] else {
            return Err(invalid("OriginalGoalFormation"));
        };
        let Fact::AtomicFact(goal) = &builtin.conclusions[0] else {
            return Err(invalid("OriginalGoal"));
        };
        let scope = SourcePosition::new(
            Some(&formed),
            SourceOwner::FactWD(&conclusions_wd[0]),
            usize::MAX,
        );
        let objects = args
            .iter()
            .map(|o| self.compile_object_reference(o, &scope))
            .collect::<Result<Vec<_>, _>>()?;
        let raw = objects
            .iter()
            .map(|o| format!("(Litex.denote {o})"))
            .collect::<Vec<_>>();
        let (view, domain_match) =
            self.compile_multivariable_limit_view(&args[0], source, &scope)?;
        let base = context - 1;
        let context_args = vec![args[0].clone(), args[1].clone(), args[2].clone()];
        let real = self.compile_euclidean_limit_function_context(
            &context_args,
            &builtin.requirements[..base],
            source,
            if total { Some(&args[3]) } else { None },
            &scope,
        )?;
        let mut lines = vec![view, real];
        lines.extend(
            self.compile_atomic_wd_locals(wd, goal, &formed)?
                .into_iter()
                .map(|s| format!("  {}", s.replace('\n', "\n  "))),
        );
        let natural = format!("(Litex.inNPos_natural {} {})", objects[2], refs[0]);
        let geometry = format!(
            "{} _multivariable_real ({domain_match} ▸ {})",
            refs[base - 1],
            refs[base]
        );
        let proof = if total {
            let output_natural = format!("(Litex.inNPos_natural {} {})", objects[3], refs[2]);
            format!(
                "Litex.{law} {} {natural} {output_natural} {geometry} {}",
                raw.join(" "),
                refs[context]
            )
        } else if partial {
            let PredicateDomainProof::MultivariableAnalysis(goal_capture) = &wd
                .as_detailed()
                .map_err(|_| invalid("DetailedGoalFormation"))?
                .predicate_domain
            else {
                return Err(invalid("OriginalCoordinateFormation"));
            };
            if goal_capture.requirements.len() != 7
                || !matches!(&goal_capture.requirements[5].requirement,Fact::AtomicFact(AtomicFact::InFact(p)) if p.element.ir()==args[4].ir()&&p.set.ir()==schema::indices(args[2].clone()).ir())
            {
                return Err(invalid("OriginalCoordinateMembership"));
            }
            format!(
                "Litex.{law} {} {natural} {geometry} h_{} {}",
                raw.join(" "),
                goal_capture.requirements[5].requirement.fact_id().value(),
                refs[context]
            )
        } else {
            format!(
                "Litex.{law} {} {natural} {geometry} {}",
                raw.join(" "),
                refs[context]
            )
        };
        let statement = self.compile_formed_fact_proposition(
            &conclusions_wd[0],
            &builtin.conclusions[0],
            &formed,
        )?;
        Ok((
            definitions,
            format!(
                "(show {statement} from (by\n{}\n  exact {proof}\n))",
                lines.join("\n")
            ),
            builtin.conclusions.clone(),
        ))
    }
}
