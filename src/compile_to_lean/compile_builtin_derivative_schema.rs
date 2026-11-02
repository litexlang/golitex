//! Native derivative schema actions replay their recorded verification pipeline.
use super::compile_multivariable_limit_context::validate_limit_context;
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainProof;
use crate::execute::execute_fact_stmt::multivariable::helper as schema;
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Action {
    Unique,
    Exists,
    Selected,
}
struct NativeSchema {
    action: Action,
    predicate: &'static str,
    selector: Option<&'static str>,
    theorem: &'static str,
    context: usize,
    derived: usize,
}
fn native_schema(id: BuiltinTheoremId) -> Option<NativeSchema> {
    use BuiltinTheoremId::*;
    let (action, predicate, selector, theorem, context, derived) = match id {
        PartialAtUnique => (
            Action::Unique,
            "has_partial_derivative_at",
            Some("partial_derivative"),
            "partialDerivativeCandidatesEqual",
            6,
            3,
        ),
        PartialAtExists => (
            Action::Exists,
            "has_partial_derivative_at",
            Some("partial_derivative"),
            "partialDerivativeExistsOfCandidate",
            6,
            3,
        ),
        PartialAtSelected => (
            Action::Selected,
            "has_partial_derivative_at",
            Some("partial_derivative"),
            "partialDerivativeValueSelected",
            6,
            3,
        ),
        SecondPartialAtUnique => (
            Action::Unique,
            "has_second_partial_derivative_at",
            None,
            "secondPartialCandidatesEqual",
            7,
            2,
        ),
        SecondPartialAtExists => (
            Action::Exists,
            "has_second_partial_derivative_at",
            None,
            "secondPartialExistsOfCandidate",
            7,
            2,
        ),
        GradientAtUnique => (
            Action::Unique,
            "has_gradient_at",
            Some("gradient_at"),
            "gradientCandidatesEqual",
            5,
            2,
        ),
        GradientAtExists => (
            Action::Exists,
            "has_gradient_at",
            Some("gradient_at"),
            "gradientExistsOfCandidate",
            5,
            2,
        ),
        GradientAtSelected => (
            Action::Selected,
            "has_gradient_at",
            Some("gradient_at"),
            "gradientValueSelected",
            5,
            2,
        ),
        JacobianAtUnique => (
            Action::Unique,
            "has_jacobian_at",
            Some("jacobian"),
            "jacobianCandidatesEqual",
            6,
            2,
        ),
        JacobianAtExists => (
            Action::Exists,
            "has_jacobian_at",
            Some("jacobian"),
            "jacobianExistsOfCandidate",
            6,
            2,
        ),
        JacobianAtSelected => (
            Action::Selected,
            "has_jacobian_at",
            Some("jacobian"),
            "jacobianValueSelected",
            6,
            2,
        ),
        HessianAtUnique => (
            Action::Unique,
            "has_hessian_at",
            Some("hessian"),
            "hessianCandidatesEqual",
            5,
            2,
        ),
        HessianAtExists => (
            Action::Exists,
            "has_hessian_at",
            Some("hessian"),
            "hessianExistsOfCandidate",
            5,
            2,
        ),
        HessianAtSelected => (
            Action::Selected,
            "has_hessian_at",
            Some("hessian"),
            "hessianValueSelected",
            5,
            2,
        ),
        DivergenceAtUnique => (
            Action::Unique,
            "has_divergence_at",
            Some("divergence"),
            "divergenceCandidatesEqual",
            6,
            2,
        ),
        DivergenceAtExists => (
            Action::Exists,
            "has_divergence_at",
            Some("divergence"),
            "divergenceExistsOfCandidate",
            6,
            2,
        ),
        DivergenceAtSelected => (
            Action::Selected,
            "has_divergence_at",
            Some("divergence"),
            "divergenceValueSelected",
            6,
            2,
        ),
        CurlAtUnique => (
            Action::Unique,
            "has_curl_at",
            Some("curl"),
            "curlCandidatesEqual",
            6,
            2,
        ),
        CurlAtExists => (
            Action::Exists,
            "has_curl_at",
            Some("curl"),
            "curlExistsOfCandidate",
            6,
            2,
        ),
        CurlAtSelected => (
            Action::Selected,
            "has_curl_at",
            Some("curl"),
            "curlValueSelected",
            6,
            2,
        ),
        LaplacianAtUnique => (
            Action::Unique,
            "has_laplacian_at",
            Some("laplacian"),
            "laplacianCandidatesEqual",
            5,
            2,
        ),
        LaplacianAtExists => (
            Action::Exists,
            "has_laplacian_at",
            Some("laplacian"),
            "laplacianExistsOfCandidate",
            5,
            2,
        ),
        LaplacianAtSelected => (
            Action::Selected,
            "has_laplacian_at",
            Some("laplacian"),
            "laplacianValueSelected",
            5,
            2,
        ),
        ScalarDifferentialAtUnique => (
            Action::Unique,
            "has_scalar_differential_at",
            Some("scalar_differential"),
            "scalarDifferentialCandidatesEqual",
            5,
            3,
        ),
        ScalarDifferentialAtExists => (
            Action::Exists,
            "has_scalar_differential_at",
            Some("scalar_differential"),
            "scalarDifferentialExistsOfCandidate",
            5,
            3,
        ),
        ScalarDifferentialAtSelected => (
            Action::Selected,
            "has_scalar_differential_at",
            Some("scalar_differential"),
            "scalarDifferentialValueSelected",
            5,
            3,
        ),
        TotalDerivativeAtUnique => (
            Action::Unique,
            "has_total_derivative_at",
            Some("differential"),
            "totalDifferentialCandidatesEqual",
            6,
            3,
        ),
        TotalDerivativeAtExists => (
            Action::Exists,
            "has_total_derivative_at",
            Some("differential"),
            "totalDifferentialExistsOfCandidate",
            6,
            3,
        ),
        TotalDerivativeAtSelected => (
            Action::Selected,
            "has_total_derivative_at",
            Some("differential"),
            "totalDifferentialValueSelected",
            6,
            3,
        ),
        _ => return None,
    };
    Some(NativeSchema {
        action,
        predicate,
        selector,
        theorem,
        context,
        derived,
    })
}
pub(super) fn supports(id: BuiltinTheoremId) -> bool {
    native_schema(id).is_some()
}
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("DerivativeSchema/{stage}"))
}
fn relation(fact: &Fact) -> Result<&MultivariableAnalysisRelation, LeanCompileError> {
    let Fact::AtomicFact(AtomicFact::MultivariableAnalysisFact(f)) = fact else {
        return Err(invalid("PositiveCandidate"));
    };
    Ok(&f.relation)
}
fn candidate(fact: &Fact, spec: &NativeSchema, expected: &[&Obj]) -> Result<(), LeanCompileError> {
    let r = relation(fact)?;
    let actual = r.argument_refs();
    if r.predicate_name() != spec.predicate
        || actual.len() != expected.len()
        || !actual.iter().zip(expected).all(|(a, b)| a.ir() == b.ir())
    {
        return Err(invalid("CandidateArguments"));
    }
    Ok(())
}
fn same_object(a: &Obj, b: &Obj) -> bool {
    a.ir()==b.ir() || crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::compound_objs_alpha_equal(a,b)
}
fn existence(
    fact: &Fact,
    spec: &NativeSchema,
    r: &MultivariableAnalysisRelation,
    args: &[Obj],
) -> Result<(), LeanCompileError> {
    let Fact::ExistFact(e) = fact else {
        return Err(invalid("Existence"));
    };
    let p = parameter(&e.typed_parameters, &schema::value_carrier(r))?;
    if args.iter().any(|a| contains_parameter(a, p.id)) {
        return Err(invalid("WitnessCapture"));
    }
    let [QuantifierFreeFact::AtomicFact(f)] = e.facts.as_slice() else {
        return Err(invalid("ExistenceBody"));
    };
    let value = Obj::Identifier(IdentifierObj::from_bound_name(p));
    let mut expected = r.argument_refs();
    *expected
        .last_mut()
        .ok_or_else(|| invalid("ValueArgument"))? = &value;
    candidate(&Fact::AtomicFact(f.clone()), spec, &expected)
}
pub(super) fn validate_context(
    r: &MultivariableAnalysisRelation,
    req: &[Fact],
    source: &CompleteFunctionDomainProof,
) -> Result<(), LeanCompileError> {
    let args = r.argument_refs();
    let n = schema::input_dimension(r);
    let m = schema::function_output_dimension(r);
    let base = 4 + usize::from(m.is_some());
    let axes = match r {
        MultivariableAnalysisRelation::PartialDerivativeAt(p) => vec![&p.coordinate],
        MultivariableAnalysisRelation::SecondPartialDerivativeAt(p) => {
            vec![&p.first_coordinate, &p.second_coordinate]
        }
        _ => Vec::new(),
    };
    if req.len() != base + 1 + axes.len() {
        return Err(invalid("ContextArity"));
    }
    let context_args = vec![args[0].clone(), args[1].clone(), n.clone()];
    validate_limit_context(&context_args, &req[..base], source, m.as_ref())?;
    let domain = schema::actual_domain(&source.signature).ok_or_else(|| invalid("ActualDomain"))?;
    if !matches!(&req[base],Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==args[1].ir()&&same_object(&f.set,&domain))
    {
        return Err(invalid("PointInOriginalDomain"));
    }
    for (fact, axis) in req[base + 1..].iter().zip(axes) {
        if !matches!(fact,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==axis.ir()&&same_object(&f.set,&schema::indices(n.clone())))
        {
            return Err(invalid("CoordinateDomain"));
        }
    }
    Ok(())
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_derivative_schema(
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
        let spec = native_schema(builtin.theorem).ok_or_else(|| invalid("Id"))?;
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        let count = spec.context + if spec.action == Action::Unique { 2 } else { 1 };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
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
        let r = if spec.action == Action::Selected {
            let r = relation(&builtin.conclusions[0])?;
            if r.predicate_name() != spec.predicate {
                return Err(invalid("SelectedFamily"));
            }
            let selected = Obj::from_multivariable_selector(
                spec.selector.ok_or_else(|| invalid("UnselectableFamily"))?,
                args,
            )
            .ok_or_else(|| invalid("SelectedConstructor"))?;
            let mut expected = args.iter().collect::<Vec<_>>();
            expected.push(&selected);
            candidate(&builtin.conclusions[0], &spec, &expected)?;
            existence(&builtin.requirements[spec.context], &spec, r, args)?;
            r
        } else {
            let expected = args
                .iter()
                .take(args.len() - usize::from(spec.action == Action::Unique))
                .collect::<Vec<_>>();
            candidate(&builtin.requirements[spec.context], &spec, &expected)?;
            if spec.action == Action::Unique {
                let mut other = expected.clone();
                *other.last_mut().unwrap() = args.last().unwrap();
                candidate(&builtin.requirements[spec.context + 1], &spec, &other)?;
                if !matches!(&builtin.conclusions[0],Fact::AtomicFact(AtomicFact::EqualFact(f)) if f.left.ir()==expected.last().unwrap().ir()&&f.right.ir()==args.last().unwrap().ir())
                {
                    return Err(invalid("UniqueConclusion"));
                }
            }
            let r = relation(&builtin.requirements[spec.context])?;
            if spec.action == Action::Exists {
                existence(&builtin.conclusions[0], &spec, r, args)?;
            }
            r
        };
        let source = if spec.action == Action::Selected {
            let FactWellDefinedProof::AtomicExceptEquality(wd) = &conclusions_wd[0] else {
                return Err(invalid("SelectedFormation"));
            };
            let PredicateDomainProof::MultivariableAnalysis(capture) = &wd
                .as_detailed()
                .map_err(|_| invalid("DetailedFormation"))?
                .predicate_domain
            else {
                return Err(invalid("SelectedOriginalDomain"));
            };
            if capture.requirements.len()!=spec.context+1 || !builtin.requirements[..spec.context].iter().zip(&capture.requirements[..spec.context]).all(|(a,b)|crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::quantifier_free_source_facts_alpha_equal(a,&b.requirement)) {return Err(invalid("SelectedOriginalContext"));}
            &capture.function_domain
        } else {
            let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(
                rules,
            ))) = &dom_stores[spec.context].infer
            else {
                return Err(invalid("OriginalInference"));
            };
            let [InferMultivariableAnalysisFactResult::Definition(capture)] = rules.as_slice()
            else {
                return Err(invalid("OriginalInference"));
            };
            if capture.source_fact_id != builtin.requirements[spec.context].fact_id()
                || capture.derived.len() != spec.derived
            {
                return Err(invalid("OriginalInferenceIdentity"));
            }
            capture
                .function_domain
                .as_ref()
                .ok_or_else(|| invalid("OriginalCompleteDomain"))?
        };
        validate_context(r, &builtin.requirements[..spec.context], source)?;
        let mut definitions = Vec::new();
        for (index, ((fact, checked), store)) in builtin
            .requirements
            .iter()
            .zip(dom_proofs)
            .zip(dom_stores)
            .enumerate()
        {
            if source_subject(checked)? != *fact {
                return Err(invalid("OriginalProofSubject"));
            }
            let prior = SourcePosition {
                before: index,
                ..*position
            };
            let compiled = self.compile_verify(checked, &prior)?;
            self.validate_store(&store.store, fact)?;
            definitions.push(self.emit_internal_fact(fact, &compiled, &prior)?);
            definitions.extend(self.compile_stored_inferences(
                store,
                fact,
                &(compiled.0, format!("h_{}", fact.fact_id().value())),
                &SourcePosition {
                    before: index + 1,
                    ..*position
                },
            )?);
        }
        let formed = SourcePosition {
            before: count,
            ..*position
        };
        self.compile_fact_wd(&conclusions_wd[0], &builtin.conclusions[0], &formed)?;
        let scope = SourcePosition::new(
            Some(&formed),
            SourceOwner::FactWD(&conclusions_wd[0]),
            usize::MAX,
        );
        let raw = args
            .iter()
            .map(|o| {
                self.compile_object_reference(o, &scope)
                    .map(|v| format!("(Litex.denote {v})"))
            })
            .collect::<Result<Vec<_>, _>>()?
            .join(" ");
        let original = format!("h_{}", builtin.requirements[spec.context].fact_id().value());
        let proof=match spec.action {
            Action::Unique if matches!(r, MultivariableAnalysisRelation::ScalarDifferentialAt(_) | MultivariableAnalysisRelation::TotalDerivativeAt(_)) => {
                let n = schema::input_dimension(r);
                let m = schema::function_output_dimension(r);
                let base = 4 + usize::from(m.is_some());
                let context_args = vec![args[0].clone(), args[1].clone(), n];
                let (view, domain_match) = self.compile_multivariable_limit_view(&args[0], source, &scope)?;
                let context = self.compile_euclidean_limit_function_context(
                    &context_args, &builtin.requirements[..base], source, m.as_ref(), &scope,
                )?;
                let natural = format!("(Litex.inNPos_natural _ h_{})", builtin.requirements[0].fact_id().value());
                let output_natural = if m.is_some() {
                    format!(" (Litex.inNPos_natural _ h_{})", builtin.requirements[2].fact_id().value())
                } else { String::new() };
                let point_member = builtin.requirements[base-1].fact_id().value();
                let point_domain = builtin.requirements[base].fact_id().value();
                let other = builtin.requirements[spec.context+1].fact_id().value();
                format!("(by\n{view}\n{context}\n  exact Litex.{} {raw} {natural}{output_natural} h_{point_member} _multivariable_real ({domain_match} ▸ h_{point_domain}) {original} h_{other}\n)", spec.theorem)
            }
            Action::Unique=>format!("(Litex.{} {raw} {original} h_{})",spec.theorem,builtin.requirements[spec.context+1].fact_id().value()),
            Action::Exists=>format!("(by\n  obtain ⟨value,hv,hc⟩ := Litex.{} {raw} {original}\n  exact ⟨value,hv,hc⟩\n)",spec.theorem),
            Action::Selected=>format!("(by\n  apply Litex.{} {raw}\n  obtain ⟨value,hv,hc⟩ := {original}\n  exact ⟨Litex.denote value,hc⟩\n)",spec.theorem),
        };
        let statement = self.compile_formed_fact_proposition(
            &conclusions_wd[0],
            &builtin.conclusions[0],
            &formed,
        )?;
        Ok((
            definitions,
            format!("(show {statement} from {proof})"),
            builtin.conclusions.clone(),
        ))
    }
}
