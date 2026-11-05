use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::{
    AtomicExceptEqualityFactSearchProofByDefinition, BuiltinPropDefinitionProof, UserDefinedPropDefinitionProof,
};
use crate::execute::ExecDefPropStmtSuccessResult;
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferNormalAtomicFactResult, InferAtomicFactResult, InferResult,
};
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_prop_definition(
        &self,
        goal: &AtomicFact,
        wd: &AtomicFactWellDefinedProof,
        proof: &AtomicExceptEqualityFactSearchProofByDefinition,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match (goal, proof) {
            (AtomicFact::IsMatrixInvFact(_),AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(BuiltinPropDefinitionProof::IsMatrixInv(p))) => self.compile_matrix_inverse_definition(goal,wd,&p.requirement_facts,&p.proof_of_requirement_facts,position),
            (AtomicFact::MatrixInversibleFact(_),AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(BuiltinPropDefinitionProof::MatrixInversible(p))) => self.compile_matrix_inverse_definition(goal,wd,&p.requirement_facts,&p.proof_of_requirement_facts,position),

            (
                AtomicFact::NormalAtomicFact(normal),
                AtomicExceptEqualityFactSearchProofByDefinition::UserDefinedProp(proof),
            ) => self.compile_user_prop_fold(normal, proof, position),
            (_, AtomicExceptEqualityFactSearchProofByDefinition::UserDefinedProp(_)) => {
                Err(LeanCompileError::new(
                    "Prop/FoldFamily",
                    "Concrete predicate folding has another source predicate family.",
                ))
            }
            (
                AtomicFact::SubsetFact(fact),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::Subset(proof),
                ),
            ) => self.compile_subset_definition(
                fact,
                &proof.requirement_facts,
                &proof.proof_of_requirement_facts,
                position,
            ),
            (
                AtomicFact::InjectiveFact(_),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::Injective(p),
                ),
            ) => self.compile_mapping_definition(
                goal,
                &p.requirement_facts,
                &p.proof_of_requirement_facts,
                position,
            ),
            (
                AtomicFact::SurjectiveFact(_),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::Surjective(p),
                ),
            ) => self.compile_mapping_definition(
                goal,
                &p.requirement_facts,
                &p.proof_of_requirement_facts,
                position,
            ),
            (
                AtomicFact::BijectiveFact(_),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::Bijective(p),
                ),
            ) => self.compile_mapping_definition(
                goal,
                &p.requirement_facts,
                &p.proof_of_requirement_facts,
                position,
            ),
            (
                AtomicFact::SupersetFact(f),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::Superset(p),
                ),
            ) => self.compile_subset_definition(
                &SubsetFact {
                    fact_id: f.fact_id,
                    left: f.right.clone(),
                    right: f.left.clone(),
                    line_file: f.line_file.clone(),
                },
                &p.requirement_facts,
                &p.proof_of_requirement_facts,
                position,
            ),
            (
                AtomicFact::ProperSubsetFact(_),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::ProperSubset(p),
                ),
            ) => self.compile_proper_inclusion_definition(
                goal,
                &p.requirement_facts,
                &p.proof_of_requirement_facts,
                position,
            ),
            (
                AtomicFact::ProperSupersetFact(_),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::ProperSuperset(p),
                ),
            ) => self.compile_proper_inclusion_definition(
                goal,
                &p.requirement_facts,
                &p.proof_of_requirement_facts,
                position,
            ),
            (
                AtomicFact::RealSetBoundFact(_),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::RealSetBound(p),
                ),
            ) => self.compile_real_bound_definition(
                goal,
                &p.requirement_facts,
                &p.proof_of_requirement_facts,
                position,
            ),
            (
                AtomicFact::RealSetBoundedFact(_),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::RealSetBounded(p),
                ),
            ) => self.compile_real_bound_definition(
                goal,
                &p.requirement_facts,
                &p.proof_of_requirement_facts,
                position,
            ),
            (
                AtomicFact::SequenceAnalysisFact(f),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::SequenceAnalysis(p),
                ),
            ) => self.compile_sequence_analysis_definition(
                f,
                &p.requirement_facts,
                &p.proof_of_requirement_facts,
                position,
            ),
            (
                AtomicFact::HasSequenceLimitFact(f),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::SequenceLimit(p),
                ),
            ) => self.compile_sequence_epsilon_definition(
                &f.sequence,
                Some(&f.value),
                &p.requirement_facts,
                &p.proof_of_requirement_facts,
                position,
            ),
            (
                AtomicFact::HasSequenceLimsupFact(f),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::SequenceLimsup(p),
                ),
            ) => self.compile_sequence_extremum_definition(
                true,
                &f.sequence,
                &f.value,
                &p.requirement_facts,
                &p.proof_of_requirement_facts,
                position,
            ),
            (
                AtomicFact::HasSequenceLiminfFact(f),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::SequenceLiminf(p),
                ),
            ) => self.compile_sequence_extremum_definition(
                false,
                &f.sequence,
                &f.value,
                &p.requirement_facts,
                &p.proof_of_requirement_facts,
                position,
            ),
            (
                AtomicFact::HasFunctionLimitFact(f),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::FunctionLimit(p),
                ),
            ) => self.compile_function_limit_definition(f, wd, p, position),
            (
                AtomicFact::FunctionContinuousAtFact(f),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::FunctionContinuousAt(p),
                ),
            ) => self.compile_function_continuity_definition(f, wd, p, position),
            (
                AtomicFact::FunctionLipschitzFact(f),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(BuiltinPropDefinitionProof::FunctionLipschitz(p)),
            ) => self.compile_lipschitz_definition(f, wd, p, position),
            (
                AtomicFact::FunctionContinuousFact(f),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(BuiltinPropDefinitionProof::FunctionContinuous(p)),
            ) => if f.property == FunctionContinuityProperty::UniformContinuous {
                self.compile_uniform_continuity_definition(f, wd, p, position)
            } else { self.compile_global_continuity_definition(f, wd, p, position) },
            (
                AtomicFact::RealAccumulationFact(f),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::RealAccumulation(p),
                ),
            ) => self.compile_real_accumulation_definition(
                f,
                &p.requirement_facts,
                &p.proof_of_requirement_facts,
                position,
            ),
            (
                AtomicFact::MultivariableAnalysisFact(f),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::MultivariableAnalysis(
                        crate::execute::execute_fact_stmt::multivariable::definition::MultivariableDefinitionProof::ScalarContinuousAt(p)),
                ),
            ) => {
                if !matches!(&f.relation,MultivariableAnalysisRelation::ScalarContinuousAt(_)) {return Err(LeanCompileError::unsupported("MultivariableContinuity/DefinitionFamily"));}
                self.compile_multivariable_continuity_definition(&f.relation,wd,&p.requirement_facts,&p.proof_of_requirement_facts,position)
            },
            (
                AtomicFact::MultivariableAnalysisFact(f),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::MultivariableAnalysis(
                        crate::execute::execute_fact_stmt::multivariable::definition::MultivariableDefinitionProof::VectorContinuousAt(p)),
                ),
            ) => {
                if !matches!(&f.relation,MultivariableAnalysisRelation::VectorContinuousAt(_)) {return Err(LeanCompileError::unsupported("MultivariableContinuity/DefinitionFamily"));}
                self.compile_multivariable_continuity_definition(&f.relation,wd,&p.requirement_facts,&p.proof_of_requirement_facts,position)
            },
            (
                AtomicFact::MultivariableAnalysisFact(f),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::MultivariableAnalysis(
                        crate::execute::execute_fact_stmt::multivariable::definition::MultivariableDefinitionProof::ScalarDifferentiableAt(p)),
                ),
            ) => {
                if !matches!(&f.relation,MultivariableAnalysisRelation::ScalarDifferentiableAt(_)) {return Err(LeanCompileError::unsupported("MultivariableDifferentiability/DefinitionFamily"));}
                self.compile_multivariable_differentiability_definition(&f.relation,&p.requirement_facts,&p.proof_of_requirement_facts,position)
            },
            (
                AtomicFact::MultivariableAnalysisFact(f),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::MultivariableAnalysis(
                        crate::execute::execute_fact_stmt::multivariable::definition::MultivariableDefinitionProof::TotalDifferentiableAt(p)),
                ),
            ) => {
                if !matches!(&f.relation,MultivariableAnalysisRelation::TotalDifferentiableAt(_)) {return Err(LeanCompileError::unsupported("MultivariableDifferentiability/DefinitionFamily"));}
                self.compile_multivariable_differentiability_definition(&f.relation,&p.requirement_facts,&p.proof_of_requirement_facts,position)
            },
            (
                AtomicFact::MultivariableAnalysisFact(f),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::MultivariableAnalysis(
                        crate::execute::execute_fact_stmt::multivariable::definition::MultivariableDefinitionProof::ScalarLimit(p)),
                ),
            ) => {
                let MultivariableAnalysisRelation::ScalarLimit(r)=&f.relation else{return Err(LeanCompileError::unsupported("MultivariableScalarLimit/DefinitionSubject"));};
                self.compile_multivariable_scalar_definition(r,p,position)
            },
            (
                AtomicFact::MultivariableAnalysisFact(f),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::MultivariableAnalysis(
                        crate::execute::execute_fact_stmt::multivariable::definition::MultivariableDefinitionProof::VectorLimit(p)),
                ),
            ) => {
                let MultivariableAnalysisRelation::VectorLimit(r)=&f.relation else{return Err(LeanCompileError::unsupported("MultivariableVectorLimit/DefinitionSubject"));};
                self.compile_multivariable_vector_definition(r,p,position)
            },
            (
                AtomicFact::MultivariableAnalysisFact(f),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::MultivariableAnalysis(
                        crate::execute::execute_fact_stmt::multivariable::definition::MultivariableDefinitionProof::PartialDerivativeAt(p)),
                ),
            ) => {
                let MultivariableAnalysisRelation::PartialDerivativeAt(r)=&f.relation else{return Err(LeanCompileError::unsupported("PartialDerivativeAt/DefinitionSubject"));};
                self.compile_partial_derivative_definition(r,p,position)
            },
            (
                AtomicFact::MultivariableAnalysisFact(f),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::MultivariableAnalysis(
                        crate::execute::execute_fact_stmt::multivariable::definition::MultivariableDefinitionProof::JacobianAt(p)),
                ),
            ) => {
                let MultivariableAnalysisRelation::JacobianAt(r)=&f.relation else{return Err(LeanCompileError::unsupported("JacobianAt/DefinitionSubject"));};
                self.compile_jacobian_definition(r,p,position)
            },
            (
                AtomicFact::MultivariableAnalysisFact(f),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::MultivariableAnalysis(
                        crate::execute::execute_fact_stmt::multivariable::definition::MultivariableDefinitionProof::SecondPartialDerivativeAt(p)),
                ),
            ) => {
                let MultivariableAnalysisRelation::SecondPartialDerivativeAt(r)=&f.relation else{return Err(LeanCompileError::unsupported("SecondPartialDerivativeAt/DefinitionSubject"));};
                self.compile_second_partial_definition(r,p,position)
            },
            (
                AtomicFact::MultivariableAnalysisFact(f),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::MultivariableAnalysis(
                        crate::execute::execute_fact_stmt::multivariable::definition::MultivariableDefinitionProof::CurlAt(p)),
                ),
            ) => {
                let MultivariableAnalysisRelation::CurlAt(r)=&f.relation else{return Err(LeanCompileError::unsupported("CurlAt/DefinitionSubject"));};
                self.compile_curl_definition(r,p,position)
            },
            (
                AtomicFact::MultivariableAnalysisFact(f),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::MultivariableAnalysis(
                        crate::execute::execute_fact_stmt::multivariable::definition::MultivariableDefinitionProof::DivergenceAt(p)),
                ),
            ) => {
                let MultivariableAnalysisRelation::DivergenceAt(r)=&f.relation else{return Err(LeanCompileError::unsupported("DivergenceAt/DefinitionSubject"));};
                self.compile_divergence_definition(r,p,position)
            },
            (
                AtomicFact::MultivariableAnalysisFact(f),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::MultivariableAnalysis(
                        crate::execute::execute_fact_stmt::multivariable::definition::MultivariableDefinitionProof::HessianAt(p)),
                ),
            ) => {
                let MultivariableAnalysisRelation::HessianAt(r)=&f.relation else{return Err(LeanCompileError::unsupported("HessianAt/DefinitionSubject"));};
                self.compile_hessian_definition(r,p,position)
            },
            (
                AtomicFact::MultivariableAnalysisFact(f),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::MultivariableAnalysis(
                        crate::execute::execute_fact_stmt::multivariable::definition::MultivariableDefinitionProof::ScalarDifferentialAt(p)),
                ),
            ) => {
                let MultivariableAnalysisRelation::ScalarDifferentialAt(r)=&f.relation else{return Err(LeanCompileError::unsupported("ScalarDifferentialAt/DefinitionSubject"));};
                self.compile_scalar_differential_definition(r,p,position)
            },
            (
                AtomicFact::MultivariableAnalysisFact(f),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::MultivariableAnalysis(
                        crate::execute::execute_fact_stmt::multivariable::definition::MultivariableDefinitionProof::TotalDerivativeAt(p)),
                ),
            ) => {
                let MultivariableAnalysisRelation::TotalDerivativeAt(r)=&f.relation else{return Err(LeanCompileError::unsupported("TotalDerivativeAt/DefinitionSubject"));};
                self.compile_total_differential_definition(r,p,position)
            },
            (
                AtomicFact::MultivariableAnalysisFact(f),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::MultivariableAnalysis(
                        crate::execute::execute_fact_stmt::multivariable::definition::MultivariableDefinitionProof::LaplacianAt(p)),
                ),
            ) => {
                let MultivariableAnalysisRelation::LaplacianAt(r)=&f.relation else{return Err(LeanCompileError::unsupported("LaplacianAt/DefinitionSubject"));};
                self.compile_laplacian_definition(r,p,position)
            },
            (
                AtomicFact::MultivariableAnalysisFact(f),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::MultivariableAnalysis(
                        crate::execute::execute_fact_stmt::multivariable::definition::MultivariableDefinitionProof::GradientAt(p)),
                ),
            ) => {
                let MultivariableAnalysisRelation::GradientAt(r)=&f.relation else{return Err(LeanCompileError::unsupported("GradientAt/DefinitionSubject"));};
                self.compile_gradient_definition(r,p,position)
            },
            (
                AtomicFact::HasDerivativeAtFact(f),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::HasDerivativeAt(p),
                ),
            ) => self.compile_derivative_definition(f, wd, p, position),
            (
                AtomicFact::FunctionDifferentiableAtFact(f),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::FunctionDifferentiableAt(p),
                ),
            ) => self.compile_differentiability_definition(f, p, position),
            (
                AtomicFact::DvdFact(f),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(BuiltinPropDefinitionProof::Dvd(p)),
            ) => self.compile_dvd_definition(f, &p.requirement_facts, &p.proof_of_requirement_facts, position),
            (
                AtomicFact::FunctionRiemannIntegrableFact(f),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(BuiltinPropDefinitionProof::FunctionRiemannIntegrable(p)),
            ) => self.compile_riemann_integrability_definition(f,p,position),
            (
                AtomicFact::HasRiemannIntegralFact(f),
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(BuiltinPropDefinitionProof::HasRiemannIntegral(p)),
            ) => self.compile_riemann_definition(f, wd, p, position),
            (_, AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(_)) => {
                Err(LeanCompileError::unsupported("Prop/BuiltinDefinition"))
            }
        }
    }

    fn compile_user_prop_fold(
        &self,
        normal: &NormalAtomicFact,
        proof: &UserDefinedPropDefinitionProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (declaration, _, _) = position.visible_prop(&normal.predicate, &self.runtime)?;
        let substitution = self.prop_argument_substitution(declaration, normal)?;
        let parameters = declaration
            .statement
            .typed_parameters
            .groups
            .iter()
            .flat_map(|group| {
                group
                    .params
                    .iter()
                    .map(|parameter| (parameter, &group.param_type))
            })
            .collect::<Vec<_>>();
        let expected_count = parameters.len() + declaration.statement.iff_facts.len();
        if declaration.statement.iff_facts.is_empty()
            || proof.requirement_facts.len() != expected_count
            || proof.proof_of_requirement_facts.len() != expected_count
        {
            return Err(LeanCompileError::new(
                "Prop/FoldArity",
                "The selected definition proof omits or adds an ordered domain/body requirement.",
            ));
        }
        let mut witnesses = Vec::new();
        for (index, (requirement, checked)) in proof
            .requirement_facts
            .iter()
            .zip(&proof.proof_of_requirement_facts)
            .enumerate()
        {
            if index < parameters.len() {
                let (_, param_type) = parameters[index];
                if !parameter_type_fact_matches(
                    param_type,
                    &normal.body[index],
                    requirement,
                    &substitution,
                ) {
                    return Err(LeanCompileError::new(
                        "Prop/FoldDomain",
                        "A selected definition requirement proves another argument, carrier or exact set kind.",
                    ));
                }
            } else if !instantiated_fact_matches(
                &declaration.statement.iff_facts[index - parameters.len()],
                requirement,
                &substitution,
            ) {
                return Err(LeanCompileError::new("Prop/FoldBody", "A selected definition requirement differs from its instantiated defining clause."));
            }
            if source_subject(checked)? != *requirement {
                return Err(LeanCompileError::new("Prop/FoldRequirementSubject", "A definition requirement and its actual proof have different source subjects or IDs."));
            }
            let prior = SourcePosition {
                parent: Some(position),
                owner: SourceOwner::PropRequirements(proof),
                before: index,
            };
            let term_scope = SourcePosition::new(Some(&prior), SourceOwner::Term, 0);
            let replay = if matches!(requirement, Fact::ForallFact(_)) {
                &term_scope
            } else {
                &prior
            };
            let (proposition, term) = self.compile_verify(checked, replay)?;
            // Defining forall clauses use semantic objects. Apply the exact
            // checked polymorphic proof to those objects and their hypotheses.
            witnesses.push(
                if let (Fact::ForallFact(fact), VerifyFactResult::ForallFact(result)) =
                    (requirement, checked)
                {
                    let (introduced, assumed, owner) = match result.as_ref() {
                        VerifyForallFactResult::Success(
                            VerifyForallFactProof::ByLocalIntroduction(p),
                        ) => (&p.introduced_params, p.assumed_dom_facts.as_slice(), SourceOwner::Forall(p)),
                        VerifyForallFactResult::Success(
                            VerifyForallFactProof::ByKnownForallFact(p),
                        ) => (&p.well_defined.detailed_ref().introduced_params,
                            p.well_defined.detailed_ref().assumed_dom_facts.as_slice(), SourceOwner::KnownForall(p)),
                        VerifyForallFactResult::Success(
                            VerifyForallFactProof::ByEmptyParameterDomain(p),
                        ) => (&p.well_defined.detailed_ref().introduced_params,
                            p.well_defined.detailed_ref().assumed_dom_facts.as_slice(), SourceOwner::EmptyForall(p)),
                        _ => return Err(LeanCompileError::unsupported("Prop/FoldForallProof")),
                    };
                    let scope = SourcePosition::new(Some(&term_scope), owner, 0);
                    let (mut binders, _, mut definitions) =
                        self.compile_forall_head(fact, introduced, assumed, &scope)?;
                    let mut arguments = Vec::new();
                    for (index, (id, store)) in fact
                        .typed_parameters
                        .ordered_param_ids()
                        .iter()
                        .zip(&introduced.defined_params.store_and_infer_results)
                        .enumerate()
                    {
                        let value = format!("_value_i{}", id.value());
                        binders[2 * index] = format!("({value} : Litex.Obj (M := M) M.Value)");
                        arguments.extend([
                            "M.Value".to_string(),
                            "(inferInstance)".to_string(),
                            value,
                            format!("h_{}", store.primary_fact_id().value()),
                        ]);
                    }
                    arguments.extend(
                        fact.dom_facts
                            .iter()
                            .map(|f| format!("h_{}", f.fact_id().value())),
                    );
                    // The definition's forall is over semantic objects. Fix
                    // that telescope before checking the already selected
                    // polymorphic proof, rather than letting an untyped intro
                    // infer binders from a delayed proposition construction.
                    definitions.push(format!("have _fold_forall : {proposition} := {term}"));
                    definitions.push(format!("exact (@_fold_forall {})", arguments.join(" ")));
                    let body = format!("(by\n  {}\n)", definitions.join("\n").replace('\n', "\n  "));
                    if binders.is_empty() { body }
                    else { format!("(fun {} => {body})", binders.join(" ")) }
                } else {
                    term
                },
            );
        }
        let mut proof = witnesses
            .pop()
            .expect("validated nonempty definition requirements");
        for witness in witnesses.into_iter().rev() {
            proof = format!("(Exists.intro {witness} {proof})");
        }
        Ok(proof)
    }

    pub(in crate::compile_to_lean) fn compile_normal_atomic_proposition(
        &self,
        normal: &NormalAtomicFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if crate::compile_to_lean::compile_antiderivative::is_predicate(&normal.predicate) {
            if normal.body.len() != 3 {
                return Err(crate::compile_to_lean::compile_antiderivative::invalid(
                    "PredicateArity",
                ));
            }
            let args = normal
                .body
                .iter()
                .map(|x| {
                    self.compile_object_reference(x, position)
                        .map(|s| format!("(Litex.denote {s})"))
                })
                .collect::<Result<Vec<_>, _>>()?;
            return Ok(format!(
                "Litex.IsAntiderivativeOnValue M {}",
                args.join(" ")
            ));
        }
        if crate::compile_to_lean::compile_riemann_integral::is_enclosure(&normal.predicate) {
            if normal.body.len() != 7 {
                return Err(LeanCompileError::unsupported(
                    "RiemannIntegral/EnclosureArity",
                ));
            }
            let args = normal
                .body
                .iter()
                .map(|x| {
                    self.compile_object_reference(x, position)
                        .map(|s| format!("(Litex.denote {s})"))
                })
                .collect::<Result<Vec<_>, _>>()?;
            return Ok(format!("Litex.DarbouxEnclosureValue {}", args.join(" ")));
        }
        if let Some(name) =
            crate::compile_to_lean::compile_real_extrema::certificate_name(&normal.predicate)
        {
            if normal.body.len() != 2 {
                return Err(LeanCompileError::unsupported(
                    "RealExtremum/CertificateArity",
                ));
            }
            return Ok(format!(
                "(Litex.{name} {} {})",
                self.compile_object_reference(&normal.body[0], position)?,
                self.compile_object_reference(&normal.body[1], position)?
            ));
        }
        if position.visible_abstract_prop(&normal.predicate).is_some() {
            let arguments = normal
                .body
                .iter()
                .map(|object| {
                    self.compile_object_reference(object, position)
                        .map(|term| format!("(Litex.denote {term})"))
                })
                .collect::<Result<Vec<_>, _>>()?;
            return self
                .compile_abstract_predicate_proposition(&normal.predicate, &arguments, position)?
                .ok_or_else(|| LeanCompileError::unsupported("AbstractProp/Producer"));
        }
        let (declaration, declaration_position, index) =
            position.visible_prop(&normal.predicate, &self.runtime)?;
        self.prop_argument_substitution(declaration, normal)?;
        let mut arguments = Vec::new();
        for (index, object) in normal.body.iter().enumerate() {
            let term = self.compile_object_reference(object, position)?;
            arguments.push(if declaration_position.is_local() {
                // Local lets cannot generalize host universe levels between
                // applications. Predicates observe denotations, so use the
                // existing semantic view of this exact certified object.
                let name = format!("_local_prop_argument_{index}");
                format!("(let {name} := {term}; Litex.semanticObject (Litex.denote {name}) (Litex.isSet {name}))")
            } else {
                term
            });
        }
        let name = crate::compile_to_lean::compile_def_prop_stmt_result::concrete_prop_name(
            declaration,
            index + 1,
            declaration_position.is_local(),
        )?;
        let predicate = position.declaration_reference(&name, &declaration_position)?;
        Ok(if arguments.is_empty() {
            predicate
        } else {
            format!("({predicate} {})", arguments.join(" "))
        })
    }

    pub(in crate::compile_to_lean) fn validate_prop_predicate_signature(
        &self,
        signature: &PredicateSignatureWellDefinedProof,
        fact: &AtomicFact,
        position: &SourcePosition<'_>,
    ) -> Result<(), LeanCompileError> {
        let negative_view;
        let (normal, predicate, arity) = match (fact, signature) {
            (
                AtomicFact::NormalAtomicFact(normal),
                PredicateSignatureWellDefinedProof::Prop { predicate, arity },
            ) => (normal, predicate, arity),
            (
                AtomicFact::NotNormalAtomicFact(normal),
                PredicateSignatureWellDefinedProof::Prop { predicate, arity },
            ) => {
                negative_view = NormalAtomicFact {
                    fact_id: normal.fact_id,
                    predicate: normal.predicate.clone(),
                    body: normal.body.clone(),
                    line_file: normal.line_file.clone(),
                };
                (&negative_view, predicate, arity)
            }
            _ => {
                return Err(LeanCompileError::new(
                    "Prop/SignatureFamily",
                    "The concrete predicate signature has another source family.",
                ))
            }
        };
        if predicate != &normal.predicate || *arity != normal.body.len() {
            return Err(LeanCompileError::new(
                "Prop/Signature",
                "The recorded predicate identity or arity differs from its occurrence.",
            ));
        }
        let (declaration, _, _) = position.visible_prop(predicate, &self.runtime)?;
        self.prop_argument_substitution(declaration, normal)?;
        Ok(())
    }

    pub(in crate::compile_to_lean) fn prop_argument_substitution(
        &self,
        declaration: &ExecDefPropStmtSuccessResult,
        normal: &NormalAtomicFact,
    ) -> Result<HashMap<IdentifierId, Obj>, LeanCompileError> {
        // Namespace identity has already been resolved by visible_prop. This
        // helper validates the declaration's local signature and substitution.
        if normal.predicate.local_name() != declaration.statement.name {
            return Err(LeanCompileError::new(
                "Prop/Identity",
                "The predicate occurrence does not name this prior concrete declaration.",
            ));
        }
        let parameters = declaration
            .statement
            .typed_parameters
            .groups
            .iter()
            .flat_map(|group| &group.params)
            .collect::<Vec<_>>();
        if parameters.len() != normal.body.len() {
            return Err(LeanCompileError::new(
                "Prop/Arguments",
                "The concrete predicate has another argument arity.",
            ));
        }
        let mut substitution = HashMap::new();
        for (parameter, argument) in parameters.iter().zip(&normal.body) {
            if substitution
                .insert(parameter.id, argument.clone())
                .is_some()
            {
                return Err(LeanCompileError::new(
                    "Prop/ParameterIdentity",
                    "The concrete declaration repeats a parameter identity.",
                ));
            }
        }
        Ok(substitution)
    }

    pub(in crate::compile_to_lean) fn compile_prop_inferences(
        &self,
        store: &StoreFactAndInferResult,
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        if !matches!(seed, Fact::AtomicFact(AtomicFact::NormalAtomicFact(_))) {
            return Ok(Vec::new());
        }
        self.validate_store(&store.store, seed)?;
        let rules = match &store.infer {
            Some(InferResult::AtomicFact(InferAtomicFactResult::NormalAtomicFact(rules))) => rules,
            _ => {
                return Err(LeanCompileError::new(
                    "Prop/InferFamily",
                    "The stored predicate has another inference family.",
                ))
            }
        };
        let scope = SourcePosition {
            parent: Some(position),
            owner: SourceOwner::PropInference(store),
            before: 0,
        };
        self.compile_prop_inference_rules(rules, seed, compiled, &scope)
    }

    pub(in crate::compile_to_lean) fn compile_prop_inference_rules(
        &self,
        rules: &[InferNormalAtomicFactResult],
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let normal = match seed {
            Fact::AtomicFact(AtomicFact::NormalAtomicFact(normal)) => normal,
            _ => return Ok(Vec::new()),
        };
        if crate::compile_to_lean::compile_antiderivative::is_predicate(&normal.predicate) {
            return if normal.body.len() == 3 && rules.is_empty() {
                Ok(Vec::new())
            } else {
                Err(crate::compile_to_lean::compile_antiderivative::invalid(
                    "OriginalInference",
                ))
            };
        }
        if crate::compile_to_lean::compile_riemann_integral::is_enclosure(&normal.predicate) {
            return if normal.body.len() == 7 && rules.is_empty() {
                Ok(Vec::new())
            } else {
                Err(crate::compile_to_lean::compile_riemann_integral::invalid(
                    "EnclosureInference",
                ))
            };
        }
        if crate::compile_to_lean::compile_real_extrema::certificate_name(&normal.predicate)
            .is_some()
        {
            return if normal.body.len() == 2 && rules.is_empty() {
                Ok(Vec::new())
            } else {
                Err(LeanCompileError::unsupported(
                    "RealExtremum/UnexpectedInference",
                ))
            };
        }
        if position.visible_abstract_prop(&normal.predicate).is_some() {
            return if rules.is_empty() {
                Ok(Vec::new())
            } else {
                Err(LeanCompileError::unsupported(
                    "AbstractProp/UnexpectedInference",
                ))
            };
        }
        let (declaration, _, _) = position.visible_prop(&normal.predicate, &self.runtime)?;
        let substitution = self.prop_argument_substitution(declaration, normal)?;
        let parameters = declaration
            .statement
            .typed_parameters
            .groups
            .iter()
            .flat_map(|group| {
                group
                    .params
                    .iter()
                    .map(|parameter| (parameter, &group.param_type))
            })
            .collect::<Vec<_>>();
        let witness_ids = declaration
            .defined_params
            .store_and_infer_results
            .iter()
            .map(|stored| stored.primary_fact_id())
            .chain(declaration.statement.iff_facts.iter().map(Fact::fact_id))
            .collect::<Vec<_>>();
        let mut declarations = Vec::new();
        let mut seen_members = false;
        let mut seen_body = false;
        let mut completed = 0;
        for rule in rules {
            let (derived, body) = match rule {
                InferNormalAtomicFactResult::ParamTypes(proof) => {
                    if seen_members || seen_body || proof.derived.len() != parameters.len() {
                        return Err(LeanCompileError::new("Prop/InferDomainOrder", "Predicate domain projections have another original arity or stage order."));
                    }
                    seen_members = true;
                    (&proof.derived, false)
                }
                InferNormalAtomicFactResult::ExpandDefinition(proof) => {
                    if seen_body
                        || (!parameters.is_empty() && !seen_members)
                        || proof.derived.len() != declaration.statement.iff_facts.len()
                    {
                        return Err(LeanCompileError::new("Prop/InferBodyOrder", "Predicate body projections have another original arity or stage order."));
                    }
                    seen_body = true;
                    (&proof.derived, true)
                }
            };
            for (index, derived) in derived.iter().enumerate() {
                let fact = match &derived.store {
                    StoreFactResult::AtomicFact(fact) => Fact::AtomicFact(fact.fact.clone()),
                    StoreFactResult::AndFact(fact) => Fact::AndFact(fact.fact.clone()),
                    StoreFactResult::ForallFact(fact) => Fact::ForallFact(fact.fact.clone()),
                    StoreFactResult::ChainFact(fact) => Fact::ChainFact(fact.fact.clone()),
                    StoreFactResult::ExistShapedFact(stored) => match &stored.fact {
                        ExistShapedFact::Exist(fact) => Fact::ExistFact(fact.clone()),
                        _ => return Err(LeanCompileError::unsupported("Prop/InferExistFamily")),
                    },
                    _ => return Err(LeanCompileError::unsupported("Prop/InferCompoundClause")),
                };
                let witness_index = if body {
                    parameters.len() + index
                } else {
                    index
                };
                if body {
                    if !instantiated_fact_matches(
                        &declaration.statement.iff_facts[index],
                        &fact,
                        &substitution,
                    ) {
                        return Err(LeanCompileError::new("Prop/InferBodySubject", "An inferred predicate body differs from its exact instantiated defining clause."));
                    }
                } else {
                    if !parameter_type_fact_matches(
                        parameters[index].1,
                        &normal.body[index],
                        &fact,
                        &substitution,
                    ) {
                        return Err(LeanCompileError::new(
                            "Prop/InferDomainSubject",
                            "An inferred predicate domain differs from its actual argument, carrier or exact set kind.",
                        ));
                    }
                }
                let prior = SourcePosition {
                    before: completed,
                    ..*position
                };
                if self.resolve_fact(derived.store.primary_fact_id(), &prior)? != fact {
                    return Err(LeanCompileError::new(
                        "Prop/InferIdentity",
                        "The captured derived store differs from its exact source fact ID.",
                    ));
                }
                self.validate_store(&derived.store, &fact)?;
                if position.is_local()
                    && matches!(
                        fact,
                        Fact::AtomicFact(_) | Fact::ExistFact(_) | Fact::ForallFact(_)
                    )
                {
                    // The checked predicate already determines this projection's
                    // type, including constructors certified in its declaration.
                    // Do not demand a second, instantiated WD run just to print it.
                    let mut projection = format!("(show {} from {})", compiled.0, compiled.1);
                    for _ in 0..witness_index {
                        projection = format!("(Classical.choose_spec {projection})");
                    }
                    if witness_index + 1 < witness_ids.len() {
                        projection = format!("(Classical.choose {projection})");
                    }
                    declarations.push(format!(
                        "have h_{} :=\n  {}",
                        fact.fact_id().value(),
                        projection.replace('\n', "\n  ")
                    ));
                    completed += 1;
                    continue;
                }
                let formed = SourcePosition {
                    parent: Some(&prior),
                    owner: SourceOwner::InferredStore(&derived.store),
                    before: usize::MAX,
                };
                let names = witness_ids
                    .iter()
                    .map(|id| format!("h_{}", id.value()))
                    .collect::<Vec<_>>();
                let proof = if names.len() == 1 {
                    compiled.1.clone()
                } else {
                    format!(
                        "(by rcases {} with ⟨{}⟩; exact {})",
                        compiled.1,
                        names.join(", "),
                        names[witness_index]
                    )
                };
                let proposition = if matches!(fact, Fact::ExistFact(_) | Fact::ForallFact(_)) {
                    self.compile_prop_clause_instance(normal, index, &compiled.1, &formed)?
                } else {
                    self.fact_proposition(&fact, &formed)?
                };
                let member = (proposition, proof);
                declarations.push(self.emit_internal_fact(&fact, &member, position)?);
                declarations.extend(self.compile_stored_projections(
                    &derived.store,
                    &fact,
                    &member,
                    &formed,
                )?);
                completed += 1;
            }
        }
        Ok(declarations)
    }
}
