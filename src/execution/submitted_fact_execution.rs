use crate::error::RuntimeError;
use crate::fact::Fact;
use crate::inference::InferReason;
use crate::result::{
    StmtResult, SuccessFactProofNode, SuccessFactProofResult, SuccessFactStmtResult,
    SuccessStoreFactResult, SuccessTemplateInstantiationResult,
    SuccessVerifyBinderObjectWellDefinedResult, SuccessVerifyBinderPremiseResult,
    SuccessVerifyFactBinderResult, SuccessVerifyFactForObjWellDefinedResult,
    SuccessVerifyFactWellDefinedProofResult, SuccessVerifyFiniteAggregateModeResult,
    SuccessVerifyFiniteReduceDomainCoverageResult, SuccessVerifyIterationCoverageResult,
    SuccessVerifyIterationIntervalResult, SuccessVerifyIterationScalarReturnResult,
    SuccessVerifyObjWellDefinedResult, SuccessVerifyReduceModeResult, VerifyFactResult,
};
use crate::runtime::Runtime;
use crate::verification::nested_obj_binder_normalized_fact_key;
use crate::verification::VerifyState;
use std::collections::HashSet;
use std::result::Result;

/// Semantic effects produced while materializing a template are represented
/// by the template's retained body Result.  The verification child
/// environment is deliberately discarded after a submitted fact; this
/// collector selects only those body/surface facts that are mathematical
/// consequences of the successful object construction and therefore need to
/// be replayed in the parent environment.
struct TemplateSemanticEffectCollector {
    seen_templates: HashSet<String>,
    seen_facts: HashSet<String>,
    facts: Vec<Fact>,
}

impl TemplateSemanticEffectCollector {
    fn new() -> Self {
        Self {
            seen_templates: HashSet::new(),
            seen_facts: HashSet::new(),
            facts: Vec::new(),
        }
    }

    fn collect_from_fact_result(&mut self, result: &VerifyFactResult) {
        self.collect_from_fact_well_definedness(&result.checked().proof);
    }

    fn collect_from_fact_well_definedness(
        &mut self,
        result: &SuccessVerifyFactWellDefinedProofResult,
    ) {
        match result {
            SuccessVerifyFactWellDefinedProofResult::AtomicFact(atomic) => {
                for argument in &atomic.arguments {
                    self.collect_from_object(&argument.result);
                }
                for domain_check in &atomic.predicate.domain_checks {
                    self.collect_from_fact_result(&domain_check.result);
                }
            }
            SuccessVerifyFactWellDefinedProofResult::AndFact(and) => {
                for conjunct in &and.conjuncts {
                    self.collect_from_fact_well_definedness(conjunct);
                }
            }
            SuccessVerifyFactWellDefinedProofResult::ChainFact(chain) => {
                for comparison in &chain.comparisons {
                    self.collect_from_fact_well_definedness(comparison);
                }
            }
            SuccessVerifyFactWellDefinedProofResult::OrFact(or) => {
                for branch in &or.branches {
                    self.collect_from_fact_well_definedness(branch);
                }
            }
            SuccessVerifyFactWellDefinedProofResult::ExistFact(exist) => {
                self.collect_from_binder(&exist.binder);
                for body in &exist.body {
                    self.collect_from_fact_well_definedness(&body.well_definedness);
                }
            }
            SuccessVerifyFactWellDefinedProofResult::ForallFact(forall) => {
                self.collect_from_binder(&forall.binder);
                for premise in &forall.premises {
                    self.collect_from_fact_well_definedness(&premise.well_definedness);
                }
                for conclusion in &forall.conclusions {
                    self.collect_from_fact_well_definedness(&conclusion.well_definedness);
                }
            }
            SuccessVerifyFactWellDefinedProofResult::ForallFactWithIff(iff) => {
                self.collect_from_fact_well_definedness(&iff.forward);
                self.collect_from_fact_well_definedness(&iff.reverse);
            }
            SuccessVerifyFactWellDefinedProofResult::NotForallFact(not_forall) => {
                self.collect_from_fact_well_definedness(&not_forall.inner);
            }
        }
    }

    fn collect_from_binder(&mut self, binder: &SuccessVerifyFactBinderResult) {
        for group in &binder.parameter_groups {
            if let Some(carrier) = &group.carrier {
                self.collect_from_object(&carrier.result);
            }
            for parameter in &group.parameters {
                self.collect_from_fact_well_definedness(&parameter.well_definedness.proof);
            }
        }
    }

    fn collect_from_object(&mut self, result: &SuccessVerifyObjWellDefinedResult) {
        match result {
            SuccessVerifyObjWellDefinedResult::Direct(direct) => {
                let steps = &direct.steps;
                for child in &steps.children {
                    self.collect_from_object(&child.result);
                }
                if let Some(binder) = &steps.binder {
                    self.collect_from_object_binder(binder);
                }
                if let Some(template) = &steps.template_instantiation {
                    self.collect_from_template(template);
                }
            }
            SuccessVerifyObjWellDefinedResult::Reuse(reuse) => {
                self.collect_from_object(&SuccessVerifyObjWellDefinedResult::Direct(
                    reuse.source.clone(),
                ));
            }
        }
    }

    fn collect_from_object_binder(&mut self, binder: &SuccessVerifyBinderObjectWellDefinedResult) {
        match binder {
            SuccessVerifyBinderObjectWellDefinedResult::SetBuilder(set_builder) => {
                self.collect_from_object(&set_builder.parameter_carrier.result);
                self.collect_from_binder_premise(&set_builder.parameter);
                for condition in &set_builder.conditions {
                    self.collect_from_fact_well_definedness(&condition.well_definedness.proof);
                }
            }
            SuccessVerifyBinderObjectWellDefinedResult::FunctionSet(function_set) => {
                for carrier in &function_set.parameter_carriers {
                    self.collect_from_object(&carrier.result);
                }
                for parameter in &function_set.parameters {
                    self.collect_from_binder_premise(parameter);
                }
                for domain in &function_set.domains {
                    self.collect_from_binder_premise(domain);
                }
                self.collect_from_object(&function_set.return_carrier.result);
            }
            SuccessVerifyBinderObjectWellDefinedResult::AnonymousFunction(function) => {
                for carrier in &function.parameter_carriers {
                    self.collect_from_object(&carrier.result);
                }
                for parameter in &function.parameters {
                    self.collect_from_binder_premise(parameter);
                }
                for domain in &function.domains {
                    self.collect_from_binder_premise(domain);
                }
                self.collect_from_object(&function.return_carrier.result);
                self.collect_from_object(&function.body.result);
            }
            SuccessVerifyBinderObjectWellDefinedResult::Iteration(iteration) => {
                self.collect_from_iteration_interval(&iteration.interval);
                if let Some(scalar_return) = &iteration.scalar_return {
                    self.collect_from_iteration_scalar_return(scalar_return);
                }
            }
            SuccessVerifyBinderObjectWellDefinedResult::FiniteAggregate(aggregate) => {
                if let Some(scalar_return) = &aggregate.scalar_return {
                    self.collect_from_iteration_scalar_return(scalar_return);
                }
                self.collect_from_finite_aggregate_mode(&aggregate.mode);
            }
            SuccessVerifyBinderObjectWellDefinedResult::Reduce(reduce) => {
                self.collect_from_fact_for_object(&reduce.seed_membership);
                if let Some(laws) = &reduce.operation_laws {
                    self.collect_from_object(&laws.parameter_carrier.result);
                    for parameter in &laws.parameters {
                        self.collect_from_binder_premise(parameter);
                    }
                    self.collect_from_fact_for_object(&laws.associativity);
                    self.collect_from_fact_for_object(&laws.commutativity);
                }
                self.collect_from_reduce_mode(&reduce.mode);
            }
            SuccessVerifyBinderObjectWellDefinedResult::Structure(structure) => {
                for argument in &structure.header_arguments {
                    self.collect_from_fact_for_object(&argument.verification);
                }
                for domain in &structure.header_domains {
                    self.collect_from_fact_for_object(domain);
                }
                for field in &structure.fields {
                    self.collect_from_object(&field.carrier.result);
                    self.collect_from_binder_premise(&field.premise);
                }
                for equivalent in &structure.equivalent_facts {
                    self.collect_from_fact_well_definedness(&equivalent.well_definedness.proof);
                }
            }
        }
    }

    fn collect_from_binder_premise(&mut self, premise: &SuccessVerifyBinderPremiseResult) {
        self.collect_from_fact_well_definedness(&premise.well_definedness.proof);
    }

    fn collect_from_fact_for_object(&mut self, fact: &SuccessVerifyFactForObjWellDefinedResult) {
        self.collect_from_truth_proof(&fact.verification);
    }

    fn collect_from_truth_proof(&mut self, proof: &SuccessFactProofNode) {
        match proof.proof() {
            SuccessFactProofResult::BuiltinRule(result)
            | SuccessFactProofResult::BuiltinStrategy(result) => {
                for subgoal in &result.subgoals {
                    self.collect_from_fact_result(subgoal);
                }
            }
            SuccessFactProofResult::CombinedProofs(result) => {
                if let Some(primary) = &result.primary {
                    self.collect_from_truth_proof(primary);
                }
                for step in &result.steps {
                    self.collect_from_fact_result(step);
                }
            }
            SuccessFactProofResult::ForallProof(result) => {
                for proved in &result.proves {
                    self.collect_from_fact_result(&proved.result);
                }
            }
            SuccessFactProofResult::Transform(result) => {
                self.collect_from_truth_proof(&result.source);
            }
            SuccessFactProofResult::DefinitionReduction(result) => {
                for (_, check) in result
                    .verification
                    .clause_facts
                    .iter()
                    .zip(result.verification.clause_checks.iter())
                {
                    self.collect_from_fact_result(check);
                }
            }
            SuccessFactProofResult::CheckedFunctionDefinitionReduction(result) => {
                self.collect_from_fact_result(&result.verification.reduced_equality);
            }
            SuccessFactProofResult::KnownForallInstantiation(result) => {
                for requirement in &result.requirements {
                    self.collect_from_fact_result(&requirement.result);
                }
            }
            SuccessFactProofResult::StoredFactCitation(_)
            | SuccessFactProofResult::DiagnosticOnly(_)
            | SuccessFactProofResult::Reuse(_) => {}
        }
    }

    fn collect_from_iteration_scalar_return(
        &mut self,
        scalar_return: &SuccessVerifyIterationScalarReturnResult,
    ) {
        for carrier in &scalar_return.parameter_carriers {
            self.collect_from_object(&carrier.result);
        }
        for parameter in &scalar_return.parameters {
            self.collect_from_binder_premise(parameter);
        }
        for domain in &scalar_return.domains {
            self.collect_from_binder_premise(domain);
        }
        self.collect_from_object(&scalar_return.return_carrier.result);
        self.collect_from_fact_for_object(&scalar_return.return_subset);
    }

    fn collect_from_iteration_interval(&mut self, interval: &SuccessVerifyIterationIntervalResult) {
        self.collect_from_iteration_coverage(&interval.coverage);
        for carrier in &interval.parameter_carriers {
            self.collect_from_object(&carrier.result);
        }
        for parameter in &interval.parameters {
            self.collect_from_binder_premise(parameter);
        }
        for domain in &interval.domains {
            self.collect_from_truth_proof(&domain.verification);
        }
        self.collect_from_object(&interval.return_carrier.result);
        if let Some(body) = &interval.body {
            self.collect_from_object(&body.result);
        }
    }

    fn collect_from_iteration_coverage(&mut self, coverage: &SuccessVerifyIterationCoverageResult) {
        match coverage {
            SuccessVerifyIterationCoverageResult::Enumerated(result) => {
                for check in &result.checks {
                    self.collect_from_fact_for_object(check);
                }
            }
            SuccessVerifyIterationCoverageResult::Endpoint(result) => {
                self.collect_from_fact_for_object(&result.check);
            }
            SuccessVerifyIterationCoverageResult::IntervalSubset(result) => {
                self.collect_from_fact_for_object(&result.check);
            }
            SuccessVerifyIterationCoverageResult::UniversalIntegerCarrier(_) => {}
        }
    }

    fn collect_from_finite_aggregate_mode(
        &mut self,
        mode: &SuccessVerifyFiniteAggregateModeResult,
    ) {
        match mode {
            SuccessVerifyFiniteAggregateModeResult::Empty(result) => {
                self.collect_from_fact_for_object(&result.empty_set);
            }
            SuccessVerifyFiniteAggregateModeResult::Elements(result) => {
                for membership in &result.body_memberships {
                    self.collect_from_fact_for_object(membership);
                }
                for application in &result.applications {
                    self.collect_from_object(&application.result);
                }
            }
            SuccessVerifyFiniteAggregateModeResult::ClosedRange(result) => {
                self.collect_from_object(&result.aggregate_dependency.result);
            }
            SuccessVerifyFiniteAggregateModeResult::Symbolic(_) => {}
        }
    }

    fn collect_from_reduce_mode(&mut self, mode: &SuccessVerifyReduceModeResult) {
        match mode {
            SuccessVerifyReduceModeResult::Empty(result) => {
                self.collect_from_fact_for_object(&result.empty_range_or_set);
            }
            SuccessVerifyReduceModeResult::Interval(result) => {
                self.collect_from_iteration_interval(&result.interval);
            }
            SuccessVerifyReduceModeResult::Elements(result) => {
                for membership in &result.body_memberships {
                    self.collect_from_fact_for_object(membership);
                }
                for application in &result.applications {
                    self.collect_from_object(&application.result);
                }
            }
            SuccessVerifyReduceModeResult::Symbolic(result) => {
                self.collect_from_reduce_coverage(&result.coverage);
            }
        }
    }

    fn collect_from_reduce_coverage(
        &mut self,
        coverage: &SuccessVerifyFiniteReduceDomainCoverageResult,
    ) {
        if let SuccessVerifyFiniteReduceDomainCoverageResult::Subset(result) = coverage {
            self.collect_from_fact_for_object(&result.subset);
        }
    }

    fn collect_from_template(&mut self, template: &SuccessTemplateInstantiationResult) {
        let application = match template {
            SuccessTemplateInstantiationResult::Reused(result) => &result.application,
            SuccessTemplateInstantiationResult::Created(result) => &result.application,
        };
        if !self.seen_templates.insert(application.to_string()) {
            return;
        }
        let SuccessTemplateInstantiationResult::Created(created) = template else {
            return;
        };
        self.collect_store(&created.surface_equality);
        for store in &created.public_value_equalities {
            self.collect_store(store);
        }
        for store in &created.supplemental_stores {
            self.collect_store(store);
        }
        if let Some(infers) = created.body_statement_result.environment_effects() {
            for output in &infers.store_fact_outputs {
                self.collect_fact(output.itself_and_why_itself_is_stored.0.clone());
            }
        }
    }

    fn collect_store(&mut self, store: &SuccessStoreFactResult) {
        self.collect_fact(store.fact.clone());
    }

    fn collect_fact(&mut self, fact: Fact) {
        if self.seen_facts.insert(fact.to_string()) {
            self.facts.push(fact);
        }
    }
}

impl Runtime {
    pub fn execute_submitted_fact(&mut self, fact: &Fact) -> Result<StmtResult, RuntimeError> {
        // WD and truth search may store intermediate facts so later recursive
        // calls in this same verification process can cite them. Those stores
        // are proof-local evidence, not mathematical consequences published
        // by the source statement. Freeze their exact FactIds into the
        // returned Result DAG before discarding the temporary Runtime
        // environment; only reusable object-shape knowledge and the
        // submitted fact itself are stored below.
        let ((verification, template_effects), verification_environment) = self
            .run_in_local_env_and_take(|runtime| {
                let mut verification =
                    runtime.verify_fact_or_error(fact, &VerifyState::initial())?;
                runtime.attach_known_fact_ids_to_verify_fact_result(&mut verification)?;
                let mut collector = TemplateSemanticEffectCollector::new();
                collector.collect_from_fact_result(&verification);
                Ok::<_, RuntimeError>((verification, collector.facts))
            })?;
        // Object-shape knowledge learned while checking the fact is a
        // mathematical consequence of the successful verification (for
        // example a template instance's registered set-builder definition).
        // Preserve that knowledge, but deliberately drop the child fact
        // table and inference cache: those are process-local proof stores and
        // are already frozen into `verification` where needed.
        self.top_level_env()
            .merge_committed_object_effects(verification_environment)?;
        // Replay only semantic template effects selected from the retained WD
        // DAG.  Each fact is stored through the ordinary inference path so the
        // parent gets fresh persistent identities and indexes, while the
        // process-local WD/search tables remain discarded.
        let submitted_fact_key = nested_obj_binder_normalized_fact_key(fact);
        for effect in template_effects {
            // The submitted proposition itself must remain an explicit
            // statement store (and retain that statement's FactId).  A
            // template body may contain the same proposition under a
            // capture-avoiding binder renaming; let the statement store it
            // below instead of turning it into an already-cached zero-output
            // store result.
            if nested_obj_binder_normalized_fact_key(&effect) == submitted_fact_key {
                continue;
            }
            self.store_without_well_defined_verification_and_infer_with_reason(
                effect,
                InferReason::StoredFact,
            )?;
        }
        let VerifyFactResult::Verified(verification) = verification else {
            unreachable!("verify_fact_or_error cannot return an unknown fact")
        };
        let infer_result = self.store_without_well_defined_verification_and_infer(fact.clone())?;
        let mut store = SuccessStoreFactResult::new(fact.clone(), infer_result);
        store.fact_id = Some(fact.fact_id());
        Ok(SuccessFactStmtResult::verified(verification, store).into())
    }

    pub fn execute_fact_with_trust(&mut self, fact: &Fact) -> Result<StmtResult, RuntimeError> {
        let infer_result = self.store_fact_with_trust_and_infer_with_reason(
            fact.clone(),
            InferReason::StatementWithVerification,
        )?;

        Ok(SuccessFactStmtResult::trusted(fact.clone(), infer_result).into())
    }
}
