use crate::prelude::*;
use std::fmt;
use std::rc::Rc;

/// Successful output of checking one object for well-definedness.
/// Direct checks own their recursively returned children; cache hits retain
/// the current source occurrence and cite the exact earlier proof node.
#[derive(Debug)]
pub enum SuccessVerifyObjWellDefinedResult {
    Direct(Box<SuccessVerifyDirectObjWellDefinedResult>),
    Reuse(Box<SuccessReuseObjWellDefinedResult>),
    RecursiveReference(Box<SuccessRecursiveObjWellDefinedResult>),
}

pub struct SuccessVerifyDirectObjWellDefinedResult {
    pub object: Obj,
    pub cache_key: WellDefinedCacheKey,
    pub steps: SuccessVerifyObjWellDefinedStepsResult,
    pub intrinsic_result_set: Option<Obj>,
}

impl SuccessVerifyDirectObjWellDefinedResult {
    pub fn new(
        object: Obj,
        cache_key: WellDefinedCacheKey,
        steps: SuccessVerifyObjWellDefinedStepsResult,
        intrinsic_result_set: Option<Obj>,
    ) -> Self {
        Self {
            object,
            cache_key,
            steps,
            intrinsic_result_set,
        }
    }
}

pub struct SuccessReuseObjWellDefinedResult {
    pub object: Obj,
    pub source: Rc<SuccessVerifyObjWellDefinedResult>,
}

impl SuccessReuseObjWellDefinedResult {
    pub fn new(object: Obj, source: Rc<SuccessVerifyObjWellDefinedResult>) -> Self {
        Self { object, source }
    }
}

/// Historical recursive re-entry suppression made explicit in the result.
/// A validator accepts it only below an ancestor with the same object key.
pub struct SuccessRecursiveObjWellDefinedResult {
    pub object: Obj,
    pub ancestor_key: ObjString,
}

impl SuccessRecursiveObjWellDefinedResult {
    pub fn new(object: Obj, ancestor_key: ObjString) -> Self {
        Self {
            object,
            ancestor_key,
        }
    }
}

/// Ordered semantic outputs produced by one constructor-specific WD check.
#[derive(Debug, Default)]
pub struct SuccessVerifyObjWellDefinedStepsResult {
    pub children: Vec<SuccessVerifyChildObjWellDefinedResult>,
    pub fact_checks: Vec<SuccessVerifyFactForObjWellDefinedResult>,
    pub target_requirements: Vec<SuccessVerifyObjTargetRequirementResult>,
    pub stores: Vec<SuccessStoreFactResult>,
    pub binder: Option<Box<SuccessVerifyBinderObjectWellDefinedResult>>,
    pub template_materialization: Option<Box<SuccessVerifyTemplateMaterializationResult>>,
}

impl SuccessVerifyObjWellDefinedStepsResult {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn push_child(&mut self, child: SuccessVerifyChildObjWellDefinedResult) {
        self.children.push(child);
    }

    pub fn push_fact_check(&mut self, check: SuccessVerifyFactForObjWellDefinedResult) {
        self.fact_checks.push(check);
    }

    pub fn push_target_requirement(
        &mut self,
        requirement: SuccessVerifyObjTargetRequirementResult,
    ) {
        self.target_requirements.push(requirement);
    }

    pub fn push_store(&mut self, store: SuccessStoreFactResult) {
        self.stores.push(store);
    }

    pub fn append(&mut self, mut other: Self) {
        self.children.append(&mut other.children);
        self.fact_checks.append(&mut other.fact_checks);
        self.target_requirements
            .append(&mut other.target_requirements);
        self.stores.append(&mut other.stores);
        if self.binder.is_none() {
            self.binder = other.binder;
        }
        if self.template_materialization.is_none() {
            self.template_materialization = other.template_materialization;
        }
    }
}

pub struct SuccessVerifyChildObjWellDefinedResult {
    pub role: WellDefinedObjChildRole,
    pub source_object: Obj,
    pub result: Rc<SuccessVerifyObjWellDefinedResult>,
}

impl SuccessVerifyChildObjWellDefinedResult {
    pub fn new(
        role: WellDefinedObjChildRole,
        source_object: Obj,
        result: Rc<SuccessVerifyObjWellDefinedResult>,
    ) -> Self {
        Self {
            role,
            source_object,
            result,
        }
    }
}

#[derive(Debug)]
pub struct SuccessVerifyFactForObjWellDefinedResult {
    pub expected_proposition: Fact,
    pub verification: Rc<SuccessVerifyFactResult>,
}

impl SuccessVerifyFactForObjWellDefinedResult {
    pub fn new(expected_proposition: Fact, verification: Rc<SuccessVerifyFactResult>) -> Self {
        Self {
            expected_proposition,
            verification,
        }
    }
}

pub struct SuccessVerifyObjTargetRequirementResult {
    pub source_object: Obj,
    pub role: WellDefinednessRequirementRole,
    pub expected_proposition: Fact,
    pub verification: Rc<SuccessVerifyFactResult>,
}

impl SuccessVerifyObjTargetRequirementResult {
    pub fn new(
        source_object: Obj,
        role: WellDefinednessRequirementRole,
        expected_proposition: Fact,
        verification: Rc<SuccessVerifyFactResult>,
    ) -> Self {
        Self {
            source_object,
            role,
            expected_proposition,
            verification,
        }
    }
}

#[derive(Debug)]
pub enum SuccessVerifyBinderObjectWellDefinedResult {
    SetBuilder(Box<SuccessVerifySetBuilderWellDefinedResult>),
    FunctionSet(Box<SuccessVerifyFunctionSetWellDefinedResult>),
    AnonymousFunction(Box<SuccessVerifyAnonymousFunctionWellDefinedResult>),
    Iteration(Box<SuccessVerifyIterationWellDefinedResult>),
    FiniteAggregate(Box<SuccessVerifyFiniteAggregateWellDefinedResult>),
    Reduce(Box<SuccessVerifyReduceWellDefinedResult>),
    Structure(Box<SuccessVerifyStructureWellDefinedResult>),
}

#[derive(Debug)]
pub struct SuccessVerifyBinderPremiseResult {
    pub role: WellDefinedBinderPremiseRole,
    pub symbol_id: Option<SymbolId>,
    pub proposition: Fact,
    pub well_definedness: Box<SuccessVerifyFactWellDefinedResult>,
    pub infers: SuccessInferResult,
}

impl SuccessVerifyBinderPremiseResult {
    pub fn new(
        role: WellDefinedBinderPremiseRole,
        symbol_id: Option<SymbolId>,
        proposition: Fact,
        well_definedness: SuccessVerifyFactWellDefinedResult,
        infers: SuccessInferResult,
    ) -> Self {
        Self {
            role,
            symbol_id,
            proposition,
            well_definedness: Box::new(well_definedness),
            infers,
        }
    }
}

#[derive(Debug)]
pub struct SuccessVerifySetBuilderConditionResult {
    pub condition_index: usize,
    pub well_definedness: Box<SuccessVerifyFactWellDefinedResult>,
    pub store: SuccessStoreFactResult,
}

impl SuccessVerifySetBuilderConditionResult {
    pub fn new(
        condition_index: usize,
        well_definedness: SuccessVerifyFactWellDefinedResult,
        store: SuccessStoreFactResult,
    ) -> Self {
        Self {
            condition_index,
            well_definedness: Box::new(well_definedness),
            store,
        }
    }
}

#[derive(Debug)]
pub struct SuccessVerifySetBuilderWellDefinedResult {
    pub parameter_carrier: SuccessVerifyChildObjWellDefinedResult,
    pub parameter: SuccessVerifyBinderPremiseResult,
    pub conditions: Vec<SuccessVerifySetBuilderConditionResult>,
}

#[derive(Debug)]
pub struct SuccessVerifyFunctionSetWellDefinedResult {
    pub parameter_carriers: Vec<SuccessVerifyChildObjWellDefinedResult>,
    pub parameters: Vec<SuccessVerifyBinderPremiseResult>,
    pub domains: Vec<SuccessVerifyBinderPremiseResult>,
    pub return_carrier: SuccessVerifyChildObjWellDefinedResult,
}

#[derive(Debug)]
pub struct SuccessVerifyAnonymousFunctionWellDefinedResult {
    pub parameter_carriers: Vec<SuccessVerifyChildObjWellDefinedResult>,
    pub parameters: Vec<SuccessVerifyBinderPremiseResult>,
    pub domains: Vec<SuccessVerifyBinderPremiseResult>,
    pub return_carrier: SuccessVerifyChildObjWellDefinedResult,
    pub body: SuccessVerifyChildObjWellDefinedResult,
    pub body_membership: SuccessVerifyObjTargetRequirementResult,
}

#[derive(Debug)]
pub struct SuccessVerifyIterationWellDefinedResult {
    pub operation: String,
    pub scalar_return: Option<Box<SuccessVerifyIterationScalarReturnResult>>,
    pub interval: Box<SuccessVerifyIterationIntervalResult>,
}

#[derive(Debug)]
pub struct SuccessVerifyIterationScalarReturnResult {
    pub parameter_carriers: Vec<SuccessVerifyChildObjWellDefinedResult>,
    pub parameters: Vec<SuccessVerifyBinderPremiseResult>,
    pub domains: Vec<SuccessVerifyBinderPremiseResult>,
    pub return_carrier: SuccessVerifyChildObjWellDefinedResult,
    pub return_subset: SuccessVerifyFactForObjWellDefinedResult,
}

#[derive(Debug)]
pub enum SuccessVerifyIterationCoverageResult {
    UniversalIntegerCarrier(Box<SuccessVerifyUniversalIntegerCarrierCoverageResult>),
    Enumerated(Box<SuccessVerifyEnumeratedIterationCoverageResult>),
    Endpoint(Box<SuccessVerifyEndpointIterationCoverageResult>),
    IntervalSubset(Box<SuccessVerifyIntervalSubsetCoverageResult>),
}

pub struct SuccessVerifyUniversalIntegerCarrierCoverageResult {
    pub parameter_set: Obj,
}

#[derive(Debug)]
pub struct SuccessVerifyEnumeratedIterationCoverageResult {
    pub checks: Vec<SuccessVerifyFactForObjWellDefinedResult>,
}

#[derive(Debug)]
pub struct SuccessVerifyEndpointIterationCoverageResult {
    pub check: SuccessVerifyFactForObjWellDefinedResult,
}

#[derive(Debug)]
pub struct SuccessVerifyIntervalSubsetCoverageResult {
    pub check: SuccessVerifyFactForObjWellDefinedResult,
}

#[derive(Debug)]
pub struct SuccessVerifyIterationDomainResult {
    pub proposition: Fact,
    pub verification: Rc<SuccessVerifyFactResult>,
    pub store: SuccessStoreFactResult,
}

pub struct SuccessVerifyIterationIntervalResult {
    pub parameter_set: Obj,
    pub coverage: SuccessVerifyIterationCoverageResult,
    pub parameter_carriers: Vec<SuccessVerifyChildObjWellDefinedResult>,
    pub parameters: Vec<SuccessVerifyBinderPremiseResult>,
    pub lower_bound: SuccessStoreFactResult,
    pub upper_bound: SuccessStoreFactResult,
    pub domains: Vec<SuccessVerifyIterationDomainResult>,
    pub return_carrier: SuccessVerifyChildObjWellDefinedResult,
    pub body: Option<SuccessVerifyChildObjWellDefinedResult>,
    pub body_membership: Option<SuccessVerifyObjTargetRequirementResult>,
}

impl fmt::Debug for SuccessVerifyUniversalIntegerCarrierCoverageResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyUniversalIntegerCarrierCoverageResult")
            .field("parameter_set", &self.parameter_set.to_string())
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyIterationIntervalResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyIterationIntervalResult")
            .field("parameter_set", &self.parameter_set.to_string())
            .field("coverage", &self.coverage)
            .field("parameter_carriers", &self.parameter_carriers)
            .field("parameters", &self.parameters)
            .field("lower_bound", &self.lower_bound)
            .field("upper_bound", &self.upper_bound)
            .field("domains", &self.domains)
            .field("return_carrier", &self.return_carrier)
            .field("body", &self.body)
            .field("body_membership", &self.body_membership)
            .finish()
    }
}

#[derive(Debug)]
pub struct SuccessVerifyFiniteAggregateWellDefinedResult {
    pub operation: String,
    pub scalar_return: Option<Box<SuccessVerifyIterationScalarReturnResult>>,
    pub mode: SuccessVerifyFiniteAggregateModeResult,
}

#[derive(Debug)]
pub enum SuccessVerifyFiniteAggregateModeResult {
    Empty(Box<SuccessVerifyEmptyFiniteAggregateResult>),
    Elements(Box<SuccessVerifyFiniteAggregateElementsResult>),
    ClosedRange(Box<SuccessVerifyFiniteAggregateClosedRangeResult>),
    Symbolic(Box<SuccessVerifySymbolicFiniteAggregateResult>),
}

#[derive(Debug)]
pub struct SuccessVerifyEmptyFiniteAggregateResult {
    pub empty_set: SuccessVerifyFactForObjWellDefinedResult,
}

#[derive(Debug)]
pub struct SuccessVerifyFiniteAggregateElementsResult {
    pub body_memberships: Vec<SuccessVerifyFactForObjWellDefinedResult>,
    pub applications: Vec<SuccessVerifyChildObjWellDefinedResult>,
}

#[derive(Debug)]
pub struct SuccessVerifyFiniteAggregateClosedRangeResult {
    pub aggregate_dependency: SuccessVerifyChildObjWellDefinedResult,
}

pub struct SuccessVerifySymbolicFiniteAggregateResult {
    pub exact_domain: Obj,
}

pub struct SuccessVerifyReduceWellDefinedResult {
    pub operation: String,
    pub signature: SuccessVerifyReduceOperationSignatureResult,
    pub iterand_return_carrier: Obj,
    pub seed_membership: SuccessVerifyFactForObjWellDefinedResult,
    pub operation_laws: Option<Box<SuccessVerifyFiniteReduceOperationLawsResult>>,
    pub mode: SuccessVerifyReduceModeResult,
}

pub struct SuccessVerifyReduceOperationSignatureResult {
    pub left_parameter_carrier: Obj,
    pub right_parameter_carrier: Obj,
    pub return_carrier: Obj,
}

#[derive(Debug)]
pub enum SuccessVerifyReduceModeResult {
    Empty(Box<SuccessVerifyEmptyReduceResult>),
    Interval(Box<SuccessVerifyIntervalReduceResult>),
    Elements(Box<SuccessVerifyElementwiseReduceResult>),
    Symbolic(Box<SuccessVerifySymbolicReduceResult>),
}

#[derive(Debug)]
pub struct SuccessVerifyEmptyReduceResult {
    pub empty_range_or_set: SuccessVerifyFactForObjWellDefinedResult,
}

#[derive(Debug)]
pub struct SuccessVerifyIntervalReduceResult {
    pub interval: Box<SuccessVerifyIterationIntervalResult>,
}

#[derive(Debug)]
pub struct SuccessVerifyElementwiseReduceResult {
    pub body_memberships: Vec<SuccessVerifyFactForObjWellDefinedResult>,
    pub applications: Vec<SuccessVerifyChildObjWellDefinedResult>,
}

#[derive(Debug)]
pub struct SuccessVerifySymbolicReduceResult {
    pub coverage: SuccessVerifyFiniteReduceDomainCoverageResult,
}

#[derive(Debug)]
pub enum SuccessVerifyFiniteReduceDomainCoverageResult {
    Exact(Box<SuccessVerifyExactFiniteReduceDomainResult>),
    Subset(Box<SuccessVerifySubsetFiniteReduceDomainResult>),
}

pub struct SuccessVerifyExactFiniteReduceDomainResult {
    pub aggregate_set: Obj,
    pub iterand_domain: Obj,
}

pub struct SuccessVerifySubsetFiniteReduceDomainResult {
    pub aggregate_set: Obj,
    pub iterand_domain: Obj,
    pub subset: SuccessVerifyFactForObjWellDefinedResult,
}

#[derive(Debug)]
pub struct SuccessVerifyFiniteReduceOperationLawsResult {
    pub parameter_carrier: SuccessVerifyChildObjWellDefinedResult,
    pub parameters: Vec<SuccessVerifyBinderPremiseResult>,
    pub associativity: SuccessVerifyFactForObjWellDefinedResult,
    pub commutativity: SuccessVerifyFactForObjWellDefinedResult,
}

pub struct SuccessVerifyStructureWellDefinedResult {
    pub structure_name: String,
    pub header_arguments: Vec<SuccessVerifyStructureHeaderArgumentResult>,
    pub header_domains: Vec<SuccessVerifyFactForObjWellDefinedResult>,
    pub fields: Vec<SuccessVerifyStructureFieldResult>,
    pub equivalent_facts: Vec<SuccessVerifyStructureEquivalentFactResult>,
}

pub struct SuccessVerifyStructureHeaderArgumentResult {
    pub argument_index: usize,
    pub argument: Obj,
    pub expected_type: ParamType,
    pub verification: SuccessVerifyFactForObjWellDefinedResult,
}

#[derive(Debug)]
pub struct SuccessVerifyStructureFieldResult {
    pub field_index: usize,
    pub field_name: String,
    pub carrier: SuccessVerifyChildObjWellDefinedResult,
    pub premise: SuccessVerifyBinderPremiseResult,
}

#[derive(Debug)]
pub struct SuccessVerifyStructureEquivalentFactResult {
    pub fact_index: usize,
    pub proposition: Fact,
    pub well_definedness: Box<SuccessVerifyFactWellDefinedResult>,
    pub store: SuccessStoreFactResult,
}

#[derive(Debug)]
pub enum SuccessVerifyTemplateMaterializationResult {
    Reuse(Box<SuccessReuseTemplateMaterializationResult>),
    Materialized(Box<SuccessMaterializedTemplateResult>),
}

#[derive(Debug)]
pub struct SuccessReuseTemplateMaterializationResult {
    pub instance_name: String,
}

pub struct SuccessMaterializedTemplateResult {
    pub template_name: String,
    pub instance_name: String,
    pub header_arguments: Vec<SuccessVerifyTemplateHeaderArgumentResult>,
    pub header_domains: Vec<SuccessVerifyTemplateDomainResult>,
    pub surface_equality: SuccessStoreFactResult,
    pub body_statement: Stmt,
    pub body_execution: Box<StmtResult>,
    pub public_value_equalities: Vec<SuccessStoreFactResult>,
    pub supplemental_stores: Vec<SuccessStoreFactResult>,
    pub registered_set_builder: Option<SetBuilder>,
}

pub struct SuccessVerifyTemplateHeaderArgumentResult {
    pub argument_index: usize,
    pub argument: Obj,
    pub expected_type: ParamType,
    pub verification: SuccessVerifyFactForObjWellDefinedResult,
}

#[derive(Debug)]
pub struct SuccessVerifyTemplateDomainResult {
    pub domain_index: usize,
    pub proof: SuccessVerifyFactForObjWellDefinedResult,
    pub store: SuccessStoreFactResult,
}

impl fmt::Debug for SuccessVerifySymbolicFiniteAggregateResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifySymbolicFiniteAggregateResult")
            .field("exact_domain", &self.exact_domain.to_string())
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyReduceWellDefinedResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyReduceWellDefinedResult")
            .field("operation", &self.operation)
            .field("signature", &self.signature)
            .field(
                "iterand_return_carrier",
                &self.iterand_return_carrier.to_string(),
            )
            .field("seed_membership", &self.seed_membership)
            .field("operation_laws", &self.operation_laws)
            .field("mode", &self.mode)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyReduceOperationSignatureResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyReduceOperationSignatureResult")
            .field(
                "left_parameter_carrier",
                &self.left_parameter_carrier.to_string(),
            )
            .field(
                "right_parameter_carrier",
                &self.right_parameter_carrier.to_string(),
            )
            .field("return_carrier", &self.return_carrier.to_string())
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyExactFiniteReduceDomainResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyExactFiniteReduceDomainResult")
            .field("aggregate_set", &self.aggregate_set.to_string())
            .field("iterand_domain", &self.iterand_domain.to_string())
            .finish()
    }
}

impl fmt::Debug for SuccessVerifySubsetFiniteReduceDomainResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifySubsetFiniteReduceDomainResult")
            .field("aggregate_set", &self.aggregate_set.to_string())
            .field("iterand_domain", &self.iterand_domain.to_string())
            .field("subset", &self.subset)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyStructureWellDefinedResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyStructureWellDefinedResult")
            .field("structure_name", &self.structure_name)
            .field("header_arguments", &self.header_arguments)
            .field("header_domains", &self.header_domains)
            .field("fields", &self.fields)
            .field("equivalent_facts", &self.equivalent_facts)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyStructureHeaderArgumentResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyStructureHeaderArgumentResult")
            .field("argument_index", &self.argument_index)
            .field("argument", &self.argument.to_string())
            .field("expected_type", &self.expected_type.to_string())
            .field("verification", &self.verification)
            .finish()
    }
}

impl fmt::Debug for SuccessMaterializedTemplateResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessMaterializedTemplateResult")
            .field("template_name", &self.template_name)
            .field("instance_name", &self.instance_name)
            .field("header_arguments", &self.header_arguments)
            .field("header_domains", &self.header_domains)
            .field("surface_equality", &self.surface_equality)
            .field("body_statement", &self.body_statement.to_string())
            .field("body_execution", &self.body_execution)
            .field("public_value_equalities", &self.public_value_equalities)
            .field("supplemental_stores", &self.supplemental_stores)
            .field(
                "registered_set_builder",
                &self
                    .registered_set_builder
                    .as_ref()
                    .map(ToString::to_string),
            )
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyTemplateHeaderArgumentResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyTemplateHeaderArgumentResult")
            .field("argument_index", &self.argument_index)
            .field("argument", &self.argument.to_string())
            .field("expected_type", &self.expected_type.to_string())
            .field("verification", &self.verification)
            .finish()
    }
}

impl SuccessVerifyObjWellDefinedResult {
    pub fn object(&self) -> &Obj {
        match self {
            Self::Direct(result) => &result.object,
            Self::Reuse(result) => &result.object,
            Self::RecursiveReference(result) => &result.object,
        }
    }
}

impl fmt::Debug for SuccessVerifyDirectObjWellDefinedResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyDirectObjWellDefinedResult")
            .field("object", &self.object.to_string())
            .field("cache_key", &self.cache_key)
            .field("steps", &self.steps)
            .field(
                "intrinsic_result_set",
                &self.intrinsic_result_set.as_ref().map(ToString::to_string),
            )
            .finish()
    }
}

impl fmt::Debug for SuccessReuseObjWellDefinedResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessReuseObjWellDefinedResult")
            .field("object", &self.object.to_string())
            .field("source", &self.source)
            .finish()
    }
}

impl fmt::Debug for SuccessRecursiveObjWellDefinedResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessRecursiveObjWellDefinedResult")
            .field("object", &self.object.to_string())
            .field("ancestor_key", &self.ancestor_key)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyChildObjWellDefinedResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyChildObjWellDefinedResult")
            .field("role", &self.role)
            .field("source_object", &self.source_object.to_string())
            .field("result", &self.result)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyObjTargetRequirementResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyObjTargetRequirementResult")
            .field("source_object", &self.source_object.to_string())
            .field("role", &self.role)
            .field(
                "expected_proposition",
                &self.expected_proposition.to_string(),
            )
            .field("verification", &self.verification)
            .finish()
    }
}

#[derive(Debug)]
pub enum SuccessVerifyFactWellDefinedProofResult {
    AtomicFact(Box<SuccessVerifyAtomicFactWellDefinedResult>),
    AndFact(Box<SuccessVerifyAndFactWellDefinedResult>),
    ChainFact(Box<SuccessVerifyChainFactWellDefinedResult>),
    OrFact(Box<SuccessVerifyOrFactWellDefinedResult>),
    ExistFact(Box<SuccessVerifyExistFactWellDefinedResult>),
    ForallFact(Box<SuccessVerifyForallFactWellDefinedResult>),
    ForallFactWithIff(Box<SuccessVerifyForallFactWithIffWellDefinedResult>),
    NotForallFact(Box<SuccessVerifyNotForallFactWellDefinedResult>),
}

pub struct SuccessVerifyFactObjectWellDefinedResult {
    pub argument_index: usize,
    pub source_object: Obj,
    pub result: Rc<SuccessVerifyObjWellDefinedResult>,
}

impl SuccessVerifyFactObjectWellDefinedResult {
    pub fn new(
        argument_index: usize,
        source_object: Obj,
        result: Rc<SuccessVerifyObjWellDefinedResult>,
    ) -> Self {
        Self {
            argument_index,
            source_object,
            result,
        }
    }
}

impl fmt::Debug for SuccessVerifyFactObjectWellDefinedResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyFactObjectWellDefinedResult")
            .field("argument_index", &self.argument_index)
            .field("source_object", &self.source_object.to_string())
            .field("result", &self.result)
            .finish()
    }
}

pub struct SuccessVerifyAtomicFactWellDefinedResult {
    pub statement: AtomicFact,
    pub arguments: Vec<SuccessVerifyFactObjectWellDefinedResult>,
    pub predicate: SuccessVerifyAtomicPredicateWellDefinedResult,
}

impl SuccessVerifyAtomicFactWellDefinedResult {
    pub fn new(
        statement: AtomicFact,
        arguments: Vec<SuccessVerifyFactObjectWellDefinedResult>,
        predicate: SuccessVerifyAtomicPredicateWellDefinedResult,
    ) -> Self {
        Self {
            statement,
            arguments,
            predicate,
        }
    }
}

pub struct SuccessVerifyAtomicPredicateWellDefinedResult {
    pub name: String,
    pub expected_arity: usize,
    pub domain_checks: Vec<SuccessVerifyAtomicPredicateDomainCheckResult>,
}

pub struct SuccessVerifyAtomicPredicateDomainCheckResult {
    pub role: AtomicPredicateDomainCheckRole,
    pub result: Box<StmtResult>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AtomicPredicateDomainCheckRole {
    ChoiceFunctionIndexSet,
    ChoiceFunctionFamilySet,
    ChoiceFunctionFamily,
    ChoiceFunctionMember,
    PrimeNaturalArgument,
    CoprimeNaturalArgument,
    DivisibilityIntegerArgument,
    DivisibilityNonzeroIntegerArgument,
    OrderedRealCarrierEvidence,
    FunctionPropertySignature,
}

pub struct SuccessVerifyAndFactWellDefinedResult {
    pub statement: AndFact,
    pub conjuncts: Vec<SuccessVerifyFactWellDefinedProofResult>,
}

pub struct SuccessVerifyChainFactWellDefinedResult {
    pub statement: ChainFact,
    pub comparisons: Vec<SuccessVerifyFactWellDefinedProofResult>,
}

pub struct SuccessVerifyOrFactWellDefinedResult {
    pub statement: OrFact,
    pub branches: Vec<SuccessVerifyFactWellDefinedProofResult>,
}

pub struct SuccessVerifyExistFactWellDefinedResult {
    pub statement: ExistFactEnum,
    pub binder: SuccessVerifyFactBinderResult,
    pub body: Vec<SuccessVerifyLocalFactWellDefinedResult>,
}

pub struct SuccessVerifyForallFactWellDefinedResult {
    pub statement: ForallFact,
    pub binder: SuccessVerifyFactBinderResult,
    pub premises: Vec<SuccessVerifyLocalFactWellDefinedResult>,
    pub conclusions: Vec<SuccessVerifyLocalFactWellDefinedResult>,
}

pub struct SuccessVerifyFactBinderResult {
    pub parameter_groups: Vec<SuccessVerifyFactParameterGroupResult>,
}

pub struct SuccessVerifyFactParameterGroupResult {
    pub group_index: usize,
    pub parameter_type: ParamType,
    pub carrier: Option<SuccessVerifyChildObjWellDefinedResult>,
    pub parameters: Vec<SuccessVerifyBinderPremiseResult>,
}

pub struct SuccessVerifyLocalFactWellDefinedResult {
    pub proposition: Fact,
    pub well_definedness: Box<SuccessVerifyFactWellDefinedProofResult>,
    pub store: SuccessStoreFactResult,
}

pub struct SuccessVerifyForallFactWithIffWellDefinedResult {
    pub statement: ForallFactWithIff,
    pub forward: Box<SuccessVerifyFactWellDefinedProofResult>,
    pub reverse: Box<SuccessVerifyFactWellDefinedProofResult>,
}

pub struct SuccessVerifyNotForallFactWellDefinedResult {
    pub statement: NotForallFact,
    pub inner: Box<SuccessVerifyFactWellDefinedProofResult>,
}

impl fmt::Debug for SuccessVerifyAtomicFactWellDefinedResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyAtomicFactWellDefinedResult")
            .field("statement", &self.statement.to_string())
            .field("arguments", &self.arguments)
            .field("predicate", &self.predicate)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyAtomicPredicateWellDefinedResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyAtomicPredicateWellDefinedResult")
            .field("name", &self.name)
            .field("expected_arity", &self.expected_arity)
            .field("domain_checks", &self.domain_checks)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyAtomicPredicateDomainCheckResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyAtomicPredicateDomainCheckResult")
            .field("role", &self.role)
            .field("result", &self.result)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyAndFactWellDefinedResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyAndFactWellDefinedResult")
            .field("statement", &self.statement.to_string())
            .field("conjuncts", &self.conjuncts)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyChainFactWellDefinedResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyChainFactWellDefinedResult")
            .field("statement", &self.statement.to_string())
            .field("comparisons", &self.comparisons)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyOrFactWellDefinedResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyOrFactWellDefinedResult")
            .field("statement", &self.statement.to_string())
            .field("branches", &self.branches)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyExistFactWellDefinedResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyExistFactWellDefinedResult")
            .field("statement", &self.statement.to_string())
            .field("binder", &self.binder)
            .field("body", &self.body)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyForallFactWellDefinedResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyForallFactWellDefinedResult")
            .field("statement", &self.statement.to_string())
            .field("binder", &self.binder)
            .field("premises", &self.premises)
            .field("conclusions", &self.conclusions)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyFactBinderResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyFactBinderResult")
            .field("parameter_groups", &self.parameter_groups)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyFactParameterGroupResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyFactParameterGroupResult")
            .field("group_index", &self.group_index)
            .field("parameter_type", &self.parameter_type.to_string())
            .field("carrier", &self.carrier)
            .field("parameters", &self.parameters)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyLocalFactWellDefinedResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyLocalFactWellDefinedResult")
            .field("proposition", &self.proposition.to_string())
            .field("well_definedness", &self.well_definedness)
            .field("store", &self.store)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyForallFactWithIffWellDefinedResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyForallFactWithIffWellDefinedResult")
            .field("statement", &self.statement.to_string())
            .field("forward", &self.forward)
            .field("reverse", &self.reverse)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyNotForallFactWellDefinedResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyNotForallFactWellDefinedResult")
            .field("statement", &self.statement.to_string())
            .field("inner", &self.inner)
            .finish()
    }
}
