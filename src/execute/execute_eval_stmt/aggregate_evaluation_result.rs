use crate::ast::obj::Obj;
use crate::execute::execute_fact_stmt::ObjWellDefinedProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::by_have_fn_equal::AnonFnApplicationBodyProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::KnownEqualityPathProof;
use crate::runtime::FactId;

// Four scalar aggregation branches have separate success results. The shared
// fold records every argument, checked application, beta expansion and value.
pub enum AggregateEvaluationResult {
    Sum(RangeSumEvaluationResult),
    SumOfFiniteSet(FiniteSetSumEvaluationResult),
    Product(RangeProductEvaluationResult),
    ProductOfFiniteSet(FiniteSetProductEvaluationResult),
    Reduce(RangeReduceEvaluationResult),
    FiniteSetReduce(FiniteSetReduceEvaluationResult),
}

pub struct FiniteSetReduceEvaluationResult {
    pub source:Obj,
    pub enumeration:FiniteSetEnumerationResult,
    pub seed:Obj,
    pub terms:Vec<ReduceTermEvaluationResult>,
    pub value:Obj,
}

pub struct RangeReduceEvaluationResult {
    pub source: Obj,
    pub bounds: AggregateRangeBoundsResult,
    pub seed: Obj,
    pub terms: Vec<ReduceTermEvaluationResult>,
    pub value: Obj,
}
pub struct ReduceTermEvaluationResult {
    pub argument: Obj,
    pub term: FunctionApplicationEvaluationResult,
    pub operation: FunctionApplicationEvaluationResult,
    pub accumulated_value: Obj,
}

pub struct RangeSumEvaluationResult {
    pub source: Obj,
    pub bounds: AggregateRangeBoundsResult,
    pub terms: Vec<AggregateTermEvaluationResult>,
    pub value: Obj,
}
pub struct RangeProductEvaluationResult {
    pub source: Obj,
    pub bounds: AggregateRangeBoundsResult,
    pub terms: Vec<AggregateTermEvaluationResult>,
    pub value: Obj,
}
pub struct FiniteSetSumEvaluationResult {
    pub source: Obj,
    pub enumeration: FiniteSetEnumerationResult,
    pub terms: Vec<AggregateTermEvaluationResult>,
    pub value: Obj,
}
pub struct FiniteSetProductEvaluationResult {
    pub source: Obj,
    pub enumeration: FiniteSetEnumerationResult,
    pub terms: Vec<AggregateTermEvaluationResult>,
    pub value: Obj,
}
pub struct AggregateRangeBoundsResult {
    pub start: Obj,
    pub end: Obj,
    pub cited_equal_fact_ids: Vec<FactId>,
    pub start_integer: i128,
    pub end_integer: i128,
}
pub struct FiniteSetEnumerationResult {
    pub set_equality: KnownEqualityPathProof,
    pub resolved_set: Obj,
    pub cited_equal_fact_ids: Vec<FactId>,
    pub elements: Vec<Obj>,
}
pub struct AggregateTermEvaluationResult {
    pub argument: Obj,
    pub application: Obj,
    pub application_well_defined: ObjWellDefinedProof,
    pub expansion: AggregateTermExpansion,
    // Indices in the enclosing evaluation's chronological aggregate evidence.
    pub nested_aggregate_evidence: std::ops::Range<usize>,
    pub value: Obj,
    pub accumulated_value: Obj,
}
pub enum AggregateTermExpansion {
    Function(AnonFnApplicationBodyProof),
    // Display eval may run stored algorithms; equality evaluation requires a
    // mathematical function body instead of treating an algorithm as a theorem.
    Algorithm { evaluation_index: usize },
}

pub struct FunctionApplicationEvaluationResult {
    pub application: Obj,
    pub application_well_defined: ObjWellDefinedProof,
    pub expansion: AnonFnApplicationBodyProof,
    pub value: Obj,
}

pub struct AlgoApplicationEvaluationResult {
    pub application: Obj,
    pub normalized_arguments: Vec<Obj>,
    pub return_expression: Obj,
    pub definition_evidence: AlgoDefinitionEvidence,
    pub value: Obj,
}
pub enum AlgoDefinitionEvidence {
    Display,
    Checked(crate::execute::execute_fact_stmt::VerifyFactResult),
}
