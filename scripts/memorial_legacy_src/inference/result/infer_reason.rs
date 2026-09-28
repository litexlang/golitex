use crate::prelude::*;

#[derive(Clone, Debug)]
pub enum InferReason {
    StatementWithVerification,
    ProvedClaim,
    UnsafeAssumption,
    TrustHave,
    InferredFact,
    StoredFact,
    StoredFactWithoutForallCoverageCheck,
    StoredForallFact,
    ObjectDefinition,
    FunctionDefinition,
    ExistElimination,
    TheoremInstantiation,
    ByDefinition,
    BuiltinInference(String),
    InferRule(String),
    Evaluation,
    ParameterDefinition,
    Other(String),
}

impl InferReason {
    pub fn store_reason(&self) -> String {
        match self {
            InferReason::StatementWithVerification => Fact::store_reason().to_string(),
            InferReason::ProvedClaim => ClaimStmt::store_reason().to_string(),
            InferReason::UnsafeAssumption => TrustStmt::store_reason().to_string(),
            InferReason::TrustHave => TrustHaveStmt::store_reason().to_string(),
            InferReason::InferredFact => "inferred fact".to_string(),
            InferReason::StoredFact => "stored fact".to_string(),
            InferReason::StoredFactWithoutForallCoverageCheck => {
                "stored fact without forall coverage check".to_string()
            }
            InferReason::StoredForallFact => "stored forall fact".to_string(),
            InferReason::ObjectDefinition => {
                HaveObjInNonemptySetOrParamTypeStmt::store_reason().to_string()
            }
            InferReason::FunctionDefinition => HaveFnEqualStmt::store_reason().to_string(),
            InferReason::ExistElimination => ObtainObjFromExistFact::store_reason().to_string(),
            InferReason::TheoremInstantiation => ReleaseThmStmt::store_reason().to_string(),
            InferReason::ByDefinition => "inferred by definition".to_string(),
            InferReason::BuiltinInference(rule) => {
                format!("inferred by builtin rule `{}`", rule)
            }
            InferReason::InferRule(rule) => format!("inferred by infer rule `{}`", rule),
            InferReason::Evaluation => EvalStmt::store_reason().to_string(),
            InferReason::ParameterDefinition => TypedParameterList::store_reason().to_string(),
            InferReason::Other(s) => s.clone(),
        }
    }
}
