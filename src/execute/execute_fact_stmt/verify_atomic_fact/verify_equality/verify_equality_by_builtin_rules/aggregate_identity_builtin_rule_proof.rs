use crate::ast::names::BoundName;
use crate::ast::fact::Fact;
use crate::ast::obj::Obj;
use crate::exec_env::ExecEnv;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::by_have_fn_equal::AnonFnApplicationBodyProof;

pub enum AggregateIdentityBuiltinRuleProof {
    RangeSumConstant(RangeSumConstantBuiltinRuleProof),
    RangeProductConstant(RangeProductConstantBuiltinRuleProof),
    FiniteSetSumConstant(FiniteSetSumConstantBuiltinRuleProof),
    FiniteSetProductConstant(FiniteSetProductConstantBuiltinRuleProof),
    RangeSumPartition(RangeSumPartitionBuiltinRuleProof),
    RangeProductPartition(RangeProductPartitionBuiltinRuleProof),
    FiniteSetSumRangeBridge(FiniteSetSumRangeBridgeBuiltinRuleProof),
    FiniteSetProductRangeBridge(FiniteSetProductRangeBridgeBuiltinRuleProof),
    FiniteSetSumDisjointUnion(FiniteSetSumDisjointUnionBuiltinRuleProof),
    FiniteSetProductDisjointUnion(FiniteSetProductDisjointUnionBuiltinRuleProof),
    FiniteSetProductFreshInsertion(FiniteSetProductFreshInsertionProof),
    RangeSumPointwise(RangeSumPointwiseBuiltinRuleProof),
    RangeProductPointwise(RangeProductPointwiseBuiltinRuleProof),
    FiniteSetSumPointwise(FiniteSetSumPointwiseBuiltinRuleProof),
    FiniteSetProductPointwise(FiniteSetProductPointwiseBuiltinRuleProof),
    RangeSumAdd(RangeSumAddBuiltinRuleProof),
    RangeSumSubtract(RangeSumSubtractBuiltinRuleProof),
    FiniteSetSumAdd(FiniteSetSumAddBuiltinRuleProof),
    FiniteSetSumSubtract(FiniteSetSumSubtractBuiltinRuleProof),
    RangeSumScalar(RangeSumScalarBuiltinRuleProof),
    FiniteSetSumScalar(FiniteSetSumScalarBuiltinRuleProof),
    FiniteSetProductMultiply(FiniteSetProductMultiplyBuiltinRuleProof),
    RangeSumReindex(RangeSumReindexBuiltinRuleProof),
    RangeProductReindex(RangeProductReindexBuiltinRuleProof),
}
pub struct RangeSumConstantBuiltinRuleProof {
    pub function_expansion: AnonFnApplicationBodyProof,
    pub constant: Obj,
    pub residual_equal: VerifyFactResult,
}
pub struct RangeProductConstantBuiltinRuleProof {
    pub function_expansion: AnonFnApplicationBodyProof,
    pub constant: Obj,
    pub exponent_equal: Option<VerifyFactResult>,
    pub residual_equal: VerifyFactResult,
}
pub struct FiniteSetSumConstantBuiltinRuleProof {
    pub function_expansion: AnonFnApplicationBodyProof,
    pub constant: Obj,
    pub residual_equal: VerifyFactResult,
}
pub struct FiniteSetProductConstantBuiltinRuleProof {
    pub function_expansion: AnonFnApplicationBodyProof,
    pub constant: Obj,
    pub exponent_equal: Option<VerifyFactResult>,
    pub residual_equal: VerifyFactResult,
}
pub struct RangeSumPartitionBuiltinRuleProof {
    pub premises: Vec<VerifyFactResult>,
}
pub struct RangeProductPartitionBuiltinRuleProof {
    pub premises: Vec<VerifyFactResult>,
}
pub struct FiniteSetSumRangeBridgeBuiltinRuleProof {
    pub premises: Vec<VerifyFactResult>,
}
pub struct FiniteSetProductRangeBridgeBuiltinRuleProof {
    pub premises: Vec<VerifyFactResult>,
}
pub struct FiniteSetSumDisjointUnionBuiltinRuleProof {
    pub premises: Vec<VerifyFactResult>,
}
pub struct FiniteSetProductDisjointUnionBuiltinRuleProof {
    pub premises: Vec<VerifyFactResult>,
}
pub struct FiniteSetProductFreshInsertionProof {
    pub premises: Vec<VerifyFactResult>,
    pub pointwise: AggregatePointwiseProof,
    pub factor_expansions: Vec<AnonFnApplicationBodyProof>,
    pub factor_equal: VerifyFactResult,
}
pub struct RangeSumPointwiseBuiltinRuleProof {
    pub premises: Vec<VerifyFactResult>,
    pub pointwise: AggregatePointwiseProof,
}
pub struct RangeProductPointwiseBuiltinRuleProof {
    pub premises: Vec<VerifyFactResult>,
    pub pointwise: AggregatePointwiseProof,
}
pub struct FiniteSetSumPointwiseBuiltinRuleProof {
    pub premises: Vec<VerifyFactResult>,
    pub pointwise: AggregatePointwiseProof,
}
pub struct FiniteSetProductPointwiseBuiltinRuleProof {
    pub premises: Vec<VerifyFactResult>,
    pub pointwise: AggregatePointwiseProof,
}
pub struct RangeSumAddBuiltinRuleProof {
    pub premises: Vec<VerifyFactResult>,
    pub pointwise: AggregatePointwiseProof,
}
pub struct RangeSumSubtractBuiltinRuleProof {
    pub premises: Vec<VerifyFactResult>,
    pub pointwise: AggregatePointwiseProof,
}
pub struct FiniteSetSumAddBuiltinRuleProof {
    pub premises: Vec<VerifyFactResult>,
    pub pointwise: AggregatePointwiseProof,
}
pub struct FiniteSetSumSubtractBuiltinRuleProof {
    pub premises: Vec<VerifyFactResult>,
    pub pointwise: AggregatePointwiseProof,
}
pub struct RangeSumScalarBuiltinRuleProof {
    pub premises: Vec<VerifyFactResult>,
    pub pointwise: AggregatePointwiseProof,
}
pub struct FiniteSetSumScalarBuiltinRuleProof {
    pub premises: Vec<VerifyFactResult>,
    pub pointwise: AggregatePointwiseProof,
}
pub struct FiniteSetProductMultiplyBuiltinRuleProof {
    pub premises: Vec<VerifyFactResult>,
    pub pointwise: AggregatePointwiseProof,
}
pub struct RangeSumReindexBuiltinRuleProof {
    pub premises: Vec<VerifyFactResult>,
    pub pointwise: AggregatePointwiseProof,
}
pub struct RangeProductReindexBuiltinRuleProof {
    pub premises: Vec<VerifyFactResult>,
    pub pointwise: AggregatePointwiseProof,
}
pub struct AggregatePointwiseProof {
    pub parameter: BoundName,
    pub assumptions: Vec<Fact>,
    pub function_expansions: Vec<AnonFnApplicationBodyProof>,
    pub equality: VerifyFactResult,
    pub local_env: Box<ExecEnv>,
}
