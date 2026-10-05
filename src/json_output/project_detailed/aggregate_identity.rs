use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::*;
use crate::json_output::helper::{object_for,string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;

pub(super) fn project_aggregate_identity(
    proof: &AggregateIdentityBuiltinRuleProof,
    runtime: &Runtime,
) -> JsonValue {
    match proof {
        AggregateIdentityBuiltinRuleProof::FiniteSetProductMemberRemoval(p) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("FiniteSetProductMemberRemoval")),
            ("premises", super::store::project_verify_facts(&p.premises, runtime)),
            ("pointwise", project_pointwise(&p.pointwise, runtime)),
            ("factor_expansions", project_expansions(&p.factor_expansions, runtime)),
            ("factor_equal", super::verify::project_verify_fact(&p.factor_equal, runtime)),
        ]),
        AggregateIdentityBuiltinRuleProof::FiniteSetProductFreshInsertion(p) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("FiniteSetProductFreshInsertion")),
            ("premises", super::store::project_verify_facts(&p.premises, runtime)),
            ("pointwise", project_pointwise(&p.pointwise, runtime)),
            ("factor_expansions", project_expansions(&p.factor_expansions, runtime)),
            ("factor_equal", super::verify::project_verify_fact(&p.factor_equal, runtime)),
        ]),
        AggregateIdentityBuiltinRuleProof::RangeSumConstant(p) => object_for(
            runtime,
            vec![
                ("type", string("builtin_rule")),
                ("rule", string("RangeSumConstant")),
                (
                    "function_equal",
                    super::searched::project_known_equality_path(
                        &p.function_expansion.function_equal,
                        runtime,
                    ),
                ),
                (
                    "expanded_body",
                    string(p.function_expansion.expanded_body.readable_string()),
                ),
                ("constant", string(p.constant.readable_string())),
                (
                    "residual_equal",
                    super::verify::project_verify_fact(&p.residual_equal, runtime),
                ),
            ],
        ),
        AggregateIdentityBuiltinRuleProof::RangeProductConstant(p) => object_for(
            runtime,
            vec![
                ("type", string("builtin_rule")),
                ("rule", string("RangeProductConstant")),
                (
                    "function_equal",
                    super::searched::project_known_equality_path(
                        &p.function_expansion.function_equal,
                        runtime,
                    ),
                ),
                (
                    "expanded_body",
                    string(p.function_expansion.expanded_body.readable_string()),
                ),
                ("constant", string(p.constant.readable_string())),
                (
                    "exponent_equal",
                    p.exponent_equal
                        .as_ref()
                        .map(|proof| super::verify::project_verify_fact(proof, runtime))
                        .unwrap_or(JsonValue::Null),
                ),
                (
                    "residual_equal",
                    super::verify::project_verify_fact(&p.residual_equal, runtime),
                ),
            ],
        ),
        AggregateIdentityBuiltinRuleProof::FiniteSetSumConstant(p) => object_for(
            runtime,
            vec![
                ("type", string("builtin_rule")),
                ("rule", string("FiniteSetSumConstant")),
                (
                    "function_equal",
                    super::searched::project_known_equality_path(
                        &p.function_expansion.function_equal,
                        runtime,
                    ),
                ),
                (
                    "expanded_body",
                    string(p.function_expansion.expanded_body.readable_string()),
                ),
                ("constant", string(p.constant.readable_string())),
                (
                    "residual_equal",
                    super::verify::project_verify_fact(&p.residual_equal, runtime),
                ),
            ],
        ),
        AggregateIdentityBuiltinRuleProof::FiniteSetProductConstant(p) => object_for(
            runtime,
            vec![
                ("type", string("builtin_rule")),
                ("rule", string("FiniteSetProductConstant")),
                (
                    "function_equal",
                    super::searched::project_known_equality_path(
                        &p.function_expansion.function_equal,
                        runtime,
                    ),
                ),
                (
                    "expanded_body",
                    string(p.function_expansion.expanded_body.readable_string()),
                ),
                ("constant", string(p.constant.readable_string())),
                (
                    "exponent_equal",
                    p.exponent_equal
                        .as_ref()
                        .map(|proof| super::verify::project_verify_fact(proof, runtime))
                        .unwrap_or(JsonValue::Null),
                ),
                (
                    "residual_equal",
                    super::verify::project_verify_fact(&p.residual_equal, runtime),
                ),
            ],
        ),
        AggregateIdentityBuiltinRuleProof::RangeSumPartition(p) => object_for(
            runtime,
            vec![
                ("type", string("builtin_rule")),
                ("rule", string("RangeSumPartition")),
                (
                    "premises",
                    super::store::project_verify_facts(&p.premises, runtime),
                ),
            ],
        ),
        AggregateIdentityBuiltinRuleProof::RangeProductPartition(p) => object_for(
            runtime,
            vec![
                ("type", string("builtin_rule")),
                ("rule", string("RangeProductPartition")),
                (
                    "premises",
                    super::store::project_verify_facts(&p.premises, runtime),
                ),
            ],
        ),
        AggregateIdentityBuiltinRuleProof::FiniteSetSumRangeBridge(p) => object_for(
            runtime,
            vec![
                ("type", string("builtin_rule")),
                ("rule", string("FiniteSetSumRangeBridge")),
                (
                    "premises",
                    super::store::project_verify_facts(&p.premises, runtime),
                ),
            ],
        ),
        AggregateIdentityBuiltinRuleProof::FiniteSetProductRangeBridge(p) => object_for(
            runtime,
            vec![
                ("type", string("builtin_rule")),
                ("rule", string("FiniteSetProductRangeBridge")),
                (
                    "premises",
                    super::store::project_verify_facts(&p.premises, runtime),
                ),
            ],
        ),
        AggregateIdentityBuiltinRuleProof::FiniteSetSumDisjointUnion(p) => object_for(
            runtime,
            vec![
                ("type", string("builtin_rule")),
                ("rule", string("FiniteSetSumDisjointUnion")),
                ("callbacks", JsonValue::Array(p.callbacks.iter().map(|p| project_partition_callback(p, runtime)).collect())),
                (
                    "premises",
                    super::store::project_verify_facts(&p.premises, runtime),
                ),
            ],
        ),
        AggregateIdentityBuiltinRuleProof::FiniteSetProductDisjointUnion(p) => object_for(
            runtime,
            vec![
                ("type", string("builtin_rule")),
                ("rule", string("FiniteSetProductDisjointUnion")),
                ("callbacks", JsonValue::Array(p.callbacks.iter().map(|p| project_partition_callback(p, runtime)).collect())),
                (
                    "premises",
                    super::store::project_verify_facts(&p.premises, runtime),
                ),
            ],
        ),
        AggregateIdentityBuiltinRuleProof::RangeSumPointwise(p) => object_for(
            runtime,
            vec![
                ("type", string("builtin_rule")),
                ("rule", string("RangeSumPointwise")),
                (
                    "premises",
                    super::store::project_verify_facts(&p.premises, runtime),
                ),
                ("pointwise", project_pointwise(&p.pointwise, runtime)),
            ],
        ),
        AggregateIdentityBuiltinRuleProof::RangeProductPointwise(p) => object_for(
            runtime,
            vec![
                ("type", string("builtin_rule")),
                ("rule", string("RangeProductPointwise")),
                (
                    "premises",
                    super::store::project_verify_facts(&p.premises, runtime),
                ),
                ("pointwise", project_pointwise(&p.pointwise, runtime)),
            ],
        ),
        AggregateIdentityBuiltinRuleProof::FiniteSetSumPointwise(p) => object_for(
            runtime,
            vec![
                ("type", string("builtin_rule")),
                ("rule", string("FiniteSetSumPointwise")),
                (
                    "premises",
                    super::store::project_verify_facts(&p.premises, runtime),
                ),
                ("pointwise", project_pointwise(&p.pointwise, runtime)),
            ],
        ),
        AggregateIdentityBuiltinRuleProof::FiniteSetProductPointwise(p) => object_for(
            runtime,
            vec![
                ("type", string("builtin_rule")),
                ("rule", string("FiniteSetProductPointwise")),
                (
                    "premises",
                    super::store::project_verify_facts(&p.premises, runtime),
                ),
                ("pointwise", project_pointwise(&p.pointwise, runtime)),
            ],
        ),
        AggregateIdentityBuiltinRuleProof::RangeSumAdd(p) => object_for(
            runtime,
            vec![
                ("type", string("builtin_rule")),
                ("rule", string("RangeSumAdd")),
                (
                    "premises",
                    super::store::project_verify_facts(&p.premises, runtime),
                ),
                ("pointwise", project_pointwise(&p.pointwise, runtime)),
            ],
        ),
        AggregateIdentityBuiltinRuleProof::RangeSumSubtract(p) => object_for(
            runtime,
            vec![
                ("type", string("builtin_rule")),
                ("rule", string("RangeSumSubtract")),
                (
                    "premises",
                    super::store::project_verify_facts(&p.premises, runtime),
                ),
                ("pointwise", project_pointwise(&p.pointwise, runtime)),
            ],
        ),
        AggregateIdentityBuiltinRuleProof::FiniteSetSumAdd(p) => object_for(
            runtime,
            vec![
                ("type", string("builtin_rule")),
                ("rule", string("FiniteSetSumAdd")),
                (
                    "premises",
                    super::store::project_verify_facts(&p.premises, runtime),
                ),
                ("pointwise", project_pointwise(&p.pointwise, runtime)),
            ],
        ),
        AggregateIdentityBuiltinRuleProof::FiniteSetSumSubtract(p) => object_for(
            runtime,
            vec![
                ("type", string("builtin_rule")),
                ("rule", string("FiniteSetSumSubtract")),
                (
                    "premises",
                    super::store::project_verify_facts(&p.premises, runtime),
                ),
                ("pointwise", project_pointwise(&p.pointwise, runtime)),
            ],
        ),
        AggregateIdentityBuiltinRuleProof::RangeSumScalar(p) => object_for(
            runtime,
            vec![
                ("type", string("builtin_rule")),
                ("rule", string("RangeSumScalar")),
                (
                    "premises",
                    super::store::project_verify_facts(&p.premises, runtime),
                ),
                ("pointwise", project_pointwise(&p.pointwise, runtime)),
            ],
        ),
        AggregateIdentityBuiltinRuleProof::FiniteSetSumScalar(p) => object_for(
            runtime,
            vec![
                ("type", string("builtin_rule")),
                ("rule", string("FiniteSetSumScalar")),
                (
                    "premises",
                    super::store::project_verify_facts(&p.premises, runtime),
                ),
                ("pointwise", project_pointwise(&p.pointwise, runtime)),
            ],
        ),
        AggregateIdentityBuiltinRuleProof::FiniteSetProductMultiply(p) => object_for(
            runtime,
            vec![
                ("type", string("builtin_rule")),
                ("rule", string("FiniteSetProductMultiply")),
                (
                    "premises",
                    super::store::project_verify_facts(&p.premises, runtime),
                ),
                ("pointwise", project_pointwise(&p.pointwise, runtime)),
            ],
        ),
        AggregateIdentityBuiltinRuleProof::RangeSumReindex(p) => object_for(
            runtime,
            vec![
                ("type", string("builtin_rule")),
                ("rule", string("RangeSumReindex")),
                (
                    "premises",
                    super::store::project_verify_facts(&p.premises, runtime),
                ),
                ("pointwise", project_pointwise(&p.pointwise, runtime)),
            ],
        ),
        AggregateIdentityBuiltinRuleProof::RangeProductReindex(p) => object_for(
            runtime,
            vec![
                ("type", string("builtin_rule")),
                ("rule", string("RangeProductReindex")),
                (
                    "premises",
                    super::store::project_verify_facts(&p.premises, runtime),
                ),
                ("pointwise", project_pointwise(&p.pointwise, runtime)),
            ],
        ),
    }
}
fn project_pointwise(p: &AggregatePointwiseProof, runtime: &Runtime) -> JsonValue {
    object_for(
        runtime,
        vec![
            ("parameter", string(p.parameter.to_string())),
            (
                "assumptions",
                JsonValue::Array(
                    p.assumptions
                        .iter()
                        .map(|f| string(f.readable_string()))
                        .collect(),
                ),
            ),
            (
                "function_expansions",
                JsonValue::Array(
                    p.function_expansions
                        .iter()
                        .map(|e| {
                            object_for(
                                runtime,
                                vec![
                                    (
                                        "function_equal",
                                        super::searched::project_known_equality_path(
                                            &e.function_equal,
                                            runtime,
                                        ),
                                    ),
                                    ("expanded_body", string(e.expanded_body.readable_string())),
                                ],
                            )
                        })
                        .collect(),
                ),
            ),
            (
                "equality",
                super::verify::project_verify_fact(&p.equality, runtime),
            ),
        ],
    )
}

pub(super) fn project_expansions(
    expansions: &[crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::by_have_fn_equal::AnonFnApplicationBodyProof],
    runtime: &Runtime,
) -> JsonValue {
    JsonValue::Array(expansions.iter().map(|e| object_for(runtime, vec![
        ("function_equal", super::searched::project_known_equality_path(&e.function_equal, runtime)),
        ("expanded_body", string(e.expanded_body.readable_string())),
    ])).collect())
}

fn project_partition_callback(p: &FinitePartitionCallbackAgreementProof, runtime: &Runtime) -> JsonValue {
    match p {
        FinitePartitionCallbackAgreementProof::SameFunction(_) => object_for(runtime, vec![("type", string("same_function"))]),
        FinitePartitionCallbackAgreementProof::LiteralRestriction(_) => object_for(runtime, vec![("type", string("literal_restriction"))]),
        FinitePartitionCallbackAgreementProof::EqualFunctions(p) => object_for(runtime, vec![("type", string("equal_functions")), ("equality", super::verify::project_verify_fact(&p.equality, runtime))]),
        FinitePartitionCallbackAgreementProof::Pointwise(p) => project_pointwise(p, runtime),
    }
}
