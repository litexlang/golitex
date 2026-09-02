//! Builtin proofs and typed evidence.

use super::*;

impl StatementResultRenderer {
    pub(in super::super) fn builtin_proof(
        &mut self,
        kind: &str,
        result: &SuccessBuiltinFactProofResult,
    ) -> JsonValue {
        object(vec![
            string_field("kind", kind),
            string_field("diagnostic_label", result.msg.clone()),
            (
                "evidence".to_string(),
                match &result.evidence {
                    SuccessBuiltinFactProofEvidenceResult::Typed(evidence) => object(vec![
                        string_field("kind", "Typed"),
                        string_field("rule_id", evidence.rule_id()),
                        ("value".to_string(), self.builtin_evidence(evidence)),
                    ]),
                },
            ),
            (
                "subgoals".to_string(),
                array(
                    result
                        .subgoals
                        .iter()
                        .map(|result| self.verify_fact_result(result))
                        .collect(),
                ),
            ),
        ])
    }

    pub(in super::super) fn builtin_evidence(
        &mut self,
        evidence: &BuiltinRuleEvidence,
    ) -> JsonValue {
        match evidence {
            BuiltinRuleEvidence::Uncatalogued(rule) => object(vec![
                string_field("kind", "Uncatalogued"),
                string_field("rule", format!("{rule:?}")),
                string_field("rule_id", rule.rule_id()),
            ]),
            BuiltinRuleEvidence::DefinitionProjection(result) => object(vec![
                string_field("kind", "DefinitionProjection"),
                string_field("fact", result.fact.to_string()),
                string_field("definition", result.definition.to_string()),
            ]),
            BuiltinRuleEvidence::SetBuilderMembership(result) => object(vec![
                string_field("kind", "SetBuilderMembership"),
                string_field("expected_target", result.expected_target.to_string()),
                (
                    "expected_premises".to_string(),
                    display_values(&result.expected_premises),
                ),
            ]),
            BuiltinRuleEvidence::FunctionSetMembership(result) => object(vec![
                string_field("kind", "FunctionSetMembership"),
                string_field("expected_target", result.expected_target.to_string()),
                string_field("expected_pointwise", result.expected_pointwise.to_string()),
            ]),
            BuiltinRuleEvidence::FunctionApplicationInRange(result) => object(vec![
                string_field("kind", "FunctionApplicationInRange"),
                string_field("expected_target", result.expected_target.to_string()),
            ]),
            BuiltinRuleEvidence::FunctionRangeSubset(result) => object(vec![
                string_field("kind", "FunctionRangeSubset"),
                string_field("expected_target", result.expected_target.to_string()),
                string_field(
                    "expected_codomain_subset",
                    result.expected_codomain_subset.to_string(),
                ),
            ]),
            BuiltinRuleEvidence::RealIntervalSubsetReal(result) => object(vec![
                string_field("kind", "RealIntervalSubsetReal"),
                string_field("expected_target", result.expected_target.to_string()),
            ]),
            BuiltinRuleEvidence::TupleCartesianMembership(result) => object(vec![
                string_field("kind", "TupleCartesianMembership"),
                string_field("expected_target", result.expected_target.to_string()),
                (
                    "expected_coordinate_memberships".to_string(),
                    display_values(&result.expected_coordinate_memberships),
                ),
            ]),
            BuiltinRuleEvidence::IntegerRangeSumPointwiseOrder(result) => object(vec![
                string_field("kind", "IntegerRangeSumPointwiseOrder"),
                string_field("expected_target", result.expected_target.to_string()),
                string_field(
                    "expected_start_equality",
                    result.expected_start_equality.to_string(),
                ),
                string_field(
                    "expected_end_equality",
                    result.expected_end_equality.to_string(),
                ),
                string_field("expected_pointwise", result.expected_pointwise.to_string()),
            ]),
            BuiltinRuleEvidence::RefinedNumericMembership(result) => object(vec![
                string_field("kind", "RefinedNumericMembership"),
                string_field("expected_target", result.expected_target.to_string()),
                (
                    "expected_premises".to_string(),
                    display_values(&result.expected_premises),
                ),
            ]),
            BuiltinRuleEvidence::ClosedNumericMembership(result) => object(vec![
                string_field("kind", "ClosedNumericMembership"),
                string_field("expected_target", result.expected_target.to_string()),
                string_field("target_set", result.target_set.to_string()),
                (
                    "evaluation".to_string(),
                    evaluation_value(&result.evaluation),
                ),
            ]),
            BuiltinRuleEvidence::ClosedNumericNonmembership(result) => object(vec![
                string_field("kind", "ClosedNumericNonmembership"),
                string_field("expected_target", result.expected_target.to_string()),
                string_field("target_set", result.target_set.to_string()),
                (
                    "evaluation".to_string(),
                    evaluation_value(&result.evaluation),
                ),
            ]),
            BuiltinRuleEvidence::ClosedNumericComparison(result) => object(vec![
                string_field("kind", "ClosedNumericComparison"),
                string_field("expected_target", result.expected_target.to_string()),
                (
                    "left_evaluation".to_string(),
                    evaluation_value(&result.left_evaluation),
                ),
                (
                    "right_evaluation".to_string(),
                    evaluation_value(&result.right_evaluation),
                ),
            ]),
            BuiltinRuleEvidence::OrderReflexivity(result) => object(vec![
                string_field("kind", "OrderReflexivity"),
                string_field("expected_target", result.expected_target.to_string()),
                string_field("repeated_object", result.repeated_object.to_string()),
            ]),
            BuiltinRuleEvidence::RuntimeResolvedNumericComparison(result) => object(vec![
                string_field("kind", "RuntimeResolvedNumericComparison"),
                string_field("expected_target", result.expected_target.to_string()),
                string_field("normalized_left", result.normalized_left.to_string()),
                string_field("normalized_right", result.normalized_right.to_string()),
            ]),
            BuiltinRuleEvidence::RegisteredReflexivePredicate(result) => object(vec![
                string_field("kind", "RegisteredReflexivePredicate"),
                string_field("expected_target", result.expected_target.to_string()),
                string_field("predicate_name", result.predicate_name.clone()),
            ]),
            BuiltinRuleEvidence::RegisteredSymmetricPredicate(result) => object(vec![
                string_field("kind", "RegisteredSymmetricPredicate"),
                string_field("expected_target", result.expected_target.to_string()),
                string_field("predicate_name", result.predicate_name.clone()),
                (
                    "gather".to_string(),
                    JsonValue::Array(
                        result
                            .gather
                            .iter()
                            .map(|index| JsonValue::Number(*index))
                            .collect(),
                    ),
                ),
                string_field("expected_alternate", result.expected_alternate.to_string()),
            ]),
            BuiltinRuleEvidence::RegisteredAntisymmetricPredicate(result) => object(vec![
                string_field("kind", "RegisteredAntisymmetricPredicate"),
                string_field("expected_target", result.expected_target.to_string()),
                string_field("predicate_name", result.predicate_name.clone()),
            ]),
            BuiltinRuleEvidence::ObjectReflexivity(result) => object(vec![
                string_field("kind", "ObjectReflexivity"),
                string_field("expected_target", result.expected_target.to_string()),
            ]),
            BuiltinRuleEvidence::RationalNormalization(result) => object(vec![
                string_field("kind", "RationalNormalization"),
                string_field("expected_target", result.expected_target.to_string()),
                (
                    "left_evaluation".to_string(),
                    evaluation_value(&result.left_evaluation),
                ),
                (
                    "right_evaluation".to_string(),
                    evaluation_value(&result.right_evaluation),
                ),
            ]),
            BuiltinRuleEvidence::RationalAlgebraicNormalization(result) => object(vec![
                string_field("kind", "RationalAlgebraicNormalization"),
                string_field("expected_target", result.expected_target.to_string()),
                (
                    "expected_nonzero_premises".to_string(),
                    array(
                        result
                            .expected_nonzero_premises
                            .iter()
                            .map(|fact| JsonValue::JsonString(fact.to_string()))
                            .collect(),
                    ),
                ),
            ]),
            BuiltinRuleEvidence::ComplexAlgebraicNormalization(result) => object(vec![
                string_field("kind", "ComplexAlgebraicNormalization"),
                string_field("expected_target", result.expected_target.to_string()),
                (
                    "expected_nonzero_premises".to_string(),
                    array(
                        result
                            .expected_nonzero_premises
                            .iter()
                            .map(|fact| JsonValue::JsonString(fact.to_string()))
                            .collect(),
                    ),
                ),
            ]),
            BuiltinRuleEvidence::StructuralDefinitionCongruence(result) => object(vec![
                string_field("kind", "StructuralDefinitionCongruence"),
                string_field("expected_target", result.expected_target.to_string()),
                (
                    "reductions".to_string(),
                    array(
                        result
                            .reductions
                            .iter()
                            .map(|reduction| {
                                object(vec![
                                    string_field(
                                        "definition_object",
                                        reduction.definition_object.to_string(),
                                    ),
                                    string_field(
                                        "defining_equality",
                                        reduction.defining_equality.to_string(),
                                    ),
                                    string_field(
                                        "defining_equality_fact_id",
                                        fact_id(reduction.defining_equality_fact_id),
                                    ),
                                    string_field("application", reduction.application.to_string()),
                                    string_field("reduced", reduction.reduced.to_string()),
                                ])
                            })
                            .collect(),
                    ),
                ),
            ]),
            BuiltinRuleEvidence::StructuralKnownEqualityCongruence(result) => object(vec![
                string_field("kind", "StructuralKnownEqualityCongruence"),
                string_field("expected_target", result.expected_target.to_string()),
            ]),
            BuiltinRuleEvidence::IntegralPolynomialNormalization(result) => object(vec![
                string_field("kind", "IntegralPolynomialNormalization"),
                string_field("expected_target", result.expected_target.to_string()),
            ]),
            BuiltinRuleEvidence::StandardSetNonempty(result) => object(vec![
                string_field("kind", "StandardSetNonempty"),
                string_field("expected_target", result.expected_target.to_string()),
                string_field("target_set", result.target_set.to_string()),
            ]),
            BuiltinRuleEvidence::DisjunctionIntroduction(result) => object(vec![
                string_field("kind", "DisjunctionIntroduction"),
                string_field("expected_target", result.expected_target.to_string()),
                string_field("expected_selected", result.expected_selected.to_string()),
                number_field("selected_index", result.selected_index),
            ]),
            BuiltinRuleEvidence::FunctionApplicationReturnMembership(result) => object(vec![
                string_field("kind", "FunctionApplicationReturnMembership"),
                string_field("typed_return_set", result.typed_return_set.to_string()),
                string_field("expected_target", result.expected_target.to_string()),
                string_field(
                    "expected_head_membership",
                    result.expected_head_membership.to_string(),
                ),
            ]),
            BuiltinRuleEvidence::MatrixExpressionMembership(result) => object(vec![
                string_field("kind", "MatrixExpressionMembership"),
                string_field(
                    "inferred_matrix_set",
                    Obj::from(result.inferred_matrix_set.clone()).to_string(),
                ),
                string_field("expected_target", result.expected_target.to_string()),
            ]),
            BuiltinRuleEvidence::KnownEqualityPath(result) => object(vec![
                string_field("kind", "KnownEqualityPath"),
                string_field("expected_target", result.expected_target.to_string()),
                (
                    "steps".to_string(),
                    array(
                        result
                            .steps
                            .iter()
                            .map(|step| {
                                object(vec![
                                    string_field("from", step.from.to_string()),
                                    string_field("to", step.to.to_string()),
                                    string_field("equality", step.equality.to_string()),
                                    string_field("source_fact_id", fact_id(step.source_fact_id)),
                                ])
                            })
                            .collect(),
                    ),
                ),
            ]),
            BuiltinRuleEvidence::DivNotEqualZero(result) => object(vec![
                string_field("kind", "DivNotEqualZero"),
                string_field("rule_id", result.rule_id()),
                string_field("numerator", result.numerator.to_string()),
                string_field("denominator", result.denominator.to_string()),
                string_field(
                    "orientation",
                    match result.orientation {
                        NonzeroExpressionOrientation::ExpressionOnLeft => "ExpressionOnLeft",
                        NonzeroExpressionOrientation::ExpressionOnRight => "ExpressionOnRight",
                    },
                ),
            ]),
            BuiltinRuleEvidence::Arithmetic(rule) => object(vec![
                string_field("kind", "Arithmetic"),
                string_field("rule", arithmetic_builtin_rule_name(*rule)),
                string_field("rule_id", rule.rule_id()),
            ]),
            BuiltinRuleEvidence::IntegerMembershipClosure(rule) => rule_evidence_value(
                "IntegerMembershipClosure",
                integer_membership_closure_rule_name(*rule),
            ),
            BuiltinRuleEvidence::IntegerRangeSumMembership => {
                object(vec![string_field("kind", "IntegerRangeSumMembership")])
            }
            BuiltinRuleEvidence::NaturalMembershipClosure(rule) => rule_evidence_value(
                "NaturalMembershipClosure",
                natural_membership_closure_rule_name(*rule),
            ),
            BuiltinRuleEvidence::PositiveNaturalMembershipClosure(rule) => rule_evidence_value(
                "PositiveNaturalMembershipClosure",
                positive_natural_membership_closure_rule_name(*rule),
            ),
            BuiltinRuleEvidence::RationalMembershipClosure(rule) => rule_evidence_value(
                "RationalMembershipClosure",
                rational_membership_closure_rule_name(*rule),
            ),
            BuiltinRuleEvidence::ComplexArithmeticMembershipClosure(rule) => rule_evidence_value(
                "ComplexArithmeticMembershipClosure",
                complex_membership_closure_rule_name(*rule),
            ),
            BuiltinRuleEvidence::RealArithmeticMembershipClosure(rule) => rule_evidence_value(
                "RealArithmeticMembershipClosure",
                real_membership_closure_rule_name(*rule),
            ),
            BuiltinRuleEvidence::NativeConstantMembership(rule) => rule_evidence_value(
                "NativeConstantMembership",
                native_constant_membership_rule_name(*rule),
            ),
            BuiltinRuleEvidence::EqualitySymmetry => {
                object(vec![string_field("kind", "EqualitySymmetry")])
            }
            BuiltinRuleEvidence::NotEqualSymmetry => {
                object(vec![string_field("kind", "NotEqualSymmetry")])
            }
            BuiltinRuleEvidence::NotEqualFromStrictOrder => {
                object(vec![string_field("kind", "NotEqualFromStrictOrder")])
            }
            BuiltinRuleEvidence::SetRelationDuality(rule) => {
                rule_evidence_value("SetRelationDuality", set_relation_duality_rule_name(*rule))
            }
            BuiltinRuleEvidence::Set(rule) => object(vec![
                string_field("kind", "Set"),
                string_field("rule", set_builtin_rule_name(*rule)),
                string_field("rule_id", rule.rule_id()),
            ]),
            BuiltinRuleEvidence::FiniteSet(rule) => {
                rule_evidence_value("FiniteSet", finite_set_builtin_rule_name(*rule))
            }
            BuiltinRuleEvidence::ListSetMembership(result) => object(vec![
                string_field("kind", "ListSetMembership"),
                number_field("selected_index", result.selected_index),
            ]),
            BuiltinRuleEvidence::TupleLiteralShape => {
                object(vec![string_field("kind", "TupleLiteralShape")])
            }
            BuiltinRuleEvidence::AbsoluteValue(rule) => object(vec![
                string_field("kind", "AbsoluteValue"),
                string_field("rule", absolute_value_builtin_rule_name(*rule)),
                string_field("rule_id", rule.rule_id()),
            ]),
            BuiltinRuleEvidence::Extrema(rule) => object(vec![
                string_field("kind", "Extrema"),
                string_field("rule", extrema_builtin_rule_name(*rule)),
                string_field("rule_id", rule.rule_id()),
            ]),
            BuiltinRuleEvidence::Aggregate(rule) => object(vec![
                string_field("kind", "Aggregate"),
                string_field("rule", aggregate_builtin_rule_name(*rule)),
                string_field("rule_id", rule.rule_id()),
            ]),
            BuiltinRuleEvidence::Nonzero(rule) => object(vec![
                string_field("kind", "Nonzero"),
                string_field("rule", nonzero_builtin_rule_name(*rule)),
                string_field("rule_id", rule.rule_id()),
            ]),
            BuiltinRuleEvidence::PrimeU64Reflection => {
                object(vec![string_field("kind", "PrimeU64Reflection")])
            }
            BuiltinRuleEvidence::CoprimeNaturalReflection => {
                object(vec![string_field("kind", "CoprimeNaturalReflection")])
            }
            BuiltinRuleEvidence::StandardSetMembershipProjection => object(vec![string_field(
                "kind",
                "StandardSetMembershipProjection",
            )]),
            BuiltinRuleEvidence::StandardSetSubset => {
                object(vec![string_field("kind", "StandardSetSubset")])
            }
            BuiltinRuleEvidence::LiteralSetNonempty => {
                object(vec![string_field("kind", "LiteralSetNonempty")])
            }
            BuiltinRuleEvidence::SetBuilderSubsetBase => {
                object(vec![string_field("kind", "SetBuilderSubsetBase")])
            }
            BuiltinRuleEvidence::SetBuilderInPowerSetViaParamSubset => object(vec![string_field(
                "kind",
                "SetBuilderInPowerSetViaParamSubset",
            )]),
            BuiltinRuleEvidence::LiteralSetSubset => {
                object(vec![string_field("kind", "LiteralSetSubset")])
            }
        }
    }
}
