//! Object binder well-definedness results.

use super::*;

impl StatementResultRenderer {
    pub(in super::super) fn wd_binder_result(
        &mut self,
        result: &SuccessVerifyBinderObjectWellDefinedResult,
    ) -> JsonValue {
        match result {
            SuccessVerifyBinderObjectWellDefinedResult::SetBuilder(result) => object(vec![
                string_field("kind", "SetBuilder"),
                (
                    "parameter_carrier".to_string(),
                    self.wd_child_result(&result.parameter_carrier),
                ),
                (
                    "parameter".to_string(),
                    self.wd_binder_premise_result(&result.parameter),
                ),
                (
                    "conditions".to_string(),
                    array(
                        result
                            .conditions
                            .iter()
                            .map(|condition| {
                                object(vec![
                                    number_field("condition_index", condition.condition_index),
                                    (
                                        "well_definedness".to_string(),
                                        self.fact_well_definedness(&condition.well_definedness),
                                    ),
                                    ("store".to_string(), self.store_fact(&condition.store)),
                                ])
                            })
                            .collect(),
                    ),
                ),
            ]),
            SuccessVerifyBinderObjectWellDefinedResult::FunctionSet(result) => object(vec![
                string_field("kind", "FunctionSet"),
                (
                    "parameter_carriers".to_string(),
                    array(
                        result
                            .parameter_carriers
                            .iter()
                            .map(|child| self.wd_child_result(child))
                            .collect(),
                    ),
                ),
                (
                    "parameters".to_string(),
                    array(
                        result
                            .parameters
                            .iter()
                            .map(|premise| self.wd_binder_premise_result(premise))
                            .collect(),
                    ),
                ),
                (
                    "domains".to_string(),
                    array(
                        result
                            .domains
                            .iter()
                            .map(|premise| self.wd_binder_premise_result(premise))
                            .collect(),
                    ),
                ),
                (
                    "return_carrier".to_string(),
                    self.wd_child_result(&result.return_carrier),
                ),
            ]),
            SuccessVerifyBinderObjectWellDefinedResult::AnonymousFunction(result) => object(vec![
                string_field("kind", "AnonymousFunction"),
                (
                    "parameter_carriers".to_string(),
                    array(
                        result
                            .parameter_carriers
                            .iter()
                            .map(|child| self.wd_child_result(child))
                            .collect(),
                    ),
                ),
                (
                    "parameters".to_string(),
                    array(
                        result
                            .parameters
                            .iter()
                            .map(|premise| self.wd_binder_premise_result(premise))
                            .collect(),
                    ),
                ),
                (
                    "domains".to_string(),
                    array(
                        result
                            .domains
                            .iter()
                            .map(|premise| self.wd_binder_premise_result(premise))
                            .collect(),
                    ),
                ),
                (
                    "return_carrier".to_string(),
                    self.wd_child_result(&result.return_carrier),
                ),
                ("body".to_string(), self.wd_child_result(&result.body)),
                (
                    "body_membership".to_string(),
                    object(vec![
                        (
                            "role".to_string(),
                            wd_requirement_role(result.body_membership.role),
                        ),
                        string_field(
                            "expected_proposition",
                            result.body_membership.expected_proposition.to_string(),
                        ),
                        (
                            "verification".to_string(),
                            self.shared_fact(&result.body_membership.verification),
                        ),
                    ]),
                ),
            ]),
            SuccessVerifyBinderObjectWellDefinedResult::Iteration(result) => object(vec![
                string_field("kind", "Iteration"),
                string_field("operation", result.operation.clone()),
                (
                    "scalar_return".to_string(),
                    result
                        .scalar_return
                        .as_ref()
                        .map(|value| self.iteration_scalar_return(value))
                        .unwrap_or(JsonValue::Null),
                ),
                (
                    "interval".to_string(),
                    self.iteration_interval(&result.interval),
                ),
            ]),
            SuccessVerifyBinderObjectWellDefinedResult::FiniteAggregate(result) => object(vec![
                string_field("kind", "FiniteAggregate"),
                string_field("operation", result.operation.clone()),
                (
                    "scalar_return".to_string(),
                    result
                        .scalar_return
                        .as_ref()
                        .map(|value| self.iteration_scalar_return(value))
                        .unwrap_or(JsonValue::Null),
                ),
                ("mode".to_string(), self.finite_aggregate_mode(&result.mode)),
            ]),
            SuccessVerifyBinderObjectWellDefinedResult::Reduce(result) => object(vec![
                string_field("kind", "Reduce"),
                string_field("operation", result.operation.clone()),
                (
                    "signature".to_string(),
                    object(vec![
                        string_field(
                            "left_parameter_carrier",
                            result.signature.left_parameter_carrier.to_string(),
                        ),
                        string_field(
                            "right_parameter_carrier",
                            result.signature.right_parameter_carrier.to_string(),
                        ),
                        string_field(
                            "return_carrier",
                            result.signature.return_carrier.to_string(),
                        ),
                    ]),
                ),
                string_field(
                    "iterand_return_carrier",
                    result.iterand_return_carrier.to_string(),
                ),
                (
                    "seed_membership".to_string(),
                    self.wd_fact_check(&result.seed_membership),
                ),
                (
                    "operation_laws".to_string(),
                    result
                        .operation_laws
                        .as_ref()
                        .map(|laws| self.finite_reduce_operation_laws(laws))
                        .unwrap_or(JsonValue::Null),
                ),
                ("mode".to_string(), self.reduce_mode(&result.mode)),
            ]),
            SuccessVerifyBinderObjectWellDefinedResult::Structure(result) => object(vec![
                string_field("kind", "Structure"),
                string_field("structure_name", result.structure_name.clone()),
                (
                    "header_arguments".to_string(),
                    array(
                        result
                            .header_arguments
                            .iter()
                            .map(|argument| {
                                object(vec![
                                    number_field("argument_index", argument.argument_index),
                                    string_field("argument", argument.argument.to_string()),
                                    string_field(
                                        "expected_type",
                                        argument.expected_type.to_string(),
                                    ),
                                    (
                                        "verification".to_string(),
                                        self.wd_fact_check(&argument.verification),
                                    ),
                                ])
                            })
                            .collect(),
                    ),
                ),
                (
                    "header_domains".to_string(),
                    array(
                        result
                            .header_domains
                            .iter()
                            .map(|check| self.wd_fact_check(check))
                            .collect(),
                    ),
                ),
                (
                    "fields".to_string(),
                    array(
                        result
                            .fields
                            .iter()
                            .map(|field| {
                                object(vec![
                                    number_field("field_index", field.field_index),
                                    string_field("field_name", field.field_name.clone()),
                                    ("carrier".to_string(), self.wd_child_result(&field.carrier)),
                                    (
                                        "premise".to_string(),
                                        self.wd_binder_premise_result(&field.premise),
                                    ),
                                ])
                            })
                            .collect(),
                    ),
                ),
                (
                    "equivalent_facts".to_string(),
                    array(
                        result
                            .equivalent_facts
                            .iter()
                            .map(|fact| {
                                object(vec![
                                    number_field("fact_index", fact.fact_index),
                                    string_field("proposition", fact.proposition.to_string()),
                                    (
                                        "well_definedness".to_string(),
                                        self.fact_well_definedness(&fact.well_definedness),
                                    ),
                                    ("store".to_string(), self.store_fact(&fact.store)),
                                ])
                            })
                            .collect(),
                    ),
                ),
            ]),
        }
    }
}
