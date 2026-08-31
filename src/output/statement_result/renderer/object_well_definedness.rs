//! Shared objects, object checks, children, and binder premises.

use super::*;

impl StatementResultRenderer {
    pub(in super::super) fn shared_wd_obj(
        &mut self,
        result: &Rc<SuccessVerifyObjWellDefinedResult>,
    ) -> JsonValue {
        let pointer = Rc::as_ptr(result) as usize;
        if let Some(id) = self.shared_wd_obj_ids.get(&pointer) {
            return object(vec![string_field("$ref", id.clone())]);
        }
        let id = format!("wd-node-{}", self.next_shared_wd_obj_id);
        self.next_shared_wd_obj_id += 1;
        self.shared_wd_obj_ids.insert(pointer, id.clone());
        object(vec![
            string_field("$id", id),
            ("value".to_string(), self.wd_obj_result(result)),
        ])
    }

    pub(in super::super) fn wd_obj_result(
        &mut self,
        result: &SuccessVerifyObjWellDefinedResult,
    ) -> JsonValue {
        match result {
            SuccessVerifyObjWellDefinedResult::Direct(result) => object(vec![
                string_field("kind", "Direct"),
                string_field("object", result.object.to_string()),
                (
                    "intrinsic_result_set".to_string(),
                    result
                        .intrinsic_result_set
                        .as_ref()
                        .map(|value| string(value.to_string()))
                        .unwrap_or(JsonValue::Null),
                ),
                (
                    "children".to_string(),
                    array(
                        result
                            .steps
                            .children
                            .iter()
                            .map(|child| {
                                object(vec![
                                    ("role".to_string(), wd_child_role_value(child.role)),
                                    string_field("object", child.source_object.to_string()),
                                    ("result".to_string(), self.shared_wd_obj(&child.result)),
                                ])
                            })
                            .collect(),
                    ),
                ),
                (
                    "fact_checks".to_string(),
                    array(
                        result
                            .steps
                            .fact_checks
                            .iter()
                            .map(|check| {
                                object(vec![
                                    string_field(
                                        "expected_proposition",
                                        check.expected_proposition.to_string(),
                                    ),
                                    (
                                        "verification".to_string(),
                                        self.shared_fact(&check.verification),
                                    ),
                                ])
                            })
                            .collect(),
                    ),
                ),
                (
                    "target_requirements".to_string(),
                    array(
                        result
                            .steps
                            .target_requirements
                            .iter()
                            .map(|requirement| {
                                object(vec![
                                    ("role".to_string(), wd_requirement_role(requirement.role)),
                                    string_field(
                                        "expected_proposition",
                                        requirement.expected_proposition.to_string(),
                                    ),
                                    (
                                        "verification".to_string(),
                                        self.shared_fact(&requirement.verification),
                                    ),
                                ])
                            })
                            .collect(),
                    ),
                ),
                (
                    "stores".to_string(),
                    array(
                        result
                            .steps
                            .stores
                            .iter()
                            .map(|store| self.store_fact(store))
                            .collect(),
                    ),
                ),
                (
                    "binder".to_string(),
                    result
                        .steps
                        .binder
                        .as_ref()
                        .map(|binder| self.wd_binder_result(binder))
                        .unwrap_or(JsonValue::Null),
                ),
                (
                    "template_instantiation".to_string(),
                    result
                        .steps
                        .template_instantiation
                        .as_ref()
                        .map(|instantiation| self.template_instantiation(instantiation))
                        .unwrap_or(JsonValue::Null),
                ),
            ]),
            SuccessVerifyObjWellDefinedResult::Reuse(result) => object(vec![
                string_field("kind", "Reuse"),
                string_field("object", result.object.to_string()),
                ("source".to_string(), self.shared_wd_obj(&result.source)),
            ]),
            SuccessVerifyObjWellDefinedResult::RecursiveReference(result) => object(vec![
                string_field("kind", "RecursiveReference"),
                string_field("object", result.object.to_string()),
                string_field("ancestor_key", result.ancestor_key.clone()),
            ]),
        }
    }

    pub(in super::super) fn wd_fact_check(
        &mut self,
        check: &SuccessVerifyFactForObjWellDefinedResult,
    ) -> JsonValue {
        object(vec![
            string_field(
                "expected_proposition",
                check.expected_proposition.to_string(),
            ),
            (
                "verification".to_string(),
                self.shared_fact(&check.verification),
            ),
        ])
    }

    pub(in super::super) fn wd_child_result(
        &mut self,
        child: &SuccessVerifyChildObjWellDefinedResult,
    ) -> JsonValue {
        object(vec![
            ("role".to_string(), wd_child_role_value(child.role)),
            string_field("object", child.source_object.to_string()),
            ("result".to_string(), self.shared_wd_obj(&child.result)),
        ])
    }

    pub(in super::super) fn wd_binder_premise_result(
        &mut self,
        result: &SuccessVerifyBinderPremiseResult,
    ) -> JsonValue {
        object(vec![
            ("role".to_string(), wd_binder_premise_role(result.role)),
            optional_symbol_id_field("symbol_id", result.symbol_id),
            string_field("proposition", result.proposition.to_string()),
            (
                "well_definedness".to_string(),
                self.fact_well_definedness(&result.well_definedness),
            ),
            ("infers".to_string(), infer_result_value(&result.infers)),
        ])
    }
}
