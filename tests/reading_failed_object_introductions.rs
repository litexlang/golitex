//! Actual failed object-introduction stages and retained source verification.
use litex::knowledge_base::JsonValue;
use litex::launch_command::OutputLanguage;
use litex::reading::{build_reading, ReadingInput};

trait Field {
    fn field(&self, name: &str) -> &JsonValue;
}
impl Field for JsonValue {
    fn field(&self, name: &str) -> &JsonValue {
        self.as_object()
            .ok()
            .and_then(|o| o.get(name))
            .unwrap_or(&JsonValue::Null)
    }
}
fn resolve(document: &JsonValue, value: &JsonValue) -> JsonValue {
    let mut value = value.clone();
    while value.field("kind").as_str().ok() == Some("evidence_reference") {
        value = document
            .field("evidence_nodes")
            .as_array()
            .unwrap()
            .iter()
            .find(|r| r.field("id") == value.field("evidence_id"))
            .unwrap()
            .field("node")
            .clone();
    }
    value
}
fn unwrap(document: &JsonValue, value: &JsonValue) -> JsonValue {
    let mut value = resolve(document, value);
    while value.field("fields").field("0") != &JsonValue::Null {
        value = resolve(document, value.field("fields").field("0"));
    }
    value
}
fn nodes(document: &JsonValue, name: &str) -> Vec<JsonValue> {
    document
        .field("evidence_nodes")
        .as_array()
        .unwrap()
        .iter()
        .map(|r| r.field("node"))
        .filter(|n| n.field("type").as_str().ok() == Some(name))
        .cloned()
        .collect()
}
fn build(source: &str, success: bool) -> JsonValue {
    let built = build_reading(
        &ReadingInput::Source(source.into()),
        true,
        OutputLanguage::English,
    );
    assert_eq!(built.success, success, "{source}");
    for s in built.document.field("statements").as_array().unwrap() {
        if s.field("status").as_str().ok() == Some("rejected") {
            assert!(s.field("produced_fact_ids").as_array().unwrap().is_empty());
            assert!(s.field("inferred_fact_ids").as_array().unwrap().is_empty());
        }
    }
    built.document
}

#[test]
fn nonempty_failure_retains_completed_groups_and_discarded_scope() {
    let d = build("have a R, b {}, c R", false);
    let contexts = nodes(&d, "ExecHaveObjInNonemptySetLocalFailure");
    assert_eq!(contexts.len(), 1);
    let f = contexts[0].field("fields");
    assert_eq!(f.field("completed_groups").as_array().unwrap().len(), 1);
    let stage = resolve(&d, f.field("failure"));
    assert_eq!(stage.field("variant").as_str().unwrap(), "Nonempty");
    assert_ne!(
        stage.field("fields").field("param_type_well_defined"),
        &JsonValue::Null
    );
    let scope = resolve(&d, f.field("local_env"));
    assert_ne!(scope.field("scope_id"), &JsonValue::Null);
    let source = d.field("statements").as_array().unwrap().first().unwrap();
    assert!(d
        .field("scopes")
        .as_array()
        .unwrap()
        .iter()
        .any(|s| s.field("id") == scope.field("scope_id")
            && s.field("statement_id") == source.field("id")));
}
#[test]
fn membership_failure_retains_value_checks_and_the_successful_first_membership() {
    let d = build("have a, b N = 1, -1", false);
    let contexts = nodes(&d, "ExecHaveObjEqualAfterPreflightFailure");
    assert_eq!(contexts.len(), 1);
    let f = contexts[0].field("fields");
    let stage = resolve(&d, f.field("failure"));
    assert_eq!(stage.field("variant").as_str().unwrap(), "Membership");
    let f = stage.field("fields");
    assert_eq!(
        f.field("equal_to_well_defined").as_array().unwrap().len(),
        2
    );
    assert_eq!(f.field("checked").as_array().unwrap().len(), 1);
    assert_ne!(f.field("failed"), &JsonValue::Null);
}
#[test]
fn right_value_failure_keeps_only_the_executed_value_prefix() {
    let d = build("have a, b R = 1, 1 / 0", false);
    let contexts = nodes(&d, "ExecHaveObjEqualAfterPreflightFailure");
    assert_eq!(contexts.len(), 1);
    let f = contexts[0].field("fields");
    assert_ne!(f.field("type_local_env"), &JsonValue::Null);
    let stage = resolve(&d, f.field("failure"));
    assert_eq!(stage.field("variant").as_str().unwrap(), "ValueWd");
    assert_eq!(
        stage
            .field("fields")
            .field("checked")
            .as_array()
            .unwrap()
            .len(),
        1
    );
}
#[test]
fn shared_parameter_wd_failure_preserves_real_preceding_type_and_store_records() {
    let d = build("have a R, b {1 / 0} = 1, 0", false);
    let contexts = nodes(&d, "ExecHaveObjEqualPreflightFailure");
    assert_eq!(contexts.len(), 1);
    let failure = resolve(&d, contexts[0].field("fields").field("failure"));
    assert_eq!(
        failure.field("variant").as_str().unwrap(),
        "ParamTypeWithPrefix"
    );
    let f = failure.field("fields");
    assert_eq!(
        f.field("param_type_well_defined").as_array().unwrap().len(),
        1
    );
    let defined = resolve(&d, f.field("defined_params"));
    assert_eq!(
        defined
            .field("fields")
            .field("store_and_infer_results")
            .as_array()
            .unwrap()
            .len(),
        1
    );
}
#[test]
fn obtain_count_failure_retains_the_already_verified_existential_source() {
    let d = build(
        "witness exist u R st {u=2} from 2\nobtain a,b from exist u R st {u=2}",
        false,
    );
    let contexts = nodes(&d, "ExecObtainObjFromExistFactVerifiedFailure");
    assert_eq!(contexts.len(), 1);
    let f = contexts[0].field("fields");
    let verified = unwrap(&d, f.field("verify_exist"));
    assert_eq!(
        verified.field("type").as_str().unwrap(),
        "VerifyPlainExistFactSuccess"
    );
    let failure = resolve(&d, f.field("failure"));
    assert_eq!(failure.field("variant").as_str().unwrap(), "ArityMismatch");
    assert_eq!(
        failure.field("fields").field("expected"),
        &JsonValue::String("1".into())
    );
    assert_eq!(
        failure.field("fields").field("got"),
        &JsonValue::String("2".into())
    );
}
#[test]
fn predicate_obtain_retains_projection_and_source_verification_before_bad_count() {
    let d=build("prop copy(t R):\n    exist x R st {x=t}\nwitness exist u R st {u=2} from 2\nby def $copy(2)\nobtain a,b from $copy(2)",false);
    let contexts = nodes(&d, "ExecObtainObjFromAtomicFactVerifiedFailure");
    assert_eq!(contexts.len(), 1);
    let f = contexts[0].field("fields");
    let projected = resolve(&d, f.field("projected_exist"));
    assert_eq!(projected.field("variant").as_str().unwrap(), "Exist");
    assert_ne!(f.field("verify_atomic"), &JsonValue::Null);
}
#[test]
fn failed_existence_introduction_retains_its_real_synthesized_goal() {
    let d = build("have n N:\n    n < 0", false);
    let contexts = nodes(&d, "ExecHaveObjByExistFactsFailure");
    assert_eq!(contexts.len(), 1);
    let f = contexts[0].field("fields");
    let existential = resolve(&d, f.field("exist_family"));
    assert_eq!(existential.field("variant").as_str().unwrap(), "Exist");
    let failure = resolve(&d, f.field("failed"));
    assert_eq!(
        failure.field("variant").as_str().unwrap(),
        "FailToSearchProof"
    );
    let goal = unwrap(&d, f.field("exist_family"));
    let attempted = unwrap(&d, failure.field("fields").field("fact"));
    assert_eq!(
        goal.field("fields").field("fact_id"),
        attempted.field("fields").field("fact_id")
    );
}

#[test]
fn dependent_carriers_keep_the_actual_instantiated_annotation_for_each_value() {
    let d = build("have A set, x cart(A,A) = R, (1,{})", false);
    let context = nodes(&d, "ExecHaveObjEqualAfterPreflightFailure");
    assert_eq!(context.len(), 1);
    let stage = resolve(&d, context[0].field("fields").field("failure"));
    let f = stage.field("fields");
    let types = f.field("instantiated_types").as_array().unwrap();
    let requirements = f.field("requirements").as_array().unwrap();
    assert_eq!(types.len(), 2);
    assert_eq!(requirements.len(), 2);
    assert_eq!(
        resolve(&d, &types[0]).field("variant").as_str().unwrap(),
        "Set"
    );
    let domain = resolve(&d, &types[1]);
    assert_eq!(domain.field("variant").as_str().unwrap(), "Obj");
    let actual = unwrap(&d, &requirements[1]);
    assert_eq!(actual.field("type").as_str().unwrap(), "InFact");
    assert_eq!(
        resolve(&d, actual.field("fields").field("set")),
        resolve(&d, domain.field("fields").field("0"))
    );
}
