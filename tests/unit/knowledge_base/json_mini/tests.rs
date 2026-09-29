use super::super::super::json_mini::JsonValue;

#[test]
fn round_trip_object_compact_and_pretty() {
    let v = JsonValue::object_from(vec![
        ("kind".into(), JsonValue::String("def_prop".into())),
        ("id".into(), JsonValue::Number(7.0)),
        (
            "arr".into(),
            JsonValue::Array(vec![JsonValue::Bool(true), JsonValue::Null]),
        ),
    ]);
    let compact = v.stringify();
    assert_eq!(v, JsonValue::parse(&compact).expect("parse compact"));
    let pretty = v.stringify_pretty();
    assert!(pretty.contains('\n'), "pretty JSON should be multi-line");
    assert_eq!(v, JsonValue::parse(&pretty).expect("parse pretty"));
}
