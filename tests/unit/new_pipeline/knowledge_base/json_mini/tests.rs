use super::super::super::json_mini::JsonValue;

#[test]
fn round_trip_object() {
    let v = JsonValue::object_from(vec![
        ("kind".into(), JsonValue::String("def_prop".into())),
        ("id".into(), JsonValue::Number(7.0)),
        (
            "arr".into(),
            JsonValue::Array(vec![JsonValue::Bool(true), JsonValue::Null]),
        ),
    ]);
    let text = v.stringify();
    let back = JsonValue::parse(&text).expect("parse");
    assert_eq!(v, back);
}
