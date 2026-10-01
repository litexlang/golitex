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

#[test]
fn utf8_paths_keys_and_escapes_survive_round_trip() {
    let v = JsonValue::parse(
        r#"{"中文键":"/Users/主要文件夹/é/🙂","escaped":"\u4e2d\u6587\n\"\\"}"#,
    ).expect("parse literal UTF-8 and escaped Unicode");
    let map = v.as_object().unwrap();
    assert_eq!(JsonValue::get(map, "中文键").unwrap().as_str().unwrap(), "/Users/主要文件夹/é/🙂");
    assert_eq!(JsonValue::get(map, "escaped").unwrap().as_str().unwrap(), "中文\n\"\\");
    assert_eq!(JsonValue::parse(&v.stringify()).unwrap(), v);
    assert_eq!(JsonValue::parse(&v.stringify_pretty()).unwrap(), v);
    assert!(JsonValue::parse(r#""\uZZZZ""#).is_err());
    assert!(JsonValue::parse(r#""unfinished"#).is_err());
}
