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
    let v =
        JsonValue::parse(r#"{"中文键":"/Users/主要文件夹/é/🙂","escaped":"\u4e2d\u6587\n\"\\"}"#)
            .expect("parse literal UTF-8 and escaped Unicode");
    let map = v.as_object().unwrap();
    assert_eq!(
        JsonValue::get(map, "中文键").unwrap().as_str().unwrap(),
        "/Users/主要文件夹/é/🙂"
    );
    assert_eq!(
        JsonValue::get(map, "escaped").unwrap().as_str().unwrap(),
        "中文\n\"\\"
    );
    assert_eq!(JsonValue::parse(&v.stringify()).unwrap(), v);
    assert_eq!(JsonValue::parse(&v.stringify_pretty()).unwrap(), v);
    assert!(JsonValue::parse(r#""\uZZZZ""#).is_err());
    assert!(JsonValue::parse(r#""unfinished"#).is_err());
}

#[test]
fn json_string_escapes_and_utf16_pairs_decode_and_round_trip() {
    let escaped =
        JsonValue::parse(r#""\b\f\n\r\t\/\"\\\ud83d\ude00\uD800\uDC00\udbff\udfff""#).unwrap();
    assert_eq!(
        escaped.as_str().unwrap(),
        "\u{8}\u{c}\n\r\t/\"\\😀\u{10000}\u{10ffff}"
    );
    let all_controls = JsonValue::String((0u8..=31).map(char::from).collect());
    for value in [escaped, all_controls] {
        assert_eq!(JsonValue::parse(&value.stringify()).unwrap(), value);
        assert_eq!(JsonValue::parse(&value.stringify_pretty()).unwrap(), value);
    }
}

#[test]
fn json_rejects_unescaped_controls_and_malformed_surrogates() {
    for control in 0u8..=31 {
        let input = format!("\"{}\"", char::from(control));
        assert!(JsonValue::parse(&input).is_err(), "{input:?}");
    }
    for input in [
        r#""\ud800""#,
        r#""\udc00""#,
        r#""\ud800x""#,
        r#""\ud800\u0041""#,
        r#""\ud800\ud800""#,
        r#""\ud800\uZZZZ""#,
        r#""\ud800\u12""#,
        r#""\v""#,
    ] {
        assert!(JsonValue::parse(input).is_err(), "{input}");
    }
    assert_eq!(
        JsonValue::parse("\"\u{7f}😀\"").unwrap().as_str().unwrap(),
        "\u{7f}😀"
    );
}

#[test]
fn json_accepts_only_json_whitespace_and_finite_numbers() {
    assert_eq!(
        JsonValue::parse(" \t\r\n[ 1e2 , -0.5E+1 ]\r\n").unwrap(),
        JsonValue::Array(vec![JsonValue::Number(100.0), JsonValue::Number(-5.0)])
    );
    for input in [
        "\u{b}null",
        "null\u{c}",
        "[1,\u{b}2]",
        "{\u{c}\"a\":1}",
        "1e400",
        "-1e400",
        "01",
        "1.",
        "1e",
        "--1",
        "NaN",
        "Infinity",
    ] {
        assert!(JsonValue::parse(input).is_err(), "{input:?}");
    }
    let max = JsonValue::parse("1.7976931348623157e308").unwrap();
    assert_eq!(JsonValue::parse(&max.stringify()).unwrap(), max);
}

#[test]
fn json_u64_conversion_rejects_overflow_instead_of_saturating() {
    for input in ["-1", "1.5", "18446744073709551616", "1e20"] {
        assert!(
            JsonValue::parse(input).unwrap().as_u64().is_err(),
            "{input}"
        );
    }
    let largest_exact = JsonValue::Number(18446744073709549568.0);
    assert_eq!(largest_exact.as_u64().unwrap(), 18446744073709549568);
    assert_eq!(largest_exact.stringify(), "18446744073709549568");
    for value in [JsonValue::Number(0.0), JsonValue::Number(42.0)] {
        assert_eq!(JsonValue::parse(&value.stringify()).unwrap(), value);
        assert!(value.as_u64().is_ok());
    }
    let boundary = JsonValue::Number(18446744073709551616.0);
    assert_ne!(boundary.stringify(), u64::MAX.to_string());
    assert_eq!(JsonValue::parse(&boundary.stringify()).unwrap(), boundary);
}
