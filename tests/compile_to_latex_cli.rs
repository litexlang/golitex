use litex::knowledge_base::JsonValue;
use std::process::Command;

fn convert(args: &[&str]) -> (bool, JsonValue) {
    let output = Command::new(env!("CARGO_BIN_EXE_litex"))
        .args(args)
        .output()
        .unwrap();
    let json = String::from_utf8(output.stdout).unwrap();
    let value = JsonValue::parse(&json).unwrap_or_else(|error| {
        panic!(
            "{error:?}: {json}; stderr: {}",
            String::from_utf8_lossy(&output.stderr)
        )
    });
    (output.status.success(), value)
}
#[test]
fn every_locale_runs_through_the_real_binary() {
    for lang in [
        "en", "zh", "zh-hant", "fr", "ru", "es", "ar", "ja", "ko", "vi",
    ] {
        let (ok, json) = convert(&[
            "-latex",
            "-document",
            "-lang",
            lang,
            "-f",
            "examples/stmt_nodes/compile_to_latex/identity.lit",
        ]);
        assert!(ok, "{json:?}");
        let map = json.as_object().unwrap();
        assert_eq!(map.get("language"), Some(&JsonValue::String(lang.into())));
        assert_eq!(map.get("verified"), Some(&JsonValue::Bool(false)));
        assert!(map
            .get("content")
            .unwrap()
            .as_str()
            .unwrap()
            .contains(r"\begin{document}"));
    }
}
#[test]
fn false_facts_convert_but_invalid_syntax_fails() {
    let (ok, json) = convert(&["-latex", "-e", "1 = 2"]);
    assert!(ok);
    assert!(json
        .as_object()
        .unwrap()
        .get("content")
        .unwrap()
        .as_str()
        .unwrap()
        .contains("1 = 2"));
    let (ok, json) = convert(&["-latex", "-lang", "zh", "-e", "1 = 1\nhave"]);
    assert!(!ok);
    let map = json.as_object().unwrap();
    assert_eq!(map.get("content"), Some(&JsonValue::Null));
    assert_eq!(map.get("language"), Some(&JsonValue::String("zh".into())));
    let (ok, _) = convert(&["-latex", "-session", "-e", "1 = 1"]);
    assert!(!ok);
}
#[test]
fn project_order_names_and_file_prefix_are_parse_only() {
    let (ok, json) = convert(&["-latex", "-r", "tests/fixtures/compile_to_latex/project"]);
    assert!(ok, "{json:?}");
    let text = json
        .as_object()
        .unwrap()
        .get("content")
        .unwrap()
        .as_str()
        .unwrap();
    assert!(text.contains("3 = 3"));
    assert!(text.contains(r"\section*{alpha}") && text.contains(r"\section*{beta}"));
    assert!(text.find("a = 1").unwrap() < text.find("alpha::a").unwrap());
    assert!(text.contains(r"dep\_a::base::x"));
    assert!(text.contains(r"dep\_b::base::x"));
    assert!(!text.contains("m0::f0"));
    let (ok, json) = convert(&[
        "-latex",
        "-f",
        "tests/fixtures/compile_to_latex/project/beta.lit",
    ]);
    assert!(ok, "{json:?}");
    let text = json
        .as_object()
        .unwrap()
        .get("content")
        .unwrap()
        .as_str()
        .unwrap();
    assert!(text.contains("a = 1"));
    assert!(!text.contains("3 = 3"));
}

#[test]
fn import_cycles_and_missing_manifests_fail_without_partial_content() {
    use std::fs;
    use std::time::{SystemTime, UNIX_EPOCH};
    let temp = std::env::temp_dir().join(format!(
        "litex-latex-{}-{}",
        std::process::id(),
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    fs::create_dir_all(temp.join("dep")).unwrap();
    fs::write(
        temp.join("litex.config"),
        "[import]\ndep = \"dep\"\n[export]\nmain = \"main.lit\"\n",
    )
    .unwrap();
    fs::write(temp.join("main.lit"), "1 = 1").unwrap();
    fs::write(
        temp.join("dep/litex.config"),
        "[import]\nback = \"..\"\n[export]\nmain = \"main.lit\"\n",
    )
    .unwrap();
    let (ok, json) = convert(&["-latex", "-r", temp.to_str().unwrap()]);
    let cycle_ok = !ok && json.as_object().unwrap().get("content") == Some(&JsonValue::Null);
    let cycle_message = json
        .as_object()
        .unwrap()
        .get("error")
        .unwrap()
        .as_object()
        .unwrap()
        .get("message")
        .unwrap()
        .as_str()
        .unwrap()
        .to_string();
    fs::remove_file(temp.join("dep/litex.config")).unwrap();
    let (ok, json) = convert(&["-latex", "-lang", "zh", "-r", temp.to_str().unwrap()]);
    let missing_ok = !ok && json.as_object().unwrap().get("content") == Some(&JsonValue::Null);
    fs::remove_dir_all(&temp).unwrap();
    assert!(
        cycle_ok && cycle_message.contains("import cycle"),
        "{cycle_message}"
    );
    assert!(missing_ok, "{json:?}");
}
