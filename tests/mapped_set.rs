use litex::knowledge_base::JsonValue;
use litex::launch_command::{LaunchCommand, OutputLanguage};
use litex::runtime::Runtime;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

#[test]
fn mapped_set_examples() {
    let mut runtime = runtime();
    let mut run = runtime
        .run_litex_code(include_str!("../examples/wd/obj/mapped_set.lit"))
        .unwrap();
    run.attach_normal_json(&runtime, "eval", None);
    assert!(run.success, "{:?}", run.normal_json);
}

#[test]
fn mapped_set_rejection_leaves_the_context_usable() {
    let mut runtime = runtime();
    assert!(runtime.run_litex_code("have for R = 2").unwrap().success);
    let cases = [
        (
            include_str!("../examples/wd_negative/mapped_set_unguarded_division.lit"),
            "well_defined",
            "x != 0",
        ),
        (
            "by def 1 + 3 $in {a + b for a $in {1}, b $in {2}}",
            "definition_requirement",
            "3 $in {2}",
        ),
        ("{x for x $in R} $subset N", "search_proof", "$subset N"),
        (
            "let escaped = {x for x $in R, y $in {x}}",
            "parse",
            "undefined name",
        ),
    ];
    for (source, phase, obligation) in cases {
        let mut run = runtime.run_litex_code(source).unwrap();
        run.attach_normal_json(&runtime, "eval", None);
        let output = run.normal_json.as_deref().expect("normal run JSON");
        assert!(!run.success && run.session_error.is_none(), "{output}");
        let json = JsonValue::parse(output).unwrap();
        let errors = json
            .as_object()
            .unwrap()
            .get("errors")
            .unwrap()
            .as_array()
            .unwrap();
        assert_eq!(errors.len(), 1, "{output}");
        let error = errors[0].as_object().unwrap();
        assert_eq!(
            error.get("phase").unwrap().as_str().unwrap(),
            phase,
            "{output}"
        );
        let field = if phase == "parse" {
            "message"
        } else {
            "obligation"
        };
        assert!(
            error
                .get(field)
                .unwrap()
                .as_str()
                .unwrap()
                .contains(obligation),
            "{output}"
        );
    }
    let run = runtime
        .run_litex_code("{for} = {2}\n$is_set({for + x for x $in R})")
        .unwrap();
    assert!(run.success, "{:?}", run.normal_json);
}
