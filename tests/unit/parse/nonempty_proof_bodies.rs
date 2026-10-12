use crate::prelude::*;

#[test]
fn proof_blocks_reject_missing_or_comment_only_processes() {
    for (code, syntax) in [
        ("claim:\n    ? 1 = 1", "claim"),
        ("claim:\n    ? forall x R:\n        x = x", "claim"),
        ("claim:\n    ? 1 = 1\n    # missing proof", "claim"),
        ("sketch:\n    # missing proof", "sketch"),
        ("strategy refl:\n    ? forall x R:\n        x = x", "strategy"),
        ("by extension:\n    ? {1} = {1}", "by extension"),
        ("have f fn(x R) R\nby fn_extension:\n    ? f = f", "by fn_extension"),
        ("by enumerate finite_set:\n    ? forall x {1}:\n        x = x", "by enumerate finite_set"),
        ("by for:\n    ? forall n range(0, 2):\n        n = n", "by for"),
        ("by induc n from 0:\n    ? n = n", "by induc"),
        ("by strong_induc n from 0:\n    ? n = n", "by strong_induc"),
        ("by induc n from 0:\n    ? n = n\n    ? from n = 0:\n        # missing proof\n    ? induc:\n        n + 1 = n + 1", "by induc ? from"),
        ("by induc n from 0:\n    ? n = n\n    ? from n = 0:\n        0 = 0\n    ? induc:\n        # missing proof", "by induc ? induc"),
        ("by strong_induc n from 0:\n    ? n = n\n    ? from n = 0:\n        0 = 0\n    ? strong_induc:\n        # missing proof", "by strong_induc ? strong_induc"),
        ("by cases:\n    ? 1 = 1\n    case 1 = 1:\n        # missing proof", "case"),
        ("witness exist x R st {x = 0} from 0:\n    # missing proof", "witness exist"),
        ("witness exist! x R st {x = 0} from 0:\n    # missing proof", "witness exist"),
        ("witness $is_nonempty_set({0}) from 0:\n    # missing proof", "witness $is_nonempty_set"),
        ("prop zero() :\n    exist x R st {x = 0}\nwitness $zero() from 0:\n    # missing proof", "witness `$P`"),
        ("release axiom_of_choice: set {{1}}:\n    # missing proof", "release axiom_of_choice"),
        ("release zorn_lemma: set {1}, prop le, prop upper, prop maximal:\n    # missing proof", "release zorn_lemma"),
    ] {
        let error = parse(code).unwrap_err();
        let RuntimeError::ParseError(error) = error else {
            panic!("expected parse error for {code}");
        };
        assert!(
            error.message == format!("{syntax}: expects a nonempty proof body")
                || error.message == "block header requires a nonempty body",
            "{code}: {}", error.message
        );
    }
    assert!(parse("by cases:\n    ? 1 = 1\n    case 1 = 1").is_err());
}

#[test]
fn proof_processes_preserve_inline_routes_and_named_theorem_omission() {
    for code in [
        "thm refl:\n    ? 1 = 1",
        "thm refl:\n    ? forall x R:\n        x = x",
        "claim:\n    ? 1 = 1\n    1 = 1",
        "sketch:\n    1 = 1",
        "strategy refl:\n    ? forall x R:\n        x = x\n    x = x",
        "by extension {1} = {1}",
        "by extension:\n    ? {1} = {1}\n    1 = 1",
        "have f fn(x R) R\nby fn_extension f = f",
        "by enumerate finite_set:\n    ? forall x {1}:\n        x = x\n    x = x",
        "by for:\n    ? forall n range(0, 2):\n        n = n\n    n = n",
        "by induc n from 0:\n    ? n = n\n    n = n",
        "by strong_induc n from 0:\n    ? n = n\n    n = n",
        "by induc n from 0:\n    ? n = n\n    ? from n = 0:\n        0 = 0\n    ? induc:\n        n + 1 = n + 1",
        "by cases:\n    ? 1 = 1\n    case 1 = 1:\n        1 = 1",
        "by cases:\n    ? 1 = 1\n    case 1 != 1:\n        impossible 1 = 1",
        "by contra:\n    ? 1 != 2\n    impossible 1 = 2",
        "witness exist x R st {x = 0} from 0",
        "witness exist x R st {x = 0} from 0:\n    x = 0",
        "witness $is_nonempty_set({0}) from 0",
        "release axiom_of_choice: set {{1}}",
        "release axiom_of_choice: set {{1}}:\n    1 = 1",
        "release zorn_lemma: set {1}, prop le, prop upper, prop maximal",
        "release zorn_lemma: set {1}, prop le, prop upper, prop maximal:\n    1 = 1",
        "forall x R:\n    x = x",
    ] {
        assert!(parse(code).is_ok(), "rejected valid source: {code}");
    }
}

#[test]
fn missing_process_diagnostic_points_to_its_block() {
    let RuntimeError::ParseError(error) = parse("# prefix\nclaim:\n    ? 1 = 1").unwrap_err()
    else {
        panic!("expected parse error");
    };
    assert_eq!(error.line, 2);
    assert_eq!(error.path, CodeSource::Eval);
}

#[test]
fn nonempty_process_is_not_a_proof_admission() {
    let mut runtime = runtime();
    for code in [
        "claim:\n    ? 1 = 2\n    1 = 1",
        "thm false_goal:\n    ? 1 = 2",
    ] {
        let result = runtime.run_litex_code(code).unwrap();
        assert!(!result.success, "accepted false goal: {code}");
        assert!(
            result.session_error.is_none(),
            "proof failure should remain an execution failure"
        );
    }
    assert!(runtime.run_litex_code("1 = 1").unwrap().success);
}

#[test]
fn nonempty_process_tracer_verifies() {
    let result = runtime()
        .run_litex_code(include_str!(
            "../../../examples/stmt_nodes/proof_block/nonempty_proof_bodies.lit"
        ))
        .unwrap();
    assert!(result.success, "{:?}", result.session_error);
}

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

fn parse(code: &str) -> RuntimeResult<Vec<Stmt>> {
    let mut runtime = runtime();
    let blocks = crate::tokenize::Tokenizer::new().tokenize(code, runtime.current_file.clone())?;
    runtime.parse(&blocks)
}
