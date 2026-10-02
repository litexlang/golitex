use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn parse_succeeds(code: &str) -> bool {
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let blocks = Tokenizer::new()
        .tokenize(code, runtime.current_file.clone())
        .expect("test source must tokenize");
    runtime.parse(&blocks).is_ok()
}

#[test]
fn parser_input_integrity_rejects_nested_exist_suffixes() {
    for code in [
        "forall x R:\n    exist y R st {y = x} and 0 = 1",
        "prop P(x R):\n    exist y R st {y = x} garbage",
        "forall x R:\n    exist y R st {y = x} garbage\n    =>:\n        x = x",
        "forall x R:\n    =>:\n        exist y R st {y = x} garbage\n    <=>:\n        x = x",
        "forall x R:\n    =>:\n        x = x\n    <=>:\n        exist y R st {y = x} garbage",
        "trust exist y R st {y = 0} garbage",
        "trust:\n    exist y R st {y = 0} garbage",
        "prop P(x R):\n    not exist y R st {y = x} garbage",
    ] {
        assert!(!parse_succeeds(code), "accepted unconsumed input: {code}");
    }
}

#[test]
fn parser_input_integrity_rejects_iff_header_suffixes() {
    for code in [
        "forall x R:\n    =>: garbage:\n        x = x\n    <=>:\n        x = x",
        "forall x R:\n    =>:\n        x = x\n    <=>: garbage:\n        x = x",
    ] {
        assert!(!parse_succeeds(code), "accepted unconsumed block header: {code}");
    }
}

#[test]
fn parser_input_integrity_preserves_exist_consumers() {
    for code in [
        "witness exist k R st {k = 0} from 0",
        "obtain k from exist k R st {k = 0}",
        "forall x R:\n    exist y R st {y = x}",
        "forall x R => exist y R st {y = x}",
        "prop P(x R):\n    exist y R st {y = x}",
        "forall x R:\n    =>:\n        x = x\n    <=>:\n        x = x",
    ] {
        assert!(parse_succeeds(code), "rejected valid source: {code}");
    }
}

#[test]
fn inline_forall_separates_premise_from_conclusion() {
    for code in [
        "forall x R: x > 0 => x > 0",
        "forall x R: x > 0 and x < 1 => x < 1",
        "forall x R: exist y R st {y = x} => x = x",
        "forall x R: forall y R => y = y => x = x",
    ] {
        assert!(parse_succeeds(code), "rejected inline forall: {code}");
    }
    for code in [
        "forall x R: => x = x",
        "forall x R: x > 0 =>",
        "forall x R: x > 0 garbage => x = x",
        "forall x R: x > 0 => x = x garbage",
        "forall x R: x > 0 => x = x => x = x",
    ] {
        assert!(!parse_succeeds(code), "accepted malformed inline forall: {code}");
    }
}

#[test]
fn induction_selects_existing_binder_without_declaration_shadowing() {
    assert!(parse_succeeds("thm refl:\n    ? forall n N:\n        n = n\n    by induc n from 0:\n        ? n = n\n        ? from n = 0:\n            0 = 0\n        ? induc:\n            n + 1 = n + 1"));
    assert!(!parse_succeeds("forall n N:\n    forall n N:\n        n = n"));
}
