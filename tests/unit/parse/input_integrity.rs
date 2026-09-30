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
