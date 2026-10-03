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
fn repeated_atomic_negation_preserves_parity_and_signature_validation() {
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(), session: false, strict: true, language: OutputLanguage::English,
    });
    assert!(runtime.run_litex_code("prop zero(x R):\n    x = 0\n").unwrap().success);
    // Negative predicate folding is a separate search limitation. Prove the
    // negative fact explicitly so this test isolates parsing and citation.
    assert!(runtime.run_litex_code("by contra:\n    ? not $zero(1)\n    $zero(1)\n    1 = 0\n    impossible 1 = 0\n").unwrap().success);
    for code in [
        "not not $zero(0)\n", "not not not $zero(1)\n",
        "not not not not 1 = 1\n", "1 = 1 and not not not 1 = 2\n",
    ] {
        let run = runtime.run_litex_code(code).unwrap();
        assert!(run.session_error.is_none(), "{code}: {:?}", run.session_error);
        assert!(run.success, "{code}");
    }
    for code in ["not not $zero(1)\n", "not not not $zero(0)\n", "not not $zero()\n", "not not $missing(0)\n", "0 = 1\n"] {
        let run = runtime.run_litex_code(code).unwrap();
        assert!(run.session_error.is_none());
        assert!(!run.success, "{code}");
    }
    assert!(!parse_succeeds("not not 1 < 2 < 3"));
}

#[test]
fn signed_conjunctions_preserve_each_atomic_polarity_and_reject_false_goals() {
    use crate::ast::fact::{AtomicFact, Fact};
    use crate::ast::stmt::Stmt;
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(), session: false, strict: true, language: OutputLanguage::English,
    });
    let blocks = Tokenizer::new().tokenize("1 = 1 and not 1 = 2\n", runtime.current_file.clone()).unwrap();
    let stmts = runtime.parse(&blocks).unwrap();
    let Stmt::Fact(Fact::AndFact(and)) = &stmts[0] else { panic!("expected conjunction"); };
    assert!(matches!(&and.facts[0], AtomicFact::EqualFact(_)));
    assert!(matches!(&and.facts[1], AtomicFact::NotEqualFact(_)));
    for code in [
        include_str!("../../../examples/wd/signed_conjunctions.lit"),
        "forall x R:\n    x = 0 and not x = 1\n    =>:\n        not x = 1 and x = 0\n",
    ] {
        let run = runtime.run_litex_code(code).unwrap();
        assert!(run.session_error.is_none(), "{code}: {:?}", run.session_error);
        assert!(run.success, "{code}");
    }
    for code in ["1 = 1 and not 1 = 1\n", "not 1 = 1 or 1 = 2\n", "0 = 1\n"] {
        let run = runtime.run_litex_code(code).unwrap();
        assert!(run.session_error.is_none());
        assert!(!run.success, "{code}");
    }
    assert_eq!(runtime.execution_environments_stack.len(), 1);
}

#[test]
fn signed_conjunctions_preserve_existing_chain_and_quantifier_boundaries() {
    for code in [
        "not 1 < 2 < 3", "1 = 1 and 1 < 2 < 3",
        "1 = 1 and not", "not exist! x R st {x = 0}",
        "witness exist x R st {x = 0 and not x = 1} from 0 garbage",
    ] {
        assert!(!parse_succeeds(code), "accepted malformed source: {code}");
    }
    for code in [
        "not exist x R st {x = 0}",
        "not forall x R:\n    x = 0", "1 < 2 < 3",
    ] {
        assert!(parse_succeeds(code), "rejected existing form: {code}");
    }
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
