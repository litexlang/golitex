use crate::parse::Tokenizer;
use crate::prelude::*;
use std::rc::Rc;

fn parse_one_fact_line(line: &str) -> Result<Fact, RuntimeError> {
    let mut rt = Runtime::new();
    let tokenizer = Tokenizer::new();
    let mut blocks = tokenizer.parse_blocks(line, Rc::from("test.lit"))?;
    assert_eq!(blocks.len(), 1, "{line:?}");
    rt.parse_fact(&mut blocks[0])
}

fn parse_error_msg(line: &str) -> String {
    let err = parse_one_fact_line(line).unwrap_err();
    let RuntimeError::ParseError(s) = err else {
        panic!("expected parse error, got {err:?}");
    };
    s.msg
}

#[test]
fn inline_forall_no_colon_before_arrow_when_no_dom() {
    let f = parse_one_fact_line("forall x R => x > 0").unwrap();
    let Fact::ForallFact(ff) = f else {
        panic!("expected ForallFact");
    };
    assert!(ff.dom_facts.is_empty());
    assert_eq!(ff.then_facts.len(), 1);
}

#[test]
fn inline_forall_dom_arrow_then() {
    let f = parse_one_fact_line("forall x R: x > 0 => x >= 0").unwrap();
    let Fact::ForallFact(ff) = f else {
        panic!("expected ForallFact");
    };
    assert_eq!(ff.dom_facts.len(), 1);
    assert_eq!(ff.then_facts.len(), 1);
}

#[test]
fn inline_forall_rejects_single_then_without_arrow() {
    let msg = parse_error_msg("forall x R: x > 0");
    assert!(msg.contains("Expected body"), "{}", msg);
}

#[test]
fn inline_forall_rejects_no_colon_braced_then_when_no_dom() {
    let msg = parse_error_msg("forall x R { x > 0, x + 1 > 1 }");
    assert!(msg.contains("expected `:` or `=>`"), "{}", msg);
}

#[test]
fn inline_forall_rejects_empty_dom_arrow() {
    let msg = parse_error_msg("forall x R: => x > 0");
    assert!(msg.contains("exactly one domain fact"), "{}", msg);
}

#[test]
fn inline_forall_rejects_nested_in_dom() {
    let msg = parse_error_msg("forall x R: forall y R => y > 0 => x > 0");
    assert!(msg.contains("nested `forall`"), "{}", msg);
}

#[test]
fn inline_forall_rejects_multiple_domain_facts() {
    let msg = parse_error_msg("forall x R: x > 0, x < 1 => x >= 0");
    assert!(msg.contains("exactly one domain fact"), "{}", msg);
}

#[test]
fn inline_forall_rejects_braced_then() {
    let msg = parse_error_msg("forall x R: x > 0 => {x >= 0}");
    assert!(msg.contains("must not use braces"), "{}", msg);
}

#[test]
fn inline_forall_rejects_multiple_then_facts() {
    let msg = parse_error_msg("forall x R: x > 0 => x >= 0, x + 1 > 0");
    assert!(msg.contains("unexpected token"), "{}", msg);
}

#[test]
fn not_inline_forall_parses_as_not_forall() {
    let f = parse_one_fact_line("not forall x R: x > 0 => x + 1 > 1").unwrap();
    assert!(matches!(f, Fact::NotForall(_)));
}

#[test]
fn unicode_and_ascii_facts_share_one_canonical_representation() {
    let cases = [
        ("forall x R => x != pi", "∀ x ℝ → x ≠ π"),
        ("exist x N st {x $in {}}", "∃ x ℕ st {x ∈ ∅}"),
        ("exist! x N st {x = 0}", "∃! x ℕ st {x = 0}"),
        ("0 <= 1 and 1 >= 0", "0 ≤ 1 ∧ 1 ≥ 0"),
        ("not 0 = 1 or 1 $in Z", "¬ 0 = 1 ∨ 1 ∈ ℤ"),
        ("N $subset Z", "ℕ ⊆ ℤ"),
        ("Z $superset N", "ℤ ⊇ ℕ"),
        ("{0} $proper_subset {0, 1}", "{0} ⊊ {0, 1}"),
        ("{0} $proper_subset {0, 1}", "{0} ⊂ {0, 1}"),
        ("{0, 1} $proper_superset {0}", "{0, 1} ⊋ {0}"),
        ("not x $in union(intersect(A, B), C)", "x ∉ A ∩ B ∪ C"),
        ("cart(A, B, C) = cart(A, B, C)", "A × B × C = cart(A, B, C)"),
        ("1 $in N+", "1 ∈ ℕ+"),
        ("1 $in Z+", "1 ∈ ℤ+"),
        ("1 $in Q+", "1 ∈ ℚ+"),
        ("1 $in R+", "1 ∈ ℝ+"),
        ("-1 $in Z-", "-1 ∈ ℤ-"),
        ("-1 $in Q-", "-1 ∈ ℚ-"),
        ("-1 $in R-", "-1 ∈ ℝ-"),
        ("1 $in Z*", "1 ∈ ℤ*"),
        ("1 $in Q*", "1 ∈ ℚ*"),
        ("1 $in R*", "1 ∈ ℝ*"),
        ("1 $in C*", "1 ∈ ℂ*"),
    ];

    for (ascii, unicode) in cases {
        let ascii_fact = parse_one_fact_line(ascii).unwrap();
        let unicode_fact = parse_one_fact_line(unicode).unwrap();
        assert_eq!(
            ascii_fact.to_string(),
            unicode_fact.to_string(),
            "{unicode}"
        );
    }

    assert!(
        parse_one_fact_line("1 ∈ ℕ*").is_err(),
        "ℕ* must remain unsupported because N* is not a standard set"
    );
}

#[test]
fn unicode_not_in_is_a_negated_membership_operator() {
    assert_eq!(
        parse_one_fact_line("x ∉ A").unwrap().to_string(),
        "not x $in A"
    );
    assert_eq!(
        parse_one_fact_line("not x ∉ A").unwrap().to_string(),
        "x $in A"
    );

    let msg = parse_error_msg("x ∉ A $subset B");
    assert!(msg.contains("cannot be part of a fact chain"), "{msg}");
}

#[test]
fn inline_forall_then_rejects_nested_forall() {
    let msg = parse_error_msg("forall x R: x > 0 => forall y R: y > 0 => x + y > 0");
    assert!(msg.contains("cannot contain another forall"), "{msg}");
}

#[test]
fn existential_body_rejects_inline_forall() {
    let msg = parse_error_msg("exist x R st {forall y R => y = y}");
    assert!(
        msg.contains("inline `forall` is not allowed in existential or set-builder bodies"),
        "{}",
        msg
    );
}

#[test]
fn set_builder_body_rejects_inline_forall() {
    let msg = parse_error_msg("{x R: forall y R => y = y} = {x R: x = x}");
    assert!(
        msg.contains("inline `forall` is not allowed in existential or set-builder bodies"),
        "{}",
        msg
    );
}

#[test]
fn flat_forall_computes_dependent_parameter_indices() {
    let fact = parse_one_fact_line("forall S nonempty_set, x S, y S => x = y").unwrap();
    let Fact::ForallFact(forall_fact) = fact else {
        panic!("expected a flat forall fact");
    };
    assert_eq!(forall_fact.params_def_with_type.number_of_params(), 3);
    assert_eq!(
        forall_fact
            .params_def_with_type
            .cited_param_indices_for_group(0),
        []
    );
    assert_eq!(
        forall_fact
            .params_def_with_type
            .cited_param_indices_for_group(1),
        [0]
    );
    assert_eq!(
        forall_fact
            .params_def_with_type
            .cited_param_indices_for_group(2),
        [0]
    );
}

#[test]
fn block_forall_then_rejects_nested_forall() {
    let msg = parse_error_msg(
        "forall x R:\n    x > 0\n    =>:\n        forall y R:\n            x + y > 0",
    );
    assert!(msg.contains("cannot contain another forall"), "{msg}");
}

#[test]
fn block_forall_without_arrow_rejects_nested_forall() {
    let msg = parse_error_msg("forall x R:\n    forall y R:\n        x + y = y + x");
    assert!(msg.contains("cannot contain another forall"), "{msg}");
}

#[test]
fn forall_conclusion_rejects_not_forall() {
    let msg = parse_error_msg("forall x R:\n    not forall y R:\n        x = x");
    assert!(msg.contains("cannot contain `not forall`"), "{msg}");
}
