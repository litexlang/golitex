use crate::prelude::*;

#[test]
fn bound_identifier_display_uses_one_canonical_symbol_identity() {
    let symbol = SymbolRef::new(SymbolId::new(17), "a::b::c".to_string());
    let local = Identifier::new_bound("c".to_string(), symbol.clone());
    let qualified = IdentifierWithMod::new_bound("a::b".to_string(), "c".to_string(), symbol);

    assert_eq!(local.to_string(), "a::b::#17#c");
    assert_eq!(qualified.to_string(), "a::b::#17#c");
    assert_eq!(
        strip_free_param_numeric_tags_in_display(&qualified.to_string()),
        "a::b::c"
    );
}

#[test]
fn display_keeps_parentheses_on_composite_divisor() {
    let one = number("1");
    let two = number("2");
    let three = number("3");

    let divided_by_product: Obj =
        Div::new(one.clone(), Mul::new(two.clone(), three.clone()).into()).into();
    let divided_by_quotient: Obj =
        Div::new(one.clone(), Div::new(two.clone(), three.clone()).into()).into();
    let left_associative_quotient: Obj = Div::new(Div::new(one, two).into(), three).into();

    assert_eq!(divided_by_product.to_string(), "1 / (2 * 3)");
    assert_eq!(divided_by_quotient.to_string(), "1 / (2 / 3)");
    assert_eq!(left_associative_quotient.to_string(), "1 / 2 / 3");
}

#[test]
fn display_uses_two_sided_interval_literals() {
    let zero = number("0");
    let one = number("1");

    assert_eq!(
        IntervalObj::new_left_open_right_open(zero.clone(), one.clone()).to_string(),
        "'(0, 1)"
    );
    assert_eq!(
        IntervalObj::new_left_open_right_closed(zero.clone(), one.clone()).to_string(),
        "'(0, 1]"
    );
    assert_eq!(
        IntervalObj::new_left_closed_right_open(zero.clone(), one.clone()).to_string(),
        "'[0, 1)"
    );
    assert_eq!(
        IntervalObj::new_left_closed_right_closed(zero, one).to_string(),
        "'[0, 1]"
    );
}

#[test]
fn display_uses_one_sided_interval_literals() {
    let zero = number("0");

    assert_eq!(
        OneSideInfinityIntervalObj::new_left_open(zero.clone()).to_string(),
        "'(0,)"
    );
    assert_eq!(
        OneSideInfinityIntervalObj::new_left_closed(zero.clone()).to_string(),
        "'[0,)"
    );
    assert_eq!(
        OneSideInfinityIntervalObj::new_right_open(zero.clone()).to_string(),
        "'(,0)"
    );
    assert_eq!(
        OneSideInfinityIntervalObj::new_right_closed(zero).to_string(),
        "'(,0]"
    );
}

fn number(value: &str) -> Obj {
    Number::new(value.to_string()).into()
}
