use super::*;

#[test]
fn local_builtin_schema_accepts_every_quantifier_free_premise_shape() {
    let schema = compile_local_builtin_schema(
        r#"
forall a, b, c R:
    a <= b
    a <= b and b <= c
    a <= b <= c
    a = b or b = c
    =>:
        a + b <= c
"#,
        RuleId::new("test.quantifier_free_premises").expect("valid test rule id"),
        RuleFingerprint::from_hex("0".repeat(64)).expect("valid test fingerprint"),
    )
    .expect("all quantifier-free premise variants should compile");

    assert!(matches!(
        schema.premises[0],
        QuantifierFreeFact::AtomicFact(_)
    ));
    assert!(matches!(schema.premises[1], QuantifierFreeFact::AndFact(_)));
    assert!(matches!(
        schema.premises[2],
        QuantifierFreeFact::ChainFact(_)
    ));
    assert!(matches!(schema.premises[3], QuantifierFreeFact::OrFact(_)));
}
