use super::*;

fn insert_object(environment: &mut Environment, name: &str, symbol_id: u64, kind: ParamObjType) {
    insert_symbol(environment, name, symbol_id, SymbolRole::Object);
    environment
        .defined_identifiers
        .insert(name.to_string(), kind);
}

fn insert_symbol(environment: &mut Environment, name: &str, symbol_id: u64, role: SymbolRole) {
    let binding = SymbolBinding::new(SymbolId::new(symbol_id), name.to_string(), name.to_string());
    environment
        .symbols
        .insert(SymbolDefinition::new(binding, role))
        .expect("test symbol name should be fresh");
}

#[test]
fn committed_child_reuses_exact_symbol_identity_idempotently() {
    let mut parent = Environment::new_empty_env();
    let mut child = Environment::new_empty_env();
    insert_object(
        &mut parent,
        "\\template_instance<X>",
        17,
        ParamObjType::Identifier,
    );
    insert_object(
        &mut child,
        "\\template_instance<X>",
        17,
        ParamObjType::Identifier,
    );

    parent
        .merge_committed_child(child)
        .expect("the exact interned template instance is an idempotent commit");

    assert_eq!(
        parent
            .symbols
            .get("\\template_instance<X>")
            .expect("parent symbol remains present")
            .binding()
            .id(),
        SymbolId::new(17)
    );
    assert_eq!(
        parent.defined_identifiers.get("\\template_instance<X>"),
        Some(&ParamObjType::Identifier)
    );
}

#[test]
fn committed_child_still_rejects_same_name_with_distinct_symbol_identity() {
    let mut parent = Environment::new_empty_env();
    let mut child = Environment::new_empty_env();
    insert_object(
        &mut parent,
        "\\template_instance<X>",
        17,
        ParamObjType::Identifier,
    );
    insert_object(
        &mut child,
        "\\template_instance<X>",
        18,
        ParamObjType::Identifier,
    );

    let error = parent
        .merge_committed_child(child)
        .expect_err("same spelling with a distinct identity must remain a conflict");

    assert!(matches!(error, RuntimeError::NameAlreadyUsedError(_)));
}

#[test]
fn committed_child_still_rejects_same_symbol_identity_with_distinct_role() {
    let mut parent = Environment::new_empty_env();
    let mut child = Environment::new_empty_env();
    insert_symbol(&mut parent, "shared", 17, SymbolRole::Object);
    insert_symbol(&mut child, "shared", 17, SymbolRole::Predicate);

    let error = parent
        .merge_committed_child(child)
        .expect_err("one symbol identity cannot change declaration role during commit");

    assert!(matches!(error, RuntimeError::NameAlreadyUsedError(_)));
}

#[test]
fn committed_child_still_rejects_same_symbol_identity_with_distinct_identifier_kind() {
    let mut parent = Environment::new_empty_env();
    let mut child = Environment::new_empty_env();
    insert_object(&mut parent, "shared", 17, ParamObjType::Identifier);
    insert_object(&mut child, "shared", 17, ParamObjType::Forall);

    let error = parent
        .merge_committed_child(child)
        .expect_err("one symbol identity cannot change identifier kind during commit");

    assert!(matches!(error, RuntimeError::NameAlreadyUsedError(_)));
}
