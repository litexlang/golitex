use super::*;

fn insert_object(environment: &mut ExecEnv, name: &str, symbol_id: u64) {
    insert_symbol(environment, name, symbol_id, SymbolRole::Object);
}

fn insert_symbol(environment: &mut ExecEnv, name: &str, symbol_id: u64, role: SymbolRole) {
    let binding = SymbolBinding::new(SymbolId::new(symbol_id), name.to_string(), name.to_string());
    environment
        .definitions
        .symbols
        .insert(SymbolDefinition::new(binding, role))
        .expect("test symbol name should be fresh");
}

fn remember_transparent_object_definition(
    environment: &mut ExecEnv,
    name: &str,
    value: Obj,
    fact_id: u64,
) {
    let binding = environment
        .definitions
        .symbols
        .get(name)
        .expect("the transparent symbol should already exist")
        .binding()
        .clone();
    let equality = EqualFact::new(
        Identifier::new_bound(name.to_string(), binding.as_ref()).into(),
        value.clone(),
        default_line_file(),
    );
    environment
        .definitions
        .symbols
        .get_by_id_mut(binding.id())
        .expect("the transparent symbol should remain addressable by ID")
        .remember_transparent_object_definition(TransparentObjectDefinition::new(
            value,
            equality,
            FactId::new(fact_id),
        ))
        .expect("the test installs one definition");
}

#[test]
fn committed_child_reuses_exact_symbol_identity_idempotently() {
    let mut parent = ExecEnv::new_empty_env();
    let mut child = ExecEnv::new_empty_env();
    insert_object(&mut parent, "\\template_instance<X>", 17);
    insert_object(&mut child, "\\template_instance<X>", 17);

    parent
        .merge_committed_child(child)
        .expect("the exact interned template instance is an idempotent commit");

    assert_eq!(
        parent
            .definitions
            .symbols
            .get("\\template_instance<X>")
            .expect("parent symbol remains present")
            .binding()
            .id(),
        SymbolId::new(17)
    );
    assert_eq!(
        parent
            .definitions
            .object_symbol("\\template_instance<X>")
            .map(SymbolDefinition::role),
        Some(SymbolRole::Object)
    );
}

#[test]
fn committed_child_preserves_missing_direct_struct_carrier_for_the_same_symbol() {
    let mut parent = ExecEnv::new_empty_env();
    let mut child = ExecEnv::new_empty_env();
    insert_object(&mut parent, "shared", 17);
    insert_object(&mut child, "shared", 17);
    child
        .definitions
        .symbols
        .get_by_id_mut(SymbolId::new(17))
        .expect("the child symbol should exist")
        .remember_direct_struct_carrier_if_absent(StructObj::new(
            AtomicName::WithoutMod("Pair".to_string()),
            vec![],
        ));

    parent
        .merge_committed_child(child)
        .expect("matching symbol identity should merge definition metadata");

    assert_eq!(
        parent
            .definitions
            .symbols
            .get_by_id(SymbolId::new(17))
            .and_then(SymbolDefinition::direct_struct_carrier)
            .map(ToString::to_string)
            .as_deref(),
        Some("&Pair")
    );
}

#[test]
fn committed_child_preserves_missing_transparent_definition_for_the_same_symbol() {
    let mut parent = ExecEnv::new_empty_env();
    let mut child = ExecEnv::new_empty_env();
    insert_object(&mut parent, "shared", 17);
    insert_object(&mut child, "shared", 17);
    remember_transparent_object_definition(&mut child, "shared", StandardSet::R.into(), 23);

    parent
        .merge_committed_child(child)
        .expect("matching symbol identity should merge transparent metadata");

    let transparent = parent
        .definitions
        .symbols
        .get_by_id(SymbolId::new(17))
        .and_then(SymbolDefinition::transparent_object_definition)
        .expect("the parent should retain the child's transparent definition");
    assert_eq!(transparent.value().to_string(), "R");
    assert_eq!(transparent.defining_equality_fact_id(), FactId::new(23));
}

#[test]
fn committed_child_rejects_conflicting_transparent_definition_for_the_same_symbol() {
    let mut parent = ExecEnv::new_empty_env();
    let mut child = ExecEnv::new_empty_env();
    insert_object(&mut parent, "shared", 17);
    insert_object(&mut child, "shared", 17);
    remember_transparent_object_definition(&mut parent, "shared", StandardSet::R.into(), 23);
    remember_transparent_object_definition(&mut child, "shared", StandardSet::C.into(), 24);

    let error = parent
        .merge_committed_child(child)
        .expect_err("one symbol identity cannot acquire two transparent definitions");

    assert!(matches!(error, RuntimeError::NameAlreadyUsedError(_)));
}

#[test]
fn committed_child_still_rejects_same_name_with_distinct_symbol_identity() {
    let mut parent = ExecEnv::new_empty_env();
    let mut child = ExecEnv::new_empty_env();
    insert_object(&mut parent, "\\template_instance<X>", 17);
    insert_object(&mut child, "\\template_instance<X>", 18);

    let error = parent
        .merge_committed_child(child)
        .expect_err("same spelling with a distinct identity must remain a conflict");

    assert!(matches!(error, RuntimeError::NameAlreadyUsedError(_)));
}

#[test]
fn committed_child_still_rejects_same_symbol_identity_with_distinct_role() {
    let mut parent = ExecEnv::new_empty_env();
    let mut child = ExecEnv::new_empty_env();
    insert_symbol(&mut parent, "shared", 17, SymbolRole::Object);
    insert_symbol(&mut child, "shared", 17, SymbolRole::Predicate);

    let error = parent
        .merge_committed_child(child)
        .expect_err("one symbol identity cannot change definition role during commit");

    assert!(matches!(error, RuntimeError::NameAlreadyUsedError(_)));
}

#[test]
fn committed_child_still_rejects_same_symbol_identity_with_object_and_binder_roles() {
    let mut parent = ExecEnv::new_empty_env();
    let mut child = ExecEnv::new_empty_env();
    insert_symbol(&mut parent, "shared", 17, SymbolRole::Object);
    insert_symbol(&mut child, "shared", 17, SymbolRole::Binder);

    let error = parent
        .merge_committed_child(child)
        .expect_err("one symbol identity cannot change symbol role during commit");

    assert!(matches!(error, RuntimeError::NameAlreadyUsedError(_)));
}

#[test]
fn committed_child_keeps_a_function_definition_signature_paired_with_its_rhs() {
    let mut parent = ExecEnv::new_empty_env();
    let mut child = ExecEnv::new_empty_env();
    let parent_binding = SymbolBinding::new(SymbolId::new(17), "x".to_string(), "x".to_string());
    let child_binding = SymbolBinding::new(SymbolId::new(18), "x".to_string(), "x".to_string());
    let body = |binding: &SymbolBinding| {
        FnSetBody::new(
            vec![SetBoundParameterGroup::new(
                vec![binding.clone()],
                StandardSet::R.into(),
            )],
            vec![],
            StandardSet::R.into(),
        )
    };

    let parent_info = parent.objects.function_set_mut("f".to_string());
    parent_info.fn_set = Some((body(&parent_binding), default_line_file()));
    parent_info.equal_to = Some((
        BoundParamObj::new(&parent_binding).into(),
        default_line_file(),
    ));

    let child_info = child.objects.function_set_mut("f".to_string());
    child_info.fn_set = Some((body(&child_binding), default_line_file()));

    parent
        .merge_committed_child(child)
        .expect("an inferred child signature should merge without splitting the definition pair");

    let merged = parent
        .objects
        .function_set("f")
        .expect("the parent definition should remain available");
    assert_eq!(
        merged
            .fn_set
            .as_ref()
            .expect("the paired signature remains present")
            .0
            .get_param_bindings()[0]
            .id(),
        parent_binding.id()
    );
    assert!(matches!(
        merged.equal_to.as_ref().map(|(obj, _)| obj),
        Some(Obj::Atom(AtomObj::Bound(param))) if param.symbol.id() == parent_binding.id()
    ));
}
