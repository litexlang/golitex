use super::*;

#[test]
fn simple_set_constructors_preserve_identity_and_order() {
    let left_binding =
        SymbolBinding::new(SymbolId::new(11), "left".to_string(), "left".to_string());
    let right_binding =
        SymbolBinding::new(SymbolId::new(12), "right".to_string(), "right".to_string());
    let left: Obj = Identifier::new_bound("left".to_string(), left_binding.as_ref()).into();
    let right: Obj = Identifier::new_bound("right".to_string(), right_binding.as_ref()).into();

    let union: Obj = Union::new(left.clone(), right.clone()).into();
    assert_eq!(
        LeanTargetObjectRepresentation::lower(&union).unwrap(),
        LeanTargetObjectRepresentation::BuiltinApp {
            source_occurrence_id: None,
            semantic_key: obj_equality_key(&union),
            operator: LeanTargetBuiltinObjectOperator::Union,
            arguments: vec![
                LeanTargetObjectRepresentation::Symbol {
                    symbol_id: left_binding.id(),
                    name: "left".to_string(),
                },
                LeanTargetObjectRepresentation::Symbol {
                    symbol_id: right_binding.id(),
                    name: "right".to_string(),
                },
            ],
        }
    );

    let list: Obj = ListSet::new(vec![right, left]).into();
    assert_eq!(
        LeanTargetObjectRepresentation::lower(&list).unwrap(),
        LeanTargetObjectRepresentation::Collection {
            source_occurrence_id: None,
            semantic_key: obj_equality_key(&list),
            constructor: LeanTargetCollectionObjectConstructor::ListSet,
            items: vec![
                LeanTargetObjectRepresentation::Symbol {
                    symbol_id: right_binding.id(),
                    name: "right".to_string(),
                },
                LeanTargetObjectRepresentation::Symbol {
                    symbol_id: left_binding.id(),
                    name: "left".to_string(),
                },
            ],
        }
    );
}

#[test]
fn unresolved_symbol_is_rejected() {
    let left: Obj = Identifier::new("left".to_string()).into();
    let right: Obj = Identifier::new("right".to_string()).into();
    let unresolved: Obj = Union::new(left, right).into();

    let error = LeanTargetObjectRepresentation::lower(&unresolved).unwrap_err();
    assert!(error.contains("resolved SymbolId"));
}

#[test]
fn indexed_set_family_operators_fail_closed_until_lean_semantics_are_added() {
    let index_set: Obj = ListSet::new(vec![]).into();
    let ambient_set: Obj = StandardSet::N.into();
    let family: Obj = Identifier::new("family".to_string()).into();

    let union: Obj = IndexUnion::new(index_set.clone(), ambient_set.clone(), family.clone()).into();
    let union_error = LeanTargetObjectRepresentation::lower(&union).unwrap_err();
    assert!(union_error.contains("does not yet support `index_union`"));

    let intersection: Obj = IndexIntersect::new(index_set, ambient_set, family).into();
    let intersection_error = LeanTargetObjectRepresentation::lower(&intersection).unwrap_err();
    assert!(intersection_error.contains("does not yet support `index_intersect`"));
}

#[test]
fn set_builder_is_an_explicit_binder_boundary() {
    let binding = SymbolBinding::new(SymbolId::new(7), "x".to_string(), "x".to_string());
    let parameter: Obj = SetBuilderFreeParamObj::new(binding.as_ref()).into();
    let builder: Obj = SetBuilder::new(
        binding.clone(),
        StandardSet::R.into(),
        vec![EqualFact::new(parameter.clone(), parameter, default_line_file()).into()],
    )
    .expect("test set-builder should be well formed")
    .into();

    let lowered = LeanTargetObjectRepresentation::lower(&builder)
        .expect("a set-builder has no target carrier to resolve");
    let LeanTargetObjectRepresentation::SetBuilder(lowered) = lowered else {
        panic!("expected an explicit set-builder representation node")
    };
    assert_eq!(lowered.symbol_id, binding.id());
    assert_eq!(lowered.name, "x");
    assert_eq!(
        lowered.set.as_ref(),
        &LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Real)
    );
    assert_eq!(lowered.facts.len(), 1);
    assert_eq!(lowered.facts[0].to_string(), "#7#x = #7#x");
}
