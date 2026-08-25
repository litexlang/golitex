//! Capture-avoidance contracts for fact instantiation.

use crate::prelude::*;
use std::collections::HashMap;

#[test]
fn forall_alpha_rename_avoids_every_existing_bound_name() {
    let mut runtime = Runtime::new();
    runtime.start_isolated_source("forall_alpha_rename_reserved_names");
    let a_binding = runtime
        .allocate_local_symbol_binding("a".to_string())
        .unwrap();
    let n_group = runtime
        .fresh_param_group_with_type(vec!["n".to_string()], ParamType::Set(Set::new()))
        .unwrap();
    let x1_binding = runtime
        .allocate_local_symbol_binding("x1".to_string())
        .unwrap();
    let body: AtomicFact = EqualFact::new(
        BoundParamObj::new(&a_binding).into(),
        Add::new(
            BoundParamObj::new(&n_group.params[0]).into(),
            BoundParamObj::new(&x1_binding).into(),
        )
        .into(),
        default_line_file(),
    )
    .into();
    let fact = ForallFact::new_canonical_forall(
        TypedParameterList::new(vec![n_group.clone()]),
        vec![],
        vec![body.into()],
        default_line_file(),
    )
    .unwrap();
    let mut map = HashMap::new();
    insert_symbol_substitution(
        &mut map,
        &a_binding,
        BoundParamObj::new(&n_group.params[0]).into(),
    );

    let instantiated = runtime
        .inst_forall_fact(&fact, &map, SubstitutionMode::Exact, None)
        .unwrap();
    let fresh_name = instantiated.typed_parameters.groups[0].params[0].name();
    assert_ne!(fresh_name, "n");
    assert_ne!(fresh_name, "x1");
    let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(equality)) =
        &instantiated.then_facts[0]
    else {
        panic!("expected equality body");
    };
    assert!(matches!(
        &equality.left,
        Obj::Atom(AtomObj::Bound(param)) if param.name() == "n"
    ));
    assert!(matches!(
        &equality.right,
        Obj::Add(add)
            if matches!(add.left.as_ref(), Obj::Atom(AtomObj::Bound(param)) if param.name() == fresh_name)
                && matches!(add.right.as_ref(), Obj::Atom(AtomObj::Bound(param)) if param.name() == "x1")
    ));
}

#[test]
fn exist_alpha_rename_avoids_every_existing_bound_name() {
    let mut runtime = Runtime::new();
    runtime.start_isolated_source("exist_alpha_rename_reserved_names");
    let a_binding = runtime
        .allocate_local_symbol_binding("a".to_string())
        .unwrap();
    let n_group = runtime
        .fresh_param_group_with_type(vec!["n".to_string()], ParamType::Set(Set::new()))
        .unwrap();
    let x1_binding = runtime
        .allocate_local_symbol_binding("x1".to_string())
        .unwrap();
    let body: AtomicFact = EqualFact::new(
        BoundParamObj::new(&a_binding).into(),
        Add::new(
            BoundParamObj::new(&n_group.params[0]).into(),
            BoundParamObj::new(&x1_binding).into(),
        )
        .into(),
        default_line_file(),
    )
    .into();
    let fact = ExistFactEnum::ExistFact(
        ExistentialSpec::new(
            TypedParameterList::new(vec![n_group.clone()]),
            vec![body.into()],
            default_line_file(),
        )
        .unwrap(),
    );
    let mut map = HashMap::new();
    insert_symbol_substitution(
        &mut map,
        &a_binding,
        BoundParamObj::new(&n_group.params[0]).into(),
    );

    let instantiated = runtime
        .inst_exist_fact(&fact, &map, SubstitutionMode::Exact, None)
        .unwrap();
    let fresh_name = instantiated.typed_parameters().groups[0].params[0].name();
    assert_ne!(fresh_name, "n");
    assert_ne!(fresh_name, "x1");
    let QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(equality)) = &instantiated.facts()[0]
    else {
        panic!("expected equality body");
    };
    assert!(matches!(
        &equality.left,
        Obj::Atom(AtomObj::Bound(param)) if param.name() == "n"
    ));
    assert!(matches!(
        &equality.right,
        Obj::Add(add)
            if matches!(add.left.as_ref(), Obj::Atom(AtomObj::Bound(param)) if param.name() == fresh_name)
                && matches!(add.right.as_ref(), Obj::Atom(AtomObj::Bound(param)) if param.name() == "x1")
    ));
}

#[test]
fn forall_alpha_rename_respects_dependent_parameter_scope() {
    let runtime = Runtime::new();
    let outer_n = runtime
        .allocate_local_symbol_binding("n".to_string())
        .unwrap();
    let first_group = runtime
        .fresh_param_group_with_type(
            vec!["n".to_string()],
            ParamType::Obj(BoundParamObj::new(&outer_n).into()),
        )
        .unwrap();
    let second_group = runtime
        .fresh_param_group_with_type(
            vec!["m".to_string()],
            ParamType::Obj(BoundParamObj::new(&first_group.params[0]).into()),
        )
        .unwrap();
    let fact = ForallFact::new_canonical_forall(
        TypedParameterList::new(vec![first_group.clone(), second_group.clone()]),
        vec![],
        vec![AtomicFact::from(EqualFact::new(
            BoundParamObj::new(&first_group.params[0]).into(),
            BoundParamObj::new(&second_group.params[0]).into(),
            default_line_file(),
        ))
        .into()],
        default_line_file(),
    )
    .unwrap();
    let n_fresh = runtime
        .allocate_local_symbol_binding("n_fresh".to_string())
        .unwrap();
    let m_fresh = runtime
        .allocate_local_symbol_binding("m_fresh".to_string())
        .unwrap();
    let mut rename_map = HashMap::new();
    insert_symbol_substitution(
        &mut rename_map,
        &first_group.params[0],
        BoundParamObj::new(n_fresh).into(),
    );
    insert_symbol_substitution(
        &mut rename_map,
        &second_group.params[0],
        BoundParamObj::new(m_fresh).into(),
    );

    let renamed = runtime
        .alpha_rename_forall_fact(&fact, &rename_map)
        .unwrap();
    assert!(matches!(
        &renamed.typed_parameters.groups[0].param_type,
        ParamType::Obj(Obj::Atom(AtomObj::Bound(param))) if param.name() == "n"
    ));
    assert!(matches!(
        &renamed.typed_parameters.groups[1].param_type,
        ParamType::Obj(Obj::Atom(AtomObj::Bound(param))) if param.name() == "n_fresh"
    ));
    assert_eq!(
        renamed.typed_parameters.groups[0].param_names(),
        vec!["n_fresh"],
    );
    assert_eq!(
        renamed.typed_parameters.groups[1].param_names(),
        vec!["m_fresh"],
    );
}

#[test]
fn exist_alpha_rename_respects_dependent_parameter_scope() {
    let runtime = Runtime::new();
    let outer_n = runtime
        .allocate_local_symbol_binding("n".to_string())
        .unwrap();
    let first_group = runtime
        .fresh_param_group_with_type(
            vec!["n".to_string()],
            ParamType::Obj(BoundParamObj::new(&outer_n).into()),
        )
        .unwrap();
    let second_group = runtime
        .fresh_param_group_with_type(
            vec!["m".to_string()],
            ParamType::Obj(BoundParamObj::new(&first_group.params[0]).into()),
        )
        .unwrap();
    let fact = ExistFactEnum::ExistFact(
        ExistentialSpec::new(
            TypedParameterList::new(vec![first_group.clone(), second_group.clone()]),
            vec![AtomicFact::from(EqualFact::new(
                BoundParamObj::new(&first_group.params[0]).into(),
                BoundParamObj::new(&second_group.params[0]).into(),
                default_line_file(),
            ))
            .into()],
            default_line_file(),
        )
        .unwrap(),
    );
    let n_fresh = runtime
        .allocate_local_symbol_binding("n_fresh".to_string())
        .unwrap();
    let m_fresh = runtime
        .allocate_local_symbol_binding("m_fresh".to_string())
        .unwrap();
    let mut rename_map = HashMap::new();
    insert_symbol_substitution(
        &mut rename_map,
        &first_group.params[0],
        BoundParamObj::new(n_fresh).into(),
    );
    insert_symbol_substitution(
        &mut rename_map,
        &second_group.params[0],
        BoundParamObj::new(m_fresh).into(),
    );

    let renamed = runtime.alpha_rename_exist_fact(&fact, &rename_map).unwrap();
    assert!(matches!(
        &renamed.typed_parameters().groups[0].param_type,
        ParamType::Obj(Obj::Atom(AtomObj::Bound(param))) if param.name() == "n"
    ));
    assert!(matches!(
        &renamed.typed_parameters().groups[1].param_type,
        ParamType::Obj(Obj::Atom(AtomObj::Bound(param))) if param.name() == "n_fresh"
    ));
    assert_eq!(
        renamed.typed_parameters().groups[0].param_names(),
        vec!["n_fresh"],
    );
    assert_eq!(
        renamed.typed_parameters().groups[1].param_names(),
        vec!["m_fresh"],
    );
}
