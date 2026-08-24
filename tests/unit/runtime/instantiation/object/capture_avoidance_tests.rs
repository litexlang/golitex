//! Capture-avoidance contracts for object instantiation.

use crate::prelude::*;
use std::collections::HashMap;

#[test]
fn exact_symbol_substitution_does_not_replace_a_same_name_binding() {
    let runtime = Runtime::new();
    let target_binding = runtime
        .allocate_local_symbol_binding("x".to_string())
        .unwrap();
    let other_binding = runtime
        .allocate_local_symbol_binding("x".to_string())
        .unwrap();
    let target: Obj = DefHeaderFreeParamObj::new(&target_binding).into();
    let mut map = HashMap::new();
    insert_symbol_substitution(
        &mut map,
        &other_binding,
        Number::new("1".to_string()).into(),
    );

    let instantiated = runtime
        .inst_obj(&target, &map, ParamObjType::DefHeader)
        .unwrap();

    assert!(matches!(
        instantiated,
        Obj::Atom(AtomObj::Def(param)) if param.symbol.id() == target_binding.id()
    ));
}

#[test]
fn set_builder_instantiation_alpha_renames_only_its_own_binder_kind() {
    let mut runtime = Runtime::new();
    runtime.start_isolated_source("set_builder_capture_avoidance");
    let a_binding = runtime
        .allocate_local_symbol_binding("a".to_string())
        .unwrap();
    let n_binding = runtime
        .allocate_local_symbol_binding("n".to_string())
        .unwrap();
    let replacement_n = runtime
        .allocate_local_symbol_binding("n".to_string())
        .unwrap();
    let body_fact: AtomicFact = EqualFact::new(
        DefHeaderFreeParamObj::new(&a_binding).into(),
        SetBuilderFreeParamObj::new(&n_binding).into(),
        default_line_file(),
    )
    .into();
    let object: Obj = SetBuilder::new(
        n_binding,
        Identifier::new("n".to_string()).into(),
        vec![body_fact.into()],
    )
    .unwrap()
    .into();
    let mut map = HashMap::new();
    insert_symbol_substitution(
        &mut map,
        &a_binding,
        SetBuilderFreeParamObj::new(&replacement_n).into(),
    );

    let instantiated = runtime
        .inst_obj(&object, &map, ParamObjType::DefHeader)
        .unwrap();
    let Obj::SetBuilder(instantiated) = instantiated else {
        panic!("expected set builder");
    };
    assert_ne!(instantiated.param_name(), "n");
    assert!(matches!(
        instantiated.param_set.as_ref(),
        Obj::Atom(AtomObj::Identifier(identifier)) if identifier.name == "n"
    ));
    let QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(equality)) = &instantiated.facts[0]
    else {
        panic!("expected equality body");
    };
    assert!(matches!(
        &equality.left,
        Obj::Atom(AtomObj::SetBuilder(param)) if param.name() == "n"
    ));
    assert!(matches!(
        &equality.right,
        Obj::Atom(AtomObj::SetBuilder(param)) if param.name() == instantiated.param_name()
    ));
}

#[test]
fn surviving_closed_set_builder_replacement_keeps_outer_binder_fresh() {
    let mut runtime = Runtime::new();
    runtime.start_isolated_source("closed_set_builder_replacement");
    let a_binding = runtime
        .allocate_local_symbol_binding("a".to_string())
        .unwrap();
    let target_n = runtime
        .allocate_local_symbol_binding("n".to_string())
        .unwrap();
    let target: Obj = SetBuilder::new(
        target_n.clone(),
        StandardSet::R.into(),
        vec![EqualFact::new(
            DefHeaderFreeParamObj::new(&a_binding).into(),
            SetBuilderFreeParamObj::new(&target_n).into(),
            default_line_file(),
        )
        .into()],
    )
    .unwrap()
    .into();
    let replacement_n = runtime
        .allocate_local_symbol_binding("n".to_string())
        .unwrap();
    let replacement: Obj = SetBuilder::new(
        replacement_n.clone(),
        StandardSet::R.into(),
        vec![EqualFact::new(
            SetBuilderFreeParamObj::new(&replacement_n).into(),
            SetBuilderFreeParamObj::new(&replacement_n).into(),
            default_line_file(),
        )
        .into()],
    )
    .unwrap()
    .into();
    let mut map = HashMap::new();
    insert_symbol_substitution(&mut map, &a_binding, replacement);

    let instantiated = runtime
        .inst_obj(&target, &map, ParamObjType::DefHeader)
        .unwrap();
    let Obj::SetBuilder(instantiated) = instantiated else {
        panic!("expected set builder");
    };
    assert_ne!(instantiated.param_name(), "n");

    let unused_n = runtime
        .allocate_local_symbol_binding("n".to_string())
        .unwrap();
    let unused_target: Obj = SetBuilder::new(
        unused_n.clone(),
        StandardSet::R.into(),
        vec![EqualFact::new(
            SetBuilderFreeParamObj::new(&unused_n).into(),
            SetBuilderFreeParamObj::new(&unused_n).into(),
            default_line_file(),
        )
        .into()],
    )
    .unwrap()
    .into();
    let restored = runtime
        .inst_obj(&unused_target, &map, ParamObjType::DefHeader)
        .unwrap();
    let Obj::SetBuilder(restored) = restored else {
        panic!("expected set builder");
    };
    assert_eq!(restored.param_name(), "n");
}

#[test]
fn function_binder_instantiation_preserves_outer_argument_and_concrete_type() {
    let mut runtime = Runtime::new();
    runtime.start_isolated_source("function_binder_capture_avoidance");
    let a_binding = runtime
        .allocate_local_symbol_binding("a".to_string())
        .unwrap();
    let group = runtime
        .fresh_param_group_with_set(
            vec!["n".to_string()],
            Identifier::new("n".to_string()).into(),
        )
        .unwrap();
    let n_binding = group.params[0].clone();
    let dom_fact: AtomicFact = EqualFact::new(
        DefHeaderFreeParamObj::new(&a_binding).into(),
        FnSetFreeParamObj::new(&n_binding).into(),
        default_line_file(),
    )
    .into();
    let object: Obj = FnSet::new(
        vec![group],
        vec![dom_fact.into()],
        Identifier::new("ret".to_string()).into(),
    )
    .unwrap()
    .into();
    let replacement_n = runtime
        .allocate_local_symbol_binding("n".to_string())
        .unwrap();
    let mut map = HashMap::new();
    insert_symbol_substitution(
        &mut map,
        &a_binding,
        FnSetFreeParamObj::new(&replacement_n).into(),
    );

    let instantiated = runtime
        .inst_obj(&object, &map, ParamObjType::DefHeader)
        .unwrap();
    let Obj::FnSet(instantiated) = instantiated else {
        panic!("expected function set");
    };
    let fresh_name = instantiated.body.params_def_with_set[0].params[0].name();
    assert_ne!(fresh_name, "n");
    assert!(matches!(
        instantiated.body.params_def_with_set[0].set_obj(),
        Obj::Atom(AtomObj::Identifier(identifier)) if identifier.name == "n"
    ));
    let QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(equality)) =
        &instantiated.body.dom_facts[0]
    else {
        panic!("expected equality domain fact");
    };
    assert!(matches!(
        &equality.left,
        Obj::Atom(AtomObj::FnSet(param)) if param.name() == "n"
    ));
    assert!(matches!(
        &equality.right,
        Obj::Atom(AtomObj::FnSet(param)) if param.name() == fresh_name
    ));
}

#[test]
fn anonymous_function_restores_binder_only_after_collision_disappears() {
    let mut runtime = Runtime::new();
    runtime.start_isolated_source("closed_anonymous_function_replacement");
    let f_binding = runtime
        .allocate_local_symbol_binding("f".to_string())
        .unwrap();
    let target_group = runtime
        .fresh_param_group_with_set(vec!["x".to_string()], StandardSet::R.into())
        .unwrap();
    let target: Obj = AnonymousFn::new(
        vec![target_group],
        vec![],
        StandardSet::R.into(),
        DefHeaderFreeParamObj::new(&f_binding).into(),
    )
    .unwrap()
    .into();
    let replacement_group = runtime
        .fresh_param_group_with_set(vec!["x".to_string()], StandardSet::R.into())
        .unwrap();
    let replacement_x = replacement_group.params[0].clone();
    let replacement: Obj = AnonymousFn::new(
        vec![replacement_group],
        vec![],
        StandardSet::R.into(),
        FnSetFreeParamObj::new(&replacement_x).into(),
    )
    .unwrap()
    .into();
    let mut map = HashMap::new();
    insert_symbol_substitution(&mut map, &f_binding, replacement);

    let instantiated = runtime
        .inst_obj(&target, &map, ParamObjType::DefHeader)
        .unwrap();
    let Obj::AnonymousFn(instantiated) = instantiated else {
        panic!("expected anonymous function");
    };
    assert_ne!(
        instantiated.body.params_def_with_set[0].param_names(),
        vec!["x"]
    );

    let beta_group = runtime
        .fresh_param_group_with_set(vec!["x".to_string()], StandardSet::R.into())
        .unwrap();
    let beta_x = beta_group.params[0].clone();
    let theorem_f = runtime
        .allocate_local_symbol_binding("f".to_string())
        .unwrap();
    let beta_target: Obj = AnonymousFn::new(
        vec![beta_group],
        vec![],
        StandardSet::R.into(),
        FnObj::new(
            ForallFreeParamObj::new(&theorem_f).into(),
            vec![vec![Box::new(FnSetFreeParamObj::new(&beta_x).into())]],
        )
        .into(),
    )
    .unwrap()
    .into();
    let mut theorem_map = HashMap::new();
    insert_symbol_substitution(&mut theorem_map, &theorem_f, map["f"].clone());
    let restored = runtime
        .inst_obj(
            &beta_target,
            &theorem_map,
            ParamObjType::TheoremInstantiation,
        )
        .unwrap();
    let Obj::AnonymousFn(restored) = restored else {
        panic!("expected anonymous function");
    };
    assert_eq!(
        restored.body.params_def_with_set[0].param_names(),
        vec!["x"]
    );
}

#[test]
fn set_builder_alpha_rename_updates_a_dependent_parameter_set() {
    let mut runtime = Runtime::new();
    runtime.start_isolated_source("set_builder_dependent_type_alpha_rename");
    let n_binding = runtime
        .allocate_local_symbol_binding("n".to_string())
        .unwrap();
    let a_binding = runtime
        .allocate_local_symbol_binding("a".to_string())
        .unwrap();
    let object: Obj = SetBuilder::new(
        n_binding.clone(),
        SetBuilderFreeParamObj::new(&n_binding).into(),
        vec![EqualFact::new(
            DefHeaderFreeParamObj::new(&a_binding).into(),
            SetBuilderFreeParamObj::new(&n_binding).into(),
            default_line_file(),
        )
        .into()],
    )
    .unwrap()
    .into();
    let replacement_n = runtime
        .allocate_local_symbol_binding("n".to_string())
        .unwrap();
    let mut map = HashMap::new();
    insert_symbol_substitution(
        &mut map,
        &a_binding,
        SetBuilderFreeParamObj::new(&replacement_n).into(),
    );

    let instantiated = runtime
        .inst_obj(&object, &map, ParamObjType::DefHeader)
        .unwrap();
    let Obj::SetBuilder(instantiated) = instantiated else {
        panic!("expected set builder");
    };
    assert_ne!(instantiated.param_name(), "n");
    assert!(matches!(
        instantiated.param_set.as_ref(),
        Obj::Atom(AtomObj::SetBuilder(param)) if param.name() == instantiated.param_name()
    ));
}

#[test]
fn function_alpha_rename_respects_dependent_parameter_scope() {
    let runtime = Runtime::new();
    let external_n = runtime
        .allocate_local_symbol_binding("n".to_string())
        .unwrap();
    let n_group = runtime
        .fresh_param_group_with_set(
            vec!["n".to_string()],
            FnSetFreeParamObj::new(&external_n).into(),
        )
        .unwrap();
    let n_binding = n_group.params[0].clone();
    let m_group = runtime
        .fresh_param_group_with_set(
            vec!["m".to_string()],
            FnSetFreeParamObj::new(&n_binding).into(),
        )
        .unwrap();
    let m_binding = m_group.params[0].clone();
    let body = FnSetBody::new(
        vec![n_group, m_group],
        vec![],
        FnSetFreeParamObj::new(&m_binding).into(),
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
        &n_binding,
        FnSetFreeParamObj::new(&n_fresh).into(),
    );
    insert_symbol_substitution(
        &mut rename_map,
        &m_binding,
        FnSetFreeParamObj::new(&m_fresh).into(),
    );

    let renamed = runtime
        .alpha_rename_fn_set_body(&body, &rename_map)
        .unwrap();
    assert!(matches!(
        renamed.params_def_with_set[0].set_obj(),
        Obj::Atom(AtomObj::FnSet(param)) if param.name() == "n"
    ));
    assert!(matches!(
        renamed.params_def_with_set[1].set_obj(),
        Obj::Atom(AtomObj::FnSet(param)) if param.name() == "n_fresh"
    ));
    assert_eq!(
        renamed.params_def_with_set[0].param_names(),
        vec!["n_fresh"]
    );
    assert_eq!(
        renamed.params_def_with_set[1].param_names(),
        vec!["m_fresh"]
    );
    assert!(matches!(
        renamed.ret_set.as_ref(),
        Obj::Atom(AtomObj::FnSet(param)) if param.name() == "m_fresh"
    ));
}
