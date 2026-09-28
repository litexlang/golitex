//! Tests for parameter carriers and dependency metadata.

use super::*;

#[test]
fn param_def_with_type_records_flat_cited_param_indices() {
    let runtime = Runtime::default();
    let first_group = runtime
        .fresh_param_group_with_type(
            vec!["a".to_string(), "b".to_string()],
            ParamType::Set(Set::new()),
        )
        .unwrap();
    let cited_type = Tuple::new(vec![
        BoundParamObj::new(&first_group.params[0]).into(),
        BoundParamObj::new(&first_group.params[1]).into(),
    ])
    .into();
    let param_def = TypedParameterList::new(vec![
        first_group,
        runtime
            .fresh_param_group_with_type(vec!["f".to_string()], ParamType::Obj(cited_type))
            .unwrap(),
    ]);

    assert_eq!(param_def.cited_param_indices_for_group(0), []);
    assert_eq!(param_def.cited_param_indices_for_group(1), [0, 1]);
}

#[test]
fn param_def_with_set_records_flat_cited_param_indices() {
    let runtime = Runtime::default();
    let first_group = runtime
        .fresh_param_group_with_set(vec!["n".to_string()], StandardSet::NPos.into())
        .unwrap();
    let dependent_set = ClosedRange::new(
        Number::new("1".to_string()).into(),
        BoundParamObj::new(&first_group.params[0]).into(),
    )
    .into();
    let param_def = SetBoundParameterList::new(vec![
        first_group,
        runtime
            .fresh_param_group_with_set(vec!["x".to_string()], dependent_set)
            .unwrap(),
    ]);

    assert_eq!(param_def.cited_param_indices_for_group(0), []);
    assert_eq!(param_def.cited_param_indices_for_group(1), [0]);
}

#[test]
fn dependent_param_set_instantiates_with_previous_arg() {
    let runtime = Runtime::default();
    let first_group = runtime
        .fresh_param_group_with_set(vec!["n".to_string()], StandardSet::NPos.into())
        .unwrap();
    let dependent_set = ClosedRange::new(
        Number::new("1".to_string()).into(),
        BoundParamObj::new(&first_group.params[0]).into(),
    )
    .into();
    let param_def = SetBoundParameterList::new(vec![
        first_group,
        runtime
            .fresh_param_group_with_set(vec!["x".to_string()], dependent_set)
            .unwrap(),
    ]);
    let args = vec![
        Number::new("3".to_string()).into(),
        Number::new("2".to_string()).into(),
    ];
    let instantiated = runtime
        .inst_param_def_with_set_one_by_one(&param_def, &args, SubstitutionMode::Exact)
        .unwrap();

    assert_eq!(instantiated[1].to_string(), "closed_range(1, 3)");
}
